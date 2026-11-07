/* filetree - small, fast terminal file tree browser.
 *
 * Data-oriented: the visible tree is a flat struct-of-arrays (one array per
 * attribute), names live in one append-only arena, the frame is built in one
 * buffer and written with a single write().
 */
#define _GNU_SOURCE
#include <errno.h>
#include <dirent.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <ftw.h>
#include <grp.h>
#include <limits.h>
#include <poll.h>
#include <pwd.h>
#include <setjmp.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#include <jpeglib.h>
#include <png.h>

#define NOLINK 0xFFFFFFFFu
#define MAXDEPTH 1000
#define TEXT_MAX (256 * 1024)
#define MAX_PIXELS (64u * 1024 * 1024)

/* ------------------------------------------------------------------ utils */

static void *xrealloc(void *p, size_t n)
{
	p = realloc(p, n ? n : 1);
	if (!p) { fputs("filetree: out of memory\n", stderr); exit(1); }
	return p;
}

typedef struct { char *p; size_t n, cap; } Buf;

static void b_reserve(Buf *b, size_t add)
{
	if (b->n + add + 1 > b->cap) {
		size_t c = b->cap ? b->cap : 1 << 16;
		while (c < b->n + add + 1) c *= 2;
		b->p = xrealloc(b->p, c);
		b->cap = c;
	}
}
static void b_put(Buf *b, const char *s, size_t l) { b_reserve(b, l); memcpy(b->p + b->n, s, l); b->n += l; }
static void b_str(Buf *b, const char *s) { b_put(b, s, strlen(s)); }
static void b_rep(Buf *b, char c, int n)
{
	if (n <= 0) return;
	b_reserve(b, n); memset(b->p + b->n, c, n); b->n += n;
}
static void b_fmt(Buf *b, const char *fmt, ...)
{
	char tmp[128];
	va_list ap; va_start(ap, fmt);
	int l = vsnprintf(tmp, sizeof tmp, fmt, ap);
	va_end(ap);
	if (l > 0) b_put(b, tmp, l < (int)sizeof tmp ? l : (int)sizeof tmp - 1);
}

/* Append s (len bytes) clipped to maxcols columns (1 column per codepoint,
 * control characters shown as '?'). Returns columns used. */
static int put_cols(Buf *b, const char *s, size_t len, int maxcols)
{
	int cols = 0;
	size_t i = 0;
	while (i < len && cols < maxcols) {
		unsigned char c = s[i];
		size_t cl = c < 0x80 ? 1 : c >= 0xF0 ? 4 : c >= 0xE0 ? 3 : c >= 0xC0 ? 2 : 1;
		if (i + cl > len) cl = len - i;
		if (c < 0x20 || c == 0x7f) b_put(b, "?", 1);
		else b_put(b, s + i, cl);
		i += cl; cols++;
	}
	return cols;
}

/* ------------------------------------------------------------ tree (SoA) */

enum { F_DIR = 1, F_EXP = 2, F_SEL = 4, F_LNK = 8, F_EXE = 16 };

#define FIELDS(X) \
	X(name, uint32_t) X(mode, uint32_t) X(uid, uint32_t) X(gid, uint32_t) \
	X(link, uint32_t) X(size, int64_t) X(mtime, int64_t) X(depth, uint16_t) X(flags, uint8_t)

typedef struct {
	uint32_t n, cap;
#define X(f, t) t *f;
	FIELDS(X)
#undef X
} Tree;

static Tree T;
static char *arena; static size_t arena_n, arena_cap;
static char root[PATH_MAX]; static size_t rootlen;

static uint32_t arena_add(const char *s, size_t len)
{
	if (arena_n + len + 1 > arena_cap) {
		arena_cap = arena_cap ? arena_cap * 2 : 1 << 16;
		while (arena_cap < arena_n + len + 1) arena_cap *= 2;
		arena = xrealloc(arena, arena_cap);
	}
	uint32_t off = arena_n;
	memcpy(arena + arena_n, s, len); arena[arena_n + len] = 0;
	arena_n += len + 1;
	return off;
}
#define NAME(i) (arena + T.name[i])

static void tree_reserve(Tree *t, uint32_t cap)
{
	if (cap <= t->cap) return;
	if (cap < 64) cap = 64;
	uint32_t c = t->cap ? t->cap : 64;
	while (c < cap) c *= 2;
#define X(f, ty) t->f = xrealloc(t->f, c * sizeof(ty));
	FIELDS(X)
#undef X
	t->cap = c;
}
static void tree_gap(Tree *t, uint32_t pos, uint32_t k)
{
	tree_reserve(t, t->n + k);
#define X(f, ty) memmove(t->f + pos + k, t->f + pos, (t->n - pos) * sizeof(ty));
	FIELDS(X)
#undef X
	t->n += k;
}
static void tree_cut(Tree *t, uint32_t pos, uint32_t k)
{
#define X(f, ty) memmove(t->f + pos, t->f + pos + k, (t->n - pos - k) * sizeof(ty));
	FIELDS(X)
#undef X
	t->n -= k;
}
static void tree_free(Tree *t)
{
#define X(f, ty) free(t->f);
	FIELDS(X)
#undef X
	memset(t, 0, sizeof *t);
}

/* Absolute path of row i. */
static void row_path(uint32_t i, char *out)
{
	uint32_t idx[MAXDEPTH + 2];
	int d = T.depth[i];
	idx[d] = i;
	uint32_t cur = i;
	for (int dd = d; dd > 0; dd--) {
		while (T.depth[--cur] != dd - 1) ;
		idx[dd - 1] = cur;
	}
	size_t o = rootlen;
	memcpy(out, root, rootlen);
	for (int dd = 0; dd <= d; dd++) {
		const char *nm = NAME(idx[dd]);
		size_t l = strlen(nm);
		if (o + l + 2 >= PATH_MAX) break;
		out[o++] = '/';
		memcpy(out + o, nm, l); o += l;
	}
	out[o] = 0;
}

/* ------------------------------------------------------------- selection */

static char **sel; static size_t sel_n, sel_cap;

static long sel_find(const char *p)
{
	for (size_t i = 0; i < sel_n; i++) if (!strcmp(sel[i], p)) return i;
	return -1;
}
static void sel_clear(void)
{
	for (size_t i = 0; i < sel_n; i++) free(sel[i]);
	sel_n = 0;
	for (uint32_t i = 0; i < T.n; i++) T.flags[i] &= ~F_SEL;
}
static void sel_toggle(uint32_t i)
{
	char p[PATH_MAX]; row_path(i, p);
	long f = sel_find(p);
	if (f >= 0) { free(sel[f]); sel[f] = sel[--sel_n]; T.flags[i] &= ~F_SEL; }
	else {
		if (sel_n == sel_cap) { sel_cap = sel_cap ? sel_cap * 2 : 16; sel = xrealloc(sel, sel_cap * sizeof *sel); }
		sel[sel_n++] = strdup(p);
		T.flags[i] |= F_SEL;
	}
}

/* ------------------------------------------------------------ dir loading */

static const Tree *sort_t;
static int cmp_perm(const void *a, const void *b)
{
	uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
	int dx = sort_t->flags[x] & F_DIR, dy = sort_t->flags[y] & F_DIR;
	if (dx != dy) return dy - dx;
	const char *nx = arena + sort_t->name[x], *ny = arena + sort_t->name[y];
	int c = strcasecmp(nx, ny);
	return c ? c : strcmp(nx, ny);
}

/* Read directory `path` and splice its entries in at row `pos`. */
static int load_dir(const char *path, int depth, uint32_t pos)
{
	int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
	if (fd < 0) return -1;
	DIR *d = fdopendir(fd);
	if (!d) { close(fd); return -1; }
	Tree t = {0};
	struct dirent *e;
	while ((e = readdir(d))) {
		if (e->d_name[0] == '.' && (!e->d_name[1] || (e->d_name[1] == '.' && !e->d_name[2]))) continue;
		struct stat st;
		if (fstatat(fd, e->d_name, &st, AT_SYMLINK_NOFOLLOW) < 0) continue;
		tree_reserve(&t, t.n + 1);
		uint32_t k = t.n++;
		uint8_t fl = 0;
		t.link[k] = NOLINK;
		if (S_ISDIR(st.st_mode)) fl |= F_DIR;
		else if (S_ISLNK(st.st_mode)) {
			fl |= F_LNK;
			char tg[PATH_MAX];
			ssize_t l = readlinkat(fd, e->d_name, tg, sizeof tg - 1);
			if (l > 0) t.link[k] = arena_add(tg, l);
		} else if (S_ISREG(st.st_mode) && (st.st_mode & 0111)) fl |= F_EXE;
		t.name[k] = arena_add(e->d_name, strlen(e->d_name));
		t.mode[k] = st.st_mode; t.uid[k] = st.st_uid; t.gid[k] = st.st_gid;
		t.size[k] = S_ISDIR(st.st_mode) ? -1 : st.st_size;
		t.mtime[k] = st.st_mtime; t.flags[k] = fl;
	}
	closedir(d);
	uint32_t *perm = xrealloc(NULL, (t.n + 1) * sizeof *perm);
	for (uint32_t i = 0; i < t.n; i++) perm[i] = i;
	sort_t = &t;
	qsort(perm, t.n, sizeof *perm, cmp_perm);
	tree_gap(&T, pos, t.n);
	for (uint32_t i = 0; i < t.n; i++) {
		uint32_t s = perm[i], o = pos + i;
#define X(f, ty) T.f[o] = t.f[s];
		FIELDS(X)
#undef X
		T.depth[o] = depth;
	}
	if (sel_n) {
		for (uint32_t i = 0; i < t.n; i++) {
			char p[PATH_MAX]; row_path(pos + i, p);
			if (sel_find(p) >= 0) T.flags[pos + i] |= F_SEL;
		}
	}
	free(perm);
	tree_free(&t);
	return 0;
}

static char status[256];

static void expand(uint32_t i)
{
	if (!(T.flags[i] & F_DIR) || (T.flags[i] & F_EXP)) return;
	if (T.depth[i] >= MAXDEPTH) return;
	char p[PATH_MAX]; row_path(i, p);
	if (load_dir(p, T.depth[i] + 1, i + 1) < 0) {
		snprintf(status, sizeof status, "cannot open %.150s: %s", p, strerror(errno));
		return;
	}
	T.flags[i] |= F_EXP;
}
static void collapse(uint32_t i)
{
	if (!(T.flags[i] & F_EXP)) return;
	uint32_t e = i + 1;
	while (e < T.n && T.depth[e] > T.depth[i]) e++;
	tree_cut(&T, i + 1, e - i - 1);
	T.flags[i] &= ~F_EXP;
}

static uint32_t cur, top;

/* Reload everything from disk, keeping expanded dirs and the cursor. */
static void rebuild(void)
{
	char **exp = NULL; size_t en = 0, ec = 0;
	char curp[PATH_MAX] = "";
	if (T.n) row_path(cur, curp);
	for (uint32_t i = 0; i < T.n; i++) if (T.flags[i] & F_EXP) {
		char p[PATH_MAX]; row_path(i, p);
		if (en == ec) { ec = ec ? ec * 2 : 16; exp = xrealloc(exp, ec * sizeof *exp); }
		exp[en++] = strdup(p);
	}
	tree_free(&T); arena_n = 0;
	load_dir(root[0] ? root : "/", 0, 0);
	for (uint32_t i = 0; i < T.n; i++) {
		if (!(T.flags[i] & F_DIR)) continue;
		char p[PATH_MAX]; row_path(i, p);
		for (size_t k = 0; k < en; k++) if (!strcmp(exp[k], p)) { expand(i); break; }
	}
	for (size_t k = 0; k < en; k++) free(exp[k]);
	free(exp);
	uint32_t found = cur < T.n ? cur : (T.n ? T.n - 1 : 0);
	if (curp[0]) for (uint32_t i = 0; i < T.n; i++) {
		char p[PATH_MAX]; row_path(i, p);
		if (!strcmp(p, curp)) { found = i; break; }
	}
	cur = found;
}

/* ------------------------------------------------------- image libraries */

typedef struct {
	int (*png_begin)(png_imagep, const char *);
	int (*png_finish)(png_imagep, png_const_colorp, void *, png_int_32, void *);
	void (*png_free)(png_imagep);
	struct jpeg_error_mgr *(*j_std_error)(struct jpeg_error_mgr *);
	void (*j_create)(j_decompress_ptr, int, size_t);
	void (*j_stdio_src)(j_decompress_ptr, FILE *);
	int (*j_read_header)(j_decompress_ptr, boolean);
	boolean (*j_start)(j_decompress_ptr);
	JDIMENSION (*j_scanlines)(j_decompress_ptr, JSAMPARRAY, JDIMENSION);
	boolean (*j_finish)(j_decompress_ptr);
	void (*j_destroy)(j_decompress_ptr);
} ImgLib;

static ImgLib L;
static int png_state, jpg_state; /* 0 = untried, 1 = ready, -1 = unavailable */

#ifdef STATIC_IMAGE_LIBS
static int load_png_lib(void)
{
	L.png_begin = png_image_begin_read_from_file;
	L.png_finish = png_image_finish_read;
	L.png_free = png_image_free;
	return 1;
}
static int load_jpg_lib(void)
{
	L.j_std_error = jpeg_std_error; L.j_create = jpeg_CreateDecompress;
	L.j_stdio_src = jpeg_stdio_src; L.j_read_header = jpeg_read_header;
	L.j_start = jpeg_start_decompress; L.j_scanlines = jpeg_read_scanlines;
	L.j_finish = jpeg_finish_decompress; L.j_destroy = jpeg_destroy_decompress;
	return 1;
}
#else
static void *open_any(const char *const *names)
{
	for (; *names; names++) {
		void *h = dlopen(*names, RTLD_LAZY | RTLD_LOCAL);
		if (h) return h;
	}
	return NULL;
}
static int load_png_lib(void)
{
	static const char *const names[] = { "libpng16.so.16", "libpng.so", NULL };
	void *h = open_any(names);
	if (!h) return 0;
	*(void **)&L.png_begin = dlsym(h, "png_image_begin_read_from_file");
	*(void **)&L.png_finish = dlsym(h, "png_image_finish_read");
	*(void **)&L.png_free = dlsym(h, "png_image_free");
	return L.png_begin && L.png_finish && L.png_free;
}
static int load_jpg_lib(void)
{
	static const char *const names[] = { "libjpeg.so.8", "libjpeg.so.62", "libjpeg.so", NULL };
	void *h = open_any(names);
	if (!h) return 0;
	*(void **)&L.j_std_error = dlsym(h, "jpeg_std_error");
	*(void **)&L.j_create = dlsym(h, "jpeg_CreateDecompress");
	*(void **)&L.j_stdio_src = dlsym(h, "jpeg_stdio_src");
	*(void **)&L.j_read_header = dlsym(h, "jpeg_read_header");
	*(void **)&L.j_start = dlsym(h, "jpeg_start_decompress");
	*(void **)&L.j_scanlines = dlsym(h, "jpeg_read_scanlines");
	*(void **)&L.j_finish = dlsym(h, "jpeg_finish_decompress");
	*(void **)&L.j_destroy = dlsym(h, "jpeg_destroy_decompress");
	return L.j_std_error && L.j_create && L.j_stdio_src && L.j_read_header &&
	       L.j_start && L.j_scanlines && L.j_finish && L.j_destroy;
}
#endif

/* Decode to packed RGB. Returns malloc'd buffer or NULL (err set). */
static uint8_t *img_load_png(const char *path, int *w, int *h, const char **err)
{
	if (!png_state) png_state = load_png_lib() ? 1 : -1;
	if (png_state < 0) { *err = "libpng not available"; return NULL; }
	png_image im; memset(&im, 0, sizeof im);
	im.version = PNG_IMAGE_VERSION;
	if (!L.png_begin(&im, path)) { L.png_free(&im); *err = "cannot read PNG"; return NULL; }
	if ((uint64_t)im.width * im.height > MAX_PIXELS) { L.png_free(&im); *err = "image too large"; return NULL; }
	im.format = PNG_FORMAT_RGB;
	uint8_t *buf = malloc(PNG_IMAGE_SIZE(im));
	png_color bg = { 0x30, 0x30, 0x30 };
	if (!buf || !L.png_finish(&im, &bg, buf, 0, NULL)) {
		free(buf); L.png_free(&im); *err = "cannot decode PNG"; return NULL;
	}
	*w = im.width; *h = im.height;
	L.png_free(&im);
	return buf;
}

struct jerr { struct jpeg_error_mgr pub; jmp_buf jb; };
static void jerr_exit(j_common_ptr c) { longjmp(((struct jerr *)c->err)->jb, 1); }

static uint8_t *img_load_jpeg(const char *path, int tw, int th, int *w, int *h, const char **err)
{
	if (!jpg_state) jpg_state = load_jpg_lib() ? 1 : -1;
	if (jpg_state < 0) { *err = "libjpeg not available"; return NULL; }
	FILE *f = fopen(path, "rb");
	if (!f) { *err = "cannot open file"; return NULL; }
	struct jpeg_decompress_struct ci;
	struct jerr je;
	uint8_t *volatile buf = NULL;
	memset(&ci, 0, sizeof ci);
	ci.err = L.j_std_error(&je.pub);
	je.pub.error_exit = jerr_exit;
	if (setjmp(je.jb)) {
		L.j_destroy(&ci); fclose(f); free(buf);
		*err = "cannot decode JPEG"; return NULL;
	}
	L.j_create(&ci, JPEG_LIB_VERSION, sizeof ci);
	L.j_stdio_src(&ci, f);
	L.j_read_header(&ci, TRUE);
	if ((uint64_t)ci.image_width * ci.image_height > 4 * (uint64_t)MAX_PIXELS) {
		L.j_destroy(&ci); fclose(f); *err = "image too large"; return NULL;
	}
	ci.out_color_space = JCS_RGB;
	int den = 1;
	while (den < 8 && (int)(ci.image_width / (den * 2)) >= tw && (int)(ci.image_height / (den * 2)) >= th) den *= 2;
	ci.scale_num = 1; ci.scale_denom = den;
	L.j_start(&ci);
	if (ci.output_components != 3) longjmp(je.jb, 1);
	size_t stride = (size_t)ci.output_width * 3;
	buf = malloc(stride * ci.output_height);
	if (!buf) longjmp(je.jb, 1);
	while (ci.output_scanline < ci.output_height) {
		JSAMPROW row = buf + (size_t)ci.output_scanline * stride;
		L.j_scanlines(&ci, &row, 1);
	}
	*w = ci.output_width; *h = ci.output_height;
	L.j_finish(&ci); L.j_destroy(&ci); fclose(f);
	return buf;
}

/* --------------------------------------------------------------- preview */

enum { P_NONE, P_MSG, P_TEXT, P_IMAGE };

static struct {
	char path[PATH_MAX];
	int valid, kind;
	char msg[128];
	/* text */
	char *text; size_t tlen;
	uint32_t *lines; uint32_t nlines, maxlen;
	uint32_t py, px;
	/* image */
	uint8_t *rgb; int iw, ih;
	uint8_t *scaled; int sw, sh, key_w, key_h;
} P;

static int term_w = 80, term_h = 24;

static void preview_free(void)
{
	free(P.text); free(P.lines); free(P.rgb); free(P.scaled);
	P.text = NULL; P.lines = NULL; P.rgb = NULL; P.scaled = NULL;
	P.tlen = P.nlines = P.maxlen = P.py = P.px = 0;
	P.iw = P.ih = P.sw = P.sh = P.key_w = P.key_h = 0;
	P.kind = P_NONE; P.msg[0] = 0;
}
static void preview_msg(const char *m) { P.kind = P_MSG; snprintf(P.msg, sizeof P.msg, "%s", m); }

static void preview_load(const char *path)
{
	struct stat st;
	if (stat(path, &st) < 0) { preview_msg(strerror(errno)); return; }
	if (S_ISDIR(st.st_mode)) return;
	if (!S_ISREG(st.st_mode)) { preview_msg("(not a regular file)"); return; }
	int fd = open(path, O_RDONLY | O_CLOEXEC | O_NONBLOCK);
	if (fd < 0) { preview_msg(strerror(errno)); return; }
	char *buf = xrealloc(NULL, TEXT_MAX + 1);
	ssize_t n = read(fd, buf, TEXT_MAX);
	close(fd);
	if (n < 0) { free(buf); preview_msg(strerror(errno)); return; }
	if (n >= 8 && !memcmp(buf, "\x89PNG\r\n\x1a\n", 8)) goto image_png;
	if (n >= 3 && !memcmp(buf, "\xff\xd8\xff", 3)) goto image_jpg;
	if (memchr(buf, 0, n < 4096 ? n : 4096)) { free(buf); preview_msg("(binary file)"); return; }
	P.kind = P_TEXT; P.text = buf; P.tlen = n;
	uint32_t cap = 256, cnt = 0, mx = 0, start = 0;
	P.lines = xrealloc(NULL, cap * sizeof *P.lines);
	P.lines[cnt++] = 0;
	for (ssize_t i = 0; i < n; i++) {
		if (buf[i] != '\n') continue;
		if (i - start > mx) mx = i - start;
		start = i + 1;
		if (start >= (size_t)n) break;
		if (cnt == cap) { cap *= 2; P.lines = xrealloc(P.lines, cap * sizeof *P.lines); }
		P.lines[cnt++] = start;
	}
	if (n - start > mx) mx = n - start;
	P.nlines = cnt; P.maxlen = mx;
	return;
image_png: ;
	free(buf);
	const char *err = "";
	P.rgb = img_load_png(path, &P.iw, &P.ih, &err);
	if (!P.rgb) { preview_msg(err); return; }
	P.kind = P_IMAGE;
	return;
image_jpg: ;
	free(buf);
	err = "";
	P.rgb = img_load_jpeg(path, term_w / 2, (term_h - 2) * 2, &P.iw, &P.ih, &err);
	if (!P.rgb) { preview_msg(err); return; }
	P.kind = P_IMAGE;
}

static void preview_update(void)
{
	char p[PATH_MAX] = "";
	if (T.n) row_path(cur, p);
	if (P.valid && !strcmp(p, P.path)) return;
	preview_free();
	snprintf(P.path, sizeof P.path, "%s", p);
	P.valid = 1;
	if (p[0]) preview_load(p);
}

/* Box-filter the decoded image to fit pw x ph cells (2 pixel rows per cell). */
static void preview_scale(int pw, int ph)
{
	if (P.kind != P_IMAGE || pw < 1 || ph < 1) return;
	if (P.scaled && P.key_w == pw && P.key_h == ph) return;
	free(P.scaled);
	double s = (double)pw / P.iw, s2 = (double)(2 * ph) / P.ih;
	if (s2 < s) s = s2;
	int tw = (int)(P.iw * s), th = (int)(P.ih * s);
	if (tw < 1) tw = 1;
	if (th < 1) th = 1;
	P.scaled = xrealloc(NULL, (size_t)tw * th * 3);
	for (int y = 0; y < th; y++) {
		int y0 = (int)((int64_t)y * P.ih / th), y1 = (int)((int64_t)(y + 1) * P.ih / th);
		if (y1 <= y0) y1 = y0 + 1;
		for (int x = 0; x < tw; x++) {
			int x0 = (int)((int64_t)x * P.iw / tw), x1 = (int)((int64_t)(x + 1) * P.iw / tw);
			if (x1 <= x0) x1 = x0 + 1;
			unsigned r = 0, g = 0, b = 0, c = 0;
			for (int yy = y0; yy < y1; yy++) {
				const uint8_t *px = P.rgb + ((size_t)yy * P.iw + x0) * 3;
				for (int xx = x0; xx < x1; xx++, px += 3) { r += px[0]; g += px[1]; b += px[2]; c++; }
			}
			uint8_t *o = P.scaled + ((size_t)y * tw + x) * 3;
			o[0] = r / c; o[1] = g / c; o[2] = b / c;
		}
	}
	P.sw = tw; P.sh = th; P.key_w = pw; P.key_h = ph;
}

static void render_text_line(Buf *b, const char *s, size_t len, uint32_t skip, int maxcols)
{
	int out = 0;
	uint32_t col = 0;
	size_t i = 0;
	if (len && s[len - 1] == '\r') len--;
	while (i < len && out < maxcols) {
		unsigned char c = s[i];
		if (c == '\t') {
			uint32_t w = 4 - (col & 3);
			for (uint32_t k = 0; k < w && out < maxcols; k++, col++)
				if (col >= skip) { b_put(b, " ", 1); out++; }
			i++; continue;
		}
		size_t cl = c < 0x80 ? 1 : c >= 0xF0 ? 4 : c >= 0xE0 ? 3 : c >= 0xC0 ? 2 : 1;
		if (i + cl > len) cl = len - i;
		if (col >= skip) {
			if (c < 0x20 || c == 0x7f) b_put(b, "?", 1); else b_put(b, s + i, cl);
			out++;
		}
		col++; i += cl;
	}
	b_rep(b, ' ', maxcols - out);
}

static void preview_row(Buf *b, int r, int w)
{
	if (w <= 0) return;
	if (P.kind == P_TEXT) {
		uint32_t ln = P.py + r;
		if (ln < P.nlines) {
			size_t s = P.lines[ln];
			size_t e = ln + 1 < P.nlines ? P.lines[ln + 1] - 1 : P.tlen;
			render_text_line(b, P.text + s, e - s, P.px, w);
		} else b_rep(b, ' ', w);
	} else if (P.kind == P_IMAGE && P.scaled && 2 * r < P.sh) {
		int used = P.sw < w ? P.sw : w;
		const uint8_t *top = P.scaled + (size_t)(2 * r) * P.sw * 3;
		const uint8_t *bot = 2 * r + 1 < P.sh ? top + (size_t)P.sw * 3 : NULL;
		for (int x = 0; x < used; x++) {
			b_fmt(b, "\x1b[38;2;%d;%d;%dm", top[x * 3], top[x * 3 + 1], top[x * 3 + 2]);
			if (bot) b_fmt(b, "\x1b[48;2;%d;%d;%dm", bot[x * 3], bot[x * 3 + 1], bot[x * 3 + 2]);
			else b_str(b, "\x1b[49m");
			b_str(b, "\xe2\x96\x80");
		}
		b_str(b, "\x1b[0m");
		b_rep(b, ' ', w - used);
	} else if (P.kind == P_MSG && r == 0) {
		b_str(b, "\x1b[2m");
		int c = put_cols(b, P.msg, strlen(P.msg), w);
		b_str(b, "\x1b[0m");
		b_rep(b, ' ', w - c);
	} else b_rep(b, ' ', w);
}

static void preview_scroll(int dy, int dx)
{
	if (P.kind != P_TEXT) return;
	int64_t y = (int64_t)P.py + dy, x = (int64_t)P.px + dx;
	if (y < 0) y = 0;
	if (y >= (int64_t)P.nlines) y = P.nlines - 1;
	if (x < 0) x = 0;
	if (x > (int64_t)P.maxlen) x = P.maxlen;
	P.py = y; P.px = x;
}

/* ------------------------------------------------------------ rendering */

#define IDC 64
static struct { uint32_t id; int ok; char name[32]; } ucache[IDC], gcache[IDC];

static const char *idname(uint32_t id, int group)
{
	typeof(ucache[0]) *c = &(group ? gcache : ucache)[id % IDC];
	if (!c->ok || c->id != id) {
		const char *n = NULL;
		if (group) { struct group *g = getgrgid(id); if (g) n = g->gr_name; }
		else { struct passwd *p = getpwuid(id); if (p) n = p->pw_name; }
		if (n) snprintf(c->name, sizeof c->name, "%s", n);
		else snprintf(c->name, sizeof c->name, "%u", id);
		c->id = id; c->ok = 1;
	}
	return c->name;
}

static void size_str(int64_t v, char *s, size_t n)
{
	if (v < 1024) { snprintf(s, n, "%lldB", (long long)v); return; }
	double d = v;
	const char *u = "KMGTP";
	int i = -1;
	while (d >= 1024 && i < 4) { d /= 1024; i++; }
	if (d < 10) snprintf(s, n, "%.1f%c", d, u[i]);
	else snprintf(s, n, "%.0f%c", d, u[i]);
}

static void mode_str(uint32_t m, char *s)
{
	char t = '-';
	switch (m & S_IFMT) {
	case S_IFDIR: t = 'd'; break; case S_IFLNK: t = 'l'; break;
	case S_IFCHR: t = 'c'; break; case S_IFBLK: t = 'b'; break;
	case S_IFIFO: t = 'p'; break; case S_IFSOCK: t = 's'; break;
	}
	s[0] = t;
	static const char rwx[] = "rwxrwxrwx";
	for (int i = 0; i < 9; i++) s[1 + i] = (m & (0400 >> i)) ? rwx[i] : '-';
	if (m & S_ISUID) s[3] = (m & 0100) ? 's' : 'S';
	if (m & S_ISGID) s[6] = (m & 0010) ? 's' : 'S';
	if (m & S_ISVTX) s[9] = (m & 0001) ? 't' : 'T';
	s[10] = 0;
}

static void draw_left(Buf *b, uint32_t i, int w, int ow, int gw, int show_og, int show_size, int show_date)
{
	int left = w, used;
	int is_cur = i == cur;
	uint8_t fl = T.flags[i];
	if (is_cur) b_str(b, "\x1b[7m");
	b_str(b, (fl & F_SEL) ? "\x1b[1;35m" : "");
	used = put_cols(b, (fl & F_SEL) ? "*" : " ", 1, left); left -= used;
	b_str(b, "\x1b[0m"); if (is_cur) b_str(b, "\x1b[7m");
	char ms[16]; mode_str(T.mode[i], ms);
	left -= put_cols(b, ms, 10, left);
	left -= put_cols(b, " ", 1, left);
	if (show_og) {
		const char *o = idname(T.uid[i], 0), *g = idname(T.gid[i], 1);
		int c = put_cols(b, o, strlen(o), ow < left ? ow : left); left -= c;
		b_rep(b, ' ', ow - c < left ? ow - c : left); left -= ow - c < left ? ow - c : left;
		left -= put_cols(b, " ", 1, left);
		c = put_cols(b, g, strlen(g), gw < left ? gw : left); left -= c;
		b_rep(b, ' ', gw - c < left ? gw - c : left); left -= gw - c < left ? gw - c : left;
		left -= put_cols(b, " ", 1, left);
	}
	if (show_size) {
		char zs[24] = "";
		if (T.size[i] >= 0) size_str(T.size[i], zs, sizeof zs);
		int zl = strlen(zs);
		b_rep(b, ' ', 6 - zl < left ? 6 - zl : left); left -= 6 - zl < left ? 6 - zl : left;
		left -= put_cols(b, zs, zl, left);
		left -= put_cols(b, " ", 1, left);
	}
	if (show_date) {
		char ds[24]; time_t t = T.mtime[i]; struct tm tm;
		localtime_r(&t, &tm);
		strftime(ds, sizeof ds, "%Y-%m-%d %H:%M", &tm);
		left -= put_cols(b, ds, strlen(ds), left);
		left -= put_cols(b, " ", 1, left);
	}
	int ind = 2 * T.depth[i];
	if (ind > left) ind = left;
	b_rep(b, ' ', ind); left -= ind;
	if (fl & F_DIR) left -= put_cols(b, (fl & F_EXP) ? "\xe2\x96\xbe " : "\xe2\x96\xb8 ", 4, left);
	else { b_rep(b, ' ', left >= 2 ? 2 : left); left -= left >= 2 ? 2 : left; }
	const char *col = (fl & F_DIR) ? "\x1b[33m" : (fl & F_LNK) ? "\x1b[36m" :
			  (fl & F_EXE) ? "\x1b[92m" : "\x1b[37m";
	b_str(b, col);
	if (fl & F_SEL) b_str(b, "\x1b[1m");
	const char *nm = NAME(i);
	left -= put_cols(b, nm, strlen(nm), left);
	if (fl & F_DIR) left -= put_cols(b, "/", 1, left);
	if (fl & F_LNK && T.link[i] != NOLINK) {
		left -= put_cols(b, " -> ", 4, left);
		const char *tg = arena + T.link[i];
		left -= put_cols(b, tg, strlen(tg), left);
	}
	b_rep(b, ' ', left);
	b_str(b, "\x1b[0m");
}

static const char help[] =
	" j/k:move  l:expand  h:collapse  -:up dir  space:select  Esc:deselect  c:copy  m:move  d:delete  s:dir size  /:fzf  "
	"H/J/K/L:scroll preview  r:refresh  q:quit";

static Buf fb;

static void draw(void)
{
	int mh = term_h - 2;
	int rw = term_w / 2, lw = term_w - rw;
	fb.n = 0;
	b_str(&fb, "\x1b[?25l");
	if (cur < top) top = cur;
	if (cur >= top + (uint32_t)mh) top = cur - mh + 1;
	if (top + mh > T.n && T.n > (uint32_t)mh) top = T.n - mh;
	if (T.n <= (uint32_t)mh) top = 0;

	int ow = 1, gw = 1;
	for (int r = 0; r < mh && top + r < T.n; r++) {
		int l = strlen(idname(T.uid[top + r], 0));
		if (l > ow) ow = l;
		l = strlen(idname(T.gid[top + r], 1));
		if (l > gw) gw = l;
	}
	if (ow > 16) ow = 16;
	if (gw > 16) gw = 16;
	int base = 1 + 11 + 8;                   /* marker, perms, room for name */
	int show_og = lw >= base + ow + gw + 2;
	int og_w = show_og ? ow + gw + 2 : 0;
	int show_date = lw >= base + og_w + 17;
	int show_size = lw >= base + og_w + (show_date ? 17 : 0) + 7;

	preview_scale(rw - 1, mh);
	for (int r = 0; r < mh; r++) {
		b_fmt(&fb, "\x1b[%d;1H", r + 1);
		uint32_t i = top + r;
		if (i < T.n) draw_left(&fb, i, lw, ow, gw, show_og, show_size, show_date);
		else b_rep(&fb, ' ', lw);
		b_str(&fb, "\x1b[90m\xe2\x94\x82\x1b[0m");
		preview_row(&fb, r, rw - 1);
	}
	b_fmt(&fb, "\x1b[%d;1H\x1b[1;34m", term_h - 1);
	int pc = put_cols(&fb, " ", 1, term_w);
	{
		const char *dir = root[0] ? root : "/";
		int dl = strlen(dir), cols = 0;
		for (int q = 0; q < dl; q++) cols += ((unsigned char)dir[q] & 0xC0) != 0x80;
		if (cols > term_w - 2) { /* keep the tail, show leading ellipsis */
			int skip = cols - (term_w - 3);
			const char *p = dir;
			while (skip > 0 && *p) { p++; while (((unsigned char)*p & 0xC0) == 0x80) p++; skip--; }
			pc += put_cols(&fb, "\xe2\x80\xa6", 3, term_w - pc);
			pc += put_cols(&fb, p, strlen(p), term_w - pc);
		} else pc += put_cols(&fb, dir, dl, term_w - pc);
	}
	b_rep(&fb, ' ', term_w - pc);
	b_str(&fb, "\x1b[0m");
	b_fmt(&fb, "\x1b[%d;1H\x1b[7m", term_h);
	char extra[320] = "";
	if (status[0]) snprintf(extra, sizeof extra, " | %s ", status);
	else if (sel_n) snprintf(extra, sizeof extra, " | %zu selected ", sel_n);
	int el = 0;
	for (const char *q = extra; *q; q++) el += ((unsigned char)*q & 0xC0) != 0x80;
	if (el > term_w - 10) el = term_w - 10;
	int c = put_cols(&fb, help, sizeof help - 1, term_w - (el > 0 ? el : 0));
	b_rep(&fb, ' ', term_w - el - c);
	if (el > 0) c = term_w - el + put_cols(&fb, extra, strlen(extra), el);
	else c = term_w;
	b_rep(&fb, ' ', term_w - c);
	b_str(&fb, "\x1b[0m");
	size_t off = 0;
	while (off < fb.n) {
		ssize_t w = write(1, fb.p + off, fb.n - off);
		if (w < 0) { if (errno == EINTR || errno == EAGAIN) continue; break; }
		off += w;
	}
}

/* -------------------------------------------------------------- terminal */

static struct termios orig_tio;
static int raw_on;
static volatile sig_atomic_t resized, quit_flag;

static void term_restore(void)
{
	if (!raw_on) return;
	const char s[] = "\x1b[0m\x1b[?25h\x1b[?1049l";
	if (write(1, s, sizeof s - 1) < 0) { }
	tcsetattr(0, TCSAFLUSH, &orig_tio);
	raw_on = 0;
}
static void term_raw(void)
{
	tcgetattr(0, &orig_tio);
	struct termios t = orig_tio;
	t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
	t.c_oflag &= ~OPOST;
	t.c_cflag |= CS8;
	t.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
	t.c_cc[VMIN] = 1; t.c_cc[VTIME] = 0;
	tcsetattr(0, TCSAFLUSH, &t);
	raw_on = 1;
	if (write(1, "\x1b[?1049h", 8) < 0) { }
}
static void get_size(void)
{
	struct winsize ws;
	if (ioctl(1, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0 && ws.ws_row > 0) {
		term_w = ws.ws_col; term_h = ws.ws_row;
	}
	if (term_w < 20) term_w = 20;
	if (term_h < 4) term_h = 4;
}
static void on_winch(int s) { (void)s; resized = 1; }
static void on_term(int s) { (void)s; quit_flag = 1; }

enum { K_NONE = 0, K_EOF = -1, K_ESC = 256, K_UP, K_DOWN, K_LEFT, K_RIGHT };

static int input_pending(void)
{
	struct pollfd pf = { 0, POLLIN, 0 };
	return poll(&pf, 1, 0) > 0;
}

static int read_key(void)
{
	unsigned char c;
	ssize_t r = read(0, &c, 1);
	if (r == 0) return K_EOF;
	if (r < 0) return K_NONE;
	if (c != 27) return c;
	if (!input_pending()) {
		struct pollfd pf = { 0, POLLIN, 0 };
		if (poll(&pf, 1, 30) <= 0) return K_ESC;
	}
	unsigned char c2;
	if (read(0, &c2, 1) <= 0) return K_ESC;
	if (c2 != '[' && c2 != 'O') return K_NONE;
	unsigned char f = 0;
	while (read(0, &f, 1) > 0 && (f < 0x40 || f > 0x7e)) ;
	switch (f) {
	case 'A': return K_UP; case 'B': return K_DOWN;
	case 'C': return K_RIGHT; case 'D': return K_LEFT;
	}
	return K_NONE;
}

/* Edit a line on the bottom row. Returns 1 on Enter, 0 on cancel. */
static int prompt_line(const char *label, char *buf, size_t cap)
{
	size_t len = strlen(buf);
	for (;;) {
		Buf b = {0};
		b_fmt(&b, "\x1b[%d;1H\x1b[7m", term_h);
		int c = put_cols(&b, label, strlen(label), term_w);
		c += put_cols(&b, buf, len, term_w - c);
		b_rep(&b, ' ', term_w - c);
		b_str(&b, "\x1b[0m");
		b_fmt(&b, "\x1b[%d;%dH\x1b[?25h", term_h, c + 1 > term_w ? term_w : c + 1);
		if (write(1, b.p, b.n) < 0) { }
		free(b.p);
		int k;
		do {
			struct pollfd pf = { 0, POLLIN, 0 };
			if (poll(&pf, 1, -1) < 0 && quit_flag) return 0;
			k = K_NONE;
			if (pf.revents & POLLIN) k = read_key();
		} while (k == K_NONE && !quit_flag);
		if (quit_flag || k == K_EOF) return 0;
		if (k == K_ESC || k == 3) return 0;
		if (k == '\r' || k == '\n') return 1;
		if (k == 127 || k == 8) {
			while (len && ((unsigned char)buf[len - 1] & 0xC0) == 0x80) len--;
			if (len) len--;
			buf[len] = 0;
		} else if (k == 21) { len = 0; buf[0] = 0; }
		else if (k >= 32 && k < 256 && len + 1 < cap) { buf[len++] = k; buf[len] = 0; }
	}
}

/* ------------------------------------------------------- copy / move ops */

static int copy_path(const char *src, const char *dst)
{
	struct stat st;
	if (lstat(src, &st) < 0) return -1;
	if (S_ISLNK(st.st_mode)) {
		char tg[PATH_MAX];
		ssize_t l = readlink(src, tg, sizeof tg - 1);
		if (l < 0) return -1;
		tg[l] = 0;
		return symlink(tg, dst);
	}
	if (S_ISDIR(st.st_mode)) {
		if (mkdir(dst, (st.st_mode & 07777) | 0700) < 0) return -1;
		DIR *d = opendir(src);
		if (!d) return -1;
		struct dirent *e;
		int rc = 0;
		while ((e = readdir(d))) {
			if (e->d_name[0] == '.' && (!e->d_name[1] || (e->d_name[1] == '.' && !e->d_name[2]))) continue;
			char s2[PATH_MAX], d2[PATH_MAX];
			if (snprintf(s2, sizeof s2, "%s/%s", src, e->d_name) >= (int)sizeof s2 ||
			    snprintf(d2, sizeof d2, "%s/%s", dst, e->d_name) >= (int)sizeof d2) { errno = ENAMETOOLONG; rc = -1; continue; }
			if (copy_path(s2, d2) < 0) rc = -1;
		}
		closedir(d);
		return rc;
	}
	if (!S_ISREG(st.st_mode)) return 0;
	int in = open(src, O_RDONLY | O_CLOEXEC);
	if (in < 0) return -1;
	int out = open(dst, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, st.st_mode & 07777);
	if (out < 0) { int e = errno; close(in); errno = e; return -1; }
	int rc = 0, use_cfr = 1;
	static char iobuf[64 * 1024];
	for (;;) {
		if (use_cfr) {
			ssize_t n = copy_file_range(in, NULL, out, NULL, 1u << 30, 0);
			if (n > 0) continue;
			if (n == 0) break;
			if (errno == EXDEV || errno == ENOSYS || errno == EINVAL || errno == EOPNOTSUPP) { use_cfr = 0; continue; }
			rc = -1; break;
		}
		ssize_t n = read(in, iobuf, sizeof iobuf);
		if (n == 0) break;
		if (n < 0) { rc = -1; break; }
		for (ssize_t o = 0; o < n;) {
			ssize_t w = write(out, iobuf + o, n - o);
			if (w < 0) { rc = -1; goto done; }
			o += w;
		}
	}
done:;
	int e = errno;
	close(in);
	if (close(out) < 0 && !rc) rc = -1; else errno = e;
	return rc;
}

static int rm_cb(const char *p, const struct stat *s, int t, struct FTW *f)
{
	(void)s; (void)f;
	return (t == FTW_DP ? rmdir(p) : unlink(p));
}

static void do_transfer(int move)
{
	if (!T.n) return;
	char **src = NULL; size_t sn = 0;
	if (sel_n) {
		src = xrealloc(NULL, sel_n * sizeof *src);
		for (size_t i = 0; i < sel_n; i++) src[sn++] = strdup(sel[i]);
	} else {
		src = xrealloc(NULL, sizeof *src);
		char p[PATH_MAX]; row_path(cur, p);
		src[sn++] = strdup(p);
	}
	/* default destination: cursor dir if expanded, else its parent */
	char dest[PATH_MAX];
	{
		char p[PATH_MAX]; row_path(cur, p);
		if (!(T.flags[cur] & F_EXP)) { char *s = strrchr(p, '/'); if (s && s != p) *s = 0; else if (s) s[1] = 0; }
		snprintf(dest, sizeof dest, "%s", p);
	}
	char label[96];
	snprintf(label, sizeof label, "%s %zu item%s to: ", move ? "Move" : "Copy", sn, sn == 1 ? "" : "s");
	int ok = prompt_line(label, dest, sizeof dest);
	size_t dl = strlen(dest);
	while (dl > 1 && dest[dl - 1] == '/') dest[--dl] = 0;
	if (!ok || !dl) {
		snprintf(status, sizeof status, "cancelled");
		goto out;
	}
	char abs[2 * PATH_MAX];
	if (dest[0] != '/') {
		snprintf(abs, sizeof abs, "%s/%s", rootlen ? root : "", dest);
		snprintf(dest, sizeof dest, "%.*s", (int)sizeof dest - 1, abs);
	}
	struct stat st;
	if (stat(dest, &st) < 0 || !S_ISDIR(st.st_mode)) {
		snprintf(status, sizeof status, "not a directory: %s", dest);
		goto out;
	}
	int done = 0, failed = 0;
	char firsterr[128] = "";
	for (size_t i = 0; i < sn; i++) {
		const char *base = strrchr(src[i], '/');
		base = base ? base + 1 : src[i];
		char dst[PATH_MAX];
		const char *err = NULL;
		if (snprintf(dst, sizeof dst, "%s%s%s", dest, dest[1] ? "/" : "", base) >= (int)sizeof dst) err = "path too long";
		else {
			size_t sl = strlen(src[i]);
			struct stat ss, ds;
			if (lstat(src[i], &ss) < 0) err = strerror(errno);
			else if (lstat(dst, &ds) == 0) err = "destination exists";
			else if (S_ISDIR(ss.st_mode) && !strncmp(dst, src[i], sl) && dst[sl] == '/') err = "cannot copy into itself";
			else if (move) {
				if (rename(src[i], dst) < 0) {
					if (errno == EXDEV) {
						if (copy_path(src[i], dst) < 0) err = strerror(errno);
						else if (nftw(src[i], rm_cb, 16, FTW_DEPTH | FTW_PHYS) < 0) err = strerror(errno);
					} else err = strerror(errno);
				}
			} else if (copy_path(src[i], dst) < 0) err = strerror(errno);
		}
		if (err) { failed++; if (!firsterr[0]) snprintf(firsterr, sizeof firsterr, "%s: %s", base, err); }
		else done++;
	}
	sel_clear();
	rebuild();
	if (failed) snprintf(status, sizeof status, "%d ok, %d failed (%s)", done, failed, firsterr);
	else snprintf(status, sizeof status, "%s %d item%s", move ? "moved" : "copied", done, done == 1 ? "" : "s");
out:
	for (size_t i = 0; i < sn; i++) free(src[i]);
	free(src);
	P.valid = 0;
}

static int64_t sz_total;
static int sz_cb(const char *p, const struct stat *st, int t, struct FTW *f)
{
	(void)p; (void)f;
	if (t != FTW_D && t != FTW_DP && t != FTW_DNR && t != FTW_NS) sz_total += st->st_size;
	return 0;
}

static void do_size(void)
{
	if (!T.n || !(T.flags[cur] & F_DIR)) return;
	char p[PATH_MAX]; row_path(cur, p);
	sz_total = 0;
	nftw(p, sz_cb, 16, FTW_PHYS);
	T.size[cur] = sz_total;
}

static void do_delete(void)
{
	if (!T.n) return;
	char **src = NULL; size_t sn = 0;
	if (sel_n) {
		src = xrealloc(NULL, sel_n * sizeof *src);
		for (size_t i = 0; i < sel_n; i++) src[sn++] = strdup(sel[i]);
	} else {
		src = xrealloc(NULL, sizeof *src);
		char p[PATH_MAX]; row_path(cur, p);
		src[sn++] = strdup(p);
	}
	char label[96], ans[8] = "";
	snprintf(label, sizeof label, "Delete %zu item%s? Type y to confirm: ", sn, sn == 1 ? "" : "s");
	if (!prompt_line(label, ans, sizeof ans) || (strcmp(ans, "y") && strcmp(ans, "yes"))) {
		snprintf(status, sizeof status, "cancelled");
	} else {
		int done = 0, failed = 0;
		char firsterr[128] = "";
		for (size_t i = 0; i < sn; i++) {
			if (nftw(src[i], rm_cb, 16, FTW_DEPTH | FTW_PHYS) < 0) {
				failed++;
				if (!firsterr[0]) snprintf(firsterr, sizeof firsterr, "%.60s: %s", src[i], strerror(errno));
			} else done++;
		}
		sel_clear();
		rebuild();
		if (failed) snprintf(status, sizeof status, "%d deleted, %d failed (%s)", done, failed, firsterr);
		else snprintf(status, sizeof status, "deleted %d item%s", done, done == 1 ? "" : "s");
	}
	for (size_t i = 0; i < sn; i++) free(src[i]);
	free(src);
	P.valid = 0;
}

/* Expand ancestors of absolute path `abs` (below root) and put the cursor on it. */
static int reveal(const char *abs)
{
	if (strncmp(abs, root, rootlen) || (abs[rootlen] != '/' && abs[rootlen] != 0)) return -1;
	const char *p = abs + rootlen;
	int64_t idx = -1;
	int d = 0;
	while (*p == '/') {
		while (*p == '/') p++;
		if (!*p) break;
		const char *e = strchr(p, '/');
		size_t l = e ? (size_t)(e - p) : strlen(p);
		uint32_t r = idx < 0 ? 0 : idx + 1;
		int found = 0;
		for (; r < T.n && (idx < 0 || T.depth[r] > T.depth[idx]); r++)
			if (T.depth[r] == d && strlen(NAME(r)) == l && !strncmp(NAME(r), p, l)) { found = 1; break; }
		if (!found) return -1;
		idx = r;
		p += l;
		if (*p) {
			if (!(T.flags[r] & F_DIR)) return -1;
			expand(r);
			d++;
		}
	}
	if (idx < 0) return -1;
	cur = idx;
	return 0;
}

/* Fuzzy-find below the cursor's directory with fzf and jump to the result. */
static void do_fzf(void)
{
	char scope[PATH_MAX];
	snprintf(scope, sizeof scope, "%s", root[0] ? root : "/");
	if (T.n) {
		row_path(cur, scope);
		if (!(T.flags[cur] & F_DIR)) {
			char *sl = strrchr(scope, '/');
			if (sl && sl != scope) *sl = 0; else if (sl) sl[1] = 0;
		}
	}
	char walker[PATH_MAX + 32], prompt[PATH_MAX + 16];
	snprintf(walker, sizeof walker, "--walker-root=%s", scope);
	snprintf(prompt, sizeof prompt, "--prompt=%s> ", scope);
	int pfd[2];
	if (pipe(pfd) < 0) { snprintf(status, sizeof status, "pipe: %s", strerror(errno)); return; }
	term_restore();
	pid_t pid = fork();
	if (pid == 0) {
		dup2(pfd[1], 1);
		close(pfd[0]); close(pfd[1]);
		execlp("fzf", "fzf", "--walker=file,dir,hidden", walker, "--scheme=path", prompt, (char *)NULL);
		_exit(127);
	}
	close(pfd[1]);
	char out[PATH_MAX + 2]; size_t n = 0;
	if (pid > 0) {
		ssize_t r;
		while (n < sizeof out - 1 && (r = read(pfd[0], out + n, sizeof out - 1 - n)) != 0) {
			if (r < 0) { if (errno == EINTR) continue; break; }
			n += r;
		}
	}
	close(pfd[0]);
	int st = 0;
	if (pid > 0) while (waitpid(pid, &st, 0) < 0 && errno == EINTR) ;
	term_raw();
	P.valid = 0;
	out[n] = 0;
	char *nl = strchr(out, '\n'); if (nl) *nl = 0;
	int code = pid > 0 && WIFEXITED(st) ? WEXITSTATUS(st) : -1;
	if (code == 127) { snprintf(status, sizeof status, "fzf not found"); return; }
	if (code == 1) { snprintf(status, sizeof status, "no match"); return; }
	if (code != 0 || !out[0]) { snprintf(status, sizeof status, "cancelled"); return; }
	char target[2 * PATH_MAX];
	const char *rel = out;
	if (!strncmp(rel, "./", 2)) rel += 2;
	if (rel[0] == '/') snprintf(target, sizeof target, "%s", rel);
	else snprintf(target, sizeof target, "%s%s%s", scope, scope[1] ? "/" : "", rel);
	if (reveal(target) < 0) snprintf(status, sizeof status, "not found in tree: %.150s", out);
}

/* Make the parent of the current root the new root, cursor on the old root. */
static void go_up(void)
{
	if (!rootlen) return;
	char old[PATH_MAX];
	snprintf(old, sizeof old, "%s", strrchr(root, '/') + 1);
	char *sl = strrchr(root, '/');
	if (sl == root) { root[1] = 0; rootlen = 0; } else { *sl = 0; rootlen = strlen(root); }
	if (chdir(root) < 0) { snprintf(status, sizeof status, "cannot enter %.150s", root); return; }
	tree_free(&T); arena_n = 0;
	load_dir(root, 0, 0);
	cur = 0; top = 0;
	for (uint32_t i = 0; i < T.n; i++)
		if (!strcmp(NAME(i), old)) { cur = i; expand(i); break; }
	P.valid = 0;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv)
{
	if (argc > 1 && chdir(argv[1]) < 0) { perror(argv[1]); return 1; }
	if (!getcwd(root, sizeof root)) { perror("getcwd"); return 1; }
	rootlen = strlen(root);
	if (rootlen == 1) rootlen = 0;
	if (!isatty(0) || !isatty(1)) { fputs("filetree: needs a terminal\n", stderr); return 1; }

	rebuild();

	struct sigaction sa; memset(&sa, 0, sizeof sa);
	sa.sa_handler = on_winch; sigaction(SIGWINCH, &sa, NULL);
	sa.sa_handler = on_term; sigaction(SIGTERM, &sa, NULL); sigaction(SIGHUP, &sa, NULL);
	atexit(term_restore);
	term_raw();
	get_size();

	int dirty = 1;
	while (!quit_flag) {
		if (resized) { resized = 0; get_size(); P.valid = 0; dirty = 1; }
		if (dirty && !input_pending()) {
			if (cur >= T.n && T.n) cur = T.n - 1;
			preview_update();
			draw();
			dirty = 0;
		}
		struct pollfd pf = { 0, POLLIN, 0 };
		if (poll(&pf, 1, -1) < 0) continue;
		int k = read_key();
		if (k == K_EOF) break;
		if (k == K_NONE) continue;
		if (status[0]) { status[0] = 0; dirty = 1; }
		dirty = 1;
		uint32_t n = T.n;
		switch (k) {
		case 'q': case 3: quit_flag = 1; break;
		case 'j': case K_DOWN: if (cur + 1 < n) cur++; break;
		case 'k': case K_UP: if (cur > 0) cur--; break;
		case 'g': cur = 0; break;
		case 'G': if (n) cur = n - 1; break;
		case 'l': case K_RIGHT:
			if (!n || !(T.flags[cur] & F_DIR)) break;
			if (!(T.flags[cur] & F_EXP)) expand(cur);
			else if (cur + 1 < n && T.depth[cur + 1] > T.depth[cur]) cur++;
			break;
		case 'h': case K_LEFT:
			if (!n) break;
			if (T.flags[cur] & F_EXP) collapse(cur);
			else if (T.depth[cur] > 0) {
				uint32_t d = T.depth[cur];
				while (cur > 0 && T.depth[cur] >= d) cur--;
			}
			break;
		case ' ':
			if (!n) break;
			sel_toggle(cur);
			if (cur + 1 < n) cur++;
			break;
		case K_ESC: sel_clear(); break;
		case 'c': do_transfer(0); break;
		case 'm': do_transfer(1); break;
		case 'd': do_delete(); break;
		case 's': do_size(); break;
		case '-': go_up(); break;
		case '/': do_fzf(); break;
		case 'r': rebuild(); P.valid = 0; break;
		case 'J': preview_scroll(1, 0); break;
		case 'K': preview_scroll(-1, 0); break;
		case 'H': preview_scroll(0, -4); break;
		case 'L': preview_scroll(0, 4); break;
		default: dirty = 0; break;
		}
	}
	term_restore();
	return 0;
}
