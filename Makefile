CC      ?= cc
CFLAGS  ?= -O2
CFLAGS  += -std=gnu11 -Wall -Wextra
TARGET   = filetree

# Default: libpng/libjpeg are dlopen()'d lazily, the first time an image is previewed.
# `make STATIC=1` links them (and everything else) statically instead.
ifeq ($(STATIC),1)
CFLAGS  += -DSTATIC_IMAGE_LIBS
LDFLAGS += -static
LDLIBS  += -lpng -ljpeg -lz -lm
else
LDLIBS  += -ldl
endif

all: $(TARGET)

$(TARGET): filetree.c
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

run: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)

.PHONY: all run clean
