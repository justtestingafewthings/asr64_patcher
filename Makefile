CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra -Wpedantic

.PHONY: all clean
all: asr64_patcher
asr64_patcher: asr64_patcher.c
	$(CC) $(CPPFLAGS) $(CFLAGS) asr64_patcher.c $(LDFLAGS) -o $@

clean:
	rm -f asr64_patcher
