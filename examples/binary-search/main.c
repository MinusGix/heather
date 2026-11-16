/* lowerbound: where would a byte go in a sorted file?

   Reads all of standard input as a span of bytes in ascending order and
   asks the compiled Heather function `lower_bound` (search.hthr) where the
   byte given as the argument would go: the first offset whose byte is at
   least it. Prints that offset.

   This file is outside the proof: it reads the input and prints the answer.
   What the answer means is the Heather theorem `lower_bound_splits`, which
   holds when the input is in ascending order; the driver checks that first
   and refuses input that is not. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t lower_bound(const uint8_t *bytes, uint64_t length, uint64_t key);

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: lowerbound BYTE < sorted-input\n");
        return 2;
    }
    char *end;
    unsigned long key = strtoul(argv[1], &end, 0);
    if (*argv[1] == '\0' || *end != '\0' || key > 255) {
        fprintf(stderr, "lowerbound: the key is a byte, 0 to 255\n");
        return 2;
    }
    size_t cap = 1 << 16, len = 0;
    uint8_t *buf = malloc(cap);
    if (!buf) return 2;
    for (;;) {
        if (len == cap) {
            cap *= 2;
            uint8_t *grown = realloc(buf, cap);
            if (!grown) return 2;
            buf = grown;
        }
        size_t got = fread(buf + len, 1, cap - len, stdin);
        if (got == 0) break;
        len += got;
    }
    if (ferror(stdin)) return 2;
    for (size_t i = 1; i < len; i++) {
        if (buf[i - 1] > buf[i]) {
            fprintf(stderr, "lowerbound: the input is not in ascending order at byte %zu\n", i);
            return 2;
        }
    }
    printf("%" PRIu64 "\n", lower_bound(buf, len, key));
    return 0;
}
