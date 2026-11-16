/* utf8check: is standard input UTF-8?

   Reads all of standard input and asks the compiled Heather function
   `utf8_valid_up_to` (utf8_check.hthr) for the longest prefix that is UTF-8.
   Prints `valid` and exits 0 when that is the whole input; otherwise prints
   the offset of the first byte where no sequence starts and exits 1.

   This file is outside the proof: it reads the input and prints the answer.
   What the answer means is the Heather theorem. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t utf8_valid_up_to(const uint8_t *bytes, uint64_t length);

int main(void) {
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
    uint64_t good = utf8_valid_up_to(buf, len);
    if (good == len) {
        puts("valid");
        return 0;
    }
    printf("invalid at byte %" PRIu64 "\n", good);
    return 1;
}
