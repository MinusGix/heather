/* bytesort: sort standard input's bytes.

   Reads all of standard input, sorts its bytes in place with the compiled
   Heather function `sort_in_place` (sort.hthr), and writes them out.

   This file is outside the proof: it reads the input and writes the result.
   That the result is the input's bytes in ascending order is the Heather
   theorem `sort_in_place_sorts`. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t sort_in_place(uint8_t *bytes, uint64_t length);

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
    sort_in_place(buf, len);
    if (fwrite(buf, 1, len, stdout) != len) return 2;
    return 0;
}
