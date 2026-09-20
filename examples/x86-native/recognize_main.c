// Host adapter only: fixed input storage and display. Recognition, byte loads,
// bounds checks, and cursor updates execute in Heather-generated code.
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

struct cursor_reply { uint64_t status, next; };
extern struct cursor_reply recognize_plus(const unsigned char *, uint64_t, uint64_t);

int main(int argc, char **argv) {
    unsigned char input[256];
    uint64_t length = 0, cursor = 0;
    if (argc < 2 || argc > 3) return 64;
    while (argv[1][length]) {
        if (length == sizeof input) return 65;
        input[length] = (unsigned char)argv[1][length];
        ++length;
    }
    if (argc == 3) {
        if (!argv[2][0]) return 64;
        for (size_t i = 0; argv[2][i]; ++i) {
            unsigned char c = (unsigned char)argv[2][i];
            if (c < '0' || c > '9' || cursor > (UINT64_MAX - (c - '0')) / 10) return 64;
            cursor = cursor * 10 + (c - '0');
        }
    }
    struct cursor_reply reply = recognize_plus(input, length, cursor);
    const char *name = reply.status == 0 ? "match " : reply.status == 1 ? "mismatch " : "end ";
    char output[40];
    size_t used = 0;
    while (*name) output[used++] = *name++;
    char digits[20];
    size_t n = 0;
    do { digits[n++] = (char)('0' + reply.next % 10); reply.next /= 10; } while (reply.next);
    while (n) output[used++] = digits[--n];
    output[used++] = '\n';
    return write(STDOUT_FILENO, output, used) == (ssize_t)used ? 0 : 74;
}
