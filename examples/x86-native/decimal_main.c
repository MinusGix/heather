// Host adapter only: fixed input storage and display. Decimal parsing, byte loads,
// bounds checks, and cursor updates execute in Heather-generated code.
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

struct scan_reply { uint64_t status, value, next; };
extern struct scan_reply scan_buffer(const unsigned char *, uint64_t, uint64_t);

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
    struct scan_reply reply = scan_buffer(input, length, cursor);
    const char *name = reply.status == 0 ? "ok " : reply.status == 1 ? "no-digits " : reply.status == 2 ? "overflow " : "limit ";
    char output[64];
    size_t used = 0;
    while (*name) output[used++] = *name++;
    uint64_t values[2] = { reply.value, reply.next };
    for (size_t field = 0; field < 2; ++field) {
        char digits[20];
        size_t n = 0;
        do { digits[n++] = (char)('0' + values[field] % 10); values[field] /= 10; } while (values[field]);
        while (n) output[used++] = digits[--n];
        output[used++] = field ? '\n' : ' ';
    }
    return write(STDOUT_FILENO, output, used) == (ssize_t)used ? 0 : 74;
}
