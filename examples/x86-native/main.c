#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t mix(uint64_t left, uint64_t right);

int main(void) {
    const uint64_t cases[][2] = {
        {20, 22}, {0, 0}, {UINT64_MAX, 1}, {UINT64_MAX, UINT64_MAX},
        {UINT64_C(0x8000000000000000), 7},
    };
    for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        uint64_t left = cases[i][0], right = cases[i][1];
        uint64_t shared = left + right;
        uint64_t expected = shared ^ (shared + 7);
        uint64_t actual = mix(left, right);
        if (actual != expected) return 1;
    }
    uint64_t seed = 42;
    for (unsigned i = 0; i < 10000; ++i) {
        seed = seed * UINT64_C(6364136223846793005) + 1;
        uint64_t left = seed;
        seed = seed * UINT64_C(6364136223846793005) + 1;
        uint64_t shared = left + seed;
        if (mix(left, seed) != (shared ^ (shared + 7))) return 2;
    }
    printf("mix(20, 22) = %" PRIu64 "; 10005 native cases passed\n", mix(20, 22));
    return 0;
}
