/*
 * Characteristic polynomials of all intervals of a finite lattice of flats.
 *
 * Input (little-endian binary on stdin):
 *   int64 n, int64 words, int64 ranks[n], uint64 masks[n][words]
 * Flats must be sorted by rank; flat 0 is the bottom, flat n-1 the top.
 * Output (stdout):
 *   int64 total_pairs, int64 width (= top rank + 1),
 *   int64 offsets[n+1], int64 cols[total_pairs], int64 coeffs[total_pairs][width]
 * Row i lists every j >= i with flat_i a subset of flat_j, in index order, with the
 * coefficients c_k of chi_[i,j](t) = sum_{i <= h <= j} mu(i,h) t^(rk j - rk h).
 * Exact int64 arithmetic; any overflow aborts with exit status 3. This program is an
 * accelerator for solved.matroid_lattice.interval_characteristic and is differentially
 * tested against it.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void die(const char *msg, int code) {
    fprintf(stderr, "lattice_intervals: %s\n", msg);
    exit(code);
}

static void read_exact(void *buf, size_t size, size_t count) {
    if (count && fread(buf, size, count, stdin) != count) die("short input", 2);
}

static void write_exact(const void *buf, size_t size, size_t count) {
    if (count && fwrite(buf, size, count, stdout) != count) die("short write", 2);
}

static inline int subset(const uint64_t *a, const uint64_t *b, int64_t words) {
    for (int64_t w = 0; w < words; w++)
        if (a[w] & ~b[w]) return 0;
    return 1;
}

int main(void) {
    int64_t n, words;
    read_exact(&n, sizeof n, 1);
    read_exact(&words, sizeof words, 1);
    if (n < 1 || words < 1 || n > (int64_t)1 << 31) die("bad header", 2);
    int64_t *rank = malloc(sizeof(int64_t) * n);
    uint64_t *mask = malloc(sizeof(uint64_t) * n * words);
    if (!rank || !mask) die("out of memory", 4);
    read_exact(rank, sizeof(int64_t), n);
    read_exact(mask, sizeof(uint64_t), n * words);
    for (int64_t i = 1; i < n; i++)
        if (rank[i] < rank[i - 1]) die("flats not sorted by rank", 2);
    int64_t width = rank[n - 1] + 1;

    int64_t *offsets = calloc(n + 1, sizeof(int64_t));
    int64_t *up = malloc(sizeof(int64_t) * n);
    int64_t *mu = malloc(sizeof(int64_t) * n);
    if (!offsets || !up || !mu) die("out of memory", 4);

    /* First pass: count pairs so the output can be sized. */
    for (int64_t i = 0; i < n; i++) {
        int64_t count = 0;
        for (int64_t j = i; j < n; j++)
            if (subset(mask + i * words, mask + j * words, words)) count++;
        offsets[i + 1] = offsets[i] + count;
    }
    int64_t total = offsets[n];
    int64_t *cols = malloc(sizeof(int64_t) * total);
    int64_t *coeffs = calloc((size_t)total * width, sizeof(int64_t));
    if (!cols || !coeffs) die("out of memory", 4);

    for (int64_t i = 0; i < n; i++) {
        int64_t m = 0;
        for (int64_t j = i; j < n; j++)
            if (subset(mask + i * words, mask + j * words, words)) up[m++] = j;
        int64_t base = offsets[i];
        for (int64_t a = 0; a < m; a++) {
            int64_t j = up[a];
            int64_t *chi = coeffs + (base + a) * width;
            int64_t s = 0;
            const uint64_t *mj = mask + j * words;
            for (int64_t b = 0; b < a; b++) {
                int64_t h = up[b];
                if (rank[h] >= rank[j]) break; /* up[] is in rank order */
                if (!subset(mask + h * words, mj, words)) continue;
                if (__builtin_add_overflow(s, mu[b], &s)) die("overflow", 3);
                int64_t k = rank[j] - rank[h];
                if (__builtin_add_overflow(chi[k], mu[b], &chi[k])) die("overflow", 3);
            }
            int64_t value = (a == 0) ? 1 : -s;
            if (a != 0 && s == INT64_MIN) die("overflow", 3);
            mu[a] = value;
            if (__builtin_add_overflow(chi[0], value, &chi[0])) die("overflow", 3);
            cols[base + a] = j;
        }
    }
    write_exact(&total, sizeof total, 1);
    write_exact(&width, sizeof width, 1);
    write_exact(offsets, sizeof(int64_t), n + 1);
    write_exact(cols, sizeof(int64_t), total);
    write_exact(coeffs, sizeof(int64_t), (size_t)total * width);
    return 0;
}
