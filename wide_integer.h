#ifndef OCEAN_WIDE_INTEGER_H
#define OCEAN_WIDE_INTEGER_H
#include "token.h"
#include <stdio.h>
#include <stdlib.h>

#include <stdint.h>
#include <string.h>

// Little-endian base-2^32 natural numbers used to convert long decimal literals.
// Conversion is divide and conquer (high * 10^k + low) with Karatsuba
// multiplication, so even literals near the maximum width convert quickly.
#define OCEAN_BIG_SCHOOLBOOK 48
#define OCEAN_BIG_SMALL_DIGITS 1800

static inline size_t oceanBigTrim(const uint32_t *w, size_t n) {
    while (n && !w[n - 1]) n--;
    return n;
}
static inline uint32_t *oceanBigAlloc(size_t n) {
    uint32_t *w = calloc(n ? n : 1, sizeof(*w));
    if (!w) exit(1);
    return w;
}
// r[at...] += x; r has room for the carry.
static inline void oceanBigAddAt(uint32_t *r, size_t rn, const uint32_t *x, size_t xn, size_t at) {
    uint64_t carry = 0;
    size_t i = 0;
    for (; i < xn; i++) {
        uint64_t sum = (uint64_t)r[at + i] + x[i] + carry;
        r[at + i] = (uint32_t)sum; carry = sum >> 32;
    }
    for (size_t k = at + i; carry && k < rn; k++) {
        uint64_t sum = (uint64_t)r[k] + carry;
        r[k] = (uint32_t)sum; carry = sum >> 32;
    }
}
// x -= y, where x >= y.
static inline void oceanBigSubtract(uint32_t *x, size_t xn, const uint32_t *y, size_t yn) {
    uint64_t borrow = 0;
    for (size_t i = 0; i < xn; i++) {
        uint64_t sub = (i < yn ? y[i] : 0) + borrow;
        borrow = x[i] < sub;
        x[i] = (uint32_t)(x[i] - sub);
        if (i >= yn && !borrow) break;
    }
}
// Returns a * b in an + bn limbs (zero-padded); the caller frees it.
static uint32_t *oceanBigMultiply(const uint32_t *a, size_t an, const uint32_t *b, size_t bn) {
    if (an < bn) { const uint32_t *t = a; a = b; b = t; size_t tn = an; an = bn; bn = tn; }
    uint32_t *r = oceanBigAlloc(an + bn);
    if (!bn) return r;
    if (bn < OCEAN_BIG_SCHOOLBOOK) {
        for (size_t i = 0; i < bn; i++) {
            uint64_t carry = 0;
            for (size_t j = 0; j < an; j++) {
                uint64_t v = (uint64_t)b[i] * a[j] + r[i + j] + carry;
                r[i + j] = (uint32_t)v; carry = v >> 32;
            }
            r[i + an] = (uint32_t)carry;
        }
        return r;
    }
    if (an >= 2 * bn) { // Unbalanced: multiply bn-limb slices of a.
        for (size_t at = 0; at < an; at += bn) {
            size_t len = an - at < bn ? an - at : bn;
            uint32_t *part = oceanBigMultiply(a + at, len, b, bn);
            oceanBigAddAt(r, an + bn, part, len + bn, at);
            free(part);
        }
        return r;
    }
    size_t m = an / 2; // bn > m because an < 2 * bn.
    uint32_t *z0 = oceanBigMultiply(a, m, b, m);
    uint32_t *z2 = oceanBigMultiply(a + m, an - m, b + m, bn - m);
    size_t s1n = an - m + 1, s2n = (m > bn - m ? m : bn - m) + 1;
    uint32_t *s1 = oceanBigAlloc(s1n), *s2 = oceanBigAlloc(s2n);
    memcpy(s1, a + m, (an - m) * sizeof(*s1)); oceanBigAddAt(s1, s1n, a, m, 0);
    memcpy(s2, b, m * sizeof(*s2)); oceanBigAddAt(s2, s2n, b + m, bn - m, 0);
    size_t z1n = s1n + s2n;
    uint32_t *z1 = oceanBigMultiply(s1, s1n, s2, s2n);
    oceanBigSubtract(z1, z1n, z0, 2 * m);
    oceanBigSubtract(z1, z1n, z2, an + bn - 2 * m);
    oceanBigAddAt(r, an + bn, z0, 2 * m, 0);
    oceanBigAddAt(r, an + bn, z2, an + bn - 2 * m, 2 * m);
    oceanBigAddAt(r, an + bn, z1, oceanBigTrim(z1, z1n), m);
    free(z0); free(z1); free(z2); free(s1); free(s2);
    return r;
}
// Schoolbook conversion of a short decimal run, nine digits per step.
static uint32_t *oceanBigFromDecimalSmall(const char *d, size_t len, size_t *n) {
    size_t cap = len / 9 + 2, count = 1;
    uint32_t *w = oceanBigAlloc(cap);
    for (size_t i = 0; i < len;) {
        size_t take = len - i < 9 ? len - i : 9;
        uint32_t mul = 1, chunk = 0;
        for (size_t k = 0; k < take; k++, i++) { mul *= 10; chunk = chunk * 10 + (uint32_t)(d[i] - '0'); }
        uint64_t carry = chunk;
        for (size_t j = 0; j < count; j++) {
            uint64_t v = (uint64_t)w[j] * mul + carry;
            w[j] = (uint32_t)v; carry = v >> 32;
        }
        if (carry) w[count++] = (uint32_t)carry;
    }
    *n = oceanBigTrim(w, count);
    return w;
}
typedef struct { size_t exponent, n; uint32_t *w; } OceanPow10;
typedef struct { OceanPow10 entries[256]; size_t count; } OceanPow10Cache;
// 10^e, cached; the cache owns the result.
static const uint32_t *oceanBigPow10(OceanPow10Cache *cache, size_t e, size_t *n) {
    for (size_t i = 0; i < cache->count; i++)
        if (cache->entries[i].exponent == e) { *n = cache->entries[i].n; return cache->entries[i].w; }
    uint32_t *w; size_t wn;
    if (e <= 9) {
        w = oceanBigAlloc(1); w[0] = 1; for (size_t i = 0; i < e; i++) w[0] *= 10; wn = 1;
    } else {
        size_t hn; const uint32_t *half = oceanBigPow10(cache, e / 2, &hn);
        w = oceanBigMultiply(half, hn, half, hn); wn = oceanBigTrim(w, 2 * hn);
        if (e & 1) {
            uint32_t *grown = oceanBigAlloc(wn + 1); uint64_t carry = 0;
            for (size_t i = 0; i < wn; i++) { uint64_t v = (uint64_t)w[i] * 10 + carry; grown[i] = (uint32_t)v; carry = v >> 32; }
            grown[wn] = (uint32_t)carry; free(w); w = grown; wn = oceanBigTrim(w, wn + 1);
        }
    }
    if (cache->count < sizeof(cache->entries) / sizeof(*cache->entries))
        cache->entries[cache->count++] = (OceanPow10){e, wn, w};
    else { // Cache full: replace an entry. No caller holds a cached power across lookups.
        free(cache->entries[0].w); cache->entries[0] = (OceanPow10){e, wn, w};
    }
    *n = wn;
    return w;
}
static uint32_t *oceanBigFromDecimal(OceanPow10Cache *cache, const char *d, size_t len, size_t *n) {
    if (len <= OCEAN_BIG_SMALL_DIGITS) return oceanBigFromDecimalSmall(d, len, n);
    size_t low = len / 2, high = len - low, hn, ln, pn;
    uint32_t *h = oceanBigFromDecimal(cache, d, high, &hn);
    uint32_t *l = oceanBigFromDecimal(cache, d + high, low, &ln);
    const uint32_t *p = oceanBigPow10(cache, low, &pn);
    uint32_t *r = oceanBigMultiply(h, hn, p, pn);
    oceanBigAddAt(r, hn + pn, l, ln, 0);
    *n = oceanBigTrim(r, hn + pn);
    free(h); free(l);
    return r;
}

// Convert source digits to LLVM's exact unsigned hexadecimal literal spelling.
// Limbs are temporary; the returned spelling belongs to the token storage.
static inline char *wideIntegerLiteral(const char *digits, size_t length, unsigned base,
                                       unsigned *bits, int *powerOfTwo) {
    // Power-of-two bases can be packed directly, even at LLVM's maximum width.
    if (base != 10) {
        while (length && *digits == '0') { digits++; length--; }
        unsigned digitBits = base == 16 ? 4 : base == 8 ? 3 : 1;
        unsigned char first = length ? (unsigned char)*digits : '0';
        unsigned top = first <= '9' ? first - '0' : (first | 32) - 'a' + 10;
        unsigned topBits = 0; for (unsigned value = top; value; value >>= 1) topBits++;
        if (length && length - 1 > (OCEAN_MAX_INTEGER_BITS - topBits) / digitBits) return NULL;
        *bits = length ? (unsigned)((length - 1) * digitBits + topBits) : 0;
        *powerOfTwo = top && !(top & (top - 1));
        size_t nibbles = *bits ? (*bits + 3) / 4 : 1;
        char *result = malloc(nibbles + 4);
        if (!result) exit(1);
        result[0] = 'u'; result[1] = '0'; result[2] = 'x';
        unsigned pending = 0, pendingBits = 0;
        size_t output = nibbles + 3;
        result[output] = 0;
        for (size_t i = length; i; i--) {
            unsigned char c = digits[i - 1];
            unsigned digit = c <= '9' ? c - '0' : (c | 32) - 'a' + 10;
            if (i != 1 && digit) *powerOfTwo = 0;
            pending |= digit << pendingBits; pendingBits += digitBits;
            while (pendingBits >= 4 && output > 3) {
                result[--output] = "0123456789abcdef"[pending & 15];
                pending >>= 4; pendingBits -= 4;
            }
        }
        if (output > 3) result[--output] = "0123456789abcdef"[pending & 15];
        return result;
    }
    // Decimal: 2^8388608 has 2,525,223 digits, so longer literals cannot fit.
    while (length > 1 && *digits == '0') { digits++; length--; }
    if (length > 2525223) return NULL;
    OceanPow10Cache *cache = calloc(1, sizeof(*cache));
    if (!cache) exit(1);
    size_t count;
    uint32_t *words = oceanBigFromDecimal(cache, digits, length, &count);
    for (size_t i = 0; i < cache->count; i++) free(cache->entries[i].w);
    free(cache);
    if (!count) count = 1;
    if (count > OCEAN_MAX_INTEGER_BITS / 32) { free(words); return NULL; }
    unsigned topBits = 0; uint32_t top = words[count - 1];
    for (uint32_t value = top; value; value >>= 1) topBits++;
    *bits = (unsigned)((count - 1) * 32 + topBits);
    *powerOfTwo = top && !(top & (top - 1));
    for (size_t i = 0; i + 1 < count; i++) if (words[i]) *powerOfTwo = 0;
    char *result = malloc(4 + count * 8);
    if (!result) exit(1);
    size_t cursor = (size_t)sprintf(result, "u0x%x", top);
    for (size_t i = count - 1; i; i--) cursor += (size_t)sprintf(result + cursor, "%08x", words[i - 1]);
    free(words); return result;
}
#endif
