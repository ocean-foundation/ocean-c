#ifndef OCEAN_ARRAY_TYPE_H
#define OCEAN_ARRAY_TYPE_H
#include "buffer_type.h"

/* Split map[K]V while respecting nested key types. Suffixes belong to V. */
static inline int mapTypeParts(typeTokens t, typeTokens *key, typeTokens *value) {
    if (t.nTokens < 5 || t.tokens[0].type != IDENTIFIER ||
        strcmp(t.tokens[0].lexeme, "map") || t.tokens[1].type != LEFT_BRACKET) return 0;
    size_t depth = 1, i = 2;
    for (; i < t.nTokens; i++) {
        if (t.tokens[i].type == LEFT_BRACKET) depth++;
        if (t.tokens[i].type == RIGHT_BRACKET) { if (!--depth) break; }
    }
    if (i == 2 || i + 1 >= t.nTokens) return 0;
    *key = (typeTokens){i - 2, t.tokens + 2};
    *value = (typeTokens){t.nTokens - i - 1, t.tokens + i + 1};
    return 1;
}
/* Index after the ']' closing the bracket at t.tokens[open], or 0. */
static inline size_t closingBracket(typeTokens t, size_t open) {
    size_t depth = 0;
    for (size_t i = open; i < t.nTokens; i++) {
        if (t.tokens[i].type == LEFT_BRACKET) depth++;
        if (t.tokens[i].type == RIGHT_BRACKET && !--depth) return i + 1;
    }
    return 0;
}
/* []T, optionally preceded by mixed: a dynamic array of T. */
static inline int arrayElementType(typeTokens t, typeTokens *element) {
    if (t.nTokens && t.tokens[0].type == MIXED) { t.tokens++; t.nTokens--; }
    if (t.nTokens < 3 || t.tokens[0].type != LEFT_BRACKET || t.tokens[1].type != RIGHT_BRACKET)
        return 0;
    *element = (typeTokens){t.nTokens - 2, t.tokens + 2};
    return 1;
}
/* [N]T or [n]T: the outer dimension and its element type. */
static inline int sizedArrayTypeParts(typeTokens t, typeTokens *element, typeTokens *dimension) {
    if (t.nTokens < 4 || t.tokens[0].type != LEFT_BRACKET || t.tokens[1].type == RIGHT_BRACKET)
        return 0;
    size_t end = closingBracket(t, 0);
    if (!end || end >= t.nTokens) return 0;
    *dimension = (typeTokens){end - 2, t.tokens + 1};
    *element = (typeTokens){t.nTokens - end, t.tokens + end};
    return 1;
}
static inline int arrayHasRuntimeDimension(typeTokens t) {
    typeTokens element, dimension;
    if (!sizedArrayTypeParts(t, &element, &dimension)) return 0;
    return bufferDimensionKind(dimension) == 2 || arrayHasRuntimeDimension(element);
}
/* array<T> erases only the length of an immutable-size array. */
static inline int unsizedArrayTypeParts(typeTokens t, typeTokens *element) {
    if (t.nTokens < 4 || t.tokens[0].type != IDENTIFIER ||
        strcmp(t.tokens[0].lexeme, "array") || t.tokens[1].type != LESS_THAN ||
        t.tokens[t.nTokens - 1].type != GREATER_THAN) return 0;
    size_t depth = 0;
    for (size_t i = 2; i + 1 < t.nTokens; i++) {
        enum tokenType k = t.tokens[i].type;
        if (k == LESS_THAN) depth++;
        else if (k == GREATER_THAN) { if (!depth) return 0; depth--; }
        else if (k == COMMA && !depth) return 0;
    }
    if (depth) return 0;
    *element = (typeTokens){t.nTokens - 3, t.tokens + 2};
    return 1;
}
static inline int builtinStorageTypeName(const char *name) {
    const char *names[] = {"int", "uint", "i8",  "i16", "i32",  "i64",   "u8",
                           "u16", "u32",  "u64",  "float", "f32", "f64", "bool", "string", "any"};
    for (size_t i = 0; i < sizeof(names) / sizeof(*names); i++)
        if (!strcmp(name, names[i]))
            return 1;
    return 0;
}
#endif
