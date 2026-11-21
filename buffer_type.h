#ifndef OCEAN_BUFFER_TYPE_H
#define OCEAN_BUFFER_TYPE_H

#include "ast.h"
#include <string.h>

static inline int isBufferType(typeTokens t) {
    return t.nTokens && t.tokens[0].type == IDENTIFIER && !strcmp(t.tokens[0].lexeme, "buffer");
}

/* Split buffer<T> (unsized) and buffer<T, dimension>. */
static inline int bufferTypeParts(typeTokens t, typeTokens *element, typeTokens *dimension) {
    if (!isBufferType(t) || t.nTokens < 4 || t.tokens[1].type != LESS_THAN ||
        t.tokens[t.nTokens - 1].type != GREATER_THAN)
        return 0;
    *dimension = (typeTokens){0};
    size_t depth = 0, comma = 0, close = t.nTokens - 1;
    for (size_t i = 2; i < close; i++) {
        enum tokenType kind = t.tokens[i].type;
        if (kind == LESS_THAN || kind == LEFT_BRACKET || kind == LEFT_PAREN || kind == LEFT_CURLY_BRACE)
            depth++;
        else if (kind == GREATER_THAN || kind == RIGHT_BRACKET || kind == RIGHT_PAREN ||
                 kind == RIGHT_CURLY_BRACE) {
            if (!depth) return 0;
            depth--;
        } else if (kind == COMMA && !depth) {
            if (comma) return 0;
            comma = i;
        }
    }
    if (depth) return 0;
    size_t elementEnd = comma ? comma : close;
    if (elementEnd <= 2) return 0;
    *element = (typeTokens){elementEnd - 2, t.tokens + 2};
    if (comma) {
        if (comma + 1 >= close) return 0;
        *dimension = (typeTokens){close - comma - 1, t.tokens + comma + 1};
    }
    return 1;
}

/* Unsized = 0, fixed = 1, runtime expression = 2, invalid literal = -1. */
static inline int bufferDimensionKind(typeTokens dimension) {
    if (!dimension.nTokens)
        return 0;
    if (dimension.nTokens == 1 && dimension.tokens[0].type == LITERAL_INT)
        return dimension.tokens[0].numValue.integer > 0 ? 1 : -1;
    if (dimension.nTokens == 2 && dimension.tokens[0].type == MINUS &&
        dimension.tokens[1].type == LITERAL_INT)
        return -1;
    return 2;
}
#endif
