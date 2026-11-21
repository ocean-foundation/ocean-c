#ifndef OCEAN_LEGACY_TYPES_H
#define OCEAN_LEGACY_TYPES_H
#include <stddef.h>
#include "token.h"

/* Parse a type written in the removed postfix syntax (int[], T*, buffer<T>[N])
 * starting at tokens[0] and return the equivalent prefix spelling ([]int, *T,
 * buffer<T, N>). Nested type arguments, parameters, and bodies are copied
 * verbatim; `ocean fix` repeats until no legacy spans remain. *consumed
 * receives the number of tokens read. Returns NULL if no legacy suffix follows
 * a type at tokens[0]. The caller frees the result. */
enum { LEGACY_ARRAY = 1, LEGACY_POINTER = 2, LEGACY_BUFFER_SIZE = 4 };
/* kinds receives the LEGACY_* forms that were found. */
/* source, when non-NULL, is the text the tokens came from; verbatim parts are copied from it. */
char *legacyTypeRewrite(const token *tokens, size_t count, size_t *consumed, int *kinds,
                         const char *source);
/* The diagnostic for a legacy span, naming its prefix replacement. */
char *legacyTypeMessage(const char *replacement, int kinds);

/* Join tokens with conventional spacing, for diagnostics and rewrites. */
char *joinTypeTokens(const token *tokens, size_t count);

#endif
