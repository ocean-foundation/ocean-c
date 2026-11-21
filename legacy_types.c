#include "legacy_types.h"
#include <stdlib.h>
#include <string.h>

typedef struct { char *text; size_t length, capacity; } Text;

static void append(Text *t, const char *s, size_t n) {
    if (t->length + n + 1 > t->capacity) {
        t->capacity = (t->length + n + 1) * 2;
        t->text = realloc(t->text, t->capacity);
        if (!t->text) abort();
    }
    memcpy(t->text + t->length, s, n);
    t->length += n;
    t->text[t->length] = 0;
}
static void appends(Text *t, const char *s) { append(t, s, strlen(s)); }
static void prepend(Text *t, const char *s) {
    Text joined = {0};
    appends(&joined, s);
    if (t->text) appends(&joined, t->text);
    free(t->text);
    *t = joined;
}

static int word(enum tokenType k) {
    return k == IDENTIFIER || k == LITERAL_INT || k == LITERAL_FLOAT || k == UNDERSCORE ||
           (k >= TYPE && k <= ASM);
}

char *joinTypeTokens(const token *tokens, size_t count) {
    Text out = {0};
    appends(&out, "");
    for (size_t i = 0; i < count; i++) {
        enum tokenType k = tokens[i].type;
        if (i) {
            enum tokenType p = tokens[i - 1].type;
            int space = (word(p) && word(k)) || p == COMMA || p == SEMICOLON ||
                k == BITWISE_OR || p == BITWISE_OR ||
                (p == RIGHT_PAREN && (word(k) || k == LEFT_PAREN || k == STAR || k == LEFT_BRACKET)) ||
                (p == LEFT_CURLY_BRACE && k != RIGHT_CURLY_BRACE) ||
                (k == RIGHT_CURLY_BRACE && p != LEFT_CURLY_BRACE) ||
                (k == LEFT_CURLY_BRACE && word(p));
            if (space)
                appends(&out, " ");
        }
        appends(&out, tokens[i].lexeme ? tokens[i].lexeme : "");
    }
    return out.text;
}

typedef struct { const token *tokens; size_t count; const char *source; } Legacy;

static enum tokenType kind(Legacy *g, size_t i) { return i < g->count ? g->tokens[i].type : EOF_TOKEN; }
static int named(Legacy *g, size_t i, const char *name) {
    return kind(g, i) == IDENTIFIER && !strcmp(g->tokens[i].lexeme, name);
}
static size_t sourceOffset(const char *source, token at) {
    size_t offset = 0;
    for (long line = 1; source[offset] && line < at.line; offset++)
        if (source[offset] == '\n') line++;
    return offset + (size_t)(at.column > 0 ? at.column - 1 : 0);
}
/* Copy tokens [from, to) as written in the source when possible, else re-spaced. */
static void verbatim(Legacy *g, Text *out, size_t from, size_t to) {
    if (from >= to) return;
    int exact = g->source != NULL;
    for (size_t i = from; exact && i < to; i++)
        if (g->tokens[i].type == LITERAL_STRING || !g->tokens[i].lexeme ||
            g->tokens[i].filename != g->tokens[from].filename) exact = 0;
    if (exact) {
        size_t start = sourceOffset(g->source, g->tokens[from]);
        size_t end = sourceOffset(g->source, g->tokens[to - 1]) + strlen(g->tokens[to - 1].lexeme);
        if (end > start && end <= strlen(g->source) &&
            !strncmp(g->source + start, g->tokens[from].lexeme, strlen(g->tokens[from].lexeme))) {
            append(out, g->source + start, end - start);
            return;
        }
    }
    char *s = joinTypeTokens(g->tokens + from, to - from);
    appends(out, s);
    free(s);
}
/* Index after the delimiter matching the opener at i, or 0 if delimiters are
 * mismatched or a statement ends first. Angle closers count >> as two. */
static size_t balanced(Legacy *g, size_t i) {
    enum tokenType open = kind(g, i);
    if (open == LESS_THAN) {
        size_t depth = 0;
        for (; i < g->count; i++) {
            enum tokenType k = kind(g, i);
            if (k == LESS_THAN) depth++;
            else if (k == GREATER_THAN) depth--;
            else if (k == BITSHIFT_RIGHT) depth = depth >= 2 ? depth - 2 : 0;
            else if (k == SEMICOLON || k == LEFT_CURLY_BRACE || k == EOF_TOKEN) return 0;
            if (!depth) return i + 1;
        }
        return 0;
    }
    enum tokenType stack[256];
    size_t depth = 0;
    for (; i < g->count; i++) {
        enum tokenType k = kind(g, i);
        if (k == LEFT_PAREN || k == LEFT_BRACKET || k == LEFT_CURLY_BRACE) {
            if (depth == sizeof(stack) / sizeof(*stack)) return 0;
            stack[depth++] = k == LEFT_PAREN ? RIGHT_PAREN : k == LEFT_BRACKET ? RIGHT_BRACKET : RIGHT_CURLY_BRACE;
        } else if (k == RIGHT_PAREN || k == RIGHT_BRACKET || k == RIGHT_CURLY_BRACE) {
            if (!depth || stack[depth - 1] != k) return 0;
            if (!--depth) return i + 1;
        } else if ((k == SEMICOLON && open != LEFT_CURLY_BRACE) || k == EOF_TOKEN) return 0;
    }
    return 0;
}
static int startsType(enum tokenType k) {
    return k == IDENTIFIER || k == ANY || k == STAR || k == LEFT_BRACKET || k == FUNC ||
           k == MIXED || k == STRUCT || k == INTERFACE;
}

static size_t legacyType(Legacy *g, size_t i, Text *out, int *changed);

/* A base type without its postfix suffixes. Returns the index after it, or 0. */
static size_t legacyBase(Legacy *g, size_t i, Text *out, int *changed) {
    enum tokenType k = kind(g, i);
    if (named(g, i, "buffer")) {
        if (kind(g, i + 1) != LESS_THAN) { appends(out, "buffer"); return i + 1; }
        size_t close = balanced(g, i + 1);
        if (!close) return 0;
        // A buffer's first bracket is its own dimension: buffer<T>[N] -> buffer<T, N>.
        if (kind(g, close) == LEFT_BRACKET) {
            size_t end = balanced(g, close);
            if (!end) return 0;
            *changed |= LEGACY_BUFFER_SIZE;
            verbatim(g, out, i, close - 1);
            if (end > close + 2) { appends(out, ", "); verbatim(g, out, close + 1, end - 1); }
            appends(out, ">");
            return end;
        }
        verbatim(g, out, i, close);
        return close;
    }
    // varint(n) / varuint(n): the parenthesized width belongs to the base type.
    if ((named(g, i, "varint") || named(g, i, "varuint")) && kind(g, i + 1) == LEFT_PAREN) {
        size_t close = balanced(g, i + 1);
        if (!close) return 0;
        verbatim(g, out, i, close);
        return close;
    }
    if (named(g, i, "map") && kind(g, i + 1) == LEFT_BRACKET) {
        size_t close = balanced(g, i + 1);
        if (!close) return 0;
        verbatim(g, out, i, close);
        Text value = {0};
        size_t end = legacyType(g, close, &value, changed);
        if (!end) { free(value.text); return 0; }
        appends(out, value.text);
        free(value.text);
        return end;
    }
    if (k == FUNC) {
        if (kind(g, i + 1) != LEFT_PAREN) return 0;
        size_t params = balanced(g, i + 1);
        if (!params) return 0;
        verbatim(g, out, i, params);
        if (kind(g, params) == LEFT_PAREN) {
            size_t results = balanced(g, params);
            if (!results) return 0;
            appends(out, " ");
            verbatim(g, out, params, results);
            return results;
        }
        if (!startsType(kind(g, params))) return params;
        Text result = {0};
        size_t end = legacyType(g, params, &result, changed);
        if (!end) { free(result.text); return params; }
        appends(out, " ");
        appends(out, result.text);
        free(result.text);
        return end;
    }
    if (k == STRUCT || k == INTERFACE) {
        if (kind(g, i + 1) != LEFT_CURLY_BRACE) return 0;
        size_t end = balanced(g, i + 1);
        if (!end) return 0;
        verbatim(g, out, i, end);
        return end;
    }
    if (k != IDENTIFIER && k != ANY) return 0;
    size_t end = i + 1;
    while (kind(g, end) == DOT && kind(g, end + 1) == IDENTIFIER) end += 2;
    if (kind(g, end) == LESS_THAN) {
        size_t close = balanced(g, end);
        if (!close) return 0;
        end = close;
    }
    verbatim(g, out, i, end);
    return end;
}

static size_t legacyType(Legacy *g, size_t i, Text *out, int *changed) {
    if (kind(g, i) == STAR || kind(g, i) == MIXED) {
        // A prefix modifier already precedes the complete type.
        Text rest = {0};
        size_t end = legacyType(g, i + 1, &rest, changed);
        if (!end) { free(rest.text); return 0; }
        appends(out, kind(g, i) == STAR ? "*" : "mixed ");
        appends(out, rest.text);
        free(rest.text);
        return end;
    }
    if (kind(g, i) == LEFT_BRACKET) {
        size_t close = balanced(g, i);
        if (!close) return 0;
        Text rest = {0};
        size_t end = legacyType(g, close, &rest, changed);
        if (!end) { free(rest.text); return 0; }
        verbatim(g, out, i, close);
        appends(out, rest.text);
        free(rest.text);
        return end;
    }
    Text base = {0};
    appends(&base, "");
    size_t end = legacyBase(g, i, &base, changed);
    if (!end) { free(base.text); return 0; }
    // Postfix suffixes wrap the type built so far, so each one becomes a prefix.
    for (;;) {
        if (kind(g, end) == STAR) {
            prepend(&base, "*");
            end++; *changed |= LEGACY_POINTER;
        } else if (kind(g, end) == LEFT_BRACKET) {
            size_t close = balanced(g, end);
            if (!close) break;
            Text suffix = {0};
            verbatim(g, &suffix, end, close);
            prepend(&base, suffix.text);
            free(suffix.text);
            end = close; *changed |= LEGACY_ARRAY;
        } else break;
    }
    appends(out, base.text);
    free(base.text);
    return end;
}

char *legacyTypeRewrite(const token *tokens, size_t count, size_t *consumed, int *kinds,
                         const char *source) {
    Legacy g = {tokens, count, source};
    Text out = {0};
    appends(&out, "");
    int changed = 0;
    size_t end = legacyType(&g, 0, &out, &changed);
    if (!end || !changed) { free(out.text); return NULL; }
    if (consumed) *consumed = end;
    if (kinds) *kinds = changed;
    return out.text;
}

char *legacyTypeMessage(const char *replacement, int kinds) {
    const char *lead = kinds & LEGACY_ARRAY ? "Square brackets go before the type for an array." :
                       kinds & LEGACY_POINTER ? "The pointer star goes before the type." :
                       "A buffer's size is its second type argument.";
    Text out = {0};
    appends(&out, lead);
    appends(&out, " Did you mean '");
    appends(&out, replacement);
    appends(&out, "'?");
    return out.text;
}
