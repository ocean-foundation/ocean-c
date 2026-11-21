#define _POSIX_C_SOURCE 200809L
#include <limits.h>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "parser.h"
#include "diagnostic.h"

#include "dynarray.h"
#include "token.h"
#include "ast.h"
#include "value_list.h"
#include "core.h"
#include "legacy_types.h"

typedef struct parserState {
    char *packageName;
    const char *source;

    token *tokens;
    size_t tokenIndex;
    size_t tokensLen;

    char hasError;
    char isSynchronizing;
    char quietErrors;
    char recoverStatements;
    char pendingGreater; // Second half of >> while closing nested angle types.
    char allowTypeGuard;
    size_t typeGuards;
    size_t functionDepth;
    size_t loopDepth;
    size_t switchDepth;
    size_t syntaxDepth;
    size_t signatureDepth;
    size_t fallthroughDepth;

    char castTarget;     // An ungrouped cast target ends before a following '*'.
    char legacyPending;  // A speculative parse accepted legacy postfix type syntax.
    char fixMode;        // Record legacy type rewrites instead of reporting them.
    typeRewrite *rewrites;
    size_t nRewrites;
    char **knownTypes;   // Fix mode: names that denote types in expressions.
    size_t nKnownTypes;
    token *typeScope;    // Fix mode: enclosing type parameter names.
    size_t nTypeScope;
} parserState;

static token endToken(parserState *state) {
    token tok = {.type = EOF_TOKEN, .lexeme = "EOF", .filename = "<input>"};
    if (state->tokensLen) {
        tok = state->tokens[state->tokensLen - 1];
        tok.type = EOF_TOKEN;
    }
    return tok;
}

static token currentToken(parserState *state) {
    token tok = state->tokens[state->tokenIndex];
    if (state->pendingGreater) { tok.type = GREATER_THAN; tok.column++; tok.lexeme = ">"; }
    return tok;
}

static token advance(parserState *state) {
    if (state->tokenIndex + 1 >= state->tokensLen) {
        state->hasError = state->isSynchronizing = 1;
        return endToken(state);
    }
    state->pendingGreater = 0;
    state->tokenIndex++;
    return currentToken(state);
}

static token peek(parserState *state) {
    if (state->tokenIndex + 1 >= state->tokensLen) return endToken(state);
    return state->tokens[state->tokenIndex + 1];
}

#define CHECK_MALLOC(ptr) do {\
        if (ptr == nullptr) {\
            printf("Compiler Error: Out of memory - Unable to allocate heap memory.");\
            if (ABORT_ON_ERROR) abort();\
            exit(-1);\
        }\
    } while (0)

#define CHECK_SYNC if (state->isSynchronizing) return (expr){0}

#define SET_TOK tok = currentToken(state)

#define DEFINE_TOK token SET_TOK

#define CONSTRUCT_EXPR_RES(typeP, underlyingP, res)\
    expr res = {0};\
    res.type = typeP;\
    res.underlying = malloc(sizeof(underlyingP));\
    CHECK_MALLOC(res.underlying);\
    memcpy(res.underlying, &underlyingP, sizeof(underlyingP));

#define isAssignmentOperator(t) (t > TOKEN_SPECIAL_ASSIGN_START && t < TOKEN_SPECIAL_ASSIGN_END)



#define expect(tokType, message, retType) do {\
        if (tok.type != tokType) {\
            diagnostic(state->source, tok, "syntax", "error", "%s", message);\
            state->hasError = 1;\
            state->isSynchronizing = 1;\
            return (retType){0};\
        }\
    } while (0)

static expr comma(parserState *state);
static char signatureEllipsis(parserState *state);
static char parseCastTarget(parserState *state, typeTokens *target);
static char parseSignatureType(parserState *state, size_t depth);
static char parseTypeConstraint(parserState *state);
static char parseInterfaceBody(parserState *state, struct stmt_interface *node);
static char tryCallTypeArguments(parserState *state, struct expr_instantiation *result);
static typeTokens copySignatureSpan(parserState *state, size_t start, size_t end);
static char signatureError(parserState *state, const char *message);
static char legacySuffix(parserState *state, size_t start);
static size_t tokenPosition(parserState *state, token at);
static token expressionRoot(expr e);
static char typeLikeExpression(parserState *state, expr e);

static expr assignment(parserState *state);

static stmt parseFuncDeclaration(parserState *state, char isExtern, char hasKeyword, char anonymous);

static expr parseComposite(parserState *state, expr type) {
    token location = currentToken(state);
    token tok = advance(state);
    exprlist keys = {0}, values = {0};
    init_exprlist(&keys);
    init_exprlist(&values);
    int keyed = -1;
    while (tok.type != RIGHT_CURLY_BRACE) {
        expr value = assignment(state);
        if (state->isSynchronizing) goto invalid;
        SET_TOK;
        expr key = {0};
        char hasKey = tok.type == COLON;
        if (keyed != -1 && keyed != hasKey) {
            diagnostic(state->source, tok, "syntax", "error", "Cannot mix keyed and positional literal entries");
            goto invalid;
        }
        keyed = hasKey;
        if (hasKey) {
            key = value;
            advance(state);
            value = assignment(state);
            if (state->isSynchronizing) goto invalid;
            SET_TOK;
        }
        push_exprlist(&keys, key);
        push_exprlist(&values, value);
        if (tok.type == RIGHT_CURLY_BRACE) break;
        if (tok.type != COMMA) {
            diagnostic(state->source, tok, "syntax", "error", "Expected comma between literal entries");
            goto invalid;
        }
        tok = advance(state);
    }
    advance(state);
    struct expr_composite node = {.type = type, .location = location, .nEntries = values.top,
        .keys = keys.top ? to_exprarray(&keys) : nullptr,
        .values = values.top ? to_exprarray(&values) : nullptr};
    free_exprlist(&keys);
    free_exprlist(&values);
    CONSTRUCT_EXPR_RES(EXPR_TYPE_COMPOSITE, node, result);
    result.location = location;
    return result;
invalid:
    free_exprlist(&keys);
    free_exprlist(&values);
    state->hasError = state->isSynchronizing = 1;
    return (expr){0};
}

static expr atomicImpl(parserState *state);
static expr atomic(parserState *state) {
    token location = currentToken(state);
    expr result = atomicImpl(state);
    result.location = location;
    return result;
}

// A type in expression position: a literal prefix ([]int{...}, buffer<int, 4>{...},
// mixed []any{...}) or, without a body, a type operand ([n]T allocation, sizeof).
static expr typeExpressionAtom(parserState *state, char requireBody) {
    token tok = currentToken(state);
    size_t start = state->tokenIndex;
    if (!parseSignatureType(state, 0)) return (expr){0};
    struct expr_zero *prefix = calloc(1, sizeof(*prefix));
    CHECK_MALLOC(prefix);
    prefix->type = copySignatureSpan(state, start, state->tokenIndex);
    expr name = {.type = EXPR_TYPE_TYPE_NAME, .underlying = prefix, .location = tok};
    typeTokens *span = &prefix->type;
    char inferred = span->nTokens > 4 && span->tokens[0].type == LEFT_BRACKET &&
        span->tokens[1].type == DOT && span->tokens[2].type == DOT && span->tokens[3].type == DOT;
    if (currentToken(state).type != LEFT_CURLY_BRACE) {
        if (requireBody || inferred) {
            free(prefix->type.tokens); free(prefix);
            signatureError(state, inferred ? "Inferred array length requires a literal body"
                                           : "Array type expression requires a literal body");
            return (expr){0};
        }
        return name;
    }
    expr literal = parseComposite(state, name);
    if (inferred && literal.type == EXPR_TYPE_COMPOSITE) {
        // Normalize [...]T to the counted [n]T.
        size_t count = ((struct expr_composite *)literal.underlying)->nEntries;
        token dimension = span->tokens[1];
        dimension.type = LITERAL_INT;
        dimension.numValue.integer = (int64_t)count;
        char *text = malloc(24);
        CHECK_MALLOC(text);
        snprintf(text, 24, "%zu", count);
        dimension.lexeme = text;
        span->tokens[1] = dimension;
        memmove(span->tokens + 2, span->tokens + 4, (span->nTokens - 4) * sizeof(token));
        span->nTokens -= 2;
    }
    return literal;
}

static expr atomicImpl(parserState *state) {
    DEFINE_TOK;
    switch (tok.type) {
        case MIXED:
        case INTERFACE:
            return typeExpressionAtom(state, 1);
        case LEFT_BRACKET:
            return typeExpressionAtom(state, 0);
        case EXTERN: {
            tok = advance(state);
            expect(DOT, "Expected '.' after extern in an expression", expr);
            tok = advance(state);
            expect(IDENTIFIER, "Expected extern function name after extern.", expr);
            struct expr_identifier *identifier = malloc(sizeof(*identifier));
            CHECK_MALLOC(identifier);
            *identifier = (struct expr_identifier){.lexeme = tok, .externReference = 1};
            advance(state);
            return (expr){.type = EXPR_TYPE_IDENTIFIER, .underlying = identifier};
        }
        case NULL_KEYWORD: {
            struct expr_literal *literal = malloc(sizeof(*literal));
            CHECK_MALLOC(literal);
            *literal = (struct expr_literal){.type = LITERAL_TYPE_NULL};
            advance(state);
            return (expr){.type = EXPR_TYPE_LITERAL, .underlying = literal};
        }
        case LEFT_CURLY_BRACE:
            return parseComposite(state, (expr){0});
        case FUNC: {
            stmt function = parseFuncDeclaration(state, 0, 1, 1);
            CHECK_SYNC;
            return (expr){.type = EXPR_TYPE_FUNCTION, .underlying = function.value};
        }
        case VARINT:
        case VARUINT:
        case UNDERSCORE:
        case ANY:
        case IDENTIFIER: {
            if (tok.type == VARINT || tok.type == VARUINT) {
                size_t start = state->tokenIndex;
                if (!parseSignatureType(state, 0)) return (expr){0};
                struct expr_zero *prefix = calloc(1, sizeof(*prefix));
                CHECK_MALLOC(prefix);
                prefix->type = copySignatureSpan(state, start, state->tokenIndex);
                return (expr){.type = EXPR_TYPE_TYPE_NAME, .underlying = prefix, .location = tok};
            }
            if (tok.type == IDENTIFIER && !strcmp(tok.lexeme, "map") && peek(state).type == LEFT_BRACKET) {
                parserState trial = *state; trial.quietErrors = 1;
                if (parseSignatureType(&trial, 0) && currentToken(&trial).type == LEFT_CURLY_BRACE) {
                    size_t start = state->tokenIndex;
                    if (!parseSignatureType(state, 0)) return (expr){0};
                    struct expr_zero *prefix = calloc(1, sizeof(*prefix));
                    CHECK_MALLOC(prefix);
                    prefix->type = copySignatureSpan(state, start, state->tokenIndex);
                    expr name = {.type = EXPR_TYPE_TYPE_NAME, .underlying = prefix, .location = tok};
                    return parseComposite(state, name);
                }
            }
            if (tok.type == IDENTIFIER && !strcmp(tok.lexeme, "buffer") && peek(state).type == LESS_THAN) {
                // buffer<T, n> allocates; buffer<T>{...} and buffer<T, N>{...} are literals.
                parserState trial = *state; trial.quietErrors = 1;
                if (parseSignatureType(&trial, 0) && !trial.isSynchronizing) {
                    char sized = 0;
                    for (size_t i = state->tokenIndex; i < trial.tokenIndex; i++)
                        if (state->tokens[i].type == COMMA) sized = 1;
                    if (sized || currentToken(&trial).type == LEFT_CURLY_BRACE)
                        return typeExpressionAtom(state, 0);
                }
            }
            parserState constructorTrial = *state;
            constructorTrial.quietErrors = 1;
            char constructorSyntax = 0;
            if (tok.type == IDENTIFIER && (!strcmp(tok.lexeme, "make") || !strcmp(tok.lexeme, "new")) &&
                peek(state).type == LEFT_PAREN) {
                advance(&constructorTrial); advance(&constructorTrial);
                constructorSyntax = parseSignatureType(&constructorTrial, 0) &&
                    currentToken(&constructorTrial).type == RIGHT_PAREN;
            }
            if (tok.type == IDENTIFIER && (!strcmp(tok.lexeme, "zero") || (constructorSyntax &&
                 ((!strcmp(tok.lexeme, "make") && constructorTrial.tokenIndex >= 2 &&
                   (state->tokens[state->tokenIndex + 2].type == LEFT_BRACKET ||
                    constructorTrial.legacyPending ||
                    !strcmp(state->tokens[state->tokenIndex + 2].lexeme, "map"))) ||
                  !strcmp(tok.lexeme, "new")))) &&
                peek(state).type == LEFT_PAREN) {
                enum exprType constructor = !strcmp(tok.lexeme, "make") ? EXPR_TYPE_MAKE :
                    !strcmp(tok.lexeme, "new") ? EXPR_TYPE_NEW : EXPR_TYPE_ZERO;
                advance(state);
                tok = advance(state);
                if (tok.type == RIGHT_PAREN) {
                    signatureError(state, "zero requires exactly one type argument");
                    return (expr){0};
                }
                size_t start = state->tokenIndex;
                if (!parseSignatureType(state, 0)) return (expr){0};
                SET_TOK;
                expect(RIGHT_PAREN, "Expected closing parenthesis after zero type", expr);
                struct expr_zero zero = {.type = copySignatureSpan(state, start, state->tokenIndex)};
                advance(state);
                CONSTRUCT_EXPR_RES(constructor, zero, result);
                return result;
            }
            struct expr_identifier ident = {0};
            ident.lexeme = tok;
            expr ident_expr = {0};
            ident_expr.underlying = malloc(sizeof(struct expr_identifier));
            CHECK_MALLOC(ident_expr.underlying);
            ident_expr.type = EXPR_TYPE_IDENTIFIER;
            *(struct expr_identifier*) ident_expr.underlying = ident;
            tok = advance(state);
            return ident_expr;
        }
        case LITERAL_INT:
            struct expr_literal lit_int = {0};
            lit_int.type = LITERAL_TYPE_INT;
            lit_int.unsignedLiteral = tok.unsignedLiteral;
            lit_int.wideInteger = tok.wideInteger; lit_int.integerBits = tok.integerBits;
            lit_int.integerPowerOfTwo = tok.integerPowerOfTwo;
            lit_int.value = malloc(sizeof(int64_t));
            CHECK_MALLOC(lit_int.value);
            *(int64_t*) lit_int.value = tok.numValue.integer;
            expr lit_int_expr = {0};
            lit_int_expr.type = EXPR_TYPE_LITERAL;
            lit_int_expr.underlying = malloc(sizeof(struct expr_literal));
            CHECK_MALLOC(lit_int_expr.underlying);
            *(struct expr_literal*) lit_int_expr.underlying = lit_int;
            tok = advance(state);
            return lit_int_expr;
        case LITERAL_FLOAT:
            struct expr_literal lit_float = {0};
            lit_float.type = LITERAL_TYPE_FLOAT;
            lit_float.floatSpelling = tok.lexeme;
            lit_float.value = malloc(sizeof(double));
            CHECK_MALLOC(lit_float.value);
            *(double*) lit_float.value = tok.numValue.floating;
            expr lit_float_expr = {0};
            lit_float_expr.type = EXPR_TYPE_LITERAL;
            lit_float_expr.underlying = malloc(sizeof(struct expr_literal));
            CHECK_MALLOC(lit_float_expr.underlying);
            *(struct expr_literal*) lit_float_expr.underlying = lit_float;
            tok = advance(state);
            return lit_float_expr;
        case LITERAL_STRING:            
            struct expr_literal lit_str = {0};
            lit_str.type = LITERAL_TYPE_STRING;
            lit_str.value = tok.lexeme;
            lit_str.stringLength = tok.stringLength;
            expr lit_str_expr = {0};
            lit_str_expr.type = EXPR_TYPE_LITERAL;
            lit_str_expr.underlying = malloc(sizeof(struct expr_literal));
            CHECK_MALLOC(lit_str_expr.underlying);
            *(struct expr_literal*) lit_str_expr.underlying = lit_str;
            tok = advance(state);
            return lit_str_expr;
        default:
            diagnostic(state->source, tok, "syntax", "error", "Unexpected '%s', expected expression", tok.lexeme);
            state->isSynchronizing = 1;
            return (expr){0};
    }
    diagnostic(state->source, tok, "syntax", "error", "expected literal or identifier");
    return (expr){0};
}

// primary includes:
// member access (for structs and packages), array indexing,
// grouping (), function calls, and postfix ++ and --
static expr primary(parserState *state) {
    DEFINE_TOK;
    expr parent = {0};
    if (tok.type == LEFT_PAREN) {
        tok = advance(state);
        parent = comma(state);
        CHECK_SYNC;
        SET_TOK;
        expect(RIGHT_PAREN, "expected right paren", expr);
        tok = advance(state);
    } else {
        parent = atomic(state);
    }
    CHECK_SYNC;
    struct expr_unary unary_temp = {0};
    for (size_t i = 0; i < PARSER_MAX_RECURSION_DEPTH; i++) {
        SET_TOK;
        token location = tok;
        switch (tok.type) {
            case ARROW: {
                advance(state);
                struct expr_typecast cast = {.child = parent};
                if (!parseCastTarget(state, &cast.type)) return (expr){0};
                CONSTRUCT_EXPR_RES(EXPR_TYPE_TYPECAST, cast, result);
                parent = result;
                break;
            }

            case LEFT_CURLY_BRACE: {
                if (parent.type != EXPR_TYPE_IDENTIFIER && parent.type != EXPR_TYPE_DOT &&
                    parent.type != EXPR_TYPE_INDEX && parent.type != EXPR_TYPE_INSTANTIATION &&
                    parent.type != EXPR_TYPE_TYPE_NAME) goto endLoop;
                // Legacy int[]{...} / T[N]{...}: array brackets now precede the element type.
                if (parent.type == EXPR_TYPE_INDEX &&
                    !legacySuffix(state, tokenPosition(state, expressionRoot(parent)))) return (expr){0};
                expr typeName = parent;
                while (typeName.type == EXPR_TYPE_INDEX || typeName.type == EXPR_TYPE_INSTANTIATION)
                    typeName = typeName.type == EXPR_TYPE_INDEX ?
                        ((struct expr_index*)typeName.underlying)->parent :
                        ((struct expr_instantiation*)typeName.underlying)->parent;
                if (typeName.type == EXPR_TYPE_DOT)
                    typeName = ((struct expr_dot*)typeName.underlying)->field;
                parent = parseComposite(state, parent);
                CHECK_SYNC;
                break;
            }
            case DOT:
                if (signatureEllipsis(state)) goto endLoop;
                // member access
                tok = advance(state);
                if (tok.type == LEFT_PAREN) {
                    tok = advance(state);
                    struct expr_assertion assertion = {.child = parent};
                    if (tok.type == TYPE) {
                        if (!state->allowTypeGuard) {
                            signatureError(state, "Type guard is only valid in a type switch header");
                            return (expr){0};
                        }
                        assertion.isTypeGuard = 1;
                        state->typeGuards++;
                        tok = advance(state);
                    } else {
                        size_t start = state->tokenIndex;
                        if (!parseSignatureType(state, 0)) return (expr){0};
                        assertion.type = copySignatureSpan(state, start, state->tokenIndex);
                        SET_TOK;
                    }
                    if (currentToken(state).type == LEFT_CURLY_BRACE) {
                        expr pattern = parseComposite(state, (expr){0});
                        if (state->isSynchronizing) return (expr){0};
                        assertion.pattern = malloc(sizeof(expr));
                        CHECK_MALLOC(assertion.pattern);
                        *assertion.pattern = pattern;
                        SET_TOK;
                    }
                    expect(RIGHT_PAREN, "Expected closing type assertion parenthesis", expr);
                    advance(state);
                    CONSTRUCT_EXPR_RES(EXPR_TYPE_ASSERTION, assertion, result);
                    parent = result;
                    break;
                }
                expect(IDENTIFIER, "Expected member name after dot", expr);
                struct expr_dot dot = {0};
                dot.parent = parent;
                dot.field = atomic(state);
                CHECK_SYNC;
                parent.underlying = malloc(sizeof(struct expr_dot));
                CHECK_MALLOC(parent.underlying);
                *(struct expr_dot*) parent.underlying = dot;
                parent.type = EXPR_TYPE_DOT;
                break;
            case LESS_THAN:
            case LEFT_BRACKET: {
                char angle = tok.type == LESS_THAN;
                parserState inferred = *state;
                if (!angle) advance(&inferred);
                inferred.quietErrors = 1;
                // T[], T[...]{...}, and T[n] after a type name are legacy array syntax.
                if (!angle && (signatureEllipsis(&inferred) || currentToken(&inferred).type == RIGHT_BRACKET ||
                               typeLikeExpression(state, parent))) {
                    // Legacy T[...]{...}, T[] and T[n] (or buffer<T>[n]) after a type name.
                    if (!legacySuffix(state, tokenPosition(state, expressionRoot(parent)))) return (expr){0};
                    if (currentToken(state).type == LEFT_CURLY_BRACE) {
                        parent = parseComposite(state, (expr){0});
                        CHECK_SYNC;
                    }
                    break;
                }
                struct expr_instantiation instance = {.parent = parent, .location = tok};
                if (angle && tryCallTypeArguments(state, &instance)) {
                    CONSTRUCT_EXPR_RES(EXPR_TYPE_INSTANTIATION, instance, result);
                    parent = result;
                    break;
                }
                if (angle) goto endLoop;
                // Not a type-argument list: index.
                // array indexing
                token indexLocation = tok;
                tok = advance(state);
                expr index = tok.type == COLON ? (expr){0} : comma(state);
                CHECK_SYNC;
                SET_TOK;
                if (tok.type == COLON) {
                    advance(state);
                    struct expr_slice slice = {.parent = parent, .start = index, .location = indexLocation};
                    if (currentToken(state).type != RIGHT_BRACKET) slice.end = comma(state);
                    CHECK_SYNC;
                    SET_TOK;
                    expect(RIGHT_BRACKET, "expected right bracket after slice", expr);
                    CONSTRUCT_EXPR_RES(EXPR_TYPE_SLICE, slice, result);
                    parent = result;
                    tok = advance(state);
                    break;
                }
                expect(RIGHT_BRACKET, "expected right bracket", expr);
                struct expr_index index_n = {.location = indexLocation};
                index_n.parent = parent;
                index_n.index = index;
                parent.underlying = malloc(sizeof(struct expr_index));
                CHECK_MALLOC(parent.underlying);
                *(struct expr_index*) parent.underlying = index_n;
                parent.type = EXPR_TYPE_INDEX;
                tok = advance(state);
                break;
            }
            case LEFT_PAREN:
                // function call
                token callLocation = tok;
                tok = advance(state);
                struct expr_call call = {.location = callLocation};
                call.func = parent;
                // parse func params
                exprlist *list = (exprlist*)malloc(sizeof(exprlist));
                CHECK_MALLOC(list);
                *list = (exprlist){0};
                init_exprlist(list);
                while (tok.type != RIGHT_PAREN) {
                    expr param = assignment(state);
                    CHECK_SYNC;
                    call.nParams++;
                    push_exprlist(list, param);
                    if (signatureEllipsis(state)) {
                        advance(state); advance(state); advance(state);
                        call.spread = 1;
                        if (currentToken(state).type != RIGHT_PAREN) {
                            signatureError(state, "Expanded argument must be last");
                            return (expr){0};
                        }
                    }
                    SET_TOK;
                    if (tok.type == COMMA) {
                        tok = advance(state);
                    } else if (tok.type != RIGHT_PAREN) {
                        diagnostic(state->source, tok, "syntax", "error", "expected comma or right paren");
                        state->isSynchronizing = 1;
                        return (expr){0};
                    }
                }
                tok = advance(state);
                call.params = call.nParams ? to_exprarray(list) : nullptr;
                free_exprlist(list);
                free(list);
                parent.underlying = malloc(sizeof(struct expr_call));
                CHECK_MALLOC(parent.underlying);
                *(struct expr_call*) parent.underlying = call;
                parent.type = EXPR_TYPE_CALL;
                break;
            case PLUS_PLUS:
                // postfix increment
                tok = advance(state);
                unary_temp.child = parent;
                unary_temp.operation = UNARY_POSTFIX_INCREMENT;
                parent.underlying = malloc(sizeof(struct expr_unary));
                CHECK_MALLOC(parent.underlying);
                *(struct expr_unary*) parent.underlying = unary_temp;
                parent.type = EXPR_TYPE_UNARY;
                break;
            case MINUS_MINUS:
                // postfix decrement
                tok = advance(state);
                unary_temp.child = parent;
                unary_temp.operation = UNARY_POSTFIX_DECREMENT;
                parent.underlying = malloc(sizeof(struct expr_unary));
                CHECK_MALLOC(parent.underlying);
                *(struct expr_unary*) parent.underlying = unary_temp;
                parent.type = EXPR_TYPE_UNARY;
                break;
            default:
                goto endLoop;
        }
        parent.location = location;

    }
    printf("Fatal compiler error: Parser maximum recursion depth reached.\n");
    if (ABORT_ON_ERROR) abort();
    exit(5);
    endLoop:
    return parent;
}

// secondary includes:
// sizeof(), address of (&), dereference (*),
// logical and bitwise not, unary negation, and
// prefix ++ and --
static expr secondaryImpl(parserState *state);
static expr secondary(parserState *state) {
    if (state->syntaxDepth >= PARSER_MAX_RECURSION_DEPTH) {
        token tok = state->tokens[state->tokenIndex];
        diagnostic(state->source, tok, "syntax", "error", "Parser nesting limit exceeded");
        state->hasError = state->isSynchronizing = 1;
        return (expr){0};
    }
    token location = currentToken(state);
    state->syntaxDepth++;
    expr result = secondaryImpl(state);
    state->syntaxDepth--;
    if (!result.location.filename)
        result.location = location;
    return result;
}

static expr secondaryImpl(parserState *state) {
    DEFINE_TOK;
    switch (tok.type) {
        case IDENTIFIER:
            if (strcmp(tok.lexeme, "sizeof") == 0 && peek(state).type == LEFT_PAREN) {
                tok = advance(state);
                tok = advance(state);
                expr inner = comma(state);
                CHECK_SYNC;
                SET_TOK;
                expect(RIGHT_PAREN, "expected right paren to close call to sizeof operator", expr);
                tok = advance(state);
                struct expr_unary unary_n = {0};
                unary_n.child = inner;
                unary_n.operation = UNARY_SIZEOF;
                CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n, res);
                return res;
            }
            return primary(state);
            break;
        case AMPERSAND:
            tok = advance(state);
            expr var = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n = {0};
            unary_n.child = var;
            unary_n.operation = UNARY_ADDRESS_OF;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n, res);
            return res;
        case STAR:
            tok = advance(state);
            expr ptr = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n2 = {0};
            unary_n2.child = ptr;
            unary_n2.operation = UNARY_DEREFERENCE;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n2, res2);
            return res2;
        case EXCLAMATION:
            tok = advance(state);
            expr child = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n3 = {0};
            unary_n3.child = child;
            unary_n3.operation = UNARY_LOGICAL_NOT;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n3, res3);
            return res3;
        case TILDE:
            tok = advance(state);
            expr child1 = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n4 = {0};
            unary_n4.child = child1;
            unary_n4.operation = UNARY_BITWISE_NOT;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n4, res4);
            return res4;
        case MINUS:
            tok = advance(state);
            expr child2 = secondary(state);
            CHECK_SYNC;
            if (child2.type == EXPR_TYPE_LITERAL) {
                struct expr_literal *literal = child2.underlying;
                if (literal->type == LITERAL_TYPE_INT && literal->wideInteger) {
                    literal->negativeWide = !literal->negativeWide;
                    return child2;
                }
                if (literal->type == LITERAL_TYPE_INT && literal->unsignedLiteral &&
                    *(uint64_t *)literal->value == (uint64_t)INT64_MAX + 1) {
                    literal->unsignedLiteral = 0; *(int64_t *)literal->value = INT64_MIN;
                    return child2;
                }
                if (literal->type == LITERAL_TYPE_INT && literal->unsignedLiteral) {
                    literal->wideInteger = malloc(24); CHECK_MALLOC(literal->wideInteger);
                    snprintf(literal->wideInteger, 24, "u0x%" PRIx64, *(uint64_t *)literal->value);
                    literal->integerBits = 64; literal->integerPowerOfTwo = 0;
                    literal->negativeWide = 1; return child2;
                }
            }
            struct expr_unary unary_n5 = {0};
            unary_n5.child = child2;
            unary_n5.operation = UNARY_NEGATE;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n5, res5);
            return res5;
        case PLUS_PLUS:
            tok = advance(state);
            expr child3 = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n6 = {0};
            unary_n6.child = child3;
            unary_n6.operation = UNARY_PREFIX_INCREMENT;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n6, res6);
            return res6;
        case MINUS_MINUS:
            tok = advance(state);
            expr child4 = secondary(state);
            CHECK_SYNC;
            struct expr_unary unary_n7 = {0};
            unary_n7.child = child4;
            unary_n7.operation = UNARY_PREFIX_DECREMENT;
            CONSTRUCT_EXPR_RES(EXPR_TYPE_UNARY, unary_n7, res7);
            return res7;
        default:
            return primary(state);
    }
    return (expr){0};
}

// All binary operators here associate left-to-right. Assignment and ternary
// expressions are parsed separately because they associate right-to-left.
static int binaryOperator(enum tokenType type, enum binaryExprType *operation) {
    switch (type) {
#define BINARY(tokenType, astType, precedence) case tokenType: *operation = astType; return precedence
        BINARY(LOGICAL_OR, EXPR_LOGICAL_OR, 1);
        BINARY(LOGICAL_AND, EXPR_LOGICAL_AND, 2);
        BINARY(BITWISE_OR, EXPR_BITWISE_OR, 3);
        BINARY(XOR, EXPR_XOR, 4);
        BINARY(AMPERSAND, EXPR_BITWISE_AND, 5);
        BINARY(EQUALS_EQUALS, EXPR_EQUALITY, 6);
        BINARY(NOT_EQUALS, EXPR_NOT_EQUALS, 6);
        BINARY(LESS_THAN, EXPR_LESS_THAN, 7);
        BINARY(LESS_EQUALS, EXPR_LESS_EQUALS, 7);
        BINARY(GREATER_THAN, EXPR_GREATER_THAN, 7);
        BINARY(GREATER_EQUALS, EXPR_GREATER_EQUALS, 7);
        BINARY(BITSHIFT_LEFT, EXPR_BITSHIFT_LEFT, 8);
        BINARY(BITSHIFT_RIGHT, EXPR_BITSHIFT_RIGHT, 8);
        BINARY(PLUS, EXPR_ADD, 9);
        BINARY(MINUS, EXPR_SUBTRACT, 9);
        BINARY(STAR, EXPR_MULTIPLY, 10);
        BINARY(SLASH, EXPR_DIVIDE, 10);
        BINARY(MODULO, EXPR_MODULO, 10);
#undef BINARY
        default: return 0;
    }
}

static expr binary(parserState *state, int minimumPrecedence) {
    expr left = secondary(state);
    CHECK_SYNC;
    DEFINE_TOK;
    enum binaryExprType operation;
    int precedence;
    while ((precedence = binaryOperator(tok.type, &operation)) >= minimumPrecedence) {
        token location = tok;
        tok = advance(state);
        expr right = binary(state, precedence + 1);
        CHECK_SYNC;
        struct expr_binary node = {.left = left, .right = right, .operation = operation};
        CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, node, result);
        result.location = location;
        left = result;
        SET_TOK;
    }
    return left;
}

static expr ternaryImpl(parserState *state);
static expr ternary(parserState *state) {
    if (state->syntaxDepth >= PARSER_MAX_RECURSION_DEPTH) {
        token tok = state->tokens[state->tokenIndex];
        diagnostic(state->source, tok, "syntax", "error", "Parser nesting limit exceeded");
        state->hasError = state->isSynchronizing = 1;
        return (expr){0};
    }
    state->syntaxDepth++;
    expr result = ternaryImpl(state);
    state->syntaxDepth--;
    return result;
}

static expr ternaryImpl(parserState *state) {
    const expr condition = binary(state, 1);
    CHECK_SYNC;
    DEFINE_TOK;
    if (tok.type == QUESTION_MARK) {
        token location = tok;
        tok = advance(state);
        struct expr_ternary ternary_n = {0};
        ternary_n.condition = condition;
        ternary_n.ifTrue = comma(state);
        CHECK_SYNC;
        SET_TOK;
        expect(COLON, "Expected colon for else case in ternary expression", expr);
        tok = advance(state);
        ternary_n.ifFalse = ternary(state);
        CHECK_SYNC;
        CONSTRUCT_EXPR_RES(EXPR_TYPE_TERNARY, ternary_n, res)
        res.location = location;
        return res;
    }
    return condition;
}

static expr assignmentImpl(parserState *state);
static expr assignment(parserState *state) {
    if (state->syntaxDepth >= PARSER_MAX_RECURSION_DEPTH) {
        token tok = state->tokens[state->tokenIndex];
        diagnostic(state->source, tok, "syntax", "error", "Parser nesting limit exceeded");
        state->hasError = state->isSynchronizing = 1;
        return (expr){0};
    }
    state->syntaxDepth++;
    expr result = assignmentImpl(state);
    state->syntaxDepth--;
    return result;
}

static expr assignmentImpl(parserState *state) {
    const expr variable = ternary(state);
    CHECK_SYNC;
    DEFINE_TOK;
    if (isAssignmentOperator(tok.type)) {
        token location = tok;
        enum binaryExprType bType;
        switch (tok.type) {
            case EQUALS:
                bType = EXPR_ASSIGNMENT;
                break;
            case PLUS_EQUALS:
                bType = EXPR_ADD_EQUALS;
                break;
            case MINUS_EQUALS:
                bType = EXPR_SUBTRACT_EQUALS;
                break;
            case STAR_EQUALS:
                bType = EXPR_MULTIPLY_EQUALS;
                break;
            case SLASH_EQUALS:
                bType = EXPR_DIVIDE_EQUALS;
                break;
            case MODULO_EQUALS:
                bType = EXPR_MODULO_EQUALS;
                break;
            case XOR_EQUALS:
                bType = EXPR_XOR_EQUALS;
                break;
            case AMPERSAND_EQUALS:
                bType = EXPR_BITWISE_AND_EQUALS;
                break;
            case BITWISE_OR_EQUALS:
                bType = EXPR_BITWISE_OR_EQUALS;
                break;
            case BITSHIFT_LEFT_EQUALS:
                bType = EXPR_BITSHIFT_LEFT_EQUALS;
                break;
            case BITSHIFT_RIGHT_EQUALS:
                bType = EXPR_BITSHIFT_RIGHT_EQUALS;
                break;
            default:
                diagnostic(state->source, tok, "syntax", "error", "Unsupported assignment operator %s", tok.lexeme);
                state->hasError = state->isSynchronizing = 1;
                return (expr){0};
        }

        tok = advance(state);
        struct expr_binary assign_n = {0};

        assign_n.operation = bType;
        assign_n.left = variable;
        assign_n.right = assignment(state);
        CHECK_SYNC;
        CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, assign_n, res)
        res.location = location;
        return res;
    }
    return variable;
}

// Normalizing simultaneous assignment retains the leaves and replaces list nodes.
static void freeCommaNodes(expr *e) {
    if (!isComma(e)) return;
    struct expr_binary *v = e->underlying;
    freeCommaNodes(&v->left);
    freeCommaNodes(&v->right);
    free(v);
}

static expr comma(parserState *state) {
    expr left = assignment(state);
    CHECK_SYNC;
    DEFINE_TOK;
    while (tok.type == COMMA) {
        token location = tok;
        tok = advance(state);
        struct expr_binary binary_n = {0};
        binary_n.left = left;
        binary_n.operation = EXPR_COMMA;
        binary_n.right = assignment(state);
        CHECK_SYNC;
        SET_TOK;
        CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, binary_n, res)
        res.location = location;
        left = res;
    }
    size_t count = commaCount(&left);
    for (size_t i = 1; i < count; i++) {
        expr *item = commaItem(&left, i);
        if (item->type != EXPR_TYPE_BINARY ||
            ((struct expr_binary *)item->underlying)->operation != EXPR_ASSIGNMENT) continue;
        char targets = 1;
        for (size_t j = 0; j < i; j++) {
            expr *candidate = commaItem(&left, j);
            if (candidate->type != EXPR_TYPE_IDENTIFIER && candidate->type != EXPR_TYPE_INDEX &&
                candidate->type != EXPR_TYPE_DOT && candidate->type != EXPR_TYPE_UNARY &&
                candidate->type != EXPR_TYPE_INSTANTIATION)
                targets = 0;
        }
        if (!targets) break;
        token location = item->location;
        struct expr_binary *last = item->underlying;
        expr lhs = *commaItem(&left, 0), rhs = last->right;
        for (size_t j = 1; j <= i; j++) {
            struct expr_binary part = {.operation = EXPR_COMMA, .left = lhs,
                .right = j == i ? last->left : *commaItem(&left, j)};
            CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, part, joined);
            joined.location = location;
            lhs = joined;
        }
        for (size_t j = i + 1; j < count; j++) {
            struct expr_binary part = {.operation = EXPR_COMMA, .left = rhs, .right = *commaItem(&left, j)};
            CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, part, joined);
            joined.location = location;
            rhs = joined;
        }
        struct expr_binary assignmentNode = {.operation = EXPR_ASSIGNMENT, .left = lhs, .right = rhs};
        CONSTRUCT_EXPR_RES(EXPR_TYPE_BINARY, assignmentNode, result);
        result.location = location;
        freeCommaNodes(&left);
        free(last);
        return result;
    }
    return left;
}

static expr *parseExpr(parserState *state) {
    expr expression = comma(state);
    if (state->isSynchronizing) {
        //printf("parseExpr synchronizing\n");
        return nullptr;
    }
    expr *heapExpr = malloc(sizeof(expression));
    CHECK_MALLOC(heapExpr);
    memcpy(heapExpr, &expression, sizeof(expression));
    return heapExpr;
}

// Reuse the expression grammar for a retained buffer dimension token span.
expr *parseBufferDimension(typeTokens dimension) {
    token *tokens = calloc(dimension.nTokens + 1, sizeof(*tokens));
    CHECK_MALLOC(tokens);
    memcpy(tokens, dimension.tokens, dimension.nTokens * sizeof(*tokens));
    tokens[dimension.nTokens] = (token){.type = EOF_TOKEN, .lexeme = "EOF"};
    parserState state = {.tokens = tokens, .tokensLen = dimension.nTokens + 1};
    expr *result = parseExpr(&state);
    if (state.hasError || currentToken(&state).type != EOF_TOKEN) {
        free(result);
        result = nullptr;
    }
    free(tokens);
    return result;
}

static stmtlist *parseBlock(parserState *state);

static stmt variableDeclaration(struct stmt_var decl) {
    struct stmt_var *result = malloc(sizeof(*result));
    CHECK_MALLOC(result);
    *result = decl;
    return (stmt){.type = STMT_VAR, .value = result};
}

static stmt parseInitializedDeclaration(parserState *state, struct stmt_var decl) {
    DEFINE_TOK;
    expect(EQUALS, "Expected equals for variable declaration", stmt);
    tok = advance(state);
    exprlist *values = &(exprlist){0};
    init_exprlist(values);
    do {
        expr parsedValue = assignment(state);
        if (state->isSynchronizing) {
            free_exprlist(values);
            free(decl.vars);
            free(decl.type.tokens);
            return (stmt){0};
        }
        push_exprlist(values, parsedValue);
        SET_TOK;
        if (tok.type != COMMA) break;
        tok = advance(state);
    } while (1);
    decl.initValues = to_exprarray(values);
    decl.nInitValues = listlen(values);
    free_exprlist(values);
    return variableDeclaration(decl);
}

static stmt parseDeclaration(parserState *state) {
    DEFINE_TOK;
    tokenlist *vars = &(tokenlist){0};
    init_tokenlist(vars);
    push_tokenlist(vars, tok);
    tok = advance(state);
    while (tok.type == COMMA) {
        tok = advance(state);
        if (tok.type != IDENTIFIER && tok.type != UNDERSCORE) {
            signatureError(state, "Expected identifier");
            return (stmt){0};
        }
        push_tokenlist(vars, tok);
        tok = advance(state);
    }
    if (tok.type != COLON) {
        diagnostic(state->source, tok, "syntax", "error", "(Compiler Error) Tried to parse declaration where none is present");
        exit(-2);
    }
    // parse var declaration
    struct stmt_var decl = {0};
    decl.nVars = listlen(vars);
    decl.vars = to_tokenarray(vars);
    free_tokenlist(vars);
    tok = advance(state);
    size_t typeStart = state->tokenIndex;
    if (tok.type != EQUALS) {
        if (!parseSignatureType(state, 0)) {
            free(decl.vars);
            return (stmt){0};
        }
        decl.type = copySignatureSpan(state, typeStart, state->tokenIndex);
        SET_TOK;
    }
    if (tok.type == SEMICOLON)
        return variableDeclaration(decl);
    return parseInitializedDeclaration(state, decl);
}

static char startsDeclaration(parserState *state) {
    size_t i = state->tokenIndex;
    while (i < state->tokensLen &&
           (state->tokens[i].type == IDENTIFIER || state->tokens[i].type == UNDERSCORE)) {
        i++;
        if (i < state->tokensLen && state->tokens[i].type == COLON) return 1;
        if (i >= state->tokensLen || state->tokens[i].type != COMMA) return 0;
        i++;
    }
    return 0;
}

// parse a declaration or an expression, and don't consume semicolon afterwards
static stmt parseDeclarationExpr(parserState *state) {
    DEFINE_TOK;
    if (startsDeclaration(state)) {
        return parseDeclaration(state);
    }
    // expression statement
    expr *expression = parseExpr(state);
    if (state->isSynchronizing) {
        state->hasError = 1;
        return (stmt){0};
    }
    if (!expression || expression->type == EXPR_TYPE_NULL) {
        state->hasError = state->isSynchronizing = 1;
        return (stmt){0};
    }
    stmt expressionStmt = {.type = STMT_EXPR, .value = expression};
    return expressionStmt;
}

// Types are kept as token spans for later type resolution.
typedef struct signatureFields {
    size_t count;
    token *names;
    typeTokens *types;
    char variadic;
    unsigned *bits;
} signatureFields;

static void freeSignatureFields(signatureFields *fields) {
    for (size_t i = 0; i < fields->count; i++) free(fields->types[i].tokens);
    free(fields->types);
    free(fields->names);
    free(fields->bits);
    *fields = (signatureFields){0};
}

static char signatureError(parserState *state, const char *message) {
    DEFINE_TOK;
    if (!state->quietErrors)
        diagnostic(state->source, tok, "syntax", "error", "%s", message);
    state->hasError = state->isSynchronizing = 1;
    return 0;
}

/* Legacy postfix type syntax (int[], T*, buffer<T>[N]) follows the complete type
 * starting at token index `start`. Speculative parses accept it so declarations
 * are still recognized; the committed parse reports it with the prefix spelling,
 * or in fix mode records a rewrite and continues after it. */
static char legacySuffix(parserState *state, size_t start) {
    size_t consumed = 0;
    int kinds = 0;
    char *text = legacyTypeRewrite(state->tokens + start, state->tokensLen - start, &consumed, &kinds,
                                   state->source);
    if (!text) {
        // Malformed legacy syntax: name the rule without guessing a spelling.
        token after = state->tokens[state->tokenIndex];
        return signatureError(state, after.type == STAR ? "The pointer star goes before the type."
                                                       : "Square brackets go before the type for an array.");
    }
    if (state->quietErrors) {
        free(text);
        state->legacyPending = 1;
    } else if (state->fixMode) {
        typeRewrite *grown = realloc(state->rewrites, (state->nRewrites + 1) * sizeof(*grown));
        CHECK_MALLOC(grown);
        state->rewrites = grown;
        state->rewrites[state->nRewrites++] = (typeRewrite){
            state->tokens[start], state->tokens[start + consumed - 1], text};
    } else {
        // Keep a preceding mixed modifier in the suggestion: mixed Value[] -> mixed []Value.
        char *shown = text;
        if (start && state->tokens[start - 1].type == MIXED) {
            shown = malloc(strlen(text) + 7);
            CHECK_MALLOC(shown);
            strcpy(shown, "mixed "); strcat(shown, text);
        }
        char *message = legacyTypeMessage(shown, kinds);
        token at = state->tokens[start];
        diagnostic(state->source, at, "syntax", "error", "%s", message);
        free(message);
        if (shown != text) free(shown);
        free(text);
        state->hasError = state->isSynchronizing = 1;
        return 0;
    }
    state->pendingGreater = 0;
    state->tokenIndex = start + consumed;
    return 1;
}
static size_t tokenPosition(parserState *state, token at) {
    for (size_t i = 0; i < state->tokensLen; i++)
        if (state->tokens[i].line == at.line && state->tokens[i].column == at.column &&
            state->tokens[i].filename == at.filename)
            return i;
    return state->tokenIndex;
}
// The first token of a type-like expression: a name, a.b, or a<...>.
static token expressionRoot(expr e) {
    for (;;) {
        if (e.type == EXPR_TYPE_INDEX) e = ((struct expr_index *)e.underlying)->parent;
        else if (e.type == EXPR_TYPE_INSTANTIATION) e = ((struct expr_instantiation *)e.underlying)->parent;
        else if (e.type == EXPR_TYPE_DOT) e = ((struct expr_dot *)e.underlying)->parent;
        else return e.location;
    }
}
static const char *const builtinTypeNames[] = {
    "int", "uint", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64",
    "float", "f32", "f64", "bool", "string"};
// Whether a legacy T[n] allocation names a type (fix mode only, or a builtin).
static char typeLikeExpression(parserState *state, expr e) {
    if (e.type == EXPR_TYPE_INSTANTIATION) return 1;
    const char *name = NULL;
    char qualified[512] = {0};
    if (e.type == EXPR_TYPE_IDENTIFIER) name = ((struct expr_identifier *)e.underlying)->lexeme.lexeme;
    else if (e.type == EXPR_TYPE_DOT) {
        struct expr_dot *dot = e.underlying;
        if (dot->parent.type != EXPR_TYPE_IDENTIFIER || dot->field.type != EXPR_TYPE_IDENTIFIER) return 0;
        snprintf(qualified, sizeof(qualified), "%s.%s",
                 ((struct expr_identifier *)dot->parent.underlying)->lexeme.lexeme,
                 ((struct expr_identifier *)dot->field.underlying)->lexeme.lexeme);
        name = qualified;
    } else return 0;
    if (!name) return 0;
    if (e.type == EXPR_TYPE_IDENTIFIER && ((struct expr_identifier *)e.underlying)->externReference) return 0;
    for (size_t i = 0; i < sizeof(builtinTypeNames) / sizeof(*builtinTypeNames); i++)
        if (!strcmp(name, builtinTypeNames[i])) return 1;
    if (!state->fixMode) return 0;
    for (size_t i = 0; i < state->nKnownTypes; i++)
        if (!strcmp(name, state->knownTypes[i])) return 1;
    for (size_t i = 0; i < state->nTypeScope; i++)
        if (!strcmp(name, state->typeScope[i].lexeme)) return 1;
    return 0;
}

static typeTokens copySignatureSpan(parserState *state, size_t start, size_t end) {
    size_t count = end - start + (state->pendingGreater && end == state->tokenIndex);
    typeTokens result = {0};
    if (!count) return result;
    result.tokens = malloc(2 * count * sizeof(token));
    CHECK_MALLOC(result.tokens);
    size_t angles = 0, brackets = 0;
    for (size_t i = 0; i < count; i++) {
        token t = state->tokens[start + i];
        if (i + 1 == count && state->pendingGreater && end == state->tokenIndex) {
            t.type = GREATER_THAN; t.lexeme = ">";
        }
        if (t.type == LEFT_BRACKET) brackets++;
        if (t.type == RIGHT_BRACKET && brackets) brackets--;
        if (!brackets && t.type == BITSHIFT_RIGHT && angles >= 2) {
            t.type = GREATER_THAN; t.lexeme = ">";
            result.tokens[result.nTokens++] = t;
            angles--;
        }
        if (!brackets && t.type == LESS_THAN) angles++;
        if (!brackets && t.type == GREATER_THAN && angles) angles--;
        result.tokens[result.nTokens++] = t;
    }
    return result;
}

static char addSignatureField(parserState *state, signatureFields *fields,
                              token name, size_t start, size_t end) {
    for (size_t i = 0; i < fields->count; i++) {
        if (name.type == IDENTIFIER && fields->names[i].type == IDENTIFIER &&
            strcmp(name.lexeme, fields->names[i].lexeme) == 0)
            return signatureError(state, "Duplicate name in function signature");
    }
    token *names = realloc(fields->names, (fields->count + 1) * sizeof(token));
    CHECK_MALLOC(names);
    fields->names = names;
    typeTokens *types = realloc(fields->types, (fields->count + 1) * sizeof(typeTokens));
    CHECK_MALLOC(types);
    fields->types = types;
    fields->names[fields->count] = name;
    fields->types[fields->count++] = copySignatureSpan(state, start, end);
    return 1;
}

static char parseSignatureFields(parserState *state, signatureFields *fields,
                                 char allowVariadic, size_t depth);

static char angleEnd(token tok) {
    return tok.type == GREATER_THAN || tok.type == BITSHIFT_RIGHT;
}
static char closeAngle(parserState *state) {
    token tok = currentToken(state);
    if (!angleEnd(tok)) return signatureError(state, "Expected closing type argument angle");
    if (tok.type == BITSHIFT_RIGHT) state->pendingGreater = 1;
    else advance(state);
    return 1;
}
static char parseAngleTypes(parserState *state, size_t depth) {
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Type nesting limit exceeded");
    token tok = advance(state);
    if (angleEnd(tok)) return signatureError(state, "Expected type argument");
    while (1) {
        if (!parseSignatureType(state, depth + 1)) return 0;
        tok = currentToken(state);
        if (tok.type != COMMA) break;
        tok = advance(state);
        if (angleEnd(tok)) break;
    }
    return closeAngle(state);
}

static char parseTypeBrackets(parserState *state, size_t depth) {
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Type nesting limit exceeded");
    token tok = advance(state);
    if (tok.type == RIGHT_BRACKET) { advance(state); return 1; }
    if (signatureEllipsis(state)) {
        // [...]T infers its length from a literal body.
        advance(state); advance(state); tok = advance(state);
        if (tok.type != RIGHT_BRACKET) return signatureError(state, "Expected closing bracket after inferred array length");
        advance(state);
        return 1;
    }
    // Inside brackets the dimension is delimited: any expression except assignment.
    ternary(state);
    if (state->isSynchronizing) return 0;
    SET_TOK;
    if (tok.type != RIGHT_BRACKET) return signatureError(state, "Expected closing array dimension bracket");
    advance(state);
    return 1;
}

// Struct fields share one type across a comma-separated list of names.
static char parseStructFields(parserState *state, signatureFields *fields,
                              signatureFields *valueParams, size_t depth) {
    DEFINE_TOK;
    size_t namesStart = state->tokenIndex, count = 0;
    do {
        if (tok.type != IDENTIFIER)
            return signatureError(state, "Expected struct field name before type");
        if (valueParams) {
            for (size_t i = 0; i < valueParams->count; i++)
                if (!strcmp(tok.lexeme, valueParams->names[i].lexeme))
                    return signatureError(state, "Struct field duplicates a value parameter");
        }
        count++;
        tok = advance(state);
        if (tok.type != COMMA) break;
        tok = advance(state);
    } while (1);
    size_t start = state->tokenIndex;
    if (!parseSignatureType(state, depth)) return 0;
    size_t end = state->tokenIndex;
    unsigned bits = 0;
    if (currentToken(state).type == COLON) {
        advance(state);
        token width = currentToken(state);
        if (width.type != LITERAL_INT || width.numValue.integer < 1 || width.numValue.integer > 64)
            return signatureError(state, "bitfield size must be an integer literal from 1 to 64");
        bits = width.numValue.integer;
        advance(state);
    }
    fields->bits = realloc(fields->bits, (fields->count + count) * sizeof(unsigned));
    CHECK_MALLOC(fields->bits);
    for (size_t i = 0; i < count; i++) {
        token name = state->tokens[namesStart + 2 * i];
        fields->bits[fields->count] = bits;
        if (!addSignatureField(state, fields, name, start, end)) return 0;
    }
    return 1;
}

static char parseCompositeTypeBody(parserState *state, size_t depth, char isInterface) {
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Composite type nesting limit exceeded");
    if (isInterface) {
        struct stmt_interface node = {0};
        char ok = parseInterfaceBody(state, &node);
        for (size_t i = 0; i < node.nConstraints; i++) free(node.constraints[i].tokens);
        free(node.constraints);
        free(node.methods);
        return ok;
    }
    token tok = advance(state); // opening brace
    signatureFields members = {0};
    while (tok.type != RIGHT_CURLY_BRACE) {
        if (!parseStructFields(state, &members, NULL, depth + 1)) goto invalid;
        SET_TOK;
        if (tok.type != SEMICOLON) {
            signatureError(state, "Expected semicolon after composite type member");
            goto invalid;
        }
        tok = advance(state);
    }
    advance(state);
    freeSignatureFields(&members);
    return 1;
invalid:
    freeSignatureFields(&members);
    return 0;
}

static char parseSignatureTypeImpl(parserState *state, size_t depth);
static char parseSignatureTypeInner(parserState *state, size_t depth);
static char parseSignatureType(parserState *state, size_t depth) {
    if (state->signatureDepth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state,"Type nesting limit exceeded");
    state->signatureDepth++;
    char ok=parseSignatureTypeInner(state,depth);
    state->signatureDepth--;
    return ok;
}
static char parseSignatureTypeInner(parserState *state, size_t depth) {
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Type nesting limit exceeded");
    DEFINE_TOK;
    size_t start = state->tokenIndex;
    if (!parseSignatureTypeImpl(state, depth)) return 0;
    SET_TOK;
    // Every type modifier is a prefix; a following '[' or '*' is removed postfix syntax.
    if (tok.type == LEFT_BRACKET || (tok.type == STAR && !state->castTarget))
        return legacySuffix(state, start);
    return 1;
}

// buffer<T> is an unsized view; buffer<T, N> has N elements (N may be a runtime value).
static char parseBufferArguments(parserState *state, size_t depth) {
    token tok = advance(state); // after '<'
    if (angleEnd(tok)) return signatureError(state, "Expected type argument");
    if (!parseSignatureType(state, depth + 1)) return 0;
    tok = currentToken(state);
    if (tok.type == COMMA) {
        advance(state);
        // Any operand, with additive and multiplicative operators only, so the
        // closing '>' is not a comparison; parenthesize other operators.
        binary(state, 9);
        if (state->isSynchronizing) return 0;
        tok = currentToken(state);
    }
    if (!angleEnd(tok)) return signatureError(state, "Expected '>' after buffer type arguments");
    return closeAngle(state);
}

static char parseSignatureTypeImpl(parserState *state, size_t depth) {
    DEFINE_TOK;
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Function signature nesting limit exceeded");
    if (tok.type == MIXED) {
        advance(state);
        size_t start = state->tokenIndex;
        if (!parseSignatureType(state, depth + 1)) return 0;
        if (state->legacyPending || state->fixMode) return 1;
        if (state->tokenIndex < start + 3 || state->tokens[start].type != LEFT_BRACKET ||
            state->tokens[start + 1].type != RIGHT_BRACKET)
            return signatureError(state, "mixed requires an array type []T");
        return 1;
    }
    if (tok.type == VARINT || tok.type == VARUINT) {
        advance(state);
        if (currentToken(state).type != LEFT_PAREN)
            return signatureError(state, !strcmp(tok.lexeme, "varuint") ? "varuint requires a bit width: varuint(n)" : "varint requires a bit width: varint(n)");
        advance(state);
        if (currentToken(state).type != LITERAL_INT)
            return signatureError(state, !strcmp(tok.lexeme, "varuint") ? "varuint width must be an integer literal from 1 to 8388608" : "varint width must be an integer literal from 1 to 8388608");
        token width = currentToken(state);
        if (width.wideInteger || width.numValue.integer < 1 || width.numValue.integer > OCEAN_MAX_INTEGER_BITS)
            return signatureError(state, !strcmp(tok.lexeme, "varuint") ? "varuint width must be from 1 to 8388608" : "varint width must be from 1 to 8388608");
        advance(state);
        if (currentToken(state).type != RIGHT_PAREN)
            return signatureError(state, !strcmp(tok.lexeme, "varuint") ? "Expected closing parenthesis after varuint width" : "Expected closing parenthesis after varint width");
        // Array modifiers are prefixes ([n]varint(w)); a trailing '[' is legacy
        // postfix syntax, reported by parseSignatureTypeInner.
        advance(state);
        return 1;
    }
    if (tok.type == IDENTIFIER && !strcmp(tok.lexeme, "buffer")) {
        tok = advance(state);
        if (tok.type != LESS_THAN) return 1; // The bare buffer family.
        return parseBufferArguments(state, depth);
    }
    if (tok.type == STAR) {
        advance(state);
        return parseSignatureType(state, depth + 1);
    }
    if (tok.type == LEFT_BRACKET) {
        if (!parseTypeBrackets(state, depth + 1)) return 0;
        return parseSignatureType(state, depth + 1);
    }
    if (tok.type == STRUCT || tok.type == INTERFACE) {
        char isInterface = tok.type == INTERFACE;
        tok = advance(state);
        if (tok.type != LEFT_CURLY_BRACE)
            return signatureError(state, "Expected composite type body");
        return parseCompositeTypeBody(state, depth + 1, isInterface);
    }
    if (tok.type == FUNC) {
        advance(state);
        signatureFields parameters = {0}, results = {0};
        char ok = parseSignatureFields(state, &parameters, 1, depth + 1);
        freeSignatureFields(&parameters);
        if (!ok) return 0;
        SET_TOK;
        if (tok.type == LEFT_PAREN) {
            ok = parseSignatureFields(state, &results, 0, depth + 1);
            freeSignatureFields(&results);
            return ok;
        }
        // A function type with no result is unambiguous before a delimiter.
        if (tok.type == COMMA || tok.type == RIGHT_PAREN || tok.type == LEFT_CURLY_BRACE ||
            tok.type == SEMICOLON || tok.type == RIGHT_BRACKET || tok.type == COLON ||
            tok.type == EQUALS || tok.type == BITWISE_OR || angleEnd(tok) ||
            tok.type == EOF_TOKEN || tok.type == FAT_ARROW)
            return 1;
        return parseSignatureType(state, depth + 1);
    }
    if (tok.type != IDENTIFIER && tok.type != ANY)
        return signatureError(state, "Expected function signature type");
    char isMap = tok.type == IDENTIFIER && strcmp(tok.lexeme, "map") == 0;
    char isChan = tok.type == IDENTIFIER && strcmp(tok.lexeme, "chan") == 0;
    tok = advance(state);
    if (isMap) {
        if (tok.type != LEFT_BRACKET) return signatureError(state, "Expected map key type");
        advance(state);
        if (!parseSignatureType(state, depth + 1)) return 0;
        SET_TOK;
        if (tok.type != RIGHT_BRACKET) return signatureError(state, "Expected closing map bracket");
        advance(state);
        return parseSignatureType(state, depth + 1);
    }
    if (isChan) return parseSignatureType(state, depth + 1);
    while (tok.type == DOT) {
        tok = advance(state);
        if (tok.type != IDENTIFIER) return signatureError(state, "Expected type name after dot");
        tok = advance(state);
    }
    // Generic type arguments and enum variant members.
    while (tok.type == LESS_THAN || tok.type == DOT) {
        if (tok.type == DOT) {
            tok = advance(state);
            if (tok.type != IDENTIFIER) return signatureError(state, "Expected type member after dot");
            advance(state);
        } else if (!parseAngleTypes(state, depth + 1)) return 0;
        SET_TOK;
    }
    return 1;
}

// Speculate using the type grammar without changing the expression cursor.
// Angle lists in expressions require a call, composite literal, or expression
// delimiter after the closing angle to distinguish relational operators.
static char tryCallTypeArguments(parserState *state, struct expr_instantiation *result) {
    parserState trial = *state;
    trial.quietErrors = 1;
    if (currentToken(state).type != LESS_THAN) return 0;
    token tok = advance(&trial);
    if (angleEnd(tok)) return 0;
    typeTokens *arguments = nullptr;
    size_t count = 0;
    do {
        size_t start = trial.tokenIndex;
        if (!parseSignatureType(&trial, 0) || trial.isSynchronizing) goto notTypes;
        typeTokens *grown = realloc(arguments, (count + 1) * sizeof(*arguments));
        CHECK_MALLOC(grown);
        arguments = grown;
        arguments[count++] = copySignatureSpan(&trial, start, trial.tokenIndex);
        tok = currentToken(&trial);
        if (tok.type != COMMA) break;
        tok = advance(&trial);
        if (angleEnd(tok)) break;
    } while (1);
    if (!angleEnd(tok) || !closeAngle(&trial)) goto notTypes;
    tok = currentToken(&trial);
    if (tok.type != LEFT_PAREN && tok.type != LEFT_CURLY_BRACE && tok.type != LEFT_BRACKET &&
        tok.type != SEMICOLON && tok.type != COMMA && tok.type != RIGHT_PAREN &&
        tok.type != RIGHT_BRACKET && tok.type != RIGHT_CURLY_BRACE &&
        tok.type != DOT && tok.type != FAT_ARROW && tok.type != EOF_TOKEN) goto notTypes;
    if (trial.legacyPending) {
        if (state->quietErrors) state->legacyPending = 1;
        else {
            // Report or record legacy argument types with the committed parser.
            advance(state);
            while (parseSignatureType(state, 0) && currentToken(state).type == COMMA &&
                   !angleEnd(advance(state)));
            if (state->isSynchronizing) goto notTypes;
        }
    }
    state->tokenIndex = trial.tokenIndex;
    state->pendingGreater = trial.pendingGreater;
    result->nTypeArguments = count;
    result->typeArguments = arguments;
    return 1;
notTypes:
    for (size_t i = 0; i < count; i++) free(arguments[i].tokens);
    free(arguments);
    return 0;
}

// Retain the type grammar's handling of nested angle closers and array dimensions.
char parseTypeApplicationArguments(typeTokens span, typeTokens **arguments, size_t *count) {
    *arguments = nullptr; *count = 0;
    if (span.nTokens < 3 || span.tokens[1].type != LESS_THAN) return 0;
    token *tokens = calloc(span.nTokens + 1, sizeof(*tokens));
    CHECK_MALLOC(tokens);
    memcpy(tokens, span.tokens, span.nTokens * sizeof(*tokens));
    tokens[span.nTokens] = (token){.type = EOF_TOKEN, .lexeme = "EOF"};
    parserState state = {.tokens = tokens, .tokensLen = span.nTokens + 1, .tokenIndex = 1, .quietErrors = 1};
    struct expr_instantiation instance = {0};
    char ok = tryCallTypeArguments(&state, &instance) && currentToken(&state).type == EOF_TOKEN;
    free(tokens);
    if (!ok) {
        for (size_t i = 0; i < instance.nTypeArguments; i++) free(instance.typeArguments[i].tokens);
        free(instance.typeArguments);
        return 0;
    }
    *arguments = instance.typeArguments; *count = instance.nTypeArguments;
    return 1;
}

static char signatureEllipsis(parserState *state) {
    size_t i = state->tokenIndex;
    return i + 2 < state->tokensLen && state->tokens[i].type == DOT &&
           state->tokens[i + 1].type == DOT && state->tokens[i + 2].type == DOT;
}

// Named fields share the same name-before-type grammar.
static char parseSignatureFields(parserState *state, signatureFields *fields,
                                 char allowVariadic, size_t depth) {
    DEFINE_TOK;
    if (depth >= PARSER_MAX_RECURSION_DEPTH)
        return signatureError(state, "Function signature nesting limit exceeded");
    if (tok.type != LEFT_PAREN) return signatureError(state, "Expected function parameter list");
    tok = advance(state);
    int named = -1;
    while (tok.type != RIGHT_PAREN) {
        size_t namesStart = state->tokenIndex, namesEnd = namesStart;
        // Prefer an entire unnamed type when it ends at a field delimiter.
        parserState trial = *state;
        trial.quietErrors = 1;
        char unnamed = parseTypeConstraint(&trial) &&
            (currentToken(&trial).type == COMMA || currentToken(&trial).type == RIGHT_PAREN);
        char hasNames = 0;
        if (!unnamed || ((tok.type == IDENTIFIER || tok.type == UNDERSCORE) && peek(state).type == COMMA)) {
            size_t cursor = namesStart;
            while (cursor + 1 < state->tokensLen &&
                   (state->tokens[cursor].type == IDENTIFIER || state->tokens[cursor].type == UNDERSCORE)) {
                token next = state->tokens[cursor + 1];
                if (next.type != COMMA) {
                    if (next.type != RIGHT_PAREN && next.type != EOF_TOKEN) {
                        hasNames = 1;
                        namesEnd = cursor;
                    }
                    break;
                }
                cursor += 2;
            }
        }
        if (named != -1 && named != hasNames)
            return signatureError(state, "Cannot mix named and unnamed parameters");
        named = hasNames;
        if (hasNames) {
            while (state->tokenIndex <= namesEnd) advance(state);
        }
        char variadic = signatureEllipsis(state);
        if (variadic) {
            if (!allowVariadic) return signatureError(state, "Variadic fields are not allowed");
            advance(state); advance(state); advance(state);
        }
        size_t start = state->tokenIndex;
        if (unnamed && !hasNames && !(trial.legacyPending && !state->quietErrors)) {
            if (trial.legacyPending) state->legacyPending = 1;
            state->tokenIndex = trial.tokenIndex;
            state->pendingGreater = trial.pendingGreater;
        } else if (!parseTypeConstraint(state)) return 0;
        size_t end = state->tokenIndex;
        if (hasNames) {
            if (variadic && namesStart != namesEnd)
                return signatureError(state, "Variadic parameter must have one name");
            for (size_t n = namesStart; n <= namesEnd; n += 2)
                if (!addSignatureField(state, fields, state->tokens[n], start, end)) return 0;
        } else if (!addSignatureField(state, fields, (token){.type = EOF_TOKEN}, start, end)) return 0;
        fields->variadic = variadic;
        tok = currentToken(state);
        if (tok.type == RIGHT_PAREN) break;
        if (tok.type != COMMA) return signatureError(state, "Expected comma or closing parenthesis");
        tok = advance(state);
        if (variadic && tok.type != RIGHT_PAREN)
            return signatureError(state, "Variadic parameter must be last");
    }
    advance(state);
    return 1;
}

// Arrow conversion targets are explicit, so no symbol lookup is needed.
static char parseCastTarget(parserState *state, typeTokens *target) {
    DEFINE_TOK;
    char grouped = tok.type == LEFT_PAREN;
    if (grouped) advance(state);
    size_t start = state->tokenIndex;
    if (grouped) {
        if (!parseSignatureType(state, state->syntaxDepth + 1)) return 0;
    } else {
        // Single names, buffer<...>, and [..]T need no parentheses; a following '*'
        // is multiplication. Legacy Name[...] is still parsed so it can be reported.
        if (tok.type != IDENTIFIER && tok.type != ANY && tok.type != LEFT_BRACKET &&
            tok.type != VARINT && tok.type != VARUINT)
            return signatureError(state, "Expected cast type; multi-token types require parentheses");
        if (tok.type == LEFT_BRACKET || tok.type == VARINT || tok.type == VARUINT ||
            (tok.type == IDENTIFIER && ((!strcmp(tok.lexeme, "buffer") && peek(state).type == LESS_THAN) ||
                                        peek(state).type == LEFT_BRACKET))) {
            char previous = state->castTarget;
            state->castTarget = 1;
            char ok = parseSignatureType(state, state->syntaxDepth + 1);
            state->castTarget = previous;
            if (!ok) return 0;
        } else advance(state);
    }
    size_t end = state->tokenIndex;
    SET_TOK;
    if (grouped) {
        if (tok.type != RIGHT_PAREN)
            return signatureError(state, "Expected closing parenthesis after cast type");
        advance(state);
    } else if (tok.type == DOT || tok.type == LEFT_BRACKET || tok.type == LEFT_PAREN) {
        return signatureError(state, "Multi-token cast types require parentheses");
    }
    *target = copySignatureSpan(state, start, end);
    return 1;
}

// Cases and generic parameters share the type-constraint grammar.
static char parseTypeConstraint(parserState *state) {
    token tok = currentToken(state);
    do {
        if (tok.type == TILDE) advance(state);
        if (!parseSignatureType(state, 0)) return 0;
        tok = currentToken(state);
        if (tok.type != BITWISE_OR) return 1;
        tok = advance(state);
    } while (1);
}

// Type parameter declarations retain Go's name-before-constraint order:
// <T, U any, V ~int | ~string>.
// Omitted constraints default to any. These names are types, not value parameters.
static char parseTypeParameters(parserState *state, signatureFields *fields) {
    DEFINE_TOK;
    if (tok.type != LESS_THAN) return signatureError(state, "Type parameters require angle brackets <...>");
    tok = advance(state);
    if (angleEnd(tok)) return signatureError(state, "Expected type parameter");
    while (!angleEnd(tok)) {
        size_t namesStart = state->tokenIndex, count = 0;
        do {
            if (tok.type != IDENTIFIER) return signatureError(state, "Expected type parameter name");
            if (!strcmp(tok.lexeme, "array")) return signatureError(state, "array is a reserved type name");
            count++;
            tok = advance(state);
            if (tok.type != COMMA) break;
            tok = advance(state);
            if (angleEnd(tok)) break;
        } while (1);
        char implicitAny = angleEnd(tok);
        size_t start = state->tokenIndex;
        if (!implicitAny && !parseTypeConstraint(state)) return 0;
        SET_TOK;
        for (size_t i = 0; i < count; i++) {
            token name = state->tokens[namesStart + 2 * i];
            if (!addSignatureField(state, fields, name, start, state->tokenIndex)) return 0;
            if (implicitAny) {
                typeTokens *constraint = &fields->types[fields->count - 1];
                free(constraint->tokens);
                constraint->tokens = malloc(sizeof(token));
                CHECK_MALLOC(constraint->tokens);
                constraint->nTokens = 1;
                constraint->tokens[0] = name;
                constraint->tokens[0].type = ANY;
                constraint->tokens[0].lexeme = "any";
            }
        }
        if (angleEnd(tok)) break;
        if (tok.type != COMMA) return signatureError(state, "Expected comma after type constraint");
        tok = advance(state);
    }
    return closeAngle(state);
}

// Receiver arguments declare names, rather than specializing the method.
static char bindReceiverParameters(parserState *state, struct stmt_func *function) {
    typeTokens base = function->receiverType;
    if (base.nTokens && base.tokens[0].type == STAR) {
        base.tokens++; base.nTokens--;
    } else if (base.nTokens && base.tokens[base.nTokens - 1].type == STAR) base.nTokens--;
    if (!base.nTokens || base.tokens[0].type != IDENTIFIER)
        return signatureError(state, "Expected a struct receiver type or pointer to one");
    if (base.nTokens == 1) return 1;
    if (base.tokens[1].type != LESS_THAN)
        return signatureError(state, "Expected a struct receiver type or pointer to one");
    typeTokens *arguments = NULL;
    size_t count = 0;
    if (!parseTypeApplicationArguments(base, &arguments, &count))
        return signatureError(state, "Invalid receiver type parameters");
    token *names = malloc(count * sizeof(*names));
    CHECK_MALLOC(names);
    char ok = 1;
    for (size_t i = 0; i < count; i++) {
        if (arguments[i].nTokens != 1 || arguments[i].tokens[0].type != IDENTIFIER) {
            signatureError(state, "Receiver type arguments must be type parameter names");
            ok = 0;
            break;
        }
        names[i] = arguments[i].tokens[0];
        for (size_t j = 0; j < i; j++) {
            if (!strcmp(names[i].lexeme, names[j].lexeme)) {
                signatureError(state, "Duplicate receiver type parameter");
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    for (size_t i = 0; i < count; i++) free(arguments[i].tokens);
    free(arguments);
    if (!ok) { free(names); return 0; }
    function->nReceiverTypeParams = count;
    function->receiverTypeParamNames = names;
    return 1;
}

static stmt parseFuncDeclaration(parserState *state, char isExtern, char hasKeyword, char anonymous) {
    DEFINE_TOK;
    if (hasKeyword) tok = advance(state);
    struct stmt_func function = {.isExtern = isExtern, .name = {.type = EOF_TOKEN},
                                 .receiverName = {.type = EOF_TOKEN}};
    signatureFields parameters = {0}, results = {0}, typeParams = {0}, receiver = {0};
    if (!anonymous) {
        if (tok.type == LEFT_PAREN) {
            if (!parseSignatureFields(state, &receiver, 1, 0)) goto invalid;
            if (receiver.variadic) {
                signatureError(state, "Method receivers cannot be variadic");
                goto invalid;
            }
            if (receiver.count != 1 || receiver.names[0].type == EOF_TOKEN) {
                signatureError(state, "Expected one named method receiver");
                goto invalid;
            }
            function.receiverName = receiver.names[0];
            function.receiverType = receiver.types[0];
            free(receiver.names);
            free(receiver.types);
            receiver = (signatureFields){0};
            if (!bindReceiverParameters(state, &function)) goto invalid;
            SET_TOK;
        }
        if (tok.type != IDENTIFIER) {
            signatureError(state, "Expected function name");
            goto invalid;
        }
        function.name = tok;
        tok = advance(state);
    }
    if ((tok.type == LEFT_BRACKET || tok.type == LESS_THAN) && !parseTypeParameters(state, &typeParams)) goto invalid;
    for (size_t i = 0; i < function.nReceiverTypeParams; i++) {
        token bound = function.receiverTypeParamNames[i];
        if (!strcmp(bound.lexeme, function.receiverName.lexeme)) {
            signatureError(state, "Receiver name duplicates a receiver type parameter");
            goto invalid;
        }
        for (size_t j = 0; j < typeParams.count; j++) {
            if (!strcmp(bound.lexeme, typeParams.names[j].lexeme)) {
                signatureError(state, "Method type parameter redeclares a receiver type parameter");
                goto invalid;
            }
        }
    }
    if (!parseSignatureFields(state, &parameters, 1, 0)) goto invalid;
    SET_TOK;
    size_t resultStart = state->tokenIndex;
    // A named function begins a new declaration, not a function result type.
    // Diagnose the unterminated extern here instead of consuming the next func
    // and reporting a parameter-list error at its name. Anonymous func(...)
    // result types remain valid.
    if (isExtern && ((tok.type == FUNC && peek(state).type == IDENTIFIER) ||
                     tok.type == EXTERN || tok.type == EOF_TOKEN)) {
        signatureError(state, "Expected semicolon after extern function");
        goto invalid;
    }
    if (tok.type == LEFT_PAREN) {
        if (!parseSignatureFields(state, &results, 0, 0)) goto invalid;
    } else if (tok.type != LEFT_CURLY_BRACE && !(isExtern && tok.type == SEMICOLON)) {
        if (!parseTypeConstraint(state)) goto invalid;
        if (!addSignatureField(state, &results, (token){.type = EOF_TOKEN},
                               resultStart, state->tokenIndex)) goto invalid;
    }
    function.type = copySignatureSpan(state, resultStart, state->tokenIndex);
    SET_TOK;
    if (tok.type != (isExtern ? SEMICOLON : LEFT_CURLY_BRACE)) {
        signatureError(state, isExtern ? "Expected semicolon after extern function" : "Expected function body");
        goto invalid;
    }
    if (function.receiverName.type == IDENTIFIER) {
        for (size_t i = 0; i < parameters.count + results.count; i++) {
            token name = i < parameters.count ? parameters.names[i] : results.names[i - parameters.count];
            if (name.type == IDENTIFIER && !strcmp(name.lexeme, function.receiverName.lexeme)) {
                signatureError(state, "Parameter or result duplicates method receiver");
                goto invalid;
            }
        }
    }
    // Result names share the function scope with parameter names.
    for (size_t i = 0; i < parameters.count; i++)
        for (size_t j = 0; j < results.count; j++)
            if (parameters.names[i].type == IDENTIFIER && results.names[j].type == IDENTIFIER &&
                strcmp(parameters.names[i].lexeme, results.names[j].lexeme) == 0) {
                signatureError(state, "Result name duplicates a parameter name");
                goto invalid;
            }
    if (isExtern) {
        advance(state);
    } else {
        size_t oldLoopDepth = state->loopDepth, oldSwitchDepth = state->switchDepth;
        state->loopDepth = state->switchDepth = 0;
        state->functionDepth++;
        char oldGuard = state->allowTypeGuard;
        size_t oldGuards = state->typeGuards;
        state->allowTypeGuard = 0;
        function.body.open = currentToken(state);
        size_t typeScope = state->nTypeScope;
        for (size_t i = 0; state->fixMode && i < typeParams.count + function.nReceiverTypeParams; i++) {
            token *grown = realloc(state->typeScope, (state->nTypeScope + 1) * sizeof(token));
            CHECK_MALLOC(grown);
            state->typeScope = grown;
            state->typeScope[state->nTypeScope++] = i < typeParams.count ? typeParams.names[i]
                : function.receiverTypeParamNames[i - typeParams.count];
        }
        stmtlist *body = parseBlock(state);
        state->nTypeScope = typeScope;
        function.body.close = state->tokens[state->tokenIndex ? state->tokenIndex-1 : 0];
        state->allowTypeGuard = oldGuard;
        state->typeGuards = oldGuards;
        state->functionDepth--;
        state->loopDepth = oldLoopDepth;
        state->switchDepth = oldSwitchDepth;
        if (!body || state->isSynchronizing) goto invalid;
        function.body.nStmts = listlen(body);
        function.body.stmts = function.body.nStmts ? to_stmtarray(body) : nullptr;
        free_stmtlist(body);
        free(body);
    }
    function.nParams = parameters.count;
    function.paramNames = parameters.names;
    function.paramTypeNames = parameters.types;
    function.isVariadic = parameters.variadic;
    function.nResults = results.count;
    function.resultNames = results.names;
    function.resultTypes = results.types;
    function.nTypeParams = typeParams.count;
    function.typeParamNames = typeParams.names;
    function.typeParamConstraints = typeParams.types;
    struct stmt_func *result = malloc(sizeof(struct stmt_func));
    CHECK_MALLOC(result);
    *result = function;
    return (stmt){.type = STMT_FUNC, .value = result};
invalid:
    freeSignatureFields(&parameters);
    freeSignatureFields(&results);
    freeSignatureFields(&typeParams);
    freeSignatureFields(&receiver);
    free(function.receiverType.tokens);
    free(function.receiverTypeParamNames);
    free(function.type.tokens);
    state->hasError = state->isSynchronizing = 1;
    return (stmt){0};
}

// Parse the same signature grammar used by literals, with a synthetic empty body.
struct stmt_func *parseFunctionType(typeTokens span) {
    if (!span.nTokens || span.tokens[0].type != FUNC) return NULL;
    token *tokens = calloc(span.nTokens + 3, sizeof(*tokens));
    CHECK_MALLOC(tokens);
    memcpy(tokens, span.tokens, span.nTokens * sizeof(*tokens));
    tokens[span.nTokens] = (token){.type = LEFT_CURLY_BRACE, .lexeme = "{"};
    tokens[span.nTokens + 1] = (token){.type = RIGHT_CURLY_BRACE, .lexeme = "}"};
    tokens[span.nTokens + 2] = (token){.type = EOF_TOKEN};
    parserState state = {.tokens = tokens, .tokensLen = span.nTokens + 3, .quietErrors = 1};
    stmt parsed = parseFuncDeclaration(&state, 0, 1, 1);
    free(tokens);
    if (state.hasError || parsed.type != STMT_FUNC) return NULL;
    struct stmt_func *function = parsed.value;
    function->name = span.tokens[0]; function->name.lexeme = "<function>";
    return function;
}

// Extern declarations use C ordering: extern result name(type parameter, ...);
static stmt parseExtern(parserState *state) {
    if (state->functionDepth) {
        signatureError(state, "Extern declarations are only allowed at file scope");
        return (stmt){0};
    }
    token tok = advance(state);
    struct stmt_func function = {.isExtern = 1, .name = {.type = EOF_TOKEN},
                                 .receiverName = {.type = EOF_TOKEN}};
    signatureFields parameters = {0}, results = {0};
    size_t start = state->tokenIndex;
    if (!parseSignatureType(state, 0)) goto invalid;
    size_t end = state->tokenIndex;
    char isVoid = end == start + 1 && !strcmp(state->tokens[start].lexeme, "void");
    if (!isVoid && !addSignatureField(state, &results, (token){.type = EOF_TOKEN}, start, end)) goto invalid;
    function.type = copySignatureSpan(state, start, isVoid ? start : end);
    tok = currentToken(state);
    if (tok.type != IDENTIFIER) {
        signatureError(state, "Expected extern function name after return type");
        goto invalid;
    }
    function.name = tok;
    tok = advance(state);
    if (tok.type != LEFT_PAREN) {
        signatureError(state, "Expected extern function parameter list");
        goto invalid;
    }
    tok = advance(state);
    if (tok.type == IDENTIFIER && !strcmp(tok.lexeme, "void") && peek(state).type == RIGHT_PAREN)
        tok = advance(state);
    while (tok.type != RIGHT_PAREN) {
        if (signatureEllipsis(state)) {
            if (!parameters.count) {
                signatureError(state, "C variadic declarations require a fixed parameter");
                goto invalid;
            }
            advance(state); advance(state); tok = advance(state);
            parameters.variadic = 1;
            if (tok.type != RIGHT_PAREN) {
                signatureError(state, "Variadic parameter must be last");
                goto invalid;
            }
            break;
        }
        start = state->tokenIndex;
        if (!parseSignatureType(state, 0)) goto invalid;
        end = state->tokenIndex;
        if (end == start + 1 && !strcmp(state->tokens[start].lexeme, "void")) {
            signatureError(state, "void must be the only parameter");
            goto invalid;
        }
        tok = currentToken(state);
        token name = {.type = EOF_TOKEN};
        if (tok.type == IDENTIFIER || tok.type == UNDERSCORE) {
            name = tok;
            tok = advance(state);
        }
        if (!addSignatureField(state, &parameters, name, start, end)) goto invalid;
        if (tok.type == RIGHT_PAREN) break;
        if (tok.type != COMMA) {
            signatureError(state, "Expected comma or closing parenthesis");
            goto invalid;
        }
        tok = advance(state);
        if (tok.type == RIGHT_PAREN) {
            signatureError(state, "Expected parameter after comma");
            goto invalid;
        }
    }
    tok = advance(state);
    if (tok.type != SEMICOLON) {
        signatureError(state, "Expected semicolon after extern function");
        goto invalid;
    }
    advance(state);
    function.nParams = parameters.count;
    function.paramNames = parameters.names;
    function.paramTypeNames = parameters.types;
    function.isVariadic = parameters.variadic;
    function.nResults = results.count;
    function.resultNames = results.names;
    function.resultTypes = results.types;
    struct stmt_func *result = malloc(sizeof(*result));
    CHECK_MALLOC(result);
    *result = function;
    return (stmt){.type = STMT_FUNC, .value = result};
invalid:
    freeSignatureFields(&parameters);
    freeSignatureFields(&results);
    free(function.type.tokens);
    state->hasError = state->isSynchronizing = 1;
    return (stmt){0};
}

static stmt parseFunc(parserState *state) {
    return parseFuncDeclaration(state, 0, 1, 0);
}

static stmt parseStatement(parserState *state);

// for (i := 0; i < 10; i++)
// for (i := 0; defer i < 10; i++)
// for (i < 10)
// for (defer i < 10)
// for (i, item := range arr)
static stmt parseFor(parserState *state) {
    DEFINE_TOK;
    tok = advance(state);
    expect(LEFT_PAREN, "Expected start of for loop header", stmt);
    tok = advance(state);
    struct stmt_for loop = {.open = tok};

    // Recognize identifier[, identifier] := range before declaration parsing.
    size_t bindingStart = state->tokenIndex;
    size_t cursor = bindingStart;
    size_t nBindings = 0;
    while (cursor < state->tokensLen &&
           (state->tokens[cursor].type == IDENTIFIER ||
            state->tokens[cursor].type == UNDERSCORE)) {
        nBindings++;
        cursor++;
        if (cursor >= state->tokensLen || state->tokens[cursor].type != COMMA) break;
        cursor++;
    }
    if (nBindings && state->tokens[cursor - 1].type != COMMA &&
        cursor + 2 < state->tokensLen &&
        state->tokens[cursor].type == COLON &&
        state->tokens[cursor + 1].type == EQUALS &&
        state->tokens[cursor + 2].type == RANGE) {
        if (nBindings > 2) {
            diagnostic(state->source, tok, "syntax", "error", "Expected one or two range bindings");
            state->hasError = state->isSynchronizing = 1;
            return (stmt){0};
        }
        loop.nBindings = nBindings;
        for (size_t i = 0; i < nBindings; i++)
            loop.bindings[i] = state->tokens[bindingStart + 2 * i];
        state->tokenIndex = cursor + 2;
        tok = advance(state);
        loop.range = parseExpr(state);
        if (state->isSynchronizing) goto invalid;
        SET_TOK;
    } else {
        // A leading defer belongs to a condition-only loop.
        if (tok.type == DEFER) {
            loop.deferCondition = 1;
            tok = advance(state);
            loop.condition = parseExpr(state);
            if (state->isSynchronizing) goto invalid;
            SET_TOK;
        } else {
            stmt first = {0};
            if (tok.type != SEMICOLON) {
                first = parseDeclarationExpr(state);
                if (state->isSynchronizing || first.type == STMT_NULL) goto invalid;
                SET_TOK;
            }
            if (tok.type == SEMICOLON) {
                if (first.type != STMT_NULL) {
                    loop.initializer = malloc(sizeof(stmt));
                    CHECK_MALLOC(loop.initializer);
                    *loop.initializer = first;
                }
                tok = advance(state);
                if (tok.type == DEFER) {
                    loop.deferCondition = 1;
                    tok = advance(state);
                }
                if (loop.deferCondition || tok.type != SEMICOLON) {
                    loop.condition = parseExpr(state);
                    if (state->isSynchronizing) goto invalid;
                    SET_TOK;
                }
                expect(SEMICOLON, "Expected semicolon after for condition", stmt);
                tok = advance(state);
                if (tok.type != RIGHT_PAREN) {
                    loop.update = parseExpr(state);
                    if (state->isSynchronizing) goto invalid;
                    SET_TOK;
                }
            } else {
                if (first.type != STMT_EXPR) {
                    diagnostic(state->source, tok, "syntax", "error", "Expected expression for for condition");
                    goto invalid;
                }
                loop.condition = first.value;
            }
        }
    }
    expect(RIGHT_PAREN, "Expected end of for loop header", stmt);
    tok = advance(state);
    state->loopDepth++;
    stmt body = parseStatement(state);
    state->loopDepth--;
    if (state->isSynchronizing) goto invalid;
    loop.body = malloc(sizeof(stmt));
    CHECK_MALLOC(loop.body);
    *loop.body = body;
    struct stmt_for *result = malloc(sizeof(struct stmt_for));
    CHECK_MALLOC(result);
    loop.close = state->tokens[state->tokenIndex ? state->tokenIndex-1 : 0];
    *result = loop;
    return (stmt){.type = STMT_FOR, .value = result};

invalid:
    state->hasError = state->isSynchronizing = 1;
    return (stmt){0};
}

static stmt parseTypeDeclaration(parserState *state) {
    DEFINE_TOK;
    tok = advance(state);
    expect(IDENTIFIER, "Expected type name", stmt);
    if (!strcmp(tok.lexeme, "array")) {
        signatureError(state, "array is a reserved type name"); return (stmt){0};
    }
    struct stmt_type node = {.name = tok, .displayName = tok.lexeme};
    tok = advance(state);
    if (tok.type == EQUALS) {
        node.isAlias = 1;
        tok = advance(state);
    }
    size_t start = state->tokenIndex;
    if (!parseSignatureType(state, 0)) return (stmt){0};
    node.underlying = copySignatureSpan(state, start, state->tokenIndex);
    SET_TOK;
    if (tok.type != SEMICOLON) {
        free(node.underlying.tokens);
        signatureError(state, "Expected semicolon after type declaration");
        return (stmt){0};
    }
    advance(state);
    struct stmt_type *result = malloc(sizeof(*result));
    CHECK_MALLOC(result);
    *result = node;
    return (stmt){.type = STMT_TYPE, .value = result};
}

static stmt parseStruct(parserState *state) {
    DEFINE_TOK;
    tok = advance(state);
    expect(IDENTIFIER, "Expected struct name", stmt);
    if (!strcmp(tok.lexeme, "array")) {
        signatureError(state, "array is a reserved type name"); return (stmt){0};
    }
    token name = tok;
    signatureFields fields = {0}, typeParams = {0}, valueParams = {0};
    tok = advance(state);
    if ((tok.type == LEFT_BRACKET || tok.type == LESS_THAN) && !parseTypeParameters(state, &typeParams)) goto invalid;
    SET_TOK;
    if (tok.type == LEFT_PAREN) {
        if (!parseSignatureFields(state, &valueParams, 1, 0)) goto invalid;
        if (valueParams.variadic) { signatureError(state, "Struct value parameters cannot be variadic"); goto invalid; }
        for (size_t i = 0; i < valueParams.count; i++) {
            if (valueParams.names[i].type != IDENTIFIER) {
                signatureError(state, "Struct value parameters require names");
                goto invalid;
            }
            for (size_t j = 0; j < typeParams.count; j++) {
                if (!strcmp(valueParams.names[i].lexeme, typeParams.names[j].lexeme)) {
                    signatureError(state, "Struct value parameter duplicates a type parameter");
                    goto invalid;
                }
            }
        }
        SET_TOK;
    }
    if (tok.type != LEFT_CURLY_BRACE) {
        signatureError(state, "Expected struct body");
        goto invalid;
    }
    tok = advance(state);
    while (tok.type != RIGHT_CURLY_BRACE) {
        if (!parseStructFields(state, &fields, &valueParams, 0)) goto invalid;
        SET_TOK;
        if (tok.type != SEMICOLON) {
            signatureError(state, "Expected semicolon after struct fields");
            goto invalid;
        }
        tok = advance(state);
    }
    advance(state);
    struct stmt_struct *result = calloc(1, sizeof(*result));
    CHECK_MALLOC(result);
    result->name = name;
    result->nTypeParams = typeParams.count;
    result->typeParamNames = typeParams.names;
    result->typeParamConstraints = typeParams.types;
    result->nVarParams = valueParams.count;
    result->nFields = valueParams.count + fields.count;
    result->fieldBits = calloc(result->nFields + 1, sizeof(unsigned));
    CHECK_MALLOC(result->fieldBits);
    if (fields.count) memcpy(result->fieldBits + valueParams.count, fields.bits, fields.count * sizeof(unsigned));
    free(fields.bits); fields.bits = NULL;
    if (valueParams.count) {
        result->fieldNames = malloc(sizeof(token) * result->nFields);
        result->fieldTypes = malloc(sizeof(typeTokens) * result->nFields);
        CHECK_MALLOC(result->fieldNames); CHECK_MALLOC(result->fieldTypes);
        memcpy(result->fieldNames, valueParams.names, sizeof(token) * valueParams.count);
        memcpy(result->fieldTypes, valueParams.types, sizeof(typeTokens) * valueParams.count);
        if (fields.count) {
            memcpy(result->fieldNames + valueParams.count, fields.names, sizeof(token) * fields.count);
            memcpy(result->fieldTypes + valueParams.count, fields.types, sizeof(typeTokens) * fields.count);
        }
        result->varParamNames = result->fieldNames;
        result->varParamTypes = result->fieldTypes;
        free(valueParams.names); free(valueParams.types);
        free(fields.names); free(fields.types);
    } else {
        result->fieldNames = fields.names;
        result->fieldTypes = fields.types;
    }
    return (stmt){.type = STMT_STRUCT, .value = result};
invalid:
    freeSignatureFields(&valueParams);
    freeSignatureFields(&typeParams);
    freeSignatureFields(&fields);
    return (stmt){0};
}

static char startsInterfaceMethod(parserState *state) {
    token tok = currentToken(state);
    if (tok.type == FUNC) return peek(state).type == IDENTIFIER;
    if (tok.type != IDENTIFIER) return 0;
    size_t i = state->tokenIndex + 1;
    if (i < state->tokensLen &&
        (state->tokens[i].type == LESS_THAN || state->tokens[i].type == LEFT_BRACKET)) {
        size_t depth = 1;
        while (++i < state->tokensLen && depth) {
            enum tokenType k = state->tokens[i].type;
            if (k == LESS_THAN || k == LEFT_BRACKET) depth++;
            if (k == GREATER_THAN || k == RIGHT_BRACKET) depth--;
            if (k == BITSHIFT_RIGHT) depth = depth > 1 ? depth - 2 : 0;
        }
    }
    return i < state->tokensLen && state->tokens[i].type == LEFT_PAREN;
}

// Interfaces contain either method signatures or one union of type terms.
// The final semicolon of a type list is optional.
static char parseInterfaceBody(parserState *state, struct stmt_interface *node) {
    token tok = advance(state);
    while (tok.type != RIGHT_CURLY_BRACE) {
        if (!startsInterfaceMethod(state)) {
            if (node->nMethods || node->nConstraints)
                return signatureError(state, "Interface must contain methods or one type list");
            size_t start = state->tokenIndex;
            if (!parseTypeConstraint(state)) return 0;
            node->constraints = malloc(sizeof(typeTokens));
            CHECK_MALLOC(node->constraints);
            node->constraints[node->nConstraints++] =
                copySignatureSpan(state, start, state->tokenIndex);
            tok = currentToken(state);
            if (tok.type == SEMICOLON) tok = advance(state);
            if (tok.type != RIGHT_CURLY_BRACE)
                return signatureError(state, "Expected end of interface type list");
            break;
        }
        if (node->nConstraints)
            return signatureError(state, "Interface must contain methods or one type list");
        if (tok.type == FUNC && peek(state).type != IDENTIFIER)
            return signatureError(state, "Interface methods have an implied receiver");
        stmt method = parseFuncDeclaration(state, 1, tok.type == FUNC, 0);
        if (state->isSynchronizing) return 0;
        struct stmt_func *signature = method.value;
        signature->isExtern = 0;
        for (size_t i = 0; i < node->nMethods; i++) {
            if (!strcmp(node->methods[i].name.lexeme, signature->name.lexeme)) {
                free(signature);
                return signatureError(state, "Duplicate interface method");
            }
        }
        struct stmt_func *methods = realloc(node->methods, (node->nMethods + 1) * sizeof(*methods));
        CHECK_MALLOC(methods);
        node->methods = methods;
        node->methods[node->nMethods++] = *signature;
        free(signature);
        tok = currentToken(state);
    }
    advance(state);
    return 1;
}

struct stmt_interface *parseInterfaceType(typeTokens span) {
    if (span.nTokens < 3 || span.tokens[0].type != INTERFACE ||
        span.tokens[1].type != LEFT_CURLY_BRACE)
        return NULL;
    token *tokens = malloc((span.nTokens + 1) * sizeof(token));
    CHECK_MALLOC(tokens);
    memcpy(tokens, span.tokens, span.nTokens * sizeof(token));
    tokens[span.nTokens] = (token){.type = EOF_TOKEN};
    parserState state = {
        .tokens = tokens, .tokensLen = span.nTokens + 1, .tokenIndex = 1, .quietErrors = 1};
    struct stmt_interface *node = calloc(1, sizeof(*node));
    CHECK_MALLOC(node);
    char ok = parseInterfaceBody(&state, node) && state.tokenIndex == span.nTokens;
    free(tokens);
    if (!ok) {
        free(node);
        return NULL;
    }
    return node;
}

static stmt parseInterface(parserState *state) {
    token tok = advance(state);
    expect(IDENTIFIER, "Expected interface name", stmt);
    if (!strcmp(tok.lexeme, "array")) {
        signatureError(state, "array is a reserved type name"); return (stmt){0};
    }
    struct stmt_interface *node = calloc(1, sizeof(*node));
    CHECK_MALLOC(node);
    node->name = tok;
    signatureFields typeParams = {0};
    tok = advance(state);
    if ((tok.type == LEFT_BRACKET || tok.type == LESS_THAN) && !parseTypeParameters(state, &typeParams)) goto invalid;
    SET_TOK;
    if (tok.type != LEFT_CURLY_BRACE) {
        signatureError(state, "Expected interface body");
        goto invalid;
    }
    if (!parseInterfaceBody(state, node)) goto invalid;
    node->nTypeParams = typeParams.count;
    node->typeParamNames = typeParams.names;
    node->typeParamConstraints = typeParams.types;
    return (stmt){.type = STMT_INTERFACE, .value = node};
invalid:
    freeSignatureFields(&typeParams);
    for (size_t i = 0; i < node->nConstraints; i++) free(node->constraints[i].tokens);
    free(node->constraints);
    // Recursive cleanup of method signature contents remains separate AST work.
    free(node->methods);
    free(node);
    return (stmt){0};
}

static stmt parseEnum(parserState *state) {
    DEFINE_TOK;
    tok = advance(state);
    expect(IDENTIFIER, "Expected enum name", stmt);
    if (!strcmp(tok.lexeme, "array")) {
        signatureError(state, "array is a reserved type name"); return (stmt){0};
    }
    struct stmt_enum node = {.name = tok};
    tok = advance(state);
    signatureFields typeParams = {0};
    if (tok.type == LEFT_BRACKET) {
        signatureError(state, "Enum type parameters require angle brackets <...>"); goto invalid;
    }
    if (tok.type == LESS_THAN && !parseTypeParameters(state, &typeParams)) goto invalid;
    node.nTypeParams = typeParams.count; node.typeParamNames = typeParams.names;
    node.typeParamConstraints = typeParams.types;
    SET_TOK;
    expect(LEFT_CURLY_BRACE, "Expected enum body", stmt);
    tok = advance(state);
    while (tok.type != RIGHT_CURLY_BRACE) {
        if (tok.type != IDENTIFIER) {
            signatureError(state, "Expected enum member name");
            goto invalid;
        }
        for (size_t i = 0; i < node.nMembers; i++) {
            if (!strcmp(node.names[i].lexeme, tok.lexeme)) {
                signatureError(state, "Duplicate enum member");
                goto invalid;
            }
        }
        token name = tok;
        tok = advance(state);
        expr *value = nullptr;
        typeTokens valueType = {0};
        signatureFields fields = {0};
        unsigned char form = 0;
        if (tok.type == LEFT_PAREN) {
            form = 1;
            if (!parseSignatureFields(state, &fields, 0, 0)) goto invalid;
            SET_TOK;
            for (size_t i = 0; i < fields.count; i++) {
                if (fields.names[i].type != EOF_TOKEN) {
                    freeSignatureFields(&fields);
                    signatureError(state, "Enum tuple payloads require unnamed types");
                    goto invalid;
                }
            }
            for (size_t i = 0; i < fields.count; i++) {
                char text[48]; snprintf(text, sizeof(text), "__tuple%zu", i);
                fields.names[i] = name; fields.names[i].lexeme = strdup(text);
            }
        } else if (tok.type == LEFT_CURLY_BRACE) {
            form = 2;
            tok = advance(state);
            while (tok.type != RIGHT_CURLY_BRACE) {
                if (!parseStructFields(state, &fields, NULL, 0)) goto invalid;
                SET_TOK;
                if (tok.type == RIGHT_CURLY_BRACE) break;
                if (tok.type != COMMA && tok.type != SEMICOLON) {
                    signatureError(state, "Expected comma between enum fields"); goto invalid;
                }
                tok = advance(state);
            }
            tok = advance(state);
        } else if (tok.type == COLON && peek(state).type != EQUALS) {
            advance(state);
            size_t start = state->tokenIndex;
            if (!parseSignatureType(state, 0)) goto invalid;
            valueType = copySignatureSpan(state, start, state->tokenIndex);
            SET_TOK;
            if (tok.type != EQUALS) { signatureError(state, "Expected fixed enum value"); goto invalid; }
        }
        if (tok.type == EQUALS || tok.type == COLON) {
            if (form) { signatureError(state, "Payload variants cannot have fixed values"); goto invalid; }
            form = 3;
            if (tok.type == COLON) {
                tok = advance(state);
                if (tok.type != EQUALS) { signatureError(state, "Expected := before enum value"); goto invalid; }
            }
            advance(state);
            expr parsed = assignment(state);
            if (state->isSynchronizing) goto invalid;
            value = malloc(sizeof(expr)); CHECK_MALLOC(value); *value = parsed;
            SET_TOK;
        }
        size_t next = node.nMembers + 1;
        node.forms = realloc(node.forms, next);
        node.payloads = realloc(node.payloads, next * sizeof(*node.payloads));
        node.valueTypes = realloc(node.valueTypes, next * sizeof(*node.valueTypes));
        CHECK_MALLOC(node.forms); CHECK_MALLOC(node.payloads); CHECK_MALLOC(node.valueTypes);
        node.forms[node.nMembers] = form;
        node.valueTypes[node.nMembers] = valueType;
        node.payloads[node.nMembers] = (struct stmt_struct){.name = name,
            .nFields = fields.count,
            .nVarParams = fields.count, .fieldNames = fields.names, .fieldTypes = fields.types};
        token *names = realloc(node.names, (node.nMembers + 1) * sizeof(token));
        CHECK_MALLOC(names);
        node.names = names;
        expr **values = realloc(node.values, (node.nMembers + 1) * sizeof(expr*));
        CHECK_MALLOC(values);
        node.values = values;
        node.names[node.nMembers] = name;
        node.values[node.nMembers++] = value;
        if (tok.type == RIGHT_CURLY_BRACE) break;
        if (tok.type != COMMA) {
            signatureError(state, "Expected comma after enum member");
            goto invalid;
        }
        tok = advance(state);
    }
    advance(state);
    struct stmt_enum *result = malloc(sizeof(*result));
    CHECK_MALLOC(result);
    *result = node;
    return (stmt){.type = STMT_ENUM, .value = result};
invalid:
    // Full recursive cleanup of partial ASTs remains to be implemented.
    for (size_t i = 0; i < node.nMembers; i++) free(node.values[i]);
    free(node.names);
    free(node.values);
    state->hasError = state->isSynchronizing = 1;
    return (stmt){0};
}

static stmt parseMatch(parserState *state) {
    advance(state);
    if (currentToken(state).type != LEFT_PAREN) { signatureError(state, "Expected match subject in parentheses"); return (stmt){0}; }
    advance(state);
    struct stmt_switch *node = calloc(1, sizeof(*node)); CHECK_MALLOC(node);
    node->isMatch = 1; node->binding.type = EOF_TOKEN;
    node->value = malloc(sizeof(expr)); CHECK_MALLOC(node->value);
    *node->value = assignment(state);
    if (state->isSynchronizing) return (stmt){0};
    if (currentToken(state).type != RIGHT_PAREN) { signatureError(state, "Expected closing match parenthesis"); return (stmt){0}; }
    advance(state);
    if (currentToken(state).type != LEFT_CURLY_BRACE) { signatureError(state, "Expected match body"); return (stmt){0}; }
    advance(state);
    while (currentToken(state).type != RIGHT_CURLY_BRACE) {
        expr pattern = assignment(state);
        if (state->isSynchronizing) return (stmt){0};
        if (currentToken(state).type != FAT_ARROW) { signatureError(state, "Expected => after match pattern"); return (stmt){0}; }
        advance(state);
        stmt body = parseStatement(state);
        if (state->isSynchronizing) return (stmt){0};
        struct switch_case branch = {.nValues = 1};
        branch.values = malloc(sizeof(expr)); CHECK_MALLOC(branch.values); *branch.values = pattern;
        if (body.type == STMT_BLOCK) branch.body = *(struct stmt_block *)body.value;
        else { branch.body.nStmts = 1; branch.body.stmts = malloc(sizeof(stmt)); CHECK_MALLOC(branch.body.stmts); *branch.body.stmts = body; }
        node->cases = realloc(node->cases, (node->nCases + 1) * sizeof(*node->cases)); CHECK_MALLOC(node->cases);
        node->cases[node->nCases++] = branch;
        if (currentToken(state).type == SEMICOLON) advance(state);
    }
    advance(state);
    return (stmt){.type = STMT_SWITCH, .value = node};
}

static stmt parseSwitch(parserState *state) {
    DEFINE_TOK;
    tok = advance(state);
    struct stmt_switch node = {.binding = {.type = EOF_TOKEN}};
    if (tok.type == LEFT_PAREN) {
        advance(state);
        char oldGuard = state->allowTypeGuard;
        size_t guards = state->typeGuards;
        state->allowTypeGuard = 1;
        stmt header = parseDeclarationExpr(state);
        state->allowTypeGuard = oldGuard;
        if (state->isSynchronizing) return (stmt){0};
        SET_TOK;
        if (tok.type == SEMICOLON) {
            if (state->typeGuards != guards) {
                signatureError(state, "Type guard cannot be a switch initializer");
                return (stmt){0};
            }
            node.initializer = header;
            tok = advance(state);
            if (tok.type != RIGHT_PAREN) {
                state->allowTypeGuard = 1;
                header = parseDeclarationExpr(state);
                state->allowTypeGuard = oldGuard;
                if (state->isSynchronizing) return (stmt){0};
            } else header = (stmt){0};
        }
        expr *guard = NULL;
        if (header.type == STMT_VAR) {
            struct stmt_var *binding = header.value;
            if (binding->nVars == 1 && !binding->type.nTokens && binding->nInitValues == 1) {
                node.binding = binding->vars[0];
                guard = &binding->initValues[0];
            }
        } else if (header.type == STMT_EXPR) guard = header.value;
        node.isTypeSwitch = guard && guard->type == EXPR_TYPE_ASSERTION &&
            ((struct expr_assertion*)guard->underlying)->isTypeGuard;
        if ((state->typeGuards != guards && (!node.isTypeSwitch || state->typeGuards != guards + 1)) ||
            (header.type != STMT_NULL && !guard) ||
            (header.type == STMT_VAR && !node.isTypeSwitch)) {
            signatureError(state, "Expected switch expression or a single type-switch binding");
            return (stmt){0};
        }
        node.value = guard;
        if (header.type == STMT_VAR) {
            struct stmt_var *binding = header.value;
            node.value = binding->initValues;
            free(binding->vars);
            free(binding);
        }
        SET_TOK;
        expect(RIGHT_PAREN, "Expected end of switch expression", stmt);
        tok = advance(state);
    }
    expect(LEFT_CURLY_BRACE, "Expected switch body", stmt);
    tok = advance(state);
    char hasDefault = 0;
    state->switchDepth++;
    while (tok.type != RIGHT_CURLY_BRACE) {
        struct switch_case clause = {0};
        exprlist values = {0};
        stmtlist body = {0};
        init_exprlist(&values);
        init_stmtlist(&body);
        if (tok.type == DEFAULT) {
            if (hasDefault) {
                signatureError(state, "Duplicate switch default");
                goto clauseError;
            }
            hasDefault = 1;
            tok = advance(state);
        } else if (tok.type == CASE) {
            do {
                advance(state);
                if (node.isTypeSwitch) {
                    size_t start = state->tokenIndex;
                    if (!parseTypeConstraint(state)) goto clauseError;
                    typeTokens *types = realloc(clause.types, (clause.nTypes + 1) * sizeof(*types));
                    CHECK_MALLOC(types);
                    clause.types = types;
                    clause.types[clause.nTypes++] = copySignatureSpan(state, start, state->tokenIndex);
                } else {
                    expr value = assignment(state);
                    if (state->isSynchronizing) goto clauseError;
                    push_exprlist(&values, value);
                }
                SET_TOK;
            } while (tok.type == COMMA);
        } else {
            signatureError(state, "Expected case or default in switch");
            goto clauseError;
        }
        if (tok.type != COLON) {
            signatureError(state, "Expected colon after switch case");
            goto clauseError;
        }
        tok = advance(state);
        while (tok.type != CASE && tok.type != DEFAULT && tok.type != RIGHT_CURLY_BRACE) {
            if (tok.type == EOF_TOKEN) {
                signatureError(state, "Expected closing switch brace");
                goto clauseError;
            }
            size_t oldFallthroughDepth = state->fallthroughDepth;
            state->fallthroughDepth = node.isTypeSwitch ? 0 : state->syntaxDepth + 1;
            stmt statement = parseStatement(state);
            state->fallthroughDepth = oldFallthroughDepth;
            if (state->isSynchronizing) goto clauseError;
            if (statement.type != STMT_NULL) push_stmtlist(&body, statement);
            SET_TOK;
            if (statement.type == STMT_FALLTHROUGH && tok.type != CASE && tok.type != DEFAULT) {
                signatureError(state, "Fallthrough must end a non-final switch case");
                goto clauseError;
            }
        }
        clause.nValues = values.top;
        clause.values = values.top ? to_exprarray(&values) : nullptr;
        clause.body.nStmts = body.top;
        clause.body.stmts = body.top ? to_stmtarray(&body) : nullptr;
        free_exprlist(&values);
        free_stmtlist(&body);
        struct switch_case *cases = realloc(node.cases, (node.nCases + 1) * sizeof(*cases));
        CHECK_MALLOC(cases);
        node.cases = cases;
        node.cases[node.nCases++] = clause;
        continue;
clauseError:
        for (size_t i = 0; i < clause.nTypes; i++) free(clause.types[i].tokens);
        free(clause.types);
        free_exprlist(&values);
        free_stmtlist(&body);
        state->switchDepth--;
        state->hasError = state->isSynchronizing = 1;
        return (stmt){0};
    }
    state->switchDepth--;
    advance(state);
    struct stmt_switch *result = malloc(sizeof(*result));
    CHECK_MALLOC(result);
    *result = node;
    return (stmt){.type = STMT_SWITCH, .value = result};
}

// Disambiguate a single-name declaration from a label. Grouped variable
// declarations are handled separately by startsDeclaration(). For ambiguous
// bodies such as "label: work();", use "label: { work(); }".
static char colonStartsDeclaration(parserState *state) {
    parserState trial = *state;
    trial.quietErrors = 1;
    advance(&trial); // colon
    token tok = advance(&trial);
    if (tok.type == EQUALS) return 1; // inferred declaration
    if (!parseSignatureType(&trial, 0) || trial.isSynchronizing) return 0;
    tok = currentToken(&trial);
    return tok.type == SEMICOLON || tok.type == EQUALS;
}

// Bind ${name} outside assembler strings/comments to scalar memory operands.
static char parseAsmOperands(parserState *state, struct stmt_asm *node) {
    const char *body = node->assembly;
    int quote = 0, lineComment = 0, blockComment = 0;
    int hashComment = strcmp(node->architecture.lexeme, "aarch64") != 0;
    for (size_t i=0; body[i]; i++) {
        char c = body[i], next = body[i+1];
        if (lineComment) { if (c == '\n') lineComment = 0; continue; }
        if (blockComment) { if (c == '*' && next == '/') { i++; blockComment = 0; } continue; }
        if (quote) { if (c == '\\' && next) i++; else if (c == quote) quote = 0; continue; }
        if (c == '/' && next == '/') { lineComment = 1; i++; continue; }
        if (c == '/' && next == '*') { blockComment = 1; i++; continue; }
        if (c == '#' && hashComment) { lineComment = 1; continue; }
        if (c == '"' || c == '\'') { quote = c; continue; }
        if (c != '$' || next != '{') continue;
        size_t begin = i, nameStart = i + 2, end = nameStart;
        uint32_t code;
        size_t bytes = unicodeDecode(body+end, &code);
        if (!bytes || !unicodeStart(code)) return signatureError(state, "Expected variable name in asm ${name} operand");
        end += bytes;
        while ((bytes = unicodeDecode(body+end, &code)) && unicodeContinue(code)) end += bytes;
        if (body[end] != '}') return signatureError(state, "Expected '}' after asm operand name");
        char *name = strndup(body+nameStart, end-nameStart);
        CHECK_MALLOC(name);
        size_t operand = 0;
        while (operand < node->nOperands && strcmp(node->operands[operand].lexeme, name)) operand++;
        if (operand == node->nOperands) {
            node->operands = realloc(node->operands, (operand+1)*sizeof(*node->operands));
            CHECK_MALLOC(node->operands);
            token at = node->architecture;
            at.lexeme = name;
            // The raw body begins immediately after its opening brace.
            at.line = currentToken(state).line; at.column = currentToken(state).column + 1;
            for (size_t j=0; j<nameStart; j++) {
                if (body[j] == '\n') { at.line++; at.column = 1; } else at.column++;
            }
            node->operands[node->nOperands++] = at;
        } else free(name);
        node->references = realloc(node->references, (node->nReferences+1)*sizeof(*node->references));
        CHECK_MALLOC(node->references);
        node->references[node->nReferences++] = (struct asm_reference){begin, end-begin+1, operand};
        i = end;
    }
    if (!strcmp(node->architecture.lexeme, "wasm") && node->nOperands)
        return signatureError(state, "Wasm asm blocks do not yet support scalar operands");
    if (strcmp(node->architecture.lexeme, "x86_64") && node->nOperands > 4)
        return signatureError(state, "AArch64 and RISC-V asm blocks support at most four distinct scalar operands");
    return 1;
}

static stmt parseStatementImpl(parserState *state);
static stmt parseStatement(parserState *state) {
    if (state->syntaxDepth >= PARSER_MAX_RECURSION_DEPTH) {
        token tok = state->tokens[state->tokenIndex];
        diagnostic(state->source, tok, "syntax", "error", "Parser nesting limit exceeded");
        state->hasError = state->isSynchronizing = 1;
        return (stmt){0};
    }
    token location = currentToken(state);
    state->syntaxDepth++;
    stmt result = parseStatementImpl(state);
    state->syntaxDepth--;
    result.location = location;
    return result;
}

static stmt parseStatementImpl(parserState *state) {
    DEFINE_TOK;
    // Contextual keyword: existing identifiers named forward remain valid.
    if (tok.type == IDENTIFIER && !strcmp(tok.lexeme, "forward") && peek(state).type == PANIC) {
        if (!state->functionDepth) {
            signatureError(state, "Forward panic is only allowed inside a function");
            return (stmt){0};
        }
        advance(state); // forward
        advance(state); // panic
        stmt result = parseStatement(state);
        result.forwardPanic = 1;
        return result;
    }
    switch (tok.type) {
        case ASM: {
            if (!state->functionDepth) {
                signatureError(state, "asm blocks are only allowed inside functions");
                return (stmt){0};
            }
            tok = advance(state);
            expect(IDENTIFIER, "Expected asm architecture (x86_64, aarch64, riscv64, wasm)", stmt);
            token architecture = tok, platform = {.type=EOF_TOKEN};
            if (strcmp(tok.lexeme, "x86_64") && strcmp(tok.lexeme, "aarch64") && strcmp(tok.lexeme, "riscv64") && strcmp(tok.lexeme, "wasm")) {
                signatureError(state, "Unknown asm architecture; expected x86_64, aarch64, riscv64, or wasm");
                return (stmt){0};
            }
            tok = advance(state);
            if (tok.type == SLASH) {
                tok = advance(state);
                expect(IDENTIFIER, "Expected asm platform after '/'", stmt);
                platform = tok;
                if (strcmp(tok.lexeme, "linux") && strcmp(tok.lexeme, "macos") && strcmp(tok.lexeme, "windows")) {
                    signatureError(state, "Unknown asm platform; expected linux, macos, or windows");
                    return (stmt){0};
                }
                tok = advance(state);
            }
            expect(ASM_BODY, "Expected required '{ ... }' asm block", stmt);
            struct stmt_asm *node = malloc(sizeof(*node));
            CHECK_MALLOC(node);
            *node = (struct stmt_asm){.architecture=architecture, .platform=platform, .assembly=tok.lexeme};
            if (!parseAsmOperands(state, node)) return (stmt){0};
            advance(state);
            if (currentToken(state).type == SEMICOLON) advance(state);
            return (stmt){.type=STMT_ASM, .value=node};
        }
        case TYPE:
            return parseTypeDeclaration(state);
        case STRUCT:
            return parseStruct(state);
        case ENUM:
            return parseEnum(state);
        case INTERFACE:
            return parseInterface(state);
        case SWITCH:
            return parseSwitch(state);
        case MATCH:
            return parseMatch(state);
        case EXTERN:
            if (peek(state).type != DOT) return parseExtern(state);
            goto expressionStatement;
        case BREAK:
        case CONTINUE:
        case GOTO:
        case FALLTHROUGH: {
            enum tokenType keyword = tok.type;
            if ((keyword == BREAK && !state->loopDepth && !state->switchDepth) ||
                (keyword == CONTINUE && !state->loopDepth) ||
                (keyword == FALLTHROUGH && (!state->switchDepth || state->syntaxDepth != state->fallthroughDepth)) ||
                (keyword == GOTO && !state->functionDepth)) {
                signatureError(state, "Branch statement is not valid in this context");
                return (stmt){0};
            }
            tok = advance(state);
            token label = {.type = EOF_TOKEN};
            if (keyword != FALLTHROUGH && tok.type == IDENTIFIER) {
                label = tok;
                tok = advance(state);
            }
            if (keyword == GOTO && label.type == EOF_TOKEN) {
                signatureError(state, "Expected goto label");
                return (stmt){0};
            }
            expect(SEMICOLON, "Expected semicolon after branch", stmt);
            advance(state);
            if (keyword == FALLTHROUGH) return (stmt){.type = STMT_FALLTHROUGH};
            struct stmt_branch *branch = malloc(sizeof(*branch));
            CHECK_MALLOC(branch);
            branch->label = label;
            return (stmt){.type = keyword == BREAK ? STMT_BREAK :
                                 keyword == CONTINUE ? STMT_CONTINUE : STMT_GOTO,
                          .value = branch};
        }
        case DEFER: {
            if (!state->functionDepth) {
                signatureError(state, "Defer is only allowed inside a function");
                return (stmt){0};
            }
            advance(state);
            expr *call = parseExpr(state);
            if (!call || state->isSynchronizing) return (stmt){0};
            if (call->type != EXPR_TYPE_CALL) {
                signatureError(state, "Expected function call after defer");
                return (stmt){0};
            }
            SET_TOK;
            expect(SEMICOLON, "Expected semicolon after defer", stmt);
            advance(state);
            struct stmt_defer *node = malloc(sizeof(*node));
            CHECK_MALLOC(node);
            node->call = call;
            return (stmt){.type = STMT_DEFER, .value = node};
        }
        case PANIC: {
            if (!state->functionDepth) {
                signatureError(state, "Panic is only allowed inside a function");
                return (stmt){0};
            }
            advance(state);
            expr *message = parseExpr(state);
            if (!message || state->isSynchronizing) return (stmt){0};
            SET_TOK;
            expect(SEMICOLON, "Expected semicolon after panic message", stmt);
            advance(state);
            return (stmt){.type = STMT_PANIC, .value = message};
        }
        case RETURN: {
            if (!state->functionDepth) {
                signatureError(state, "Return is only allowed inside a function");
                return (stmt){0};
            }
            tok = advance(state);
            if (tok.type == PANIC) {
                stmt result = parseStatement(state);
                if (result.type == STMT_PANIC) result.type = STMT_RETURN_PANIC;
                return result;
            }
            exprlist values = {0};
            init_exprlist(&values);
            while (tok.type != SEMICOLON && tok.type != RIGHT_CURLY_BRACE) {
                expr value = assignment(state);
                if (state->isSynchronizing) {
                    free_exprlist(&values);
                    state->hasError = 1;
                    return (stmt){0};
                }
                push_exprlist(&values, value);
                SET_TOK;
                if (tok.type != COMMA) break;
                tok = advance(state);
                if (tok.type == SEMICOLON || tok.type == RIGHT_CURLY_BRACE) {
                    free_exprlist(&values);
                    signatureError(state, "Expected return value after comma");
                    return (stmt){0};
                }
            }
            if (tok.type != SEMICOLON && tok.type != RIGHT_CURLY_BRACE) {
                free_exprlist(&values);
                signatureError(state, "Expected semicolon after return values");
                return (stmt){0};
            }
            struct stmt_return *result = malloc(sizeof(struct stmt_return));
            CHECK_MALLOC(result);
            result->nValues = values.top;
            result->values = result->nValues ? to_exprarray(&values) : nullptr;
            free_exprlist(&values);
            if (tok.type == SEMICOLON) advance(state);
            return (stmt){.type = STMT_RETURN, .value = result};
        }
        case UNDERSCORE:
        case IDENTIFIER:
            // A complete type followed by ';' or '=' retains the existing
            // declaration meaning. Otherwise ':' introduces any statement.
            // Probe on an isolated cursor so failed type parses stay silent.
            if (peek(state).type == COLON && !colonStartsDeclaration(state)) {
                token name = tok;
                advance(state);
                advance(state);
                stmt body = parseStatement(state);
                if (state->isSynchronizing) return (stmt){0};
                struct stmt_label *label = malloc(sizeof(*label));
                CHECK_MALLOC(label);
                label->name = name;
                label->body = malloc(sizeof(stmt));
                CHECK_MALLOC(label->body);
                *label->body = body;
                return (stmt){.type = STMT_LABEL, .value = label};
            }
            if (startsDeclaration(state)) {
                stmt decl = parseDeclaration(state);
                if (state->isSynchronizing) {
                    return (stmt){0};
                }
                SET_TOK;
                expect(SEMICOLON, "Expected semicolon", stmt);
                tok = advance(state);
                return decl;
            }
            stmt declExpr = parseDeclarationExpr(state);
            if (state->isSynchronizing) {
                state->hasError = 1;
                return (stmt){0};
            }
            SET_TOK;
            expect(SEMICOLON, "Expected semicolon", stmt);
            tok = advance(state);
            return declExpr;
        case LEFT_CURLY_BRACE:
            token blockOpen = tok;
            stmtlist *statements = parseBlock(state);
            if (!statements) {
                state->hasError = state->isSynchronizing = 1;
                return (stmt){0};
            }
            if (state->isSynchronizing) {
                return (stmt){0};
            }
            struct stmt_block *block = malloc(sizeof(struct stmt_block));
            CHECK_MALLOC(block);
            block->open = blockOpen;
            block->close = state->tokens[state->tokenIndex ? state->tokenIndex-1 : 0];
            block->stmts = to_stmtarray(statements);
            block->nStmts = listlen(statements);
            free_stmtlist(statements);
            free(statements);
            return (stmt){.type = STMT_BLOCK, .value = block};
        case IF:;
            token ifOpen = tok;
            tok = advance(state);
            expect(LEFT_PAREN, "Expected condition for if statement", stmt);
            tok = advance(state);
            stmt preStmtValue = parseDeclarationExpr(state);
            if (state->isSynchronizing) {
                state->hasError = 1;
                return (stmt){0};
            }

            SET_TOK;
            stmt *preStmt = nullptr;
            expr *condition = nullptr;
            if (tok.type == SEMICOLON) {
                tok = advance(state);
                preStmt = malloc(sizeof(stmt));
                CHECK_MALLOC(preStmt);
                *preStmt = preStmtValue;
                condition = parseExpr(state);
                if (state->isSynchronizing) {
                    state->hasError = 1;
                    return (stmt){0};
                }
            } else {
                if (preStmtValue.type != STMT_EXPR) {
                    signatureError(state, "Expected expression for if condition");
                    return (stmt){0};
                }
                condition = preStmtValue.value;
            }
            SET_TOK;
            expect(RIGHT_PAREN, "Expected right paren", stmt);
            tok = advance(state);
            stmt ifTrue = parseStatement(state);
            if (state->isSynchronizing) {
                state->hasError = 1;
                return (stmt){0};
            }
            SET_TOK;
            stmt *ifFalse = nullptr;
            if (tok.type == ELSE) {
                tok = advance(state);
                ifFalse = malloc(sizeof(stmt));
                CHECK_MALLOC(ifFalse);
                *ifFalse = parseStatement(state);
                if (state->isSynchronizing) {
                    free(ifFalse);
                    state->hasError = 1;
                    return (stmt){0};
                }
            }
            stmt ifStatement = {.type = STMT_IF, .value = malloc(sizeof(struct stmt_if))};
            CHECK_MALLOC(ifStatement.value);
            ((struct stmt_if*)ifStatement.value)->open = ifOpen;
            ((struct stmt_if*)ifStatement.value)->close = state->tokens[state->tokenIndex ? state->tokenIndex-1 : 0];
            ((struct stmt_if*)ifStatement.value)->preStmt = preStmt;
            ((struct stmt_if*)ifStatement.value)->condition = condition;
            ((struct stmt_if*)ifStatement.value)->ifTrue = malloc(sizeof(stmt));
            CHECK_MALLOC(((struct stmt_if*)ifStatement.value)->ifTrue);
            *((struct stmt_if*)ifStatement.value)->ifTrue = ifTrue;
            ((struct stmt_if*)ifStatement.value)->ifFalse = ifFalse;
            return ifStatement;
        case FOR:
            return parseFor(state);
        case SEMICOLON:
            // empty statement
            tok = advance(state);
            return (stmt){0};
        case FUNC:
            if (state->functionDepth && peek(state).type == LEFT_PAREN)
                goto expressionStatement; // Immediately invoked literal in statement position.
            return parseFunc(state);
        default:
        expressionStatement:;
            stmt expr = parseDeclarationExpr(state);
            if (state->isSynchronizing) {
                state->hasError = 1;
                return (stmt){0};
            }
            SET_TOK;
            expect(SEMICOLON, "Expected semicolon", stmt);
            tok = advance(state);
            return expr;
    }
    return (stmt){0};
}

static stmtlist *parseBlock(parserState *state) {
    DEFINE_TOK;
    expect(LEFT_CURLY_BRACE, "Expected block start", stmtlist*);
    tok = advance(state);
    stmtlist *statements = malloc(sizeof(stmtlist));
    CHECK_MALLOC(statements);
    *statements = (stmtlist){0};
    init_stmtlist(statements);
    while (tok.type != RIGHT_CURLY_BRACE && tok.type != EOF_TOKEN) {
        size_t start = state->tokenIndex;
        stmt statement = parseStatement(state);
        if (state->isSynchronizing && state->recoverStatements) {
            // Discard only the damaged statement, balancing nested blocks.
            size_t braces = 0;
            for (size_t i = start; i < state->tokenIndex; i++) {
                if (state->tokens[i].type == LEFT_CURLY_BRACE) braces++;
                else if (state->tokens[i].type == RIGHT_CURLY_BRACE && braces) braces--;
            }
            while (currentToken(state).type != EOF_TOKEN) {
                token next = currentToken(state);
                if (!braces && next.type == RIGHT_CURLY_BRACE) break;
                advance(state);
                if (next.type == LEFT_CURLY_BRACE) braces++;
                else if (next.type == RIGHT_CURLY_BRACE && braces) braces--;
                if (!braces && next.type == SEMICOLON) break;
            }
            state->hasError = 1;
            state->isSynchronizing = 0;
        } else if (state->isSynchronizing) {
            free_stmtlist(statements);
            free(statements);
            return nullptr;
        } else push_stmtlist(statements, statement);
        SET_TOK;
    }
    if (tok.type == EOF_TOKEN) {
        diagnostic(state->source, tok, "syntax", "error", "Expected end of block");
        state->hasError = state->isSynchronizing = 1;
        if (state->recoverStatements) {
            state->isSynchronizing = 0;
            return statements;
        }
        free_stmtlist(statements);
        free(statements);
        return nullptr;
    }
    tok = advance(state);
    return statements;
}

static char parseImportEntry(parserState *state, stmtlist *statements) {
    DEFINE_TOK;
    char *alias = nullptr;
    if (tok.type == IDENTIFIER || tok.type == UNDERSCORE || tok.type == DOT) {
        alias = tok.lexeme;
        tok = advance(state);
    }
    if (tok.type != LITERAL_STRING)
        return signatureError(state, "Expected quoted import path");
    token location = tok;
    char *path = tok.lexeme;
    if (!path || !*path) return signatureError(state, "Import path must not be empty");
    tok = advance(state);
    if (tok.type == AS) {
        if (alias) return signatureError(state, "Import alias specified twice");
        tok = advance(state);
        if (tok.type != IDENTIFIER && tok.type != UNDERSCORE && tok.type != DOT)
            return signatureError(state, "Expected import alias after as");
        alias = tok.lexeme;
        advance(state);
    }
    struct stmt_import *node = malloc(sizeof(*node));
    CHECK_MALLOC(node);
    *node = (struct stmt_import){.path = path, .importedName = alias};
    push_stmtlist(statements, (stmt){.type = STMT_IMPORT, .value = node, .location = location});
    return 1;
}

static char parseImports(parserState *state, stmtlist *statements) {
    token tok = advance(state);
    if (tok.type != LEFT_PAREN) {
        if (!parseImportEntry(state, statements)) return 0;
        SET_TOK;
        if (tok.type != SEMICOLON) return signatureError(state, "Expected semicolon after import");
        advance(state);
        return 1;
    }
    tok = advance(state);
    while (tok.type != RIGHT_PAREN) {
        if (!parseImportEntry(state, statements)) return 0;
        SET_TOK;
        if (tok.type == RIGHT_PAREN) break;
        if (tok.type == COMMA || tok.type == SEMICOLON) tok = advance(state);
        else if (tok.line <= state->tokens[state->tokenIndex - 1].line)
            return signatureError(state, "Expected separator between imports");
    }
    tok = advance(state);
    if (tok.type == SEMICOLON) advance(state);
    return 1;
}

// Error recovery always advances and tracks delimiters so a broken declaration
// cannot stall the parser or consume the start of the next top-level function.
static void recoverTopLevel(parserState *state, size_t start) {
    state->pendingGreater = 0;
    size_t braces = 0;
    for (size_t i = start; i < state->tokenIndex; i++) {
        if (state->tokens[i].type == LEFT_CURLY_BRACE) braces++;
        else if (state->tokens[i].type == RIGHT_CURLY_BRACE && braces) braces--;
    }
    while (state->tokenIndex < state->tokensLen) {
        enum tokenType type = state->tokens[state->tokenIndex].type;
        if (type == EOF_TOKEN) break;
        if (state->tokenIndex > start && !braces &&
            (type == FUNC || type == STRUCT || type == INTERFACE || type == ENUM ||
             type == TYPE || type == IMPORT || type == PACKAGE || type == EXTERN)) break;
        if (type == LEFT_CURLY_BRACE) braces++;
        else if (type == RIGHT_CURLY_BRACE) {
            if (braces) braces--;
            advance(state);
            if (!braces) break;
            continue;
        }
        advance(state);
        if (type == SEMICOLON && !braces) break;
    }
    state->isSynchronizing = 0;
}

parseResult parseTokens(tokenlist *tokensList) { return parseTokensWithSource(tokensList, NULL); }
static parseResult parseTokensMode(tokenlist *tokensList, const char *source, int recovery,
                                   parserState *fix);
parseResult parseTokensWithSource(tokenlist *tokensList, const char *source) {
    return parseTokensMode(tokensList, source, 0, NULL);
}
parseResult parseTokensForEditor(tokenlist *tokensList, const char *source) {
    return parseTokensMode(tokensList, source, 1, NULL);
}
size_t parseTokensForFix(tokenlist *tokensList, const char *source, char **knownTypes,
                         size_t nKnownTypes, typeRewrite **rewrites) {
    // Recover per statement so one damaged statement does not hide later rewrites.
    parserState fix = {.fixMode = 1, .knownTypes = knownTypes, .nKnownTypes = nKnownTypes};
    parseResult parsed = parseTokensMode(tokensList, source, 1, &fix);
    free(parsed.statements); // The AST is not needed; its nodes are intentionally leaked.
    free(parsed.packageName);
    free(fix.typeScope);
    *rewrites = fix.rewrites;
    return fix.nRewrites;
}
static parseResult parseTokensMode(tokenlist *tokensList, const char *source, int recovery,
                                   parserState *fix) {
    parseResult result = {.sourceText = source};
    if (!tokensList || tokensList->top <= 0 || !tokensList->arr) {
        result.hasError = 1;
        return result;
    }
    parserState state = {.tokens = to_tokenarray(tokensList), .tokensLen = tokensList->top, .source = source, .recoverStatements = recovery};
    if (fix) {
        state.fixMode = 1; state.quietErrors = 0;
        state.knownTypes = fix->knownTypes; state.nKnownTypes = fix->nKnownTypes;
    }
    stmtlist statements = {0};
    init_stmtlist(&statements);
    // Require the scanner's EOF sentinel before exposing tokens to the parser.
    if (state.tokens[state.tokensLen - 1].type != EOF_TOKEN) {
        state.hasError = 1;
        goto done;
    }
    while (state.tokens[state.tokenIndex].type != EOF_TOKEN) {
        size_t start = state.tokenIndex;
        token tok = state.tokens[start];
        if (tok.type == PACKAGE) {
            tok = advance(&state);
            if (state.packageName) signatureError(&state, "Duplicate package declaration");
            else if (statements.top) signatureError(&state, "Package declaration must precede other declarations");
            else if (tok.type != IDENTIFIER)
                signatureError(&state, "Expected unquoted package name");
            else {
                state.packageName = strdup(tok.lexeme);
                CHECK_MALLOC(state.packageName);
                tok = advance(&state);
                if (tok.type != SEMICOLON) signatureError(&state, "Expected semicolon after package declaration");
                else advance(&state);
            }
        } else if (tok.type == IMPORT) {
            parseImports(&state, &statements);
        } else {
            stmt statement = parseStatement(&state);
            if (!state.isSynchronizing && statement.type != STMT_NULL)
                push_stmtlist(&statements, statement);
        }
        if (state.isSynchronizing) {
            state.hasError = 1;
            recoverTopLevel(&state, start);
        } else if (state.tokenIndex == start) {
            signatureError(&state, "Parser made no progress");
            recoverTopLevel(&state, start);
        }
    }
done:
    if (fix) {
        fix->rewrites = state.rewrites; fix->nRewrites = state.nRewrites;
        fix->typeScope = state.typeScope;
    }
    result.hasError = state.hasError;
    result.packageName = state.packageName;
    result.nStatements = statements.top;
    result.statementsCapacity = statements.top + 10; // Embedded Result and Optional enums and methods.
    result.statements = calloc(result.statementsCapacity, sizeof(stmt));
    CHECK_MALLOC(result.statements);
    for (size_t i=0; i<statements.top; i++) result.statements[i] = get_stmtlist(&statements, i);
    free_stmtlist(&statements);
    free_tokenlist(tokensList);
    free(state.tokens);
    return result;
}
