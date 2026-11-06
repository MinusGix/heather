// The one token Heather's grammar cannot lex context-free: `>>`, a right
// shift only when whitespace comes before it (`a >> b`), and otherwise two
// closers of nested type-argument lists (`List<List<A>>`). The compiler's
// lexer decides it the same way (crates/syntax/src/lexer.rs, `TokKind::Shr`).
// tree-sitter calls an external scanner before it skips extras, so this is
// the one place that can see the space.

#include "tree_sitter/parser.h"

#include <wctype.h>

enum TokenType { SHIFT_RIGHT };

void *tree_sitter_heather_external_scanner_create(void) { return NULL; }

void tree_sitter_heather_external_scanner_destroy(void *payload) { (void)payload; }

unsigned tree_sitter_heather_external_scanner_serialize(void *payload, char *buffer) {
  (void)payload;
  (void)buffer;
  return 0;
}

void tree_sitter_heather_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
  (void)payload;
  (void)buffer;
  (void)length;
}

bool tree_sitter_heather_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
  (void)payload;
  if (!valid_symbols[SHIFT_RIGHT]) return false;
  bool spaced = false;
  while (iswspace(lexer->lookahead)) {
    spaced = true;
    lexer->advance(lexer, true);
  }
  if (!spaced || lexer->lookahead != '>') return false;
  lexer->advance(lexer, false);
  if (lexer->lookahead != '>') return false;
  lexer->advance(lexer, false);
  lexer->result_symbol = SHIFT_RIGHT;
  return true;
}
