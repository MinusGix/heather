#!/usr/bin/env node
const fs = require('fs');

const parser = fs.readFileSync('crates/syntax/src/parser.rs', 'utf8');
const grammar = fs.readFileSync('tree-sitter-heather/grammar.js', 'utf8');
const inventory = JSON.parse(fs.readFileSync('tree-sitter-heather/syntax-inventory.json', 'utf8'));
// The token kinds' spellings, from the table `TOKEN_KINDS`
// (lib/lang/lexer/lexer_kinds.hthr) as `scripts/linked` writes it for Rust:
// a line `Kind::<Name> => &["<spelling>", …],` for each kind that has one.
// The keywords are the parser's, and listed in the inventory.
const kinds = fs.readFileSync('crates/linked/generated/kinds.rs', 'utf8');

const failures = [];
for (const keyword of inventory.keywords) {
  const compilerOwns = parser.includes(`at_kw("${keyword}")`) ||
    parser.includes(`eat_kw("${keyword}")`) ||
    ['infer'].includes(keyword);
  if (!compilerOwns) failures.push(`manifest keyword is not used by parser: ${keyword}`);
  if (!grammar.includes(`'${keyword}'`)) failures.push(`grammar is missing keyword: ${keyword}`);
}

// The fixed symbols are the token kinds' spellings: the table is the one
// list, and the Rust lexer matches by it (`ScanKind::spelled_at`, generated
// with it). The grammar spells each, but those the parser refuses.
const tableSymbols = new Set();
for (const match of kinds.matchAll(/^ *Kind::\w+ => &\[(.*)\],$/gm)) {
  for (const spelling of match[1].matchAll(/"((?:[^"\\]|\\.)*)"/g)) tableSymbols.add(JSON.parse(`"${spelling[1]}"`));
}
if (tableSymbols.size === 0) failures.push('no spellings read from crates/linked/generated/kinds.rs');
for (const symbol of inventory.rejected_fixed_tokens) {
  if (!tableSymbols.has(symbol)) failures.push(`rejected manifest symbol is no spelling of the token kinds table (lib/lang/lexer/lexer_kinds.hthr): ${symbol}`);
}
for (const symbol of tableSymbols) {
  if (inventory.rejected_fixed_tokens.includes(symbol)) continue;
  if (!grammar.includes(`'${symbol}'`)) failures.push(`grammar is missing symbol: ${symbol} (a spelling of lib/lang/lexer/lexer_kinds.hthr)`);
}

const parserKeywords = new Set(
  [...parser.matchAll(/(?:at_kw|eat_kw)\("([A-Za-z_]+)"\)/g)].map(match => match[1])
);
for (const ignored of ['_', 'context', 'given']) parserKeywords.delete(ignored);
for (const keyword of parserKeywords) {
  if (!inventory.keywords.includes(keyword)) failures.push(`parser keyword is missing from manifest: ${keyword}`);
}

if (failures.length) {
  console.error(failures.map(failure => `error: ${failure}`).join('\n'));
  process.exit(1);
}
