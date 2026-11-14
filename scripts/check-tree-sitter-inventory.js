#!/usr/bin/env node
const fs = require('fs');

const parser = fs.readFileSync('crates/syntax/src/parser.rs', 'utf8');
const lexer = fs.readFileSync('crates/syntax/src/lexer.rs', 'utf8');
const grammar = fs.readFileSync('tree-sitter-heather/grammar.js', 'utf8');
const inventory = JSON.parse(fs.readFileSync('tree-sitter-heather/syntax-inventory.json', 'utf8'));
// The token kinds' spellings, from the table `TOKEN_KINDS`
// (lib/lang/lexer/lexer_kinds.hthr) as `scripts/linked` writes it for Rust:
// a line `Kind::<Name> => &["<spelling>", …],` for each kind that has one.
const kinds = fs.readFileSync('crates/linked/generated/kinds.rs', 'utf8');

const failures = [];
for (const keyword of inventory.keywords) {
  const compilerOwns = parser.includes(`at_kw("${keyword}")`) ||
    parser.includes(`eat_kw("${keyword}")`) ||
    ['infer'].includes(keyword);
  if (!compilerOwns) failures.push(`manifest keyword is not used by parser: ${keyword}`);
  if (!grammar.includes(`'${keyword}'`)) failures.push(`grammar is missing keyword: ${keyword}`);
}

for (const symbol of [...inventory.punctuation, ...inventory.fixed_operators]) {
  if (!lexer.includes(`"${symbol}"`) && !lexer.includes(`b'${symbol}'`)) {
    failures.push(`manifest symbol is not used by lexer: ${symbol}`);
  }
  if (!grammar.includes(`'${symbol}'`)) failures.push(`grammar is missing symbol: ${symbol}`);
}

const compilerSymbols = new Set();
for (const match of lexer.matchAll(/"([^"]+)"(?:\s*\|\s*"([^"]+)")?\s*=>\s*(?:Some\()?\(?TokKind::/g)) {
  compilerSymbols.add(match[1]);
  if (match[2]) compilerSymbols.add(match[2]);
}
for (const match of lexer.matchAll(/b'(.)'\s*=>\s*\(TokKind::/g)) compilerSymbols.add(match[1]);

const manifestedSymbols = new Set([
  ...inventory.punctuation,
  ...inventory.fixed_operators,
  ...inventory.rejected_fixed_tokens,
]);
for (const symbol of compilerSymbols) {
  if (!manifestedSymbols.has(symbol)) failures.push(`lexer symbol is missing from manifest: ${symbol}`);
}
for (const symbol of inventory.rejected_fixed_tokens) {
  if (!lexer.includes(`"${symbol}"`)) failures.push(`rejected manifest symbol is not used by lexer: ${symbol}`);
}

// The inventory's fixed symbols are exactly the table's spellings: a token
// added to the table and not to the inventory, or the other way, is named.
const tableSymbols = new Set();
for (const match of kinds.matchAll(/^ *Kind::\w+ => &\[(.*)\],$/gm)) {
  for (const spelling of match[1].matchAll(/"((?:[^"\\]|\\.)*)"/g)) tableSymbols.add(JSON.parse(`"${spelling[1]}"`));
}
if (tableSymbols.size === 0) failures.push('no spellings read from crates/linked/generated/kinds.rs');
for (const symbol of tableSymbols) {
  if (!manifestedSymbols.has(symbol)) failures.push(`token kinds table spelling is missing from manifest: ${symbol}`);
}
for (const symbol of manifestedSymbols) {
  if (!tableSymbols.has(symbol)) failures.push(`manifest symbol is no spelling of the token kinds table (lib/lang/lexer/lexer_kinds.hthr): ${symbol}`);
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
