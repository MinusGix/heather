#!/usr/bin/env node
const fs = require('fs');

const parser = fs.readFileSync('crates/syntax/src/parser.rs', 'utf8');
const lexer = fs.readFileSync('crates/syntax/src/lexer.rs', 'utf8');
const grammar = fs.readFileSync('tree-sitter-heather/grammar.js', 'utf8');
const inventory = JSON.parse(fs.readFileSync('tree-sitter-heather/syntax-inventory.json', 'utf8'));

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

const parserKeywords = new Set(
  [...parser.matchAll(/(?:at_kw|eat_kw)\("([A-Za-z_]+)"\)/g)].map(match => match[1])
);
for (const ignored of ['_', 'context', 'given', 'section']) parserKeywords.delete(ignored);
for (const keyword of parserKeywords) {
  if (!inventory.keywords.includes(keyword)) failures.push(`parser keyword is missing from manifest: ${keyword}`);
}

if (failures.length) {
  console.error(failures.map(failure => `error: ${failure}`).join('\n'));
  process.exit(1);
}
