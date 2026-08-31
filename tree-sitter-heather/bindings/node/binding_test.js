const assert = require("node:assert");
const fs = require("node:fs");
const path = require("node:path");
const { test } = require("node:test");

const Parser = require("tree-sitter");
const Heather = require(".");

function heatherSources(directory) {
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
    const entryPath = path.join(directory, entry.name);
    if (entry.isDirectory()) return heatherSources(entryPath);
    return entry.isFile() && entry.name.endsWith(".hthr") ? [entryPath] : [];
  });
}

test("can load grammar", () => {
  const parser = new Parser();
  assert.doesNotThrow(() => parser.setLanguage(Heather));
});

test("parses every checked-in Heather source without errors", () => {
  const parser = new Parser();
  parser.setLanguage(Heather);

  const repositoryRoot = path.resolve(__dirname, "../../..");
  const sources = ["lib", "crates"]
    .flatMap((directory) => heatherSources(path.join(repositoryRoot, directory)))
    .sort();

  assert.notEqual(sources.length, 0, "expected to find checked-in Heather sources");
  for (const sourcePath of sources) {
    const tree = parser.parse(fs.readFileSync(sourcePath, "utf8"));
    assert.equal(
      tree.rootNode.hasError,
      false,
      `${path.relative(repositoryRoot, sourcePath)} contains an ERROR node`,
    );
  }
});
