#!/usr/bin/env node
// Build one minimal Lean file from a generated exposition site, exactly as
// the browser does (same builder module). Used by the verification harness
// (python -m lean_pool.exposition.verify).
//
// Usage: node build-minimal.mjs <site-dir> <repo-root> <project> <decl-name> <out-file>
// Exit codes: 0 built, 2 declaration not found, 3 build error.
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";

const argv = process.argv.slice(2);
if (!argv[4]) {
  console.error(
    "usage: build-minimal.mjs <site-dir> <repo-root> <project> <decl-name> <out-file>");
  process.exit(3);
}
const [siteDir, repoRoot] = [path.resolve(argv[0]), path.resolve(argv[1])];
const [project, declName, outFile] = argv.slice(2);

const require = createRequire(import.meta.url);
const builder = require(
  path.join(repoRoot, "python/lean_pool/exposition/static/assets/minimal.js"));

const shard = JSON.parse(
  fs.readFileSync(path.join(siteDir, "data/projects", `${project}.json`)));

let target = shard.decls.findIndex(
  (d) => d.name === declName || d.full === declName);
if (target < 0) {
  // Card names sometimes carry an extra namespace prefix; suffix-match.
  target = shard.decls.findIndex((d) => declName.endsWith(`.${d.name}`)
    || d.name.endsWith(`.${declName}`));
}
if (target < 0) {
  console.error(`declaration not found in ${project}: ${declName}`);
  process.exit(2);
}

const sources = {};
function loadModule(index) {
  if (sources[index] !== undefined) return;
  const file = path.join(
    repoRoot, ...shard.modules[index].split("."));
  sources[index] = fs.readFileSync(`${file}.lean`);
}

const cone = builder.coneIds(shard, target);
for (const moduleIndex of cone.modules) loadModule(moduleIndex);

let result = builder.build(shard, sources, target);
for (let round = 0; result.pending && round < 4; round++) {
  for (const moduleIndex of result.pending) loadModule(moduleIndex);
  result = builder.build(shard, sources, target);
}
if (result.pending) {
  console.error(`unresolved module sources for ${declName}`);
  process.exit(3);
}

fs.mkdirSync(path.dirname(outFile), { recursive: true });
fs.writeFileSync(outFile, result.text);
console.log(
  `${project}/${declName}: ${result.declarationCount} decls, `
  + `${result.moduleCount} modules, ${(result.text.length / 1024).toFixed(1)} KB`);
