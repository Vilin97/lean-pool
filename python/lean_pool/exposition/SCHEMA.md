# Exposition site: data formats and layout contract

The exposition is a static site published at `<pages-root>/exposition/` next to
the doc-gen4 API docs (which live at `<pages-root>/`). It is produced in two
steps:

1. **Extractor** (`scripts/exposition/Extract.lean`, run via
   `lake env lean --run`): dumps one JSON object per human-written declaration
   (JSONL). Kernel-level dependency edges are pre-resolved to human-written
   declarations; compiler-generated auxiliaries are tunnelled through.
2. **Generator** (`python -m lean_pool.exposition`): reads the dump, the
   project registry (`LeanPool/projects.yml`) and the Lean sources; computes
   per-project layered layouts and stats; emits the static site.

## Extractor dump (JSONL, one line per declaration)

```json
{"id": "_private.LeanPool.X.0.Foo.aux",   // full (possibly mangled) name — unique
 "n": "Foo.aux",                           // display name (private names demangled)
 "m": "LeanPool.ABCExceptions.Section2",   // defining module
 "k": "theorem",                           // coarse kind: theorem|def|instance|structure|class|inductive|axiom|opaque
 "r": [435, 0, 446, 23],                   // range: start line, start col, end line, end col (1-based lines)
 "s": [435, 6],                            // selection (name token) line/col
 "d": "docstring",                         // optional
 "p": true,                                // optional: private
 "deps": ["<id>", ...],                    // intra-pool dependency ids (other dump lines)
 "ext": 127}                               // count of distinct external (Mathlib/core) constants used
```

The generator refines `k` from source text (`lemma` vs `theorem`, `abbrev` vs
`def`) and slices the statement text (keyword up to the top-level `:=` /
`where` / `|` boundary — same approach as `scripts/proof-profile/statements.py`).

## Site tree

```
exposition/
  index.html              # landing: pool totals + sortable project table
  decls/index.html        # all-declarations viewer
  p/<Project>/index.html  # per-project graph page (one per project)
  assets/…                # shared JS/CSS (copied verbatim from static/)
  data/index.json
  data/decls.json
  data/projects/<Project>.json
```

`<Project>` is the second component of the module name
(`LeanPool.ABCExceptions.Section2` → `ABCExceptions`). Modules sitting directly
under `LeanPool/` (e.g. `LeanPool.Basic`) form a pseudo-project named after the
module ("Basic") with no registry card.

Relative bases from `p/<Project>/index.html`: exposition root `../..`,
doc-gen4 root `../../..`. doc-gen4 page for a non-private declaration
`Foo.bar` in module `LeanPool.A.B`: `<docs-root>/LeanPool/A/B.html#Foo.bar`.
GitHub source: `https://github.com/Vilin97/lean-pool/blob/main/<LeanPool/A/B.lean>#L<line>-L<endLine>`.

## `data/projects/<Project>.json` (shard)

```json
{"schema": 1,
 "project": "ABCExceptions",
 "title": "…",                 // from projects.yml; null for pseudo-projects
 "provenance": "human",        // "human" | "AI" | "mix" | null
 "stats": {"nodes": 235, "edges": 817, "maxDepth": 14, "avgDepth": 3.71,
           "kinds": {"lemma": 120, "theorem": 75, "def": 37, "structure": 3}},
 "modules": ["LeanPool.ABCExceptions.Section2", …],
 "layers": [40, 31, …],        // node count per layer, index = layer
 "decls": [ … ]}
```

`decls[i]` — the node with id `i` (ids are shard-local array indices):

```json
{"name": "Foo.aux",
 "full": "_private.…",         // only when it differs from name (⇒ no doc-gen page)
 "kind": "lemma",              // refined source keyword
 "module": 0,                  // index into modules
 "line": 435, "endLine": 446,
 "doc": "…",                   // optional
 "statement": "lemma aux (h : …) : …",  // ≤ 1200 chars, trimmed
 "private": true,              // optional
 "deps": [3, 17],              // node ids this declaration uses
 "ext": 127,
 "layer": 5,                   // x: longest-path layer, 0 = no intra-project deps
 "order": 12}                  // y: position within layer after crossing reduction
```

Depth definitions: `layer(n) = 0` if `n` has no intra-project deps, else
`1 + max(layer(dep))` (cycles collapsed via SCC condensation — every member of
an SCC shares the layer). `maxDepth = max layer`, `avgDepth = mean layer`
(2 decimals). `edges = Σ len(deps)`.

### Card metadata (schema 1.1, additive)

Each shard additionally carries the project's registry card (from
`LeanPool/projects.yml`, matched via `entry_module`'s last component;
`card` is `null` for pseudo-projects):

```json
"card": {"authors": ["…"], "license": "Apache-2.0", "branch": "extremal combinatorics",
         "summary": "…", "tags": ["…"], "msc": ["05D05"], "status": "verified",
         "source": {"title": "…", "authors": ["…"],
                    "doi": "…" | "arxiv": "…" | "url": "…",   // one or more; link priority doi > arxiv > url
                    "github_repo": "owner/repo"}},             // optional
"mainResults": [{"id": 12, "name": "BooleanIsoperimetry.harper_theorem",
                 "informal": "…"}]                             // id null if unresolved
```

`mainResults` is the union of the card's `main_declarations` and
`main_results` (informal text when available), resolved to node ids by
display name. Every resolved id's decl entry also gets `"main": true` —
frontends render these as visually distinguished ("starred") nodes.
Link recipes: `doi` → `https://doi.org/<doi>`, `arxiv` →
`https://arxiv.org/abs/<arxiv>`, `url` as-is, `github_repo` →
`https://github.com/<github_repo>`.

### Minimal-Lean-file fields (schema 1.2, additive)

The shard gains `commit` (the exact commit its data was extracted from —
raw-source fetches for the minimal-file builder pin to it) and a
`moduleData` array parallel to `modules`:

```json
"moduleData": [{"imports": ["Mathlib.Order.Basic", …],   // external imports
                "uses": [3, 7],                           // same-project imports (module indices)
                "contexts": [[20, "namespace Foo"], …]},  // (line, text) of replayable top-level
               …]                                         //   context commands
```

`modules` may list more entries than declarations reference: modules pulled
in only through `uses` (notation-/attribute-only files) are appended so
their contexts can be replayed.

Per-declaration additions:

```json
"stmtEnd": [436, 69],   // theorem/lemma only: statement/body boundary (line, col)
"tdeps": [124, 164],    // theorem/lemma only: statement-only dependencies ⊆ deps
"span": [15, 18],       // mutual members: the whole block's line span
"host": 12,             // generated decls: the source declaration containing them
"prefix": "open Classical in"  // bare `… in` prefix excluded from Lean's range
```

The minimal-file builder (`static/assets/minimal.js`, shared verbatim with
the node validation harness) follows `tdeps` through theorems (proofs become
`:= sorry`) and full `deps` elsewhere, replays module contexts in import
order, prunes `variable`/`attribute`/`export` contexts that reference
declarations outside the cone, and grows the cone with lemmas named in
`simp only [...]`-style tactic lists (invisible to term-level dependency
extraction). `build()` may return `{pending: [moduleIndex…]}` when that
closure needs sources not yet fetched; callers fetch and retry (≤ 4 rounds).

## `data/index.json`

```json
{"schema": 1, "commit": "abc123", "generated": "2026-07-21T12:00:00Z",
 "totals": {"projects": 126, "decls": 55600, "edges": 210000,
            "maxDepth": 41, "kinds": {"lemma": …}},
 "projects": [{"slug": "ABCExceptions", "title": "…", "provenance": "human",
               "nodes": 235, "edges": 817, "maxDepth": 14, "avgDepth": 3.71,
               "authors": ["…"], "license": "Apache-2.0",
               "branch": "analytic number theory", "mainResults": 3}, …]}
```

Sorted by slug. `totals.maxDepth` is the max over projects. The last four
fields are schema 1.1 additions (null / 0 for pseudo-projects); the landing
table shows branch and license columns and an authors line under the title.

## `data/decls.json` (all-declarations viewer index)

Compact arrays to keep the file small (~55K rows):

```json
{"schema": 1,
 "kinds": ["lemma", "theorem", …],
 "projects": ["ABCExceptions", …],       // slugs, same order as index.json
 "decls": [["Foo.aux", 0, 0, 12], …]}    // [name, kindIdx, projectIdx, declId]
```

`declId` indexes into that project's shard `decls`; the viewer links a row to
`p/<slug>/index.html#d<declId>`.

## Page shells

`templates/project.html` is a template with literal `${SLUG}` and `${TITLE}`
placeholders (Python `string.Template`); the generator instantiates it once
per project. `index.html`, `decls/index.html` and everything under `assets/`
are copied verbatim from `static/` and fetch their JSON at runtime.
URL fragments on project pages: `#d<id>` (select declaration `id`),
`#cone=<id>` (dependency-cone mode for declaration `id`).
