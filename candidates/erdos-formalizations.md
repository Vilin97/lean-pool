# Complete Lean formalizations of Erdős problems — a survey

*Compiled 2026-06-24 to scope a possible `LeanPool/ErdosProblems` import. This is a **findings document**, not a content import: it inventories every complete (`sorry`-free) Lean formalization of an Erdős problem that could be located publicly, with its licensing, size, Lean toolchain, and Lean-Pool importability. No proofs are imported here.*

## Summary

- **~100 distinct Erdős problems have a complete (`sorry`-free) Lean proof** somewhere public — plus 6 partial/conditional and 5 where the community wiki marks a Lean solution but only the *statement* is actually formalized.
- **41 are cleanly importable into Lean Pool today** (Apache-2.0 / MIT, self-contained on Mathlib, axiom-clean), with **3 more disputed** (sources conflict — verify first).
- **~56 are complete but blocked, almost entirely by licensing.** The single largest proof collection, [`plby/lean-proofs`](https://github.com/plby/lean-proofs) (**29 problems**, incl. the famous #728), ships with **no license**, as do most contributor gists and every erdosproblems.com forum post. **Relicensing `plby` alone would roughly double the importable set.**
- Sources are spread across **40+ repositories/gists** at Lean toolchains from **v4.13 to v4.32**. Lean Pool pins `v4.32.0-rc1`, so *every* import needs a version bump (mostly from v4.24–v4.31).
- The **DeepMind AlphaProof Nexus** paper (arXiv:2605.22763) contributes **9 `sorry`-free files** (problems 12, 26, 125, 138, 152, 741, 846) in the Apache-2.0 repo [`google-deepmind/alphaproof-nexus-results`](https://github.com/google-deepmind/alphaproof-nexus-results). (A quick fetch initially misread its license as CC BY-NC-ND; the Lean code is Apache-2.0, verified against the LICENSE file.)
- The **unit-distance problem (#90)** is now *solved in the negative and Lean-verified* (Alpöge), Apache-2.0 — though multi-file with external dependencies.
- Already reconciled with Lean Pool: **#1196 is already in the pool**; `jcpaik/erdos-tuza-valtr` and ~10 others are already on your candidate shortlist; import worktrees already exist for #137/#346/#367/#403.
- **57 formalization-ready targets** (§11): problems whose statement is already formalized and whose solution is known, but with **no Lean proof yet** — the prime targets for new formalization work.

## How this was compiled

Four indices were treated as complementary and cross-checked against each other (no single one is exhaustive):

1. **formal-conjectures `formal_proof` registry** — the `@[... formal_proof using ... at "URL"]` markers in [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures). The community's curated pointer to complete proofs: **76 problems**.
2. **teorth/erdosproblems "AI contributions" wiki** — flagged **28 additional** "Full solution (Lean)" problems not in the registry. Verifying each *corrected the wiki*: 5 are only statement-only and 4 are partial.
3. **DeepMind AlphaProof Nexus paper** (arXiv:2605.22763) and its results repo.
4. **GitHub-wide sweep** — `gh api search/code`, `gh search repos` (~120 repos triaged, shallow-cloned, and grepped for `sorry`/`admit`/`axiom`/`native_decide`). Surfaced #90, #684, `yuta0x89` (#514/#691/#990), `jarredbarber` (#728/#729), the named-theorem repos, and a long reject list (below).

Plus reconciliation with **Lean Pool's own candidate shortlist** (`candidates/shortlist.md`).

**Important caveat — erdosproblems.com is bot-blocked.** The site and its forum return HTTP 403 to automated fetches, so **forum-only proofs (#38, #303, #434, #1051, #610) could not be downloaded or verified directly** — they are recorded from the registry/wiki with that caveat. Coverage is therefore *GitHub-centric*: a proof posted only in a forum comment or a private channel may be missed. Where the static [`teorth/erdosproblems/data/problems.yaml`](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml) mirror helped, it tracks *statement* formalization (yes/no), not complete proofs.

A **"complete"** verdict means a source file with no `sorry`/`admit`/`proof_wanted` in the proof body. Where a file additionally declares custom `axiom`s (postulating e.g. the Prime Number Theorem) or uses `native_decide`, it is **flagged** — Lean Pool's axiom audit forbids axioms beyond `Classical.choice`/`propext`/`Quot.sound`, and forbids `native_decide` (which injects `Lean.ofReduceBool`).

## 1. Importable into Lean Pool (41, + 3 to verify)

Apache-2.0 or MIT, `sorry`-free, essentially self-contained on Mathlib, no extra axioms. Each still needs a **port to `v4.32.0-rc1`** and, for the ~30 formal-conjectures-derived files, handling of the `FormalConjectures.Util.ProblemImports` scaffolding (see §6).

| # | Best source | License | Lean | LOC | Notes |
|---:|---|---|---|---:|---|
| 12 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_12.parts.i.lean) | Apache-2.0 | v4.27.0 | 143 |  |
| 26 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_26.variants.tenenbaum.lean) | Apache-2.0 | v4.27.0 | 639 |  |
| 42 | [Shashi456/erdos-formalizations](https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P42/CompactCayley/Proof.lean) | Apache-2.0 | v4.27.0 | 14802 | Large machine-generated proof (~14.8k lines, Shashi456). Also Gusarich/erdos42 (native_decide+no-license). |
| 70 | [mo271/formal-conjectures](https://github.com/mo271/formal-conjectures/blob/c024db0fa3ac32c6dddcd6c28d7b0cd994dad580/FormalConjectures/ErdosProblems/70.lean#L126) | Apache-2.0 | v4.27.0 | 243 |  |
| 90 | [kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance) | Apache-2.0 | v4.31.0-rc2 | — | **The unit-distance problem — solved.** Alpöge's negative resolution (the O(1/log log n) bound fails); sorry-free, axiom-clean. Multi-file; deps on PrimeNumberTheoremAnd + TauCeti. |
| 100 | [theaustinhatfield/formal-conjectures](https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-100-piepmeyer/FormalConjectures/ErdosProblems/100.lean) | Apache-2.0 | v4.22.0 | 2103 |  |
| 125 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean) | Apache-2.0 | v4.27.0 | 264 |  |
| 138 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_138.variants.difference.lean) | Apache-2.0 | v4.27.0 | 226 |  |
| 152 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_152.lean) | Apache-2.0 | v4.27.0 | 500 |  |
| 198 | [mzhorvath1/formal-conjectures](https://github.com/mzhorvath1/formal-conjectures/blob/21f6780f84b406de468389571eb01717b8072f09/FormalConjectures/ErdosProblems/198.lean#L84) | Apache-2.0 | v4.27.0 | 100 |  |
| 233 | [mzhorvath1/formal-conjectures](https://github.com/mzhorvath1/formal-conjectures/blob/032848c62fdf4c422bb0ee6663dc8d009d456c2c/FormalConjectures/ErdosProblems/233.lean#L57) | Apache-2.0 | v4.27.0 | 75 |  |
| 263 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/c8cf651906abe91051cf835d4232ad5648412113/FormalConjectures/ErdosProblems/263.lean#L298) | Apache-2.0 | v4.22.0 | 365 |  |
| 264 | [VjekoKovac/erdosproblems](https://github.com/VjekoKovac/erdosproblems/blob/main/Erdos264.lean) | Apache-2.0 | v4.24.0 | 213 | Apache, sorry-free, but a **partial result** (negative answer to first half; Kovač–Tao). 213 lines. |
| 267 | [mo271/formal-conjectures](https://github.com/mo271/formal-conjectures/blob/2663234a28260853790aa5752d8d4550ff0ab1ca/FormalConjectures/ErdosProblems/267.lean#L56) | Apache-2.0 | v4.27.0 | 99 |  |
| 283 | [Shashi456/erdos-formalizations](https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P283/Proof_flat.lean) | Apache-2.0 | v4.27.0 | 11230 |  |
| 307 | [ElVec1o/erdos307](https://github.com/ElVec1o/erdos307/blob/v1.0.0/lean/Erdos307/Closed.lean) | MIT | (none) | 129 |  |
| 316 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/316.lean) | Apache-2.0 | v4.22.0 | 85 |  |
| 349 | [cepadugato/formal-conjectures](https://github.com/cepadugato/formal-conjectures/blob/23c629bc2347864782ce88f957a64d6567b978a1/FormalConjectures/ErdosProblems/349.lean#L87) | Apache-2.0 | v4.27.0 | 267 |  |
| 350 | [XC0R/formal-conjectures](https://github.com/XC0R/formal-conjectures/blob/ba788c9124b563bce98a3413d474b3a2731fd0af/FormalConjectures/ErdosProblems/350.lean#L226) | Apache-2.0 | v4.27.0 | 338 |  |
| 370 | [XC0R/formal-conjectures](https://github.com/XC0R/formal-conjectures/blob/f58dea7d2cc5c9da2e050ec80a73e838b54a6dd2/FormalConjectures/ErdosProblems/370.lean#L73) | Apache-2.0 | v4.27.0 | 178 |  |
| 379 | [teorth/analysis](https://github.com/teorth/analysis/blob/4f623b0f4cacdb967f1f8132db0becaee0f1fb3d/Analysis/Misc/erdos_379.lean#L90) | Apache-2.0 | v4.29.0-rc8 | 102 |  |
| 392 | [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Erdos392.lean) | Apache-2.0 | v4.31.0 | — | Apache but **not self-contained** — lives inside PrimeNumberTheoremAnd (analytic number theory library). |
| 397 | [XC0R/formal-conjectures](https://github.com/XC0R/formal-conjectures/blob/3c356a50a21bcbf3543f960b0c92d7fb26228cb6/FormalConjectures/ErdosProblems/397.lean#L147) | Apache-2.0 | v4.27.0 | 164 |  |
| 399 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/399.lean) | Apache-2.0 | v4.22.0 | 92 |  |
| 619 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b8c7a76f267c29eaa41d1212c211a920be8b05ea/FormalConjectures/ErdosProblems/619.lean#L6009) | Apache-2.0 | v4.22.0 | 6086 |  |
| 655 | [AlperTheKing/formal-conjectures](https://github.com/AlperTheKing/formal-conjectures/blob/4aaaf544b6ed0ef22580787a8d8a19e85dc49556/FormalConjectures/ErdosProblems/655.lean) | Apache-2.0 | v4.27.0 | 262 |  |
| 684 | [gotrevor/binomial-thresholds](https://github.com/gotrevor/binomial-thresholds) | Apache-2.0 | v4.31.0 | — | Apache, clean (0 sorry/axiom/native_decide). Good import candidate. |
| 741 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_741.parts.i.lean) | Apache-2.0 | v4.27.0 | 254 |  |
| 828 | [XC0R/formal-conjectures](https://github.com/XC0R/formal-conjectures/blob/03e00cf8d44098d0fb06e891fca30c29769df619/FormalConjectures/ErdosProblems/828.lean#L49) | Apache-2.0 | v4.27.0 | 153 |  |
| 846 | [gdm/alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_846.lean) | Apache-2.0 | v4.27.0 | 724 |  |
| 848 | [The-Obstacle-Is-The-Way/erdos-banger](https://github.com/The-Obstacle-Is-The-Way/erdos-banger/blob/1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5/formal/lean/Erdos/848.lean) | Apache-2.0 | (none) | 5455 | Apache, sorry-free, but proves only the **asymptotic** (∀N≥N₀) Sawhney version, and uses elevated maxHeartbeats (Lean Pool forbids). |
| 887 | [jarekkoch-hub/erdos887-lean](https://github.com/jarekkoch-hub/erdos887-lean) | MIT | ? | 14000 | MIT, sorry-free, 14k lines — large single-author AI artifact, **doubtful significance**. |
| 978 | [mo271/formal-conjectures](https://github.com/mo271/formal-conjectures/blob/3b5d6ac2555cd63b83d418c29ff040876be9dee0/FormalConjectures/ErdosProblems/978.lean#L64) | Apache-2.0 | v4.27.0 | 170 |  |
| 1043 | [XC0R/formal-conjectures](https://github.com/XC0R/formal-conjectures/blob/7db17471701f15b125d1c36bc1fa5bb9b702d6be/FormalConjectures/ErdosProblems/1043.lean#L214) | Apache-2.0 | v4.27.0 | 254 |  |
| 1052 | [mzhorvath1/formal-conjectures](https://github.com/mzhorvath1/formal-conjectures/blob/b70a2ddf5e55f743aac9d4f4a907786b39bc9807/FormalConjectures/ErdosProblems/1052.lean#L46) | Apache-2.0 | v4.27.0 | 103 |  |
| 1074 | [mzhorvath1/formal-conjectures](https://github.com/mzhorvath1/formal-conjectures/blob/3dec597bd1a73778760b761712a1fc5fb24bc5d7/FormalConjectures/ErdosProblems/1074.lean#L99) | Apache-2.0 | v4.27.0 | 143 |  |
| 1082 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/0aca4d71095301c0fd2dca32611b7addb2ea735c/FormalConjectures/ErdosProblems/1082.lean) | Apache-2.0 | v4.22.0 | 305 |  |
| 1084 | [Sanexxxx777/formal-conjectures](https://github.com/Sanexxxx777/formal-conjectures/blob/9e4f3845be122a8fa3190d38543ebdd0a6f25605/FormalConjectures/ErdosProblems/1084.lean#L232) | Apache-2.0 | v4.27.0 | 279 |  |
| 1097 | [mo271/formal-conjectures](https://github.com/mo271/formal-conjectures/blob/f13dd54b520cdf2136fdd3a04f0f9fa50e311358/FormalConjectures/ErdosProblems/1097.lean#L306) | Apache-2.0 | v4.27.0 | 413 |  |
| 1138 | [YanYablonovskiy/formal-conjectures](https://github.com/YanYablonovskiy/formal-conjectures/blob/7c134317104d3b98ecc751afbb79ec0adddf8e7c/FormalConjectures/ErdosProblems/1138a.lean#L496) | Apache-2.0 | v4.27.0 | 505 |  |
| 1196 | [math-inc/Erdos1196](https://github.com/math-inc/Erdos1196/blob/02fba13be7487cc51315f68d8fa7ef277633d3c8/PrimitiveSetsAboveX/FormalConjecturesErdos1196.lean) | Apache-2.0 | v4.30.0-rc1 | 175 | **Already in Lean Pool** (slug `erdos1196`, math-inc). |

**Disputed — agents/sources disagreed; verify before relying:**

| # | Best source | License | Lean | LOC | Notes |
|---:|---|---|---|---:|---|
| 306 | [Yuren-Tang/erdos-306](https://github.com/Yuren-Tang/erdos-306/blob/main/lean/RequestProject/Erdos306FormalConjectures.lean) | Apache-2.0 | v4.28.0 | 139 | **Disputed:** one agent found a sorry-free file, another found 35 sorry/admit hits elsewhere in the repo. Verify. |
| 346 | [KitaKen1/erdos346-ratio-limit-lean](https://raw.githubusercontent.com/KitaKen1/erdos346-ratio-limit-lean/main/346lean/LimitExistsVariant.lean) | Apache-2.0 | v4.31.0 | 7064 | **Disputed:** sorry-free but a *re-interpretation/variant*, not the problem as stated (KitaKen1). |
| 696 | [davidturturean/erdos-696](https://github.com/davidturturean/erdos-696/blob/4fa1bf2c6ff6f2e0c7024f814614c7455404fdd3/Erdos696/Main.lean) | Apache-2.0 | v4.28.0 | 153 | **Disputed:** headline file sorry-free per one agent; repo has 2 sorry per another. Verify. |

Notable caveats within this set: **#90** and **#392** are not single self-contained files (deps on PrimeNumberTheoremAnd / TauCeti); **#848** uses elevated `maxHeartbeats` (Lean Pool forbids); **#887** is a 14k-line single-author AI artifact of doubtful significance; **#42**'s best Apache source is ~14.8k lines of machine-generated proof term.

## 2. Complete but blocked (56) — overwhelmingly licensing

These have a verified `sorry`-free proof but cannot be imported as-is. The breakdown: **no license** = `plby/lean-proofs` (29), `Woett/Lean-files` (5), `yuta0x89/ErdosProblems` (4), `ebarschkis/ErdosProblem` (2), `jarredbarber` (#728/#729), `danielchin` (#16), `AllenGrahamHart` (#699), `b-mehta/unit-fractions` (#298/#299 — *also Lean 3*); **gist/forum, no license** = 12 (#38, #194, #258, #259, #268, #303, #427, #434, #997, #1051, …); **GPL-3.0** = `d0d1/singer-theorem-lean` (#30, incompatible).

| # | Best source | License | Lean | LOC | Notes |
|---:|---|---|---|---:|---|
| 16 | [danielchin/proofs](https://github.com/danielchin/proofs/blob/main/Proofs/ErdosProblems/Erdos16.lean) | none | v4.24.0 | 346 |  |
| 36 | [other](https://github.com/google-deepmind/formal-conjectures/pull/4153/commits/2ce2d6345d0fcf3b023fe35fde9a9a490b131a86) | none (gist/forum) | - | — |  |
| 38 | [forum](https://www.erdosproblems.com/forum/thread/38#post-6131) | none (gist/forum) | - | — |  |
| 56 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos56.lean) | none | (none) | 1351 |  |
| 189 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos189.lean) | none | (none) | 608 |  |
| 194 | [gist_raw](https://gist.githubusercontent.com/ster-oc/ffe9e4fa1b813111f40c0e417bbe8be0/raw/6f748a76e55d47e24ca319a9c00fd20ab79422bb/Erdos194.lean) | none (gist/forum) | - | 618 |  |
| 204 | [Woett/Lean-files](https://github.com/Woett/Lean-files/blob/main/ErdosProblem204.lean) | none | (none) | 948 |  |
| 205 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos205.lean) | none | v4.24.0 | 545 | plby; sorry-free but **conditional on PNT** via an explicit `nth_prime_asymp` axiom. |
| 224 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos224.lean) | none | v4.29.1 | 779 |  |
| 229 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos229.lean) | none | (none) | 1604 |  |
| 258 | [gist_raw](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https://gist.githubusercontent.com/ster-oc/2b7adcf9d753cf6e29d782f7374cc57e/raw/689a8483895cbe147634dfbf2d7b1db93a3b5b5f/Erdos258.lean) | none (gist/forum) | - | 45 |  |
| 259 | [gist_raw](https://gist.githubusercontent.com/ster-oc/c7429943f6b3a634797dc8b2a3b01f2d/raw/8c6b5b7f08021f0aed2312542dd2e9ee7beaa6d6/Erdos259.lean) | none (gist/forum) | - | 1013 |  |
| 268 | [gist_raw](https://gist.githubusercontent.com/madeve-unipi/62a8f68cdb4864b85b81a6752dcb0aa4/raw/5793aaa51089c25c37d8d63f60540367f6abe506/Erdos268.lean) | none (gist/forum) | - | 1298 |  |
| 275 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos275.lean) | none | (none) | 579 |  |
| 298 | [b-mehta/unit-fractions](https://github.com/b-mehta/unit-fractions/blob/master/src/final_results.lean) | none | (none) | 2324 |  |
| 299 | [b-mehta/unit-fractions](https://github.com/b-mehta/unit-fractions/blob/master/src/final_results.lean) | none | (none) | 2324 |  |
| 303 | [forum](https://www.erdosproblems.com/forum/thread/303) | none (gist/forum) | - | — |  |
| 331 | [Woett/Lean-files](https://github.com/Woett/Lean-files/blob/main/ErdosProblem%23331.lean) | none | (none) | 1 |  |
| 333 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos333.lean) | none | v4.30.0 | 1407 |  |
| 347 | [ebarschkis/ErdosProblem](https://github.com/ebarschkis/ErdosProblem/blob/main/Problem347/Formalization.lean) | none | (none) | 2181 |  |
| 355 | [Woett/Lean-files](https://github.com/Woett/Lean-files/blob/main/ErdosProblem355.lean) | none | (none) | 3836 |  |
| 401 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos401.lean) | none | v4.29.1 (Mathlib v | 1583 |  |
| 418 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos418.lean) | none | (none) | 561 |  |
| 427 | [gist_raw](https://gist.githubusercontent.com/JohnEdwardJennings/e2c6ef0daab55857b7cc9d340de7af84/raw/8ff97800e38582c71246a238e7541a9d69488cbd/Erdos427.lean) | none (gist/forum) | - | 92 |  |
| 434 | [forum](https://www.erdosproblems.com/forum/thread/434#post-4437) | none (gist/forum) | - | — |  |
| 457 | [Woett/Lean-files](https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean) | none | (none) | 343 |  |
| 488 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos488b.lean) | none | v4.24.0 | 45 |  |
| 493 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos493.lean) | none | v4.29.1 | 57 |  |
| 505 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/96cd54930d844e3655e6bb89b96b65516397dae9/src/v4.24.0/ErdosProblems/Erdos505.lean#L1153) | none | (none) | 1162 |  |
| 514 | [yuta0x89/ErdosProblems](https://github.com/yuta0x89/ErdosProblems/blob/main/Erdos514.lean) | none | ~v4.31 | 1598 |  |
| 541 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos541.lean) | none | (none) | 3073 |  |
| 645 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos645.lean) | none | (none) | 173 |  |
| 659 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/master/src/v4.24.0/ErdosProblems/Erdos659.lean) | none | v4.24.0 | 1932 |  |
| 691 | [yuta0x89/ErdosProblems](https://github.com/yuta0x89/ErdosProblems/blob/main/Erdos691.lean) | none | ~v4.31 | 4225 |  |
| 699 | [AllenGrahamHart/FormalConjectures-Bench](https://github.com/AllenGrahamHart/FormalConjectures-Bench/blob/482dacc4d9335240f26218cdc62032da3100392b/formalizations/erdos699/Erdos699Formalization.lean#L7679) | none | (none) | 7753 |  |
| 707 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos707.lean) | none | (none) | 6360 |  |
| 728 | [jarredbarber/erdos-728b](https://github.com/jarredbarber/erdos-728b) | none | v4.27.0 | 2906 | Aristotle/AI proof. plby/lean-proofs (no-license) and jarredbarber/erdos-728b (no-license). |
| 729 | [jarredbarber/erdos-729-google](https://github.com/jarredbarber/erdos-729-google) | none | v4.27.0 | — |  |
| 845 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos845.lean) | none | (none) | 3025 |  |
| 897 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) | none | (none) | 948 |  |
| 949 | empty | none (gist/forum) | - | — |  |
| 958 | [plby/lean-proofs](https://raw.githubusercontent.com/plby/lean-proofs/main/src/v4.24.0/ErdosProblems/Erdos958.lean) | none | v4.24.0 | 182 |  |
| 966 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos966.lean) | none | v4.29.1 (file head | 425 |  |
| 990 | [yuta0x89/ErdosProblems](https://github.com/yuta0x89/ErdosProblems/blob/main/Erdos990.lean) | none | ~v4.31 | 1982 |  |
| 997 | [gist_raw](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https://gist.githubusercontent.com/pitmonticone/016f2ed66b4cd1c4c4b9998095170e60/raw/b7dfc05c525ae385b5835f89f1ada721443e4305/Erdos997.lean) | none (gist/forum) | - | 45 |  |
| 1007 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1007.lean) | none | v4.29.1 (Mathlib v | 1101 |  |
| 1026 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1026.lean) | none | v4.29.1 (Mathlib v | 4634 |  |
| 1047 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1047.lean) | none | v4.30.0 | 1034 |  |
| 1048 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1048.lean) | none | v4.24.0 | 628 |  |
| 1051 | [forum](https://www.erdosproblems.com/forum/thread/1051) | none (gist/forum) | - | — |  |
| 1067 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1067.lean) | none | (none) | 2511 |  |
| 1071 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1071.lean) | none | (none) | 3080 |  |
| 1080 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1080.lean) | none | (none) | 1390 |  |
| 1090 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/master/src/latest/ErdosProblems/Erdos1090.lean) | none | v4.29.1 (mathlib v | 523 |  |
| 1102 | [Woett/Lean-files](https://github.com/Woett/Lean-files/blob/1e075c4f6e8a907b924647fa88238f978e941742/ErdosProblem1102PropertyP.lean) | none | (none) | 899 |  |
| 1209 | [ebarschkis/ErdosProblem](https://github.com/ebarschkis/ErdosProblem/blob/main/Problem1209/Formalization.lean) | none | (none) | 482 |  |

## 3. Partial, conditional, or statement-only (not counted as complete)

The community wiki marks all of these "(Lean)", but verification shows they are **not** complete proofs of the problem as posed:

- **Statement-only** (both theorems still `sorry`): #120, #326, #477, #948, #1089.
- **Partial / conditional** (`sorry`-free but only one direction, an asymptotic, or gated behind a postulated axiom): #387, #610, #635, #1141, #1148, #1197.

| # | Best source | License | Lean | LOC | Notes |
|---:|---|---|---|---:|---|
| 120 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/120.lean) | Apache-2.0 | v4.27.0 | 55 |  |
| 326 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/326.lean) | Apache-2.0 | unknown | 54 |  |
| 387 | [slavanaprienko/erdos-387](https://github.com/slavanaprienko/erdos-387) | none | v4.29.0 | — | sorry-free but postulates 2 axioms (PNT in AP / Siegel–Walfisz) → fails axiom audit. |
| 477 | [gdm/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/477.lean) | Apache-2.0 | unknown | 86 |  |
| 610 | [forum](https://www.ulam.ai/research/erdos610.lean) | none | unknown (standalon | 335 |  |
| 635 | [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos635Problem.lean) | none | v4.26.0 | 369 |  |
| 948 | [ryantuck/erdos-ai](https://raw.githubusercontent.com/ryantuck/erdos-ai/master/deepmind/948.lean) | Apache-2.0 | v4.28.0 | 53 |  |
| 1089 | [ryantuck/erdos-ai](https://github.com/ryantuck/erdos-ai/blob/main/deepmind/1089.lean) | none | v4.28.0 | 78 |  |
| 1141 | [yuta0x89/ErdosProblems](https://github.com/yuta0x89/ErdosProblems/blob/main/Erdos1141.lean) | none | ~v4.31 | 1629 | sorry-free but postulates 2 axioms (Pollack/Mertens) → fails axiom audit. |
| 1148 | [Jayyhk/erdos-lean](https://raw.githubusercontent.com/Jayyhk/erdos-lean/main/problems/1148/Erdos1148.lean) | none | v4.28.0 | 1480 |  |
| 1197 | [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1197.lean) | none | v4.29.1 (Mathlib v | 774 |  |

## 4. Source repositories

| Repository | License | Lean | # | Problems |
|---|---|---|---:|---|
| `plby/lean-proofs` | none | v4.29.1 | 29 | 56, 189, 205, 224, 229, 275, 333, 401, 418, 488, 493, 505, 541, 645, 659, 707, 845, 897 … |
| `google-deepmind/formal-conjectures` | Apache-2.0 | v4.22.0 | 8 | 120, 263, 316, 326, 399, 477, 619, 1082 |
| `google-deepmind/alphaproof-nexus-results` | Apache-2.0 | v4.27.0 | 7 | 12, 26, 125, 138, 152, 741, 846 |
| `gist_raw` | none (gist/forum) | - | 6 | 194, 258, 259, 268, 427, 997 |
| `Woett/Lean-files` | none | (none) | 5 | 204, 331, 355, 457, 1102 |
| `XC0R/formal-conjectures` | Apache-2.0 | v4.27.0 | 5 | 350, 370, 397, 828, 1043 |
| `forum` | none (gist/forum) | - | 5 | 38, 303, 434, 610, 1051 |
| `mo271/formal-conjectures` | Apache-2.0 | v4.27.0 | 4 | 70, 267, 978, 1097 |
| `mzhorvath1/formal-conjectures` | Apache-2.0 | v4.27.0 | 4 | 198, 233, 1052, 1074 |
| `yuta0x89/ErdosProblems` | none | ~v4.31 | 4 | 514, 691, 990, 1141 |
| `Shashi456/erdos-formalizations` | Apache-2.0 | v4.27.0 | 2 | 42, 283 |
| `b-mehta/unit-fractions` | none | (none) | 2 | 298, 299 |
| `ebarschkis/ErdosProblem` | none | (none) | 2 | 347, 1209 |
| `ryantuck/erdos-ai` | none | v4.28.0 | 2 | 948, 1089 |
| `AlexKontorovich/PrimeNumberTheoremAnd` | Apache-2.0 | v4.31.0 | 1 | 392 |
| `AllenGrahamHart/FormalConjectures-Bench` | none | (none) | 1 | 699 |
| `AlperTheKing/formal-conjectures` | Apache-2.0 | v4.27.0 | 1 | 655 |
| `ElVec1o/erdos307` | MIT | (none) | 1 | 307 |
| `Jayyhk/erdos-lean` | none | v4.28.0 | 1 | 1148 |
| `KitaKen1/erdos346-ratio-limit-lean` | Apache-2.0 | v4.31.0 | 1 | 346 |
| `Sanexxxx777/formal-conjectures` | Apache-2.0 | v4.27.0 | 1 | 1084 |
| `The-Obstacle-Is-The-Way/erdos-banger` | Apache-2.0 | (none) | 1 | 848 |
| `VjekoKovac/erdosproblems` | Apache-2.0 | v4.24.0 | 1 | 264 |
| `YanYablonovskiy/formal-conjectures` | Apache-2.0 | v4.27.0 | 1 | 1138 |
| `Yuren-Tang/erdos-306` | Apache-2.0 | v4.28.0 | 1 | 306 |
| `cepadugato/formal-conjectures` | Apache-2.0 | v4.27.0 | 1 | 349 |
| `danielchin/proofs` | none | v4.24.0 | 1 | 16 |
| `davidturturean/erdos-696` | Apache-2.0 | v4.28.0 | 1 | 696 |
| `empty` | none (gist/forum) | - | 1 | 949 |
| `gotrevor/binomial-thresholds` | Apache-2.0 | v4.31.0 | 1 | 684 |
| `jarekkoch-hub/erdos887-lean` | MIT | ? | 1 | 887 |
| `jarredbarber/erdos-728b` | none | v4.27.0 | 1 | 728 |
| `jarredbarber/erdos-729-google` | none | v4.27.0 | 1 | 729 |
| `kim-em/erdos-unit-distance` | Apache-2.0 | v4.31.0-rc2 | 1 | 90 |
| `math-inc/Erdos1196` | Apache-2.0 | v4.30.0-rc1 | 1 | 1196 |
| `other` | none (gist/forum) | - | 1 | 36 |
| `rjwalters/lean-genius` | none | v4.26.0 | 1 | 635 |
| `slavanaprienko/erdos-387` | none | v4.29.0 | 1 | 387 |
| `teorth/analysis` | Apache-2.0 | v4.29.0-rc8 | 1 | 379 |
| `theaustinhatfield/formal-conjectures` | Apache-2.0 | v4.22.0 | 1 | 100 |

## 5. Licensing analysis

Of the ~100 complete formalizations: **44 are permissive** (42 Apache-2.0 + 2 MIT) and **~56 are blocked** (44 no-license + 12 gist/forum, plus GPL/CC0 outliers). Lean Pool requires Apache-2.0 or MIT.

- **The `plby/lean-proofs` lever.** It is by far the largest single proof collection (29 problems, all the headline AI solves incl. **#728**), and it has **no LICENSE file** → all-rights-reserved → unusable. A single upstream relicensing to Apache/MIT would unlock ~29 problems. Most are also available *only* via plby, so this is the highest-value action to expand coverage.
- **Gists and forum posts** carry no license by default — every gist-hosted proof (#194, #259, #397-alt, #427, …) and forum proof (#38, #303, #434, #1051) is blocked unless the author states a license.
- **GPL-3.0** (`d0d1/singer-theorem-lean`, #30) and **CC0** are outside Lean Pool's Apache/MIT allowlist. (The CC0 repo `Suro-One/...Erdos-Straus_proof` is in any case bogus — see §9.)

## 6. Lean version spread & porting implications

Toolchains range **v4.13.0-rc3 → v4.32.0-rc1**; Lean Pool targets `v4.32.0-rc1`, so every file needs a bump:
- formal-conjectures forks: mostly **v4.27.0** (upstream **v4.22.0** for older google-deepmind/theaustinhatfield files).
- `plby/lean-proofs`: **v4.24.0** and **v4.29.1** (path-versioned).
- DeepMind `alphaproof-nexus-results`: **v4.27.0**.
- standalone repos: **v4.24 – v4.31**.

About **30 importable files import `FormalConjectures.Util.ProblemImports`**, which provides the `answer`/`@[category ...]`/`formal_proof` macros and does a whole-`import Mathlib`. Vendoring that helper library wholesale would trip Lean Pool's header linter and pull all of Mathlib; a small local shim (a no-op `@[category]` attribute + `answer` notation + targeted Mathlib imports) keeps the statements verbatim while staying gate-clean.

## 7. Provenance

The bulk of recent solves are **AI-generated or AI-assisted** — Aristotle (Harmonic), the DeepMind prover agent / AlphaProof Nexus, GPT-5.x, Claude (Opus/Code/Fable), Gemini 3, Seed Prover, AlphaProof, AlphaEvolve, Aletheia. The **DeepMind AlphaProof Nexus** paper is the largest single coordinated batch (9 files, problems 12/26/125/138/152/741/846). Lean Pool already pools AI-generated projects, so provenance is not a blocker, but it should be recorded per-project (and several proofs are *human* — e.g. Bloom–Mehta unit fractions, Kovač–Tao #264, the named-theorem repos).

## 8. Reconciliation with Lean Pool

- **Already in the pool:** #1196 (`erdos1196`, math-inc) and `erdos-tuza-valtr` (`jcpaik`).
- **Already on `candidates/shortlist.md`:** `logical-intelligence/erdos-unit-distance` (a *different*, conditional unit-distance result from kim-em's #90 disproof), `scottdhughes/erdos137`/`erdos367`/`erdos942`, `KitaKen1/erdos346-ratio-limit-lean`, `gotrevor/erdos-403`, `d0d1/singer` (#30), `YuanheZ/*`, `Jayyhk/erdos-lean`, `Woett/ChatGPT-s-note-on-Erdos451`, `mitchell-horner/ErdosStone…`.
- **Active import worktrees already exist** for #137, #346, #367, #403.
- **Discrepancy worth a per-file check:** the GitHub sweep flagged `scottdhughes/erdos137`/`erdos367`/`erdos942` and `gotrevor/erdos-403` as containing `sorry`/`native_decide`, which conflicts with their "candidate" status on the shortlist. Likely these prove a *conditional* statement (postulated bound) with the conditional part as a hypothesis/axiom — worth confirming before import.

## 9. Notable specifics

- **#90, the unit-distance problem — solved.** Alpöge's 2026 one-page disproof of the uniform-constant form is formalized in [`kim-em/erdos-unit-distance`](https://github.com/kim-em/erdos-unit-distance) (Apache-2.0, `sorry`-free, axiom-clean; erdosproblems.com/90 itself states it was "verified in Lean"). Multi-file; depends on PrimeNumberTheoremAnd + TauCeti.
- **DeepMind AlphaProof Nexus (arXiv:2605.22763):** 9 sorry-free Erdős files in `google-deepmind/alphaproof-nexus-results` (Apache-2.0, v4.27.0). The repo also contains 44 OEIS-conjecture proofs and other results (algebraic geometry, graphs, optimization, quantum optics) — out of scope here.
- **#728** — the much-publicised first autonomous AI resolution (Aristotle). Public Lean sources are **`plby/lean-proofs` (no license)** and **`jarredbarber/erdos-728b` (no license)** — so currently *not* importable.
- **Named-theorem repos** (classical Erdős theorems, not numbered problems): `mitchell-horner/ErdosStoneSimonovitsKovariSosTuran` (Erdős–Stone–Simonovits + Kővári–Sós–Turán, Apache, fully clean — strong fit), `jcpaik/erdos-tuza-valtr`, `Mahesh-Ramani/erdos-turan-sidon`.
- **Rejected as bogus:** `Suro-One/auro-zera_Erdos-Straus_proof` (CC0) claims to prove the *open* Erdős–Straus conjecture — its hard case is discharged by a postulated `axiom es_witness_exists` (an axiom-as-`sorry`), and its companion Goldbach file does not even compile (`omega` cannot close the "unreachable" fallbacks). Do not import.

## 10. Coverage caveats

- **erdosproblems.com / forum are bot-blocked** → forum-only proofs are recorded but not downloaded/verified; a few may be mis-stated.
- **Very recent solves** (June 2026) may not yet be indexed by GitHub code search.
- **`neelsomani/gpt-erdos`** (~700 candidate `.lean` files) is a *benchmark of mostly-failing attempts* (its own README documents subtle errors / hidden constraints); it is excluded except where a proof was independently verified.
- The numbers are a **lower bound on what exists** but a careful, cross-checked one; the per-problem verdicts in §§1–3 reflect direct file inspection except for the bot-blocked forum entries.

## 11. Formalization-ready targets — statement formalized, solution known, proof not yet in Lean

The complement of the inventory above: **57 problems** (list supplied by the maintainer from erdosproblems.com) that satisfy all three of —
1. the **statement is formalized** (all 57 have a `FormalConjectures/ErdosProblems/<n>.lean` file in [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures), confirmed), and
2. the **informal solution is known** (per erdosproblems.com), and
3. **no Lean proof exists yet.**

These are the highest-value formalization targets: the hard "is it true and how" question is already answered, the formal statement already exists, and a Lean proof would be a genuinely new contribution. Verified against this survey — **none of the 57 overlaps any complete, partial, or statement-only entry in §§1–3** (consistent with "not yet formalized"). Each links to its erdosproblems.com page; the formal statement is at `FormalConjectures/ErdosProblems/<n>.lean`.

**Proved (38).** [4](https://www.erdosproblems.com/4), [6](https://www.erdosproblems.com/6), [13](https://www.erdosproblems.com/13), [22](https://www.erdosproblems.com/22), [48](https://www.erdosproblems.com/48), [67](https://www.erdosproblems.com/67), [69](https://www.erdosproblems.com/69), [109](https://www.erdosproblems.com/109), [139](https://www.erdosproblems.com/139), [219](https://www.erdosproblems.com/219), [228](https://www.erdosproblems.com/228), [239](https://www.erdosproblems.com/239), [245](https://www.erdosproblems.com/245), [248](https://www.erdosproblems.com/248), [250](https://www.erdosproblems.com/250), [277](https://www.erdosproblems.com/277), [285](https://www.erdosproblems.com/285), [358](https://www.erdosproblems.com/358), [402](https://www.erdosproblems.com/402), [480](https://www.erdosproblems.com/480), [494](https://www.erdosproblems.com/494), [516](https://www.erdosproblems.com/516), [590](https://www.erdosproblems.com/590), [591](https://www.erdosproblems.com/591), [594](https://www.erdosproblems.com/594), [599](https://www.erdosproblems.com/599), [697](https://www.erdosproblems.com/697), [755](https://www.erdosproblems.com/755), [822](https://www.erdosproblems.com/822), [825](https://www.erdosproblems.com/825), [851](https://www.erdosproblems.com/851), [899](https://www.erdosproblems.com/899), [937](https://www.erdosproblems.com/937), [946](https://www.erdosproblems.com/946), [1064](https://www.erdosproblems.com/1064), [1096](https://www.erdosproblems.com/1096), [1105](https://www.erdosproblems.com/1105), [1214](https://www.erdosproblems.com/1214)

**Disproved (14).** [43](https://www.erdosproblems.com/43), [92](https://www.erdosproblems.com/92), [253](https://www.erdosproblems.com/253), [266](https://www.erdosproblems.com/266), [442](https://www.erdosproblems.com/442), [448](https://www.erdosproblems.com/448), [615](https://www.erdosproblems.com/615), [705](https://www.erdosproblems.com/705), [847](https://www.erdosproblems.com/847), [884](https://www.erdosproblems.com/884), [965](https://www.erdosproblems.com/965), [1077](https://www.erdosproblems.com/1077), [1092](https://www.erdosproblems.com/1092), [1128](https://www.erdosproblems.com/1128)

**Otherwise solved (5).** [318](https://www.erdosproblems.com/318), [587](https://www.erdosproblems.com/587), [633](https://www.erdosproblems.com/633), [868](https://www.erdosproblems.com/868), [888](https://www.erdosproblems.com/888)

*(Caveat: erdosproblems.com is bot-blocked, so the "solution known / not yet formalized" status here is taken as given from the maintainer's list rather than re-scraped; it is a point-in-time snapshot and a fresh Lean proof for any of these may already be in flight.)*

## Appendix A — repos checked and rejected

From the GitHub sweep (had `sorry`/`admit`, `native_decide`-dominated "computational checks", AI-scaffold/reinterpretation, or no Lean theorem): `Jayyhk/erdos-lean` (7 sorry), `scottdhughes/erdos942`/`erdos367`/`erdos137` (sorry + native_decide), `gotrevor/erdos-403` (4 sorry), `Yuren-Tang/erdos-306` (35 sorry/admit), `davidturturean/erdos-696` (2 sorry), `lyfar/egrs75-lean` (93 sorry), `selfreferencing/erdos-86-lean` (206 sorry), `sushaan-k/erdos-straus-lean` (52 sorry), `samlavery/1135` (61 sorry), `fbundle/erdos90` (13 sorry), `Cuuper22/Erdos` (16 sorry), `KitaKen1/erdos1038-…`/`erdos176-…` and `HKUST-AARON/Erdos-Problem-1038` (native_decide-dominated, hundreds of files), assorted KitaKen1 "reinterpretation" repos, and several empty/no-Lean repos. AI-generated but gate-blocked (no license and/or axioms/native_decide): `jarredbarber/erdos-728b` & `erdos-729-google` (no license), `slavanaprienko/erdos-387` (2 axioms), `Gusarich/erdos42` (native_decide), `jarekkoch-hub/erdos887-lean` (MIT but doubtful significance).

## Appendix B — reproducibility

Built from: the formal-conjectures `formal_proof` markers (depth-1 clone, 2026-06-24), the teorth/erdosproblems wiki, arXiv:2605.22763, and ~120 GitHub repos triaged via `gh api search/code`. The 28 wiki-extras and the standalone repos were verified by a 33-agent discovery workflow (license via `gh api repos/{o}/{r}/license`, toolchain via `lean-toolchain` at the referenced ref, completeness via `sorry`/`axiom` grep on the fetched source). Intermediate data and scripts live in this session's scratchpad (not committed). Counts are point-in-time and will drift as new solves land.
