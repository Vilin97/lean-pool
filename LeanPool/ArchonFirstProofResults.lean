/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof4
import LeanPool.ArchonFirstProofResults.FirstProof6

/-!
# Archon-FirstProof-Results

Source: url:https://github.com/frenzymath/Archon-FirstProof-Results
Authors: FrenzyMath
Status: verified
Main declarations: `Problem4.harmonic_mean_inequality_full`, `Problem6.exists_eps_light_subset`
Tags: polynomials, analysis, combinatorics, linear-algebra, graph-theory
-/

/-!
## Mathematical overview

This project collects two self-contained Lean 4 formalizations from the
*FirstProof* problem set.

* **Problem 4** (`LeanPool.ArchonFirstProofResults.FirstProof4`). For monic
  real-rooted polynomials `p`, `q` of degree `n ≥ 2`, the finite additive
  convolution `p ⊞[n] q` and the functional
  `Φₙ(p) = ∑ᵢ (∑_{j ≠ i} 1 / (rᵢ - rⱼ))²` over the ordered roots satisfy the
  harmonic-mean inequality `1 / Φₙ(p ⊞[n] q) ≥ 1 / Φₙ(p) + 1 / Φₙ(q)`
  (`Problem4.harmonic_mean_inequality_full`).

* **Problem 6** (`LeanPool.ArchonFirstProofResults.FirstProof6`). Every simple
  graph `G = (V, E)` contains, for each `ε ∈ (0, 1]`, an `ε`-light vertex subset
  `S` — meaning `ε • L - L_S` is positive semidefinite for the graph Laplacian
  `L` and the induced-subgraph Laplacian `L_S` — with `(ε / 256) * |V| ≤ |S|`
  (`Problem6.exists_eps_light_subset`), via the Batson–Spielman–Srivastava
  barrier method.

## Provenance

Imported from <https://github.com/frenzymath/Archon-FirstProof-Results>;
generated autonomously by the Archon system (built on Claude Code) developed by
FrenzyMath, the AI4M team at BICMR, Peking University. Upstream contains no
`sorry`s. Ported from Lean v4.28.0 / Mathlib v4.28.0 to Lean Pool's
v4.30.0-rc2.
-/
