/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Main
import LeanPool.BollobasNikiforov.M.Main
import LeanPool.BollobasNikiforov.Spectral.Gram
import LeanPool.BollobasNikiforov.Spectral.Conic

/-!
# The Bollobás–Nikiforov conjecture

Source: url:https://github.com/ShengtongZhang-alt/BN
Authors: Gabriel Coutinho, Yinchen Liu, Thomás Jung Spier, Quanyu Tang, Shengtong Zhang
Status: verified
Main declarations: `BollobasNikiforov.lambda1_sq_add_lambda2_sq_le`
Tags: spectral-graph-theory, clique-number, completely-positive-matrices, motzkin-straus
MSC: 05C50, 15B48, 05C35, 15A18
-/

/-!
## Mathematical overview

Bollobás and Nikiforov (2007) conjectured that every noncomplete finite simple graph `G` on at
least two vertices satisfies `λ₁(G)² + λ₂(G)² ≤ 2 (1 - 1/ω(G)) |E(G)|`, where `λ₁ ≥ λ₂` are the
two largest eigenvalues of the adjacency matrix and `ω(G)` is the clique number. The case
`λ₁² ≤ 2 (1 - 1/ω) |E|` is Nikiforov's 2002 strengthening of Wilf's bound; the two-eigenvalue
form was known for weakly perfect, triangle-free and regular graphs, and with weaker constants
in general. `BollobasNikiforov.lambda1_sq_add_lambda2_sq_le` proves it in full, with the
eigenvalues taken from Mathlib's `Matrix.IsHermitian.eigenvalues₀` and `ω(G)` from
`SimpleGraph.cliqueNum`.

The proof is assembled from three results that are of independent interest:

* `LeanPool.BollobasNikiforov.Spectral.Weighted`: `BollobasNikiforov.weighted`, the weighted
  form. For a real symmetric, entrywise nonnegative, zero-diagonal matrix `B` supported on the
  edges of `G`, the sum `F(B)` of the squares of its two largest positive eigenvalues is at
  most `(1 - 1/ω(G)) ‖B‖_F²`. Its proof restricts `B` to the span of a nonnegative Perron
  eigenvector and a second eigenvector (`Spectral.Perron`, `Spectral.Interlace`), then bounds
  the resulting rank-two Gram form.
* `LeanPool.BollobasNikiforov.M.Main`: `BollobasNikiforov.matrix_theorem`. For planar vectors
  `z₁, …, zₙ` in a closed half-plane through the origin with Gram matrix `X`, the matrix
  `X ∘ X + ∑_{i<j, X_ij<0} X_ij² (eᵢ - eⱼ)(eᵢ - eⱼ)ᵀ` is completely positive. The argument
  orders the vectors by angle, eliminates the left vectors one at a time (`M.Elim`), identifies
  the Schur complement as a weighted Laplacian plus a matrix with an explicit three-column
  nonnegative factorization (`M.Schur`, `Kernel`), and uses total nonnegativity of the
  truncated-square and convex kernels via Cauchy–Binet (`TN`).
* `LeanPool.BollobasNikiforov.Spectral.Gram`: `BollobasNikiforov.gram_le`, the rank-two Gram
  inequality `∑ (A_G)_ij (X_ij)₊² ≤ (1 - 1/ω(G)) ‖X‖_F²` for positive semidefinite `X` of rank
  at most two, obtained from the matrix theorem, the closedness of the completely positive cone
  (`CP.Closed`) and the Motzkin–Straus inequality in completely positive form (`MS.Basic`).
  `LeanPool.BollobasNikiforov.Spectral.Conic` derives `BollobasNikiforov.chiVec3_eq_cliqueNum`,
  which identifies the rank-two conic parameter of Coutinho, Spier and Zhang with `ω(G)` and
  settles their Conjectures 2 and 3.

## Provenance

Imported from <https://github.com/ShengtongZhang-alt/BN> at commit
`edb5259dfd055ea31b4c46ac9ea4d33a758c2b99` (Apache-2.0), the repository registered as
Palomar entry `PALOMAR-2026-09-07-000002`. The mathematics is due to Gabriel Coutinho,
Yinchen Liu, Thomás Jung Spier, Quanyu Tang and Shengtong Zhang, with ideation and the
manuscript `docs/sol.tex` generated with GPT-6 Astra; the Lean development was written by
Grok 4.6 agents in Cursor under the direction of Shengtong Zhang, who is the responsible
maintainer, so the provenance is `AI`.

The port renames the namespace `BN` to `BollobasNikiforov`, moves from Mathlib v4.33.0-rc1 to
the pool's v4.34.0-rc1, and removes every `set_option` (twelve `linter.unusedSectionVars`
suppressions and one `maxHeartbeats` override). Unused typeclass hypotheses are dropped from
statements, which only generalizes them: `weighted` and `gram_le` no longer assume
`DecidableRel G.Adj` or `DecidableEq V`, and the positive-semidefiniteness lemmas assume
`Finite` rather than `Fintype`, following Mathlib's finitely-supported definition of
`Matrix.PosSemidef`. Flexible `simp` calls were replaced by `simp only`, deprecated names
updated, and docstrings added. Two modules that nothing imported and that duplicated
`Spectral.Gram` and `M.Schur` declaration for declaration (`Spectral.Variational`, `CP.Pair`)
were not imported. Compile-time repairs: `rank_smul_le` now goes through
`Matrix.rank_mul_le_right`, `det2_nonneg_of_min_snd` proves its cases with explicit
monotonicity lemmas instead of `nlinarith`, the three-by-three minor in
`truncatedSquare_det_three_mixed` is stated in factored form before `positivity`, and two
`nlinarith` calls and a `split_ifs <;> simp_all` were replaced by `linarith` and `ite_and`.
No statement was weakened.
-/
