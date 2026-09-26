/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.BasicResults.Auerbach
public import LeanPool.SNumbers.BasicResults.SVD
public import LeanPool.SNumbers.BasicResults.Determinant
public import LeanPool.SNumbers.BasicResults.GarlingGordon
public import LeanPool.SNumbers.BasicResults.KadetsSnobar
public import LeanPool.SNumbers.BasicResults.LittleGrothendieck
public import LeanPool.SNumbers.BasicResults.John
public import LeanPool.SNumbers.BasicResults.JohnAux
public import LeanPool.SNumbers.BasicResults.Spectral.MonotoneConvergence
public import LeanPool.SNumbers.BasicResults.Spectral.Complexification
public import LeanPool.SNumbers.BasicResults.Spectral.Projection
public import LeanPool.SNumbers.BasicResults.Spectral.RealProjection
public import LeanPool.SNumbers.BasicResults.Spectral.Representation
public import LeanPool.SNumbers.BasicResults.Spectral.MultiplicationOperator

/-!
# Basic results

A small library of generic linear-algebra / functional-analysis results
that support the s-numbers framework:

* `BasicResults.Auerbach` — Auerbach's lemma (every finite-dimensional
  normed space over `ℝ` admits an Auerbach basis).
* `BasicResults.SVD` — the singular value decomposition of a (compact)
  Hilbert-space operator via the singular-value iteration, together with
  the **scalar factorisation** `SVD.exists_scalar_factorisation` that the
  s-numbers uniqueness theorem (`SNumbers.Uniqueness`) consumes, and the
  bound `(n+1)·aₙ(T₂T₁) ≤ ‖T₁‖_HS·‖T₂‖_HS` for a compact product
  (`SVD.mul_approximationNumber_le_of_factorization`).
  Following Pietsch, *Eigenvalues and s-numbers*, §2.11.
* `BasicResults.Determinant` — elementary determinant facts:
  `det T* = conj (det T)` and `‖det T‖ = ∏ₖ σₖ` for endomorphisms of a
  finite-dimensional inner product space, the determinant of an endomorphism
  diagonal in a basis, and the bordered determinant (column-operation Schur
  formula, over any commutative ring, no invertibility).
* `BasicResults.GarlingGordon` / `BasicResults.KadetsSnobar` — the
  Garling–Gordon and Kadets–Snobar projection theorems (`‖P‖ ≤ √n`), classical
  Banach-space geometry, both proved (over any `RCLike 𝕜`) by reduction to the
  John development: Kadets–Snobar via `John.exists_projection`, and Garling–Gordon
  (ε-form, `‖P‖ ≤ √n + ε`) via `John.exists_projection_ker`.
* `BasicResults.John` — the sharp `√n` engine above: John's ellipsoid theorem
  over any `RCLike 𝕜`, fully proved. The maximal-volume inscribed ellipsoid
  exists (`John.exists_maxVolume`), the John decomposition of identity
  (`John.john_decomposition`) is established by the classical variational
  argument, and Kadets–Snobar follows: `John.exists_projection` gives a
  projection onto any finite-dimensional subspace with `‖P‖ ≤ √(dim)`.
* `BasicResults.LittleGrothendieck` — sign averaging in an inner product space
  (`∑_j ‖w_j‖² ≤ M²` whenever every signed sum `∑_j ±w_j` has norm `≤ M`) and its
  two consequences: `∑_j ‖B e_j‖² ≤ ‖B‖²` for `B : ℓ_∞ → H` (little Grothendieck
  with constant one) and, dually, `∑_j ‖row_j‖² ≤ ‖A‖²` for `A : H → ℓ₁`. Both say
  that such operators are Hilbert–Schmidt; they drive the sharp Hilbert-number
  bound for `I : ℓ₁ → ℓ_∞` in `SNumbers.Examples.IdentityL1Linfty`.
* `BasicResults.JohnAux` — general-purpose ingredients for the above, each a
  Mathlib-upstream candidate: closedness — hence compactness — of convex hulls of
  compact sets in finite dimensions, the supporting-vector form of Hahn–Banach
  dominated by a seminorm on an inner product space, trace duality for
  endomorphisms, and the product bound
  `∏(1+aᵢ) ≥ 1 - 2∑aᵢ²` for `∑aᵢ = 0`.

## The `BasicResults.Spectral` subpackage

This is the spectral-theory input that extends `s`-number uniqueness from compact to **arbitrary
bounded** operators. It produces, for any `RCLike` field, the spectral projection of `S*S` with its
two operator-norm bounds (`SpectralRepresentation.exists_spectral_projection`), and the lower-bound
subspace `(★)` the uniqueness theorem consumes — all unconditional, with no extra hypotheses. The
pipeline:

* `MonotoneConvergence` — analytic core: strong-operator limits of antitone positive operators.
* `Complexification` — the complexification of a real inner product space (missing from Mathlib),
  the vehicle for the real and `RCLike` cases.
* `Projection` — the spectral projection over `ℂ` (continuous functional calculus of `S*S`), plus
  the commutation lemma `cfc_comm_of_comm`.
* `RealProjection` — the spectral projection over `ℝ`, by complexifying and restricting.
* `Representation` — the capstone: the uniform `RCLike` spectral projection (realify → complexify
  → lift) and the lower-bound subspace `(★)`.
* `MultiplicationOperator` — independent: the multiplication operator `M_f` on `L²`. The seed of an
  alternative (multiplication-form) route to the spectral theorem; **not** used by the current
  development.

Each module here (especially `Complexification`) is a candidate for upstreaming to Mathlib.
-/


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
