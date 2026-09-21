/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirceMul


/-!
# Connections between frame blocks

`EuclideanJordan/FramePeirceMul.lean` gives the multiplication table of a Jordan frame's blocks.  This file
proves the two identities that turn that table into an *algebra*, and they are the engine of
Jacobson coordinatization.

## The two identities

**(1) An off-diagonal block element squares to a multiple of `pᵢ + pⱼ`.**
`frameBlockRaw_mul_self_eq` already gives `x ∘ x = a • pᵢ + b • pⱼ` for `x ∈ V_{ij}`.  Here
`a = b` (`frameBlockRaw_sq_coeff_eq`), so the square is a multiple of the *idempotent*
`pᵢ + pⱼ` and its coefficient is a quadratic form on the block (`exists_sq_smul`,
`sq_eq_inner_smul`).

★ **The proof is power associativity, not the trace form.**  Computing `x⁴` as `x² ∘ x²` and as
`x ∘ (x ∘ x²)` — the same element, by `EuclideanJordan/PowerAssoc.lean`'s `jpow_mul_jpow` — gives
`a² = a(a+b)/2` and `b² = b(a+b)/2` after pairing against `pᵢ` and `pⱼ`.  Adding those,
`a² + b² = (a+b)²/2 = 2ab`, so `(a - b)² = 0`.  The inner product enters only to *read off*
those two scalar equations from an equation between elements; the identity `a = b` itself is
algebraic.

**(2) `x ∘ (x ∘ y) = (a/4) • y` for `x ∈ V_{ij}` and `y ∈ V_{jk}`** (`block_sq_act`).  So `2 L_x`
restricted to `V_{jk}` squares to the scalar `a`.

★ **The plain Jordan identity gives nothing here.**  Both sides of `x ∘ (x² ∘ y) = x² ∘ (x ∘ y)`
reduce to `½ a • (x ∘ y)` using only the eigenvalue rules, so it is satisfied for *any* value of
`x ∘ (x ∘ y)`.  What works is the fully **linearised** Jordan identity — Mathlib's
`two_nsmul_lie_lmul_lmul_add_add_eq_zero`, restated pointwise here as `lin_jordan` — at
`(x, x, y)`, evaluated at `pⱼ`.  Six terms; `x ∘ y ∈ V_{ik}` is annihilated by `pⱼ`, `pⱼ` halves
`x` and `y`, and what survives is `-(x ∘ (x ∘ y)) + (a/4) • y = 0`.

## Connectors

A **connector** on `(i, j)` is a `c ∈ V_{ij}` with `c ∘ c = pᵢ + pⱼ`.  A nonzero block has one
(`exists_isConnector`: normalise by `a^{-1/2}`), and identity (2) at `a = 1` makes
`y ↦ 2 (c ∘ y)` an involution, hence a linear equivalence `V_{jk} ≃ V_{ik}` (`connEquiv`).  So
connected blocks have the same dimension, connectivity is transitive, and a block is nonzero
exactly when it carries a connector.

The **composition law** `block_mul_sq` says the coefficients multiply: if `x ∘ x = a • (pᵢ + pⱼ)`
and `y ∘ y = b • (pⱼ + p_k)` then `(2 (x ∘ y)) ∘ (2 (x ∘ y)) = (ab) • (pᵢ + p_k)`.  It follows
from (2) by pairing, once `⟪pᵢ, pᵢ⟫ = ⟪pⱼ, pⱼ⟫`.  ★ That identification is **not** unconditional:
`inner_p_eq_of_sq` gets it from (1) — the two pairings of `x ∘ x` both return `½‖x‖²`, so
`a τᵢ = a τⱼ` — and then needs `a ≠ 0` to cancel.  `V_{ij} = 0` really does leave `τᵢ` and `τⱼ`
unrelated, and `block_mul_sq` disposes of that case separately rather than through the
identification.

## Scope

★ `rank J = n` is **not** available and nothing here is a step towards it; a `JordanFrame J n` is
carried as data and its cardinality bounds the rank from below, nothing more.

★ Nothing here says a frame *is* connected.  Connectors are hypotheses everywhere they appear.
The statement "a simple `J` has every block nonzero" is **not proved anywhere in this
library**, which has no notion of a Jordan ideal to state simplicity with.
-/

noncomputable section

namespace EuclideanJordan

open EuclideanJordanAlgebra

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]
variable {n : ℕ}

/-! ## The linearised Jordan identity -/

/-- **The fully linearised Jordan identity, evaluated at a point.**

Mathlib's `two_nsmul_lie_lmul_lmul_add_add_eq_zero` states
`2 • (⁅L a, L (b∘c)⁆ + ⁅L b, L (c∘a)⁆ + ⁅L c, L (a∘b)⁆) = 0` in `AddMonoid.End J`; this is that
equation applied to `w`, with the `2 •` divided out (legitimate because `J` is a real vector
space). -/
theorem lin_jordan (a b c w : J) :
    (a * ((b * c) * w) - (b * c) * (a * w))
      + (b * ((c * a) * w) - (c * a) * (b * w))
      + (c * ((a * b) * w) - (a * b) * (c * w)) = 0 := by
  have H := two_nsmul_lie_lmul_lmul_add_add_eq_zero (A := J) a b c
  have H' := DFunLike.congr_fun H w
  simp only [Ring.lie_def, AddMonoid.End.mulLeft] at H'
  have h2 : (2 : ℕ) • ((a * (b * c * w) - b * c * (a * w)) + (b * (c * a * w) - c * a * (b * w)) +
      (c * (a * b * w) - a * b * (c * w))) = 0 := H'
  have h3 : ((2 : ℕ) : ℝ) • ((a * (b * c * w) - b * c * (a * w)) +
      (b * (c * a * w) - c * a * (b * w)) + (c * (a * b * w) - a * b * (c * w))) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]; exact h2
  rcases smul_eq_zero.mp h3 with h | h
  · norm_num at h
  · exact h

/-! ## The frame in the inner product -/

/-- Distinct frame members are orthogonal in the inner product, not merely in the algebra:
`⟪pᵢ, pⱼ⟫ = ⟪pᵢ ∘ pⱼ, 1⟫ = 0` by `EuclideanJordan/Class.lean`'s `inner_mul_one`. -/
theorem inner_p_p_of_ne (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) :
    (inner ℝ (F.p i) (F.p j) : ℝ) = 0 := by
  rw [← inner_mul_one (F.p i) (F.p j), F.orthIdem.orth i j hij, inner_zero_left]

/-- `⟪pᵢ, pᵢ⟫ > 0` — the frame members are nonzero and the inner product is definite. -/
theorem inner_p_self_pos (F : JordanFrame J n) (i : Fin n) :
    0 < (inner ℝ (F.p i) (F.p i) : ℝ) :=
  real_inner_self_pos.mpr (F.p_ne_zero i)

/-- Pairing an element of `V_{ij}` against `pᵢ`: `⟪x ∘ x, pᵢ⟫ = ½‖x‖²`. -/
theorem inner_sq_p_of_mem (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) :
    (inner ℝ (x * x) (F.p i) : ℝ) = (2 : ℝ)⁻¹ * (inner ℝ x x : ℝ) := by
  rw [inner_assoc x x (F.p i), _root_.mul_comm x (F.p i),
    frameBlockRaw_mul_left_half F hij hx, real_inner_smul_right]

/-! ## The square of an off-diagonal element

★ `EuclideanJordan/FramePeirceMul.lean`'s `frameBlockRaw_mul_self_eq` gives `x ∘ x = a • pᵢ + b • pⱼ`.
This section proves `a = b`, so that the square is a multiple of the *idempotent* `pᵢ + pⱼ`
and the coefficient is a quadratic form.  The argument is power associativity, not the trace
form: `x⁴` computed as `x² ∘ x²` and as `x ∘ (x ∘ x²)` gives `a² = a(a+b)/2` and
`b² = b(a+b)/2`, whence `(a - b)² = 0`. -/

section Square

variable [FiniteDimensional ℝ J]

omit [FiniteDimensional ℝ J] in
/-- `x⁴ = x² ∘ x²` and `x⁴ = x ∘ (x ∘ x²)` agree — `EuclideanJordan/PowerAssoc.lean`'s `jpow_mul_jpow` at
`(1, 1)`, unfolded. -/
theorem sq_mul_sq_eq (x : J) : (x * x) * (x * x) = x * (x * (x * x)) := by
  have h := jpow_mul_jpow x 1 1
  simpa using h

omit [FiniteDimensional ℝ J] in
/-- **The two coefficients of `x ∘ x` on `V_{ij}` are equal.** -/
theorem frameBlockRaw_sq_coeff_eq (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) {a b : ℝ} (hab : x * x = a • F.p i + b • F.p j) :
    a = b := by
  have hxi : F.p i * x = (2 : ℝ)⁻¹ • x := frameBlockRaw_mul_left_half F hij hx
  have hxj : F.p j * x = (2 : ℝ)⁻¹ • x := frameBlockRaw_mul_right_half F hij hx
  -- `x ∘ (x ∘ x) = ((a + b)/2) • x`
  have hcube : x * (x * x) = ((a + b) / 2) • x := by
    rw [hab]
    simp only [mul_add, mul_smul_comm, _root_.mul_comm x (F.p i), _root_.mul_comm x (F.p j),
      hxi, hxj]
    module
  -- `x ∘ (x ∘ (x ∘ x)) = ((a + b)/2) • (a • pᵢ + b • pⱼ)`
  have hquart : x * (x * (x * x)) = ((a + b) / 2 * a) • F.p i + ((a + b) / 2 * b) • F.p j := by
    rw [hcube, mul_smul_comm, hab]
    module
  -- `(x ∘ x) ∘ (x ∘ x) = a² • pᵢ + b² • pⱼ`
  have hsqsq : (x * x) * (x * x) = (a * a) • F.p i + (b * b) • F.p j := by
    rw [hab]
    simp only [_root_.add_mul, mul_add, smul_mul, mul_smul_comm, F.orthIdem.idem i,
      F.orthIdem.idem j, F.orthIdem.orth i j hij, F.orthIdem.orth j i (Ne.symm hij)]
    module
  have hkey : (a * a) • F.p i + (b * b) • F.p j
      = ((a + b) / 2 * a) • F.p i + ((a + b) / 2 * b) • F.p j := by
    rw [← hsqsq, ← hquart]; exact sq_mul_sq_eq x
  have hτi : (0 : ℝ) < inner ℝ (F.p i) (F.p i) := inner_p_self_pos F i
  have hτj : (0 : ℝ) < inner ℝ (F.p j) (F.p j) := inner_p_self_pos F j
  have hij' : (inner ℝ (F.p i) (F.p j) : ℝ) = 0 := inner_p_p_of_ne F hij
  have hji' : (inner ℝ (F.p j) (F.p i) : ℝ) = 0 := inner_p_p_of_ne F (Ne.symm hij)
  have hA : a * a = (a + b) / 2 * a := by
    have := congrArg (fun z : J => (inner ℝ z (F.p i) : ℝ)) hkey
    simp only [inner_add_left, real_inner_smul_left, hji'] at this
    field_simp [hij', hji'] at this
    nlinarith [this, hτi]
  have hB : b * b = (a + b) / 2 * b := by
    have := congrArg (fun z : J => (inner ℝ z (F.p j) : ℝ)) hkey
    simp only [inner_add_left, real_inner_smul_left, hij'] at this
    field_simp [hij', hji'] at this
    nlinarith [this, hτj]
  have hsq : (a - b) ^ 2 = 0 := by nlinarith [hA, hB]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linarith [this]

/-- **`x ∘ x = a • (pᵢ + pⱼ)` for `x ∈ V_{ij}`**, with `a ≥ 0` and `a = 0` only at `x = 0`.

The idempotent `pᵢ + pⱼ` is the unit of the Peirce subalgebra the block lives in, so this says
the square of a block element is a nonnegative multiple of that unit. -/
theorem exists_sq_smul (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) :
    ∃ a : ℝ, x * x = a • (F.p i + F.p j)
      ∧ a * (inner ℝ (F.p i) (F.p i) : ℝ) = (2 : ℝ)⁻¹ * (inner ℝ x x : ℝ) := by
  obtain ⟨a, b, hab⟩ := frameBlockRaw_mul_self_eq F hij hx hx
  have hba : a = b := frameBlockRaw_sq_coeff_eq F hij hx hab
  subst hba
  refine ⟨a, by rw [hab]; module, ?_⟩
  have h := inner_sq_p_of_mem F hij hx
  rw [hab] at h
  simp only [inner_add_left, real_inner_smul_left, inner_p_p_of_ne F (Ne.symm hij)] at h
  linarith [h]

end Square

/-! ## The key operator identity -/

/-- **`x ∘ (x ∘ y) = (a/4) • y`** for `x ∈ V_{ij}`, `y ∈ V_{jk}` with `x ∘ x = a • (pᵢ + pⱼ)`.

This is the whole engine of coordinatization: it says `2 L_x` restricted to `V_{jk}` squares to
the scalar `a`, so a *normalised* `x` gives an involution `V_{jk} ≃ V_{ik}`, and it is what makes
the coordinate product multiplicative on norms.

The proof is `lin_jordan` at `(x, x, y)` evaluated at `pⱼ`.  Every term collapses:
`x ∘ y ∈ V_{ik}` is annihilated by `pⱼ`, `pⱼ` halves both `x` and `y`, and `x ∘ x` acts on `pⱼ`
as `a` and on `y` as `a/2`.  What survives is `-(x ∘ (x ∘ y)) + (a/4) • y = 0`.

★ The plain (unlinearised) Jordan identity gives **nothing** here: both of its sides reduce to
`½ a • (x ∘ y)` by the eigenvalue rules alone.  The linearisation is essential. -/
theorem block_sq_act (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F j k)
    {a : ℝ} (hxx : x * x = a • (F.p i + F.p j)) :
    x * (x * y) = (a / 4) • y := by
  have hxy : x * y ∈ frameBlockRaw F i k := frameBlockRaw_mul_middle F hij hjk hik hx hy
  have hpjxy : (x * y) * F.p j = 0 := by
    rw [_root_.mul_comm]
    exact frameBlockRaw_mul_eq_zero F (Ne.symm hij) hjk hxy
  have hpjx : x * F.p j = (2 : ℝ)⁻¹ • x := by
    rw [_root_.mul_comm]; exact frameBlockRaw_mul_right_half F hij hx
  have hpjy : y * F.p j = (2 : ℝ)⁻¹ • y := by
    rw [_root_.mul_comm]; exact frameBlockRaw_mul_left_half F hjk hy
  have hpiy : F.p i * y = 0 := frameBlockRaw_mul_eq_zero F hij hik hy
  have hxxpj : (x * x) * F.p j = a • F.p j := by
    rw [hxx]
    simp only [smul_mul, _root_.add_mul, F.orthIdem.idem j, F.orthIdem.orth i j hij]
    module
  have hxxy : (x * x) * y = (a / 2) • y := by
    rw [hxx]
    simp only [smul_mul, _root_.add_mul, hpiy, frameBlockRaw_mul_left_half F hjk hy]
    module
  have H := lin_jordan x x y (F.p j)
  rw [_root_.mul_comm y x, hpjxy, hpjx, hxxpj] at H
  simp only [mul_zero, mul_smul_comm, hpjy, hxxy, _root_.mul_comm (x * y) x] at H
  linear_combination (norm := module) -H

/-! ## Consequences of the square rule -/

section SquareConsequences

/-- Pairing `x ∘ x = a • (pᵢ + pⱼ)` against `pᵢ`. -/
theorem sq_coeff_left (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) {a : ℝ} (hxx : x * x = a • (F.p i + F.p j)) :
    a * (inner ℝ (F.p i) (F.p i) : ℝ) = (2 : ℝ)⁻¹ * (inner ℝ x x : ℝ) := by
  have h := inner_sq_p_of_mem F hij hx
  rw [hxx] at h
  simp only [real_inner_smul_left, inner_add_left, inner_p_p_of_ne F (Ne.symm hij)] at h
  linarith [h]

/-- Pairing `x ∘ x = a • (pᵢ + pⱼ)` against `pⱼ`. -/
theorem sq_coeff_right (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) {a : ℝ} (hxx : x * x = a • (F.p i + F.p j)) :
    a * (inner ℝ (F.p j) (F.p j) : ℝ) = (2 : ℝ)⁻¹ * (inner ℝ x x : ℝ) := by
  have hx' : x ∈ frameBlockRaw F j i := (frameBlockRaw_comm F i j) ▸ hx
  have h := inner_sq_p_of_mem F (Ne.symm hij) hx'
  rw [hxx] at h
  simp only [real_inner_smul_left, inner_add_left, inner_p_p_of_ne F hij] at h
  linarith [h]

/-- A block element whose square vanishes is itself zero — positive-definiteness, not
formal reality. -/
theorem eq_zero_of_sq_coeff_zero (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) (hxx : x * x = (0 : ℝ) • (F.p i + F.p j)) : x = 0 := by
  have h := sq_coeff_left F hij hx hxx
  rw [zero_mul] at h
  have h0 : (inner ℝ x x : ℝ) = 0 := by linarith [h]
  exact inner_self_eq_zero (𝕜 := ℝ) |>.mp h0

/-- **`⟪pᵢ, pᵢ⟫ = ⟪pⱼ, pⱼ⟫` as soon as `V_{ij}` contains a nonzero element.**

The two pairings of `x ∘ x = a • (pᵢ + pⱼ)` both return `½‖x‖²`, so `a τᵢ = a τⱼ`, and `a ≠ 0`
because `a τᵢ = ½‖x‖² > 0`.  This is what makes the coordinate norm form below unambiguous:
the normalisation constant is the same at every index a connection reaches. -/
theorem inner_p_eq_of_sq (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) {a : ℝ} (hxx : x * x = a • (F.p i + F.p j)) (ha : a ≠ 0) :
    (inner ℝ (F.p i) (F.p i) : ℝ) = (inner ℝ (F.p j) (F.p j) : ℝ) :=
  mul_left_cancel₀ ha ((sq_coeff_left F hij hx hxx).trans (sq_coeff_right F hij hx hxx).symm)

end SquareConsequences

/-! ## The composition law on the blocks

★ This is the result the coordinate algebra is built out of: the blocks compose, so a
normalised element of `V_{ij}` acts on `V_{jk}` as an isometry up to the scalar `a`. -/

section Composition

variable [FiniteDimensional ℝ J]

omit [FiniteDimensional ℝ J] in
/-- **`‖x ∘ y‖² = (a/4)‖y‖²`** for `x ∈ V_{ij}`, `y ∈ V_{jk}`: `block_sq_act` paired against
`y` through the associativity of the inner product. -/
theorem inner_mul_self_of_block (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F j k)
    {a : ℝ} (hxx : x * x = a • (F.p i + F.p j)) :
    (inner ℝ (x * y) (x * y) : ℝ) = a / 4 * (inner ℝ y y : ℝ) := by
  rw [inner_assoc x y (x * y), block_sq_act F hij hjk hik hx hy hxx, real_inner_smul_right]

/-- **The composition law.**  For `x ∈ V_{ij}` and `y ∈ V_{jk}` with `x ∘ x = a • (pᵢ + pⱼ)` and
`y ∘ y = b • (pⱼ + p_k)`, the product `2 (x ∘ y) ∈ V_{ik}` satisfies

  `(2 (x ∘ y)) ∘ (2 (x ∘ y)) = (a b) • (pᵢ + p_k)`.

So the coefficient of the square — the norm form of the coordinate algebra — is multiplicative
under the doubled product `x ⊙ y = 2 (x ∘ y)`.  Everything is bookkeeping around
`block_sq_act` except the identification `τᵢ = τⱼ`, which `inner_p_eq_of_sq` supplies. -/
theorem block_mul_sq (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F j k)
    {a b : ℝ} (hxx : x * x = a • (F.p i + F.p j)) (hyy : y * y = b • (F.p j + F.p k)) :
    ((2 : ℝ) • (x * y)) * ((2 : ℝ) • (x * y)) = (a * b) • (F.p i + F.p k) := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    have hx0 : x = 0 := eq_zero_of_sq_coeff_zero F hij hx hxx
    rw [hx0, zero_mul']
    simp
  have hz : (2 : ℝ) • (x * y) ∈ frameBlockRaw F i k :=
    Submodule.smul_mem _ _ (frameBlockRaw_mul_middle F hij hjk hik hx hy)
  obtain ⟨c, hc, hcspec⟩ := exists_sq_smul F hik hz
  have hτ : (inner ℝ (F.p i) (F.p i) : ℝ) = (inner ℝ (F.p j) (F.p j) : ℝ) :=
    inner_p_eq_of_sq F hij hx hxx ha
  have hyn : b * (inner ℝ (F.p j) (F.p j) : ℝ) = (2 : ℝ)⁻¹ * (inner ℝ y y : ℝ) :=
    sq_coeff_left F hjk hy hyy
  have hzn : (inner ℝ ((2 : ℝ) • (x * y)) ((2 : ℝ) • (x * y)) : ℝ)
      = a * (inner ℝ y y : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_mul_self_of_block F hij hjk hik hx hy hxx]
    ring
  rw [hzn] at hcspec
  have hτi : (0 : ℝ) < inner ℝ (F.p i) (F.p i) := inner_p_self_pos F i
  have hcab : c = a * b := by
    have h1 : c * (inner ℝ (F.p i) (F.p i) : ℝ) = a * b * (inner ℝ (F.p i) (F.p i) : ℝ) := by
      linear_combination hcspec - a * hyn - a * b * hτ
    exact mul_right_cancel₀ (ne_of_gt hτi) h1
  rw [hc, hcab]

end Composition

/-! ## Connectors

A **connector** for the pair `(i, j)` is an element `c ∈ V_{ij}` with `c ∘ c = pᵢ + pⱼ`: a
square root of the rank-two idempotent inside the block.  It exists exactly when the block is
nonzero, and `y ↦ 2 (c ∘ y)` is then an involutive linear isomorphism `V_{jk} ≃ V_{ik}`. -/

section Connector

/-- A square root of `pᵢ + pⱼ` inside `V_{ij}`. -/
def IsConnector (F : JordanFrame J n) (i j : Fin n) (c : J) : Prop :=
  c ∈ frameBlockRaw F i j ∧ c * c = F.p i + F.p j

theorem IsConnector.mem {F : JordanFrame J n} {i j : Fin n} {c : J} (h : IsConnector F i j c) :
    c ∈ frameBlockRaw F i j := h.1

theorem IsConnector.sq {F : JordanFrame J n} {i j : Fin n} {c : J} (h : IsConnector F i j c) :
    c * c = F.p i + F.p j := h.2

theorem IsConnector.sq' {F : JordanFrame J n} {i j : Fin n} {c : J} (h : IsConnector F i j c) :
    c * c = (1 : ℝ) • (F.p i + F.p j) := by rw [h.sq, one_smul]

/-- A connector is symmetric in its two indices. -/
theorem IsConnector.symm {F : JordanFrame J n} {i j : Fin n} {c : J} (h : IsConnector F i j c) :
    IsConnector F j i c :=
  ⟨(frameBlockRaw_comm F i j) ▸ h.mem, by rw [h.sq, add_comm]⟩

/-- **`c ∘ (c ∘ y) = ¼ • y` for a connector `c` on `(i, j)` and `y ∈ V_{jk}`** — `block_sq_act`
at `a = 1`. -/
theorem IsConnector.act {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {c : J} (hc : IsConnector F i j c) {y : J} (hy : y ∈ frameBlockRaw F j k) :
    c * (c * y) = (4 : ℝ)⁻¹ • y := by
  have h := block_sq_act F hij hjk hik hc.mem hy hc.sq'
  rw [h]; norm_num

/-- The transfer map `y ↦ 2 (c ∘ y)` attached to a connector. -/
def connMap (c : J) : J →ₗ[ℝ] J := (2 : ℝ) • jmulₗ J c

@[simp] theorem connMap_apply (c y : J) : connMap c y = (2 : ℝ) • (c * y) := rfl

/-- The transfer map carries `V_{jk}` into `V_{ik}`. -/
theorem connMap_mem {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {c : J} (hc : IsConnector F i j c) {y : J} (hy : y ∈ frameBlockRaw F j k) :
    connMap c y ∈ frameBlockRaw F i k :=
  Submodule.smul_mem _ _ (frameBlockRaw_mul_middle F hij hjk hik hc.mem hy)

/-- **The transfer map is an involution on `V_{jk}`.**  Applying it twice multiplies by
`4 c ∘ (c ∘ ·) = 1`.  Note the two applications run in opposite directions, `V_{jk} → V_{ik}`
and then `V_{ik} → V_{jk}`, so the hypothesis is used at both index orders. -/
theorem connMap_connMap {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {c : J} (hc : IsConnector F i j c) {y : J} (hy : y ∈ frameBlockRaw F j k) :
    connMap c (connMap c y) = y := by
  rw [connMap_apply, connMap_apply, mul_smul_comm, smul_smul,
    IsConnector.act hij hjk hik hc hy, smul_smul]
  norm_num

variable [FiniteDimensional ℝ J]

/-- **A nonzero block has a connector.**  Normalise: `x ∘ x = a • (pᵢ + pⱼ)` with `a > 0`, and
`c := a^{-1/2} • x` has `c ∘ c = pᵢ + pⱼ`. -/
theorem exists_isConnector (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) (hx0 : x ≠ 0) : ∃ c : J, IsConnector F i j c := by
  obtain ⟨a, ha, haspec⟩ := exists_sq_smul F hij hx
  have hxx : (0 : ℝ) < inner ℝ x x := real_inner_self_pos.mpr hx0
  have hτi : (0 : ℝ) < inner ℝ (F.p i) (F.p i) := inner_p_self_pos F i
  have hapos : 0 < a := by nlinarith [haspec, hxx, hτi]
  refine ⟨(Real.sqrt a)⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
  rw [smul_mul, mul_smul_comm, ha, smul_smul, smul_smul]
  have hcoef : (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ * a = 1 := by
    have hs : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt hapos.le
    have hs0 : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hapos)
    field_simp
    linarith [hs]
  rw [hcoef, one_smul]

/-- **The transfer map preserves the square coefficient.**  If `y ∘ y = b • (pⱼ + p_k)` then
`(2 (c ∘ y)) ∘ (2 (c ∘ y)) = b • (pᵢ + p_k)` — `block_mul_sq` at `a = 1`. -/
theorem connMap_sq {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {c : J} (hc : IsConnector F i j c) {y : J} (hy : y ∈ frameBlockRaw F j k)
    {b : ℝ} (hyy : y * y = b • (F.p j + F.p k)) :
    connMap c y * connMap c y = b • (F.p i + F.p k) := by
  have h := block_mul_sq F hij hjk hik hc.mem hy hc.sq' hyy
  rw [connMap_apply, h, _root_.one_mul]

/-- The transfer map carries connectors to connectors: `V_{jk} ∋ d ↦ 2 (c ∘ d)` is a connector
for `(i, k)`. -/
theorem IsConnector.transfer {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {c d : J} (hc : IsConnector F i j c) (hd : IsConnector F j k d) :
    IsConnector F i k (connMap c d) :=
  ⟨connMap_mem hij hjk hik hc hd.mem, by
    rw [connMap_sq hij hjk hik hc hd.mem hd.sq', one_smul]⟩

end Connector

/-! ## Transfer as an equivalence, and connectivity

★ The transfer map is not merely a map: it is an involution, hence a linear **isomorphism**
`V_{jk} ≃ V_{ik}`.  So a frame all of whose blocks are connected has all its off-diagonal blocks
of the same dimension — the "coordinate algebra" does not depend on which block is read. -/

section Transfer

/-- `pᵢ + pⱼ ≠ 0` for `i ≠ j`: pair it against `pᵢ`. -/
theorem pair_ne_zero (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) :
    F.p i + F.p j ≠ 0 := by
  intro h
  have := congrArg (fun z : J => (inner ℝ z (F.p i) : ℝ)) h
  simp only [inner_add_left, inner_p_p_of_ne F (Ne.symm hij), add_zero, inner_zero_left] at this
  exact absurd this (ne_of_gt (inner_p_self_pos F i))

/-- A connector is nonzero. -/
theorem IsConnector.ne_zero {F : JordanFrame J n} {i j : Fin n} (hij : i ≠ j) {c : J}
    (hc : IsConnector F i j c) : c ≠ 0 := by
  intro h
  have hsq := hc.sq
  rw [h, zero_mul'] at hsq
  exact pair_ne_zero F hij hsq.symm

/-- **The transfer map as a linear equivalence `V_{jk} ≃ V_{ik}`.**  Both directions are the
same map, read at the two index orders; `connMap_connMap` is both inverse laws. -/
def connEquiv {F : JordanFrame J n} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {c : J} (hc : IsConnector F i j c) :
    ↥(frameBlockRaw F j k) ≃ₗ[ℝ] ↥(frameBlockRaw F i k) where
  toFun y := ⟨connMap c y, connMap_mem hij hjk hik hc y.2⟩
  map_add' y z := Subtype.ext (by simp only [Submodule.coe_add, map_add])
  map_smul' r y := Subtype.ext (by simp only [SetLike.val_smul, map_smul, RingHom.id_apply])
  invFun z := ⟨connMap c z, connMap_mem (Ne.symm hij) hik hjk hc.symm z.2⟩
  left_inv y := Subtype.ext (connMap_connMap hij hjk hik hc y.2)
  right_inv z := Subtype.ext (connMap_connMap (Ne.symm hij) hik hjk hc.symm z.2)

/-- **Connected blocks have the same dimension.** -/
theorem finrank_frameBlockRaw_eq [FiniteDimensional ℝ J] {F : JordanFrame J n} {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {c : J} (hc : IsConnector F i j c) :
    Module.finrank ℝ ↥(frameBlockRaw F j k) = Module.finrank ℝ ↥(frameBlockRaw F i k) :=
  (connEquiv hij hjk hik hc).finrank_eq

/-- **Connectivity is transitive.**  A connector on `(i,j)` and one on `(j,k)` produce one on
`(i,k)`; this is `IsConnector.transfer` stated as the graph-theoretic fact the simplicity
argument consumes.  ★ What is *not* proved anywhere in this tree is the other half of that
argument — that a **simple** `J` has every block nonzero. -/
theorem exists_isConnector_trans [FiniteDimensional ℝ J] {F : JordanFrame J n} {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : ∃ c : J, IsConnector F i j c) (h₂ : ∃ d : J, IsConnector F j k d) :
    ∃ e : J, IsConnector F i k e := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  exact ⟨connMap c d, IsConnector.transfer hij hjk hik hc hd⟩

/-- A block is nonzero exactly when it has a connector. -/
theorem exists_isConnector_iff [FiniteDimensional ℝ J] (F : JordanFrame J n) {i j : Fin n}
    (hij : i ≠ j) :
    (∃ c : J, IsConnector F i j c) ↔ frameBlockRaw F i j ≠ ⊥ := by
  constructor
  · rintro ⟨c, hc⟩ hbot
    exact hc.ne_zero hij ((Submodule.eq_bot_iff _).mp hbot c hc.mem)
  · intro hbot
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hbot
    exact exists_isConnector F hij hx hx0

end Transfer

/-! ## The square coefficient as a quadratic form

The coefficient of `x ∘ x` on `V_{ij}` is pinned by the inner product, so it is a genuine
quadratic form on the block rather than a choice.  This is the form the coordinate algebra
carries. -/

section QuadForm

/-- The coefficient of a multiple of `pᵢ + pⱼ` is unique — pair against `pᵢ`. -/
theorem smul_pair_inj (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {a b : ℝ}
    (h : a • (F.p i + F.p j) = b • (F.p i + F.p j)) : a = b := by
  have := congrArg (fun z : J => (inner ℝ z (F.p i) : ℝ)) h
  simp only [real_inner_smul_left, inner_add_left, inner_p_p_of_ne F (Ne.symm hij),
    add_zero] at this
  exact mul_right_cancel₀ (ne_of_gt (inner_p_self_pos F i)) this

variable [FiniteDimensional ℝ J]

/-- **`x ∘ x = (‖x‖² / 2τᵢ) • (pᵢ + pⱼ)`** for `x ∈ V_{ij}`, where `τᵢ = ⟪pᵢ, pᵢ⟫`.  The
coefficient supplied by `exists_sq_smul` is exactly this ratio. -/
theorem sq_eq_inner_smul (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) :
    x * x = ((inner ℝ x x : ℝ) / (2 * (inner ℝ (F.p i) (F.p i) : ℝ))) • (F.p i + F.p j) := by
  obtain ⟨a, ha, haspec⟩ := exists_sq_smul F hij hx
  have hτ : (0 : ℝ) < inner ℝ (F.p i) (F.p i) := inner_p_self_pos F i
  have : a = (inner ℝ x x : ℝ) / (2 * (inner ℝ (F.p i) (F.p i) : ℝ)) := by
    field_simp
    linarith [haspec]
  rw [ha, this]

end QuadForm

end EuclideanJordan
