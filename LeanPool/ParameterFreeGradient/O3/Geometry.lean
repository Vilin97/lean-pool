/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib

/-!
# Finite-dimensional real `ell_p` geometry for the frozen O3 probe

The exponent is a genuine real number and the dimension is an arbitrary natural
number.  We use the literal finite-sum formula from the TeX source rather than
the ambient Euclidean norm on `Fin d → ℝ`.
-/

open scoped BigOperators

namespace O3

/-- A point of the arbitrary finite-dimensional ambient space `ℝ^d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- The coordinate pairing used between `ell_p` and `ell_q`. -/
def pairing {d : ℕ} (x y : Point d) : ℝ := ∑ i, x i * y i

/-- The real conjugate exponent `q = p / (p - 1)`. -/
noncomputable def conjugateExponent (p : ℝ) : ℝ := Real.conjExponent p

theorem conjugateExponent_eq (p : ℝ) : conjugateExponent p = p / (p - 1) := rfl

theorem holderConjugate_conjugateExponent {p : ℝ} (hp : 1 < p) :
    p.HolderConjugate (conjugateExponent p) := by
  exact Real.HolderConjugate.conjExponent hp

theorem one_lt_conjugateExponent {p : ℝ} (hp : 1 < p) :
    1 < conjugateExponent p := by
  exact (holderConjugate_conjugateExponent hp).symm.lt

/-- The `p`-th power sum underlying the finite-dimensional `ell_p` norm. -/
noncomputable def lpPower (p : ℝ) {d : ℕ} (x : Point d) : ℝ := ∑ i, |x i| ^ p

/-- The literal finite-dimensional `ell_p` norm for a real exponent. -/
noncomputable def lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := (lpPower p x) ^ (1 / p)

theorem lpPower_nonneg (p : ℝ) {d : ℕ} (x : Point d) : 0 ≤ lpPower p x := by
  exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (x i)) p

theorem lpNorm_nonneg (p : ℝ) {d : ℕ} (x : Point d) : 0 ≤ lpNorm p x := by
  exact Real.rpow_nonneg (lpPower_nonneg p x) (1 / p)

@[simp] theorem lpPower_zero {p : ℝ} (hp : p ≠ 0) {d : ℕ} :
    lpPower p (0 : Point d) = 0 := by
  simp [lpPower, hp]

@[simp] theorem lpNorm_zero {p : ℝ} (hp : 0 < p) {d : ℕ} :
    lpNorm p (0 : Point d) = 0 := by
  simp [lpNorm, hp.ne']

theorem lpPower_pos_of_ne_zero {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpPower p x := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hterm : 0 < |x i| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hi) p
  exact hterm.trans_le (Finset.single_le_sum
    (fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p) (Finset.mem_univ i))

theorem lpNorm_pos_of_ne_zero {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpNorm p x := by
  exact Real.rpow_pos_of_pos (lpPower_pos_of_ne_zero hx) (1 / p)

theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) {d : ℕ} {x : Point d} :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (lpNorm_pos_of_ne_zero hx).ne' h
  · rintro rfl
    exact lpNorm_zero hp

@[simp] theorem lpPower_neg (p : ℝ) {d : ℕ} (x : Point d) :
    lpPower p (-x) = lpPower p x := by
  simp [lpPower]

@[simp] theorem lpNorm_neg (p : ℝ) {d : ℕ} (x : Point d) :
    lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

theorem pairing_comm {d : ℕ} (x y : Point d) : pairing x y = pairing y x := by
  simp only [pairing, mul_comm]

@[simp] theorem pairing_neg_left {d : ℕ} (x y : Point d) :
    pairing (-x) y = -pairing x y := by
  simp [pairing]

@[simp] theorem pairing_neg_right {d : ℕ} (x y : Point d) :
    pairing x (-y) = -pairing x y := by
  simp [pairing]

/-- Finite-dimensional Hölder inequality in the exact explicit norms used by O3. -/
theorem pairing_le_lpNorm_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x y : Point d) :
    pairing x y ≤ lpNorm p x * lpNorm q y := by
  simpa [pairing, lpNorm, lpPower] using
    (Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin d)) x y hpq)

/-- Absolute-value form of finite-dimensional Hölder. -/
theorem abs_pairing_le_lpNorm_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x y : Point d) :
    |pairing x y| ≤ lpNorm p x * lpNorm q y := by
  rw [abs_le]
  constructor
  · have h := pairing_le_lpNorm_mul hpq (-x) y
    have hB : 0 ≤ lpNorm p x * lpNorm q y :=
      mul_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg q y)
    have h' : -pairing x y ≤ lpNorm p x * lpNorm q y := by
      simpa only [pairing_neg_left, lpNorm_neg] using h
    linarith
  · exact pairing_le_lpNorm_mul hpq x y

/-- The power-duality map `J_p(u)_i = |u_i|^(p-2) u_i` from the TeX source. -/
noncomputable def powerDualityMap (p : ℝ) {d : ℕ} (u : Point d) : Point d :=
  fun i ↦ |u i| ^ (p - 2) * u i

/-- `h_c(x) = (1/p) ||x-c||_p^p`, written using its literal power sum. -/
noncomputable def uniformRegularizer (p : ℝ) {d : ℕ} (c x : Point d) : ℝ :=
  (1 / p) * lpPower p (x - c)

/-- The normalized `ell_p` duality map used in the `1 < p ≤ 2` chain. -/
noncomputable def dualityMap (p : ℝ) {d : ℕ} (u : Point d) : Point d :=
  if lpNorm p u = 0 then 0
  else fun i ↦ (lpNorm p u) ^ (2 - p) * (|u i| ^ (p - 2) * u i)

/-- `ψ_c(x) = (1/2) ||x-c||_p^2`. -/
noncomputable def quadraticRegularizer (p : ℝ) {d : ℕ} (c x : Point d) : ℝ :=
  (1 / 2 : ℝ) * (lpNorm p (x - c)) ^ (2 : ℕ)

/-- Exact unproved target of TeX Lemma `lem:puniform`.  Keeping this as a
transparent proposition records the residual obligation without presenting it
as a proved theorem. -/
noncomputable def PUniformConvexityStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d : ℕ) (x y c : Point d),
    uniformRegularizer p c y ≥
      uniformRegularizer p c x + pairing (powerDualityMap p (x - c)) (y - x) +
        (2 ^ (2 - p) / p) * (lpNorm p (y - x)) ^ p

/-- Exact unproved target of TeX Lemma `lem:belowgeometry`.  This proposition
preserves real `p` and arbitrary `d`; it is not a theorem or certificate. -/
noncomputable def BelowGeometryStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (x y : Point d),
    quadraticRegularizer p 0 y ≥
      quadraticRegularizer p 0 x + pairing (dualityMap p x) (y - x) +
        ((p - 1) / 2) * (lpNorm p (y - x)) ^ (2 : ℕ)

end O3
