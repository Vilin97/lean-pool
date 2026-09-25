/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.GeometryExperimental

/-!
# Stage 2 route D: finite-sum and duality identities

This probe-local module develops native identities needed by a direct Bregman
proof.  It contains no target-shaped hypothesis.
-/

@[expose] public section

open scoped BigOperators

namespace O3.Stage2RouteD

lemma pairing_add_left {d : ℕ} (x y z : Point d) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, Finset.sum_add_distrib, add_mul]

lemma pairing_add_right {d : ℕ} (x y z : Point d) :
    pairing x (y + z) = pairing x y + pairing x z := by
  simp [pairing, Finset.sum_add_distrib, mul_add]

lemma pairing_smul_left {d : ℕ} (a : ℝ) (x y : Point d) :
    pairing (a • x) y = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

lemma pairing_smul_right {d : ℕ} (a : ℝ) (x y : Point d) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_comm, pairing_smul_left, pairing_comm]

lemma scalar_powerDuality_self {p u : ℝ} (hp : 1 < p) :
    |u| ^ (p - 2) * u * u = |u| ^ p := by
  by_cases hu : u = 0
  · subst u
    have hp0 : p ≠ 0 := by linarith
    simp [hp0]
  · have hau : |u| ≠ 0 := (abs_ne_zero.mpr hu)
    have hpow := Real.rpow_add_intCast hau (p - 2) (2 : ℤ)
    norm_num at hpow
    rw [hpow]
    ring

lemma pairing_powerDualityMap_self {p : ℝ} (hp : 1 < p) {d : ℕ}
    (u : Point d) : pairing (powerDualityMap p u) u = lpPower p u := by
  unfold pairing powerDualityMap lpPower
  apply Finset.sum_congr rfl
  intro i _
  exact scalar_powerDuality_self hp

lemma lpNorm_rpow_p {p : ℝ} (hp : 1 < p) {d : ℕ} (u : Point d) :
    (lpNorm p u) ^ p = lpPower p u := by
  exact O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith) u

@[simp] lemma dualityMap_zero {p : ℝ} (hp : 0 < p) {d : ℕ} :
    dualityMap p (0 : Point d) = 0 := by
  simp [dualityMap, lpNorm_zero hp]

lemma dualityMap_of_ne {p : ℝ} (hp : 0 < p) {d : ℕ} {u : Point d}
    (hu : u ≠ 0) :
    dualityMap p u = fun i ↦ (lpNorm p u) ^ (2 - p) *
      (|u i| ^ (p - 2) * u i) := by
  simp [dualityMap, (lpNorm_eq_zero_iff hp).not.mpr hu]

lemma pairing_dualityMap_self {p : ℝ} (hp : 1 < p) {d : ℕ} (u : Point d) :
    pairing (dualityMap p u) u = (lpNorm p u) ^ (2 : ℕ) := by
  by_cases hu : u = 0
  · subst u
    simp [dualityMap_zero (by linarith : 0 < p), lpNorm_zero (by linarith : 0 < p), pairing]
  · rw [dualityMap_of_ne (by linarith : 0 < p) hu]
    unfold pairing
    simp only
    simp only [mul_assoc]
    change (∑ i, (lpNorm p u) ^ (2 - p) *
      (|u i| ^ (p - 2) * (u i * u i))) = (lpNorm p u) ^ (2 : ℕ)
    rw [← Finset.mul_sum]
    rw [show (∑ i, |u i| ^ (p - 2) * (u i * u i)) = lpPower p u by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [mul_assoc] using scalar_powerDuality_self (p := p) (u := u i) hp]
    rw [← lpNorm_rpow_p hp u]
    have hnorm : 0 < lpNorm p u := lpNorm_pos_of_ne_zero hu
    rw [← Real.rpow_add hnorm]
    norm_num

/-- Coordinate weights with exponent `q - 2` in the squared norm Hessian estimate. -/
noncomputable def weightVector (q : ℝ) {d : ℕ} (z : Point d) : Point d :=
  fun i ↦ |z i| ^ (q - 2)

/-- The coordinatewise square of a direction vector. -/
noncomputable def squareVector {d : ℕ} (h : Point d) : Point d :=
  fun i ↦ (h i) ^ (2 : ℕ)

lemma lpNorm_weightVector {q : ℝ} (hq : 2 < q) {d : ℕ} (z : Point d) :
    lpNorm (q / (q - 2)) (weightVector q z) =
      (lpNorm q z) ^ (q - 2) := by
  have hq0 : q ≠ 0 := by linarith
  have hqm : q - 2 ≠ 0 := by linarith
  unfold lpNorm lpPower weightVector
  have hsum :
      (∑ i, |(|z i| ^ (q - 2))| ^ (q / (q - 2))) =
        ∑ i, |z i| ^ q := by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (z i)) _)]
    rw [← Real.rpow_mul (abs_nonneg (z i))]
    congr 1
    field_simp
  rw [hsum]
  have hS : 0 ≤ ∑ i, |z i| ^ q :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (z i)) q
  rw [← Real.rpow_mul hS]
  congr 1
  field_simp

lemma lpNorm_squareVector {q : ℝ} (hq : 0 < q) {d : ℕ} (h : Point d) :
    lpNorm (q / 2) (squareVector h) = (lpNorm q h) ^ (2 : ℕ) := by
  have hq0 : q ≠ 0 := hq.ne'
  unfold lpNorm lpPower squareVector
  have hsum :
      (∑ i, |(h i) ^ (2 : ℕ)| ^ (q / 2)) = ∑ i, |h i| ^ q := by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_pow, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (abs_nonneg (h i))]
    congr 1
    ring
  rw [hsum, ← Real.rpow_two]
  have hS : 0 ≤ ∑ i, |h i| ^ q :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (h i)) q
  rw [← Real.rpow_mul hS]
  congr 1
  field_simp

/-- The exact weighted Holder estimate in the nonsingular `q > 2` Hessian.
This is the analytic core of the conjugate-smoothness route. -/
lemma weightedHolder_upper {q : ℝ} (hq : 2 < q) {d : ℕ}
    (z h : Point d) (hz : z ≠ 0) :
    (lpNorm q z) ^ (2 - q) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q h) ^ (2 : ℕ) := by
  have hden : 0 < q - 2 := by linarith
  have hr1 : 1 < q / (q - 2) := (lt_div_iff₀ hden).2 (by linarith)
  have hrs : (q / (q - 2)).HolderConjugate (q / 2) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hr1, ?_⟩
    field_simp
    ring
  have hholder := pairing_le_lpNorm_mul hrs (weightVector q z) (squareVector h)
  have hholder' :
      (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
        (lpNorm q z) ^ (q - 2) * (lpNorm q h) ^ (2 : ℕ) := by
    simpa only [pairing, weightVector, squareVector,
      lpNorm_weightVector hq z, lpNorm_squareVector (by linarith : 0 < q) h] using hholder
  have hfactor : 0 ≤ (lpNorm q z) ^ (2 - q) :=
    Real.rpow_nonneg (lpNorm_nonneg q z) _
  have hmul := mul_le_mul_of_nonneg_left hholder' hfactor
  calc
    (lpNorm q z) ^ (2 - q) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q z) ^ (2 - q) *
        ((lpNorm q z) ^ (q - 2) * (lpNorm q h) ^ (2 : ℕ)) := hmul
    _ = (lpNorm q h) ^ (2 : ℕ) := by
      have hn : 0 < lpNorm q z := lpNorm_pos_of_ne_zero hz
      rw [← mul_assoc, ← Real.rpow_add hn]
      norm_num

lemma lpPower_factor_eq_lpNorm {q : ℝ} (hq : 0 < q) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) :
    (lpPower q z) ^ (2 / q - 1) = (lpNorm q z) ^ (2 - q) := by
  have hS : 0 < lpPower q z := lpPower_pos_of_ne_zero hz
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp

lemma weightedHolder_upper_power {q : ℝ} (hq : 2 < q) {d : ℕ}
    (z h : Point d) (hz : z ≠ 0) :
    (lpPower q z) ^ (2 / q - 1) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q h) ^ (2 : ℕ) := by
  rw [lpPower_factor_eq_lpNorm (by linarith : 0 < q) hz]
  exact weightedHolder_upper hq z h hz

/-- Exact quadratic Fenchel--Young lower bound for the literal conjugate O3
norms.  This is the algebraic entry point for the dual smoothness proof. -/
lemma quadratic_fenchel_lower {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (y w : Point d) :
    pairing w y - quadraticRegularizer q 0 w ≤ quadraticRegularizer p 0 y := by
  have hh := pairing_le_lpNorm_mul hpq.symm w y
  have hs := sq_nonneg (lpNorm q w - lpNorm p y)
  simp only [quadraticRegularizer, sub_zero] at *
  nlinarith

/-- Pure algebra behind the conjugate-smoothness pivot.  Once the native
duality identities and the `q`-smoothness estimate supply these hypotheses,
the source-exact coefficient `σ/2` follows without loss. -/
lemma fenchel_smoothness_algebra {p q σ : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x h a c : Point d)
    (_hσ : 0 ≤ σ)
    (hconst : (q - 1) * σ = 1)
    (hfenchelX :
      pairing a x - quadraticRegularizer q 0 a = quadraticRegularizer p 0 x)
    (hpairC : pairing c h = (lpNorm p h) ^ (2 : ℕ))
    (hnormStep : lpNorm q (σ • c) = σ * lpNorm p h)
    (hsmooth :
      quadraticRegularizer q 0 (a + σ • c) ≤
        quadraticRegularizer q 0 a + pairing x (σ • c) +
          ((q - 1) / 2) * (lpNorm q (σ • c)) ^ (2 : ℕ)) :
    quadraticRegularizer p 0 (x + h) ≥
      quadraticRegularizer p 0 x + pairing a h +
        (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by
  have hfy := quadratic_fenchel_lower hpq (x + h) (a + σ • c)
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_smul_left] at hfy
  rw [hnormStep] at hsmooth
  have hcx : σ * pairing c x = pairing x (σ • c) := by
    rw [pairing_smul_right, pairing_comm]
  have hcoef :
      ((q - 1) / 2) * (σ * lpNorm p h) ^ (2 : ℕ) =
        (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by
    calc
      ((q - 1) / 2) * (σ * lpNorm p h) ^ (2 : ℕ) =
          (((q - 1) * σ) * σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by ring
      _ = (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by rw [hconst]; ring
  simp only [quadraticRegularizer, sub_zero] at hfenchelX hfy hsmooth ⊢
  rw [hcx, pairing_smul_left, hpairC] at hfy
  rw [hcoef] at hsmooth
  nlinarith

end O3.Stage2RouteD
