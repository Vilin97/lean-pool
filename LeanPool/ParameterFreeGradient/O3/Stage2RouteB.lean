/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Deriv.Add
import LeanPool.ParameterFreeGradient.O3.Geometry

/-!
# Stage 2, route B: the normalized duality map

This file is an isolated exploration of the strong-monotonicity route to
`O3.belowGeometry`.  It contains only native consequences of the current
explicit finite-dimensional definitions.  In particular, it does not assume
strong convexity or the frozen target.
-/

open scoped BigOperators

namespace O3.Stage2RouteB

theorem lpNorm_rpow_eq_lpPower {p : ℝ} (hp : p ≠ 0) {d : ℕ} (x : Point d) :
    (lpNorm p x) ^ p = lpPower p x := by
  unfold lpNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (lpPower_nonneg p x) hp

lemma coordinate_power_identity {p a : ℝ} (hp : 1 < p) :
    |a| ^ (p - 2) * a * a = |a| ^ p := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero]
    rw [show 0 ^ (p - 2) * 0 * 0 = (0 : ℝ) by ring]
    exact (Real.zero_rpow (by linarith : p ≠ 0)).symm
  · have habs : 0 < |a| := abs_pos.mpr ha
    calc
      |a| ^ (p - 2) * a * a = |a| ^ (p - 2) * |a| ^ (2 : ℕ) := by
        rw [sq_abs]
        ring
      _ = |a| ^ p := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add habs]
        congr 1
        ring

lemma pairing_powerDualityMap_self {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    pairing (powerDualityMap p x) x = lpPower p x := by
  simp only [pairing, powerDualityMap, lpPower]
  apply Finset.sum_congr rfl
  intro i _
  exact coordinate_power_identity hp

lemma pairing_dualityMap_self {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    pairing (dualityMap p x) x = (lpNorm p x) ^ (2 : ℕ) := by
  by_cases hx : x = 0
  · subst x
    simp [dualityMap, lpNorm_zero (by linarith : 0 < p), pairing]
  · have hnpos : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hnpow := lpNorm_rpow_eq_lpPower (p := p) (by linarith : p ≠ 0) x
    rw [dualityMap, ite_eq_right hnpos.ne']
    simp only [pairing]
    rw [show (∑ i, lpNorm p x ^ (2 - p) * (|x i| ^ (p - 2) * x i) * x i) =
        lpNorm p x ^ (2 - p) * (∑ i, |x i| ^ (p - 2) * x i * x i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [show (∑ i, |x i| ^ (p - 2) * x i * x i) = lpPower p x by
      simpa only [pairing, powerDualityMap] using pairing_powerDualityMap_self hp x]
    calc
      lpNorm p x ^ (2 - p) * lpPower p x =
          lpNorm p x ^ (2 - p) * lpNorm p x ^ p := by rw [hnpow]
      _ = lpNorm p x ^ ((2 - p) + p) := (Real.rpow_add hnpos _ _).symm
      _ = lpNorm p x ^ (2 : ℝ) := by ring_nf
      _ = lpNorm p x ^ (2 : ℕ) := by rw [Real.rpow_two]

lemma dualityMap_zero {p : ℝ} (hp : 0 < p) {d : ℕ} : dualityMap p (0 : Point d) = 0 := by
  simp [dualityMap, lpNorm_zero hp]

/-- The scalar energy written directly in terms of the finite power sum. -/
noncomputable def squaredLpEnergy (p : ℝ) {d : ℕ} (x : Point d) : ℝ :=
  (1 / 2 : ℝ) * (lpPower p x) ^ (2 / p)

lemma squaredLpEnergy_eq_quadraticRegularizer {p : ℝ} (_hp : 0 < p)
    {d : ℕ} (x : Point d) :
    squaredLpEnergy p x = quadraticRegularizer p 0 x := by
  simp only [squaredLpEnergy, quadraticRegularizer, sub_zero, lpNorm]
  congr 1
  calc
    lpPower p x ^ (2 / p) = lpPower p x ^ ((1 / p) * 2) := by
      congr 1
      ring
    _ = (lpPower p x ^ (1 / p)) ^ (2 : ℝ) :=
      Real.rpow_mul (lpPower_nonneg p x) _ _
    _ = (lpPower p x ^ (1 / p)) ^ (2 : ℕ) := by rw [Real.rpow_two]

lemma deriv_lpPower_line {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ lpPower p (fun i ↦ x i + s * h i)) t =
      p * pairing (powerDualityMap p (fun i ↦ x i + t * h i)) h := by
  simp only [lpPower, pairing, powerDualityMap]
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin d))) (fun i _ ↦
    ((hasDerivAt_abs_rpow (x i + t * h i) hp).comp t
      ((hasDerivAt_const t (x i)).add ((hasDerivAt_id t).mul_const (h i)))))
  have hd := hsum.deriv
  have hfun : (fun s : ℝ ↦ ∑ i, |x i + s * h i| ^ p) =
      ∑ i, (fun r : ℝ ↦ |r| ^ p) ∘
        ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i) := by
    funext s
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, Pi.add_apply, id_eq]
  rw [hfun]
  simpa only [zero_add, one_mul, Finset.mul_sum, mul_assoc] using hd

lemma lpPower_pos_of_point_ne_zero {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpPower p x :=
  lpPower_pos_of_ne_zero hx

lemma powerSum_factor_eq_norm_factor {p : ℝ} (hp : 0 < p) {d : ℕ}
    {x : Point d} (hx : x ≠ 0) :
    (lpPower p x) ^ (2 / p - 1) = (lpNorm p x) ^ (2 - p) := by
  have hS : 0 < lpPower p x := lpPower_pos_of_ne_zero hx
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp

lemma pairing_dualityMap_eq_powerSum_factor {p : ℝ} (hp : 0 < p) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) (h : Point d) :
    pairing (dualityMap p z) h =
      (lpPower p z) ^ (2 / p - 1) * pairing (powerDualityMap p z) h := by
  have hn : 0 < lpNorm p z := lpNorm_pos_of_ne_zero hz
  rw [dualityMap, ite_eq_right hn.ne']
  simp only [pairing, powerDualityMap]
  rw [show (∑ i, lpNorm p z ^ (2 - p) * (|z i| ^ (p - 2) * z i) * h i) =
      lpNorm p z ^ (2 - p) * (∑ i, |z i| ^ (p - 2) * z i * h i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [powerSum_factor_eq_norm_factor hp hz]

/-- Route B reaches the exact gradient formula away from the unique possible
origin crossing of an affine line. -/
lemma deriv_squaredLpEnergy_line_of_ne {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hxt : (fun i ↦ x i + t * h i) ≠ 0) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  let z : Point d := fun i ↦ x i + t * h i
  have hS : 0 < lpPower p z := lpPower_pos_of_ne_zero hxt
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin d))) (fun i _ ↦
    ((hasDerivAt_abs_rpow (x i + t * h i) hp).comp t
      ((hasDerivAt_const t (x i)).add ((hasDerivAt_id t).mul_const (h i)))))
  have hsumAt : (∑ i, ((fun r : ℝ ↦ |r| ^ p) ∘
      ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i)) t) = lpPower p z := by
    simp only [Function.comp_apply, Pi.add_apply, id_eq, lpPower, z]
  have hrawpos : 0 < (∑ i, (fun r : ℝ ↦ |r| ^ p) ∘
      ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i)) t := by
    rw [Finset.sum_apply, hsumAt]
    exact hS
  have hpow := hsum.rpow_const (p := 2 / p) (Or.inl hrawpos.ne')
  have hscaled := hpow.const_mul (1 / 2 : ℝ)
  have hd := hscaled.deriv
  have hfun : (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) =
      fun s : ℝ ↦ (1 / 2 : ℝ) *
        ((∑ i, ((fun r : ℝ ↦ |r| ^ p) ∘
          ((fun _ : ℝ ↦ x i) + fun u : ℝ ↦ id u * h i)) s) ^ (2 / p)) := by
    funext s
    simp only [squaredLpEnergy, lpPower, Function.comp_apply, Pi.add_apply, id_eq]
  rw [hfun]
  rw [pairing_dualityMap_eq_powerSum_factor (by linarith : 0 < p) hxt h]
  rw [← hsumAt]
  convert hd using 1
  · congr 1
    funext s
    congr 2
    rw [Finset.sum_apply]
  · simp only [pairing, powerDualityMap, zero_add, one_mul]
    rw [show (∑ i, p * |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) =
        p * (∑ i, |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    field_simp
    rw [Finset.sum_apply]
    simp only [Function.comp_apply, Pi.add_apply, id_eq]
    rw [show (∑ i, |x i + t * h i| ^ p) = (∑ i, |t * h i + x i| ^ p) by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      ring]
    ring_nf

lemma lpPower_scalar_mul {p a : ℝ} {d : ℕ} (h : Point d) :
    lpPower p (fun i ↦ a * h i) = |a| ^ p * lpPower p h := by
  simp only [lpPower, abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _),
    Finset.mul_sum]

lemma squaredLpEnergy_scalar_mul {p a : ℝ} (hp : 0 < p) {d : ℕ} (h : Point d) :
    squaredLpEnergy p (fun i ↦ a * h i) = a ^ (2 : ℕ) * squaredLpEnergy p h := by
  rw [squaredLpEnergy, lpPower_scalar_mul, Real.mul_rpow
    (Real.rpow_nonneg (abs_nonneg a) p) (lpPower_nonneg p h)]
  have habsp : (|a| ^ p) ^ (2 / p) = |a| ^ (2 : ℝ) := by
    rw [← Real.rpow_mul (abs_nonneg a)]
    congr 1
    field_simp
  rw [habsp, Real.rpow_two]
  rw [sq_abs]
  unfold squaredLpEnergy
  ring

/-- The same gradient identity at an origin crossing.  Here the affine line is
exactly a scalar multiple of its direction, so the squared norm is a genuine
quadratic and has derivative zero at the crossing. -/
lemma deriv_squaredLpEnergy_line_of_eq_zero {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hxt : (fun i ↦ x i + t * h i) = 0) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  have hxcoord : ∀ i, x i = -t * h i := by
    intro i
    have hi := congrFun hxt i
    simp only [Pi.zero_apply] at hi
    linarith
  have hfun : (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) =
      fun s : ℝ ↦ (s - t) ^ (2 : ℕ) * squaredLpEnergy p h := by
    funext s
    rw [show (fun i ↦ x i + s * h i) = (fun i ↦ (s - t) * h i) by
      funext i
      rw [hxcoord i]
      ring]
    exact squaredLpEnergy_scalar_mul (by linarith : 0 < p) h
  rw [hfun]
  have hd := (((hasDerivAt_id t).sub_const t).pow 2).mul_const (squaredLpEnergy p h)
  rw [hxt, dualityMap_zero (by linarith : 0 < p)]
  simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  simp

/-- The explicit finite-dimensional squared `ell_p` energy has normalized
duality-map directional derivative everywhere, including zero coordinates and
the origin. -/
lemma deriv_squaredLpEnergy_line {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  by_cases hxt : (fun i ↦ x i + t * h i) = 0
  · exact deriv_squaredLpEnergy_line_of_eq_zero hp x h t hxt
  · exact deriv_squaredLpEnergy_line_of_ne hp x h t hxt

/-! ## Conjugate-smoothness pivot

For `1 < p ≤ 2`, its conjugate exponent lies in the nonsingular range
`q ≥ 2`.  These exact arithmetic identities are the parameter bridge needed
to turn a `(q - 1)` smoothness estimate into the desired `(p - 1)` strong
convexity estimate without constant loss.
-/

lemma two_le_conjugateExponent {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ conjugateExponent p := by
  rw [conjugateExponent_eq]
  rw [le_div_iff₀ (by linarith : 0 < p - 1)]
  linarith

lemma conjugateExponent_sub_one {p : ℝ} (hp : 1 < p) :
    conjugateExponent p - 1 = 1 / (p - 1) := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_eq]
  field_simp [hne]
  ring

lemma conjugate_constant_cancel {p : ℝ} (hp : 1 < p) :
    (conjugateExponent p - 1) * (p - 1) = 1 := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_sub_one hp]
  field_simp [hne]

lemma mul_conjugateExponent_sub_one {p : ℝ} (hp : 1 < p) :
    (p - 1) * conjugateExponent p = p := by
  have hne : p - 1 ≠ 0 := by linarith
  rw [conjugateExponent_eq]
  field_simp [hne]

lemma conjugateExponent_ne_zero {p : ℝ} (hp : 1 < p) : conjugateExponent p ≠ 0 :=
  ne_of_gt (lt_trans zero_lt_one (one_lt_conjugateExponent hp))

lemma exponent_balance {p : ℝ} (hp : 1 < p) :
    (2 - p) * conjugateExponent p + p = conjugateExponent p := by
  have h := mul_conjugateExponent_sub_one hp
  linarith

lemma abs_powerDuality_coordinate {p a : ℝ} (hp : 1 < p) :
    |(|a| ^ (p - 2) * a)| = |a| ^ (p - 1) := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero, mul_zero]
    rw [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg habs.le _)]
    calc
      |a| ^ (p - 2) * |a| = |a| ^ (p - 2) * |a| ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = |a| ^ ((p - 2) + 1) := (Real.rpow_add habs _ _).symm
      _ = |a| ^ (p - 1) := by
        congr 1
        ring

lemma abs_dualityMap_coordinate {p : ℝ} (hp : 1 < p) {d : ℕ}
    {x : Point d} (hx : x ≠ 0) (i : Fin d) :
    |dualityMap p x i| =
      (lpNorm p x) ^ (2 - p) * |x i| ^ (p - 1) := by
  have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
  rw [dualityMap, ite_eq_right hn.ne']
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn.le _),
    abs_powerDuality_coordinate hp]

lemma lpPower_dualityMap {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    lpPower (conjugateExponent p) (dualityMap p x) =
      (lpNorm p x) ^ (conjugateExponent p) := by
  by_cases hx : x = 0
  · subst x
    rw [dualityMap_zero (by linarith : 0 < p)]
    rw [lpPower_zero (conjugateExponent_ne_zero hp)]
    rw [lpNorm_zero (by linarith : 0 < p)]
    exact (Real.zero_rpow (conjugateExponent_ne_zero hp)).symm
  · have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hnp := lpNorm_rpow_eq_lpPower (p := p) (by linarith : p ≠ 0) x
    simp only [lpPower]
    rw [show (∑ i, |dualityMap p x i| ^ conjugateExponent p) =
        lpNorm p x ^ ((2 - p) * conjugateExponent p) *
          (∑ i, |x i| ^ p) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_dualityMap_coordinate hp hx]
      rw [Real.mul_rpow (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [← Real.rpow_mul hn.le]
      rw [← Real.rpow_mul (abs_nonneg (x i))]
      congr 1
      rw [mul_conjugateExponent_sub_one hp]]
    change lpNorm p x ^ ((2 - p) * conjugateExponent p) * lpPower p x = _
    rw [← hnp, ← Real.rpow_add hn]
    rw [exponent_balance hp]

theorem lpNorm_dualityMap {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    lpNorm (conjugateExponent p) (dualityMap p x) = lpNorm p x := by
  change (lpPower (conjugateExponent p) (dualityMap p x)) ^
      (1 / conjugateExponent p) = lpNorm p x
  rw [lpPower_dualityMap hp]
  have hn : 0 ≤ lpNorm p x := lpNorm_nonneg p x
  rw [← Real.rpow_mul hn]
  rw [show conjugateExponent p * (1 / conjugateExponent p) = 1 by
    field_simp [conjugateExponent_ne_zero hp]]
  rw [Real.rpow_one]

lemma inner_comp_exponent {p : ℝ} (hp : 1 < p) :
    (p - 1) * (conjugateExponent p - 2) + (p - 2) = 0 := by
  have h := mul_conjugateExponent_sub_one hp
  linarith

lemma outer_comp_exponent {p : ℝ} (hp : 1 < p) :
    (2 - conjugateExponent p) + (2 - p) * (conjugateExponent p - 1) = 0 := by
  have h := mul_conjugateExponent_sub_one hp
  linarith

lemma powerDuality_coordinate_comp {p a : ℝ} (hp : 1 < p) :
    |(|a| ^ (p - 2) * a)| ^ (conjugateExponent p - 2) *
        (|a| ^ (p - 2) * a) = a := by
  by_cases ha : a = 0
  · subst a
    ring
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [abs_powerDuality_coordinate hp]
    rw [← Real.rpow_mul habs.le]
    rw [show |a| ^ ((p - 1) * (conjugateExponent p - 2)) *
        (|a| ^ (p - 2) * a) =
        |a| ^ ((p - 1) * (conjugateExponent p - 2)) *
          |a| ^ (p - 2) * a by ring]
    rw [← Real.rpow_add habs]
    rw [inner_comp_exponent hp, Real.rpow_zero]
    ring

lemma powerDuality_coordinate_scale {q c b : ℝ} (hc : 0 < c) :
    |c * b| ^ (q - 2) * (c * b) =
      c ^ (q - 1) * (|b| ^ (q - 2) * b) := by
  rw [abs_mul, abs_of_pos hc]
  rw [Real.mul_rpow hc.le (abs_nonneg b)]
  rw [show c ^ (q - 2) * |b| ^ (q - 2) * (c * b) =
      (c ^ (q - 2) * c) * (|b| ^ (q - 2) * b) by ring]
  rw [show c ^ (q - 2) * c = c ^ (q - 1) by
    calc
      c ^ (q - 2) * c = c ^ (q - 2) * c ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = c ^ ((q - 2) + 1) := (Real.rpow_add hc _ _).symm
      _ = c ^ (q - 1) := by
        congr 1
        ring]

theorem dualityMap_conjugate_comp {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    dualityMap (conjugateExponent p) (dualityMap p x) = x := by
  by_cases hx : x = 0
  · subst x
    rw [dualityMap_zero (by linarith : 0 < p)]
    exact dualityMap_zero (lt_trans zero_lt_one (one_lt_conjugateExponent hp))
  · have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hJuNorm := lpNorm_dualityMap hp x
    have hJu : dualityMap p x ≠ 0 := by
      intro hzero
      have := congrArg (lpNorm (conjugateExponent p)) hzero
      rw [hJuNorm, lpNorm_zero (lt_trans zero_lt_one (one_lt_conjugateExponent hp))] at this
      exact hn.ne' this
    rw [dualityMap, ite_eq_right (lpNorm_pos_of_ne_zero hJu).ne']
    funext i
    rw [hJuNorm]
    rw [dualityMap, ite_eq_right hn.ne']
    let c : ℝ := lpNorm p x ^ (2 - p)
    let b : ℝ := |x i| ^ (p - 2) * x i
    have hc : 0 < c := Real.rpow_pos_of_pos hn _
    change lpNorm p x ^ (2 - conjugateExponent p) *
        (|c * b| ^ (conjugateExponent p - 2) * (c * b)) = x i
    rw [powerDuality_coordinate_scale hc]
    rw [powerDuality_coordinate_comp hp]
    dsimp only [c]
    rw [← mul_assoc]
    rw [← Real.rpow_mul hn.le]
    rw [← Real.rpow_add hn]
    rw [outer_comp_exponent hp, Real.rpow_zero, one_mul]

lemma lpNorm_scalar_mul {r a : ℝ} (hr : 0 < r) {d : ℕ} (z : Point d) :
    lpNorm r (fun i ↦ a * z i) = |a| * lpNorm r z := by
  unfold lpNorm
  rw [lpPower_scalar_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) r) (lpPower_nonneg r z)]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [show r * (1 / r) = 1 by field_simp [ne_of_gt hr]]
  rw [Real.rpow_one]

lemma squaredLpEnergy_dualityMap {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    squaredLpEnergy (conjugateExponent p) (dualityMap p x) = squaredLpEnergy p x := by
  rw [squaredLpEnergy_eq_quadraticRegularizer
    (lt_trans zero_lt_one (one_lt_conjugateExponent hp))]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  rw [lpNorm_dualityMap hp]

lemma fenchelYoung_lower {p : ℝ} (hp : 1 < p) {d : ℕ} (w y : Point d) :
    pairing w y - squaredLpEnergy (conjugateExponent p) w ≤ squaredLpEnergy p y := by
  have hpair := pairing_le_lpNorm_mul (holderConjugate_conjugateExponent hp).symm w y
  rw [squaredLpEnergy_eq_quadraticRegularizer
    (lt_trans zero_lt_one (one_lt_conjugateExponent hp))]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  have hsq := sq_nonneg (lpNorm (conjugateExponent p) w - lpNorm p y)
  nlinarith

/-- Exact dual-exponent smoothness interface.  This is a reduction interface,
not an assumed theorem in the target chain. -/
noncomputable def ConjugateSmoothnessStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (u v : Point d),
    squaredLpEnergy (conjugateExponent p) v ≤
      squaredLpEnergy (conjugateExponent p) u +
        pairing (dualityMap (conjugateExponent p) u) (v - u) +
        ((conjugateExponent p - 1) / 2) *
          (lpNorm (conjugateExponent p) (v - u)) ^ (2 : ℕ)

lemma pairing_add_left' {d : ℕ} (a b c : Point d) :
    pairing (a + b) c = pairing a c + pairing b c := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma pairing_scalar_left {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing (fun i ↦ r * a i) b = r * pairing a b := by
  simp only [pairing, Finset.mul_sum, mul_assoc]

lemma pairing_add_right' {d : ℕ} (a b c : Point d) :
    pairing a (b + c) = pairing a b + pairing a c := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma pairing_scalar_right {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing a (fun i ↦ r * b i) = r * pairing a b := by
  rw [pairing_comm, pairing_scalar_left, pairing_comm]

/- The following theorem contains only the Fenchel/duality algebra.  Thus a
native proof of the displayed q-smoothness interface is sufficient to close
the frozen below-two geometry statement with no loss in its coefficient. -/
theorem conjugateSmoothness_implies_belowGeometry
    (hsmooth : ConjugateSmoothnessStatement) : BelowGeometryStatement := by
  intro p hp hp2 d x y
  let h : Point d := y - x
  let u : Point d := dualityMap p x
  let jh : Point d := dualityMap p h
  let v : Point d := u + fun i ↦ (p - 1) * jh i
  have hs := hsmooth p hp hp2 d u v
  have hvsub : v - u = (fun i ↦ (p - 1) * jh i) := by
    funext i
    simp only [v, Pi.sub_apply, Pi.add_apply]
    ring
  have hJqu : dualityMap (conjugateExponent p) u = x := by
    exact dualityMap_conjugate_comp hp x
  have hEu : squaredLpEnergy (conjugateExponent p) u = squaredLpEnergy p x := by
    exact squaredLpEnergy_dualityMap hp x
  have hnormjh : lpNorm (conjugateExponent p) jh = lpNorm p h :=
    lpNorm_dualityMap hp h
  rw [hvsub, hJqu, hEu] at hs
  rw [lpNorm_scalar_mul (lt_trans zero_lt_one (one_lt_conjugateExponent hp))] at hs
  rw [abs_of_pos (by linarith : 0 < p - 1), hnormjh] at hs
  have hconst : ((conjugateExponent p - 1) / 2) *
      ((p - 1) * lpNorm p h) ^ (2 : ℕ) =
      ((p - 1) / 2) * (lpNorm p h) ^ (2 : ℕ) := by
    have hc := conjugate_constant_cancel hp
    nlinarith
  rw [hconst] at hs
  have hfenchel := fenchelYoung_lower hp v y
  have hpairjx : pairing (dualityMap p x) x = (lpNorm p x) ^ (2 : ℕ) :=
    pairing_dualityMap_self hp x
  have hpairjh : pairing (dualityMap p h) h = (lpNorm p h) ^ (2 : ℕ) :=
    pairing_dualityMap_self hp h
  have hxy : y = x + h := by
    funext i
    simp only [h, Pi.add_apply, Pi.sub_apply]
    ring
  rw [show quadraticRegularizer p 0 y = squaredLpEnergy p y by
    exact (squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p) y).symm]
  rw [show quadraticRegularizer p 0 x = squaredLpEnergy p x by
    exact (squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p) x).symm]
  change squaredLpEnergy p x + pairing (dualityMap p x) h +
      (p - 1) / 2 * lpNorm p h ^ (2 : ℕ) ≤ squaredLpEnergy p y
  have hvpair : pairing v y = pairing u y + (p - 1) * pairing jh y := by
    change pairing (u + fun i ↦ (p - 1) * jh i) y = _
    rw [pairing_add_left', pairing_scalar_left]
  rw [hvpair] at hfenchel
  rw [hxy] at hfenchel
  rw [pairing_add_right'] at hfenchel
  simp only [u, jh] at hs hfenchel
  rw [pairing_add_right'] at hfenchel
  rw [pairing_scalar_right] at hs
  rw [pairing_comm x (dualityMap p h)] at hs
  rw [hpairjx, hpairjh] at hfenchel
  rw [hxy]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)] at hs hfenchel ⊢
  simp only [quadraticRegularizer, sub_zero] at hs hfenchel ⊢
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  nlinarith

end O3.Stage2RouteB
