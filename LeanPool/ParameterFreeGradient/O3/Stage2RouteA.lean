/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.Calculus.Deriv.Abs
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 2, route A: finite-dimensional differentiation

This file isolates the Hessian/integration route toward `O3.belowGeometry`.
It deliberately does not export the frozen theorem until the singular-line
integration argument is complete.
-/

open scoped BigOperators

namespace O3.Stage2RouteA

/-- The power sum along an affine line. -/
noncomputable def linePower (p : ℝ) {d : ℕ} (x h : Point d) (t : ℝ) : ℝ :=
  lpPower p (x + t • h)

/-- The directional pairing with the unnormalised power-duality map. -/
noncomputable def linePowerDerivative (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  p * pairing (powerDualityMap p (x + t • h)) h

lemma hasDerivAt_abs_affine_rpow {p a b t : ℝ} (hp : 1 < p) :
    HasDerivAt (fun s : ℝ ↦ |a + s * b| ^ p)
      (p * |a + t * b| ^ (p - 2) * (a + t * b) * b) t := by
  have hbase := hasDerivAt_abs_rpow (a + t * b) hp
  have haff : HasDerivAt (fun s : ℝ ↦ a + s * b) b t := by
    convert ((hasDerivAt_id t).mul_const b).const_add a using 1 <;>
      first | rfl | ring
  convert hbase.comp t haff using 1; rfl

lemma hasDerivAt_linePower {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    HasDerivAt (linePower p x h) (linePowerDerivative p x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d, |x i + s * h i| ^ p)
      (∑ i : Fin d, p * |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) t := by
    exact HasDerivAt.fun_sum (fun i _ ↦ hasDerivAt_abs_affine_rpow hp)
  convert hsum using 1 <;>
    first
    | rfl
    | simp only [linePowerDerivative, pairing, powerDualityMap,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The squared norm written as a single real power of the finite power sum. -/
lemma lpNorm_sq_eq_lpPower_rpow {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ (2 : ℕ) = (lpPower p z) ^ (2 / p) := by
  unfold lpNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (lpPower_nonneg p z)]
  congr 1
  norm_num
  field_simp

/-- The one-variable restriction of `x ↦ (1/2)‖x‖_p²`. -/
noncomputable def lineEnergy (p : ℝ) {d : ℕ} (x h : Point d) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (linePower p x h t) ^ (2 / p)

lemma lineEnergy_eq_quadraticRegularizer {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    lineEnergy p x h t = quadraticRegularizer p 0 (x + t • h) := by
  rw [lineEnergy, quadraticRegularizer, sub_zero, lpNorm_sq_eq_lpPower_rpow hp]
  rfl

lemma lpPower_rpow_two_div_sub_one_eq {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) :
    (lpPower p z) ^ (2 / p - 1) = (lpNorm p z) ^ (2 - p) := by
  have hS : 0 < lpPower p z := lpPower_pos_of_ne_zero hz
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp

lemma hasDerivAt_lineEnergy_of_ne_zero {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    HasDerivAt (lineEnergy p x h)
      (pairing (dualityMap p (x + t • h)) h) t := by
  have hp0 : p ≠ 0 := by linarith
  have hS : linePower p x h t ≠ 0 := by
    exact (lpPower_pos_of_ne_zero hz).ne'
  have hpow := (hasDerivAt_linePower hp x h t).rpow_const
    (Or.inl hS) (p := 2 / p)
  have hscaled := hpow.const_mul (1 / 2 : ℝ)
  have hnorm : lpNorm p (x + t • h) ≠ 0 :=
    (lpNorm_pos_of_ne_zero hz).ne'
  have hpair : pairing (dualityMap p (x + t • h)) h =
      (1 / 2 : ℝ) * (linePowerDerivative p x h t * (2 / p) *
        linePower p x h t ^ (2 / p - 1)) := by
    rw [dualityMap, ite_eq_right hnorm, linePowerDerivative, linePower,
      lpPower_rpow_two_div_sub_one_eq hp0 hz]
    unfold pairing powerDualityMap
    have hfactor :
        (∑ i : Fin d, (fun i ↦ lpNorm p (x + t • h) ^ (2 - p) *
            (|(x + t • h) i| ^ (p - 2) * (x + t • h) i)) i * h i) =
          lpNorm p (x + t • h) ^ (2 - p) *
            ∑ i : Fin d, |(x + t • h) i| ^ (p - 2) * (x + t • h) i * h i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor]
    field_simp
  rw [hpair]
  change HasDerivAt (fun s : ℝ ↦
    (1 / 2 : ℝ) * linePower p x h s ^ (2 / p))
    ((1 / 2 : ℝ) * (linePowerDerivative p x h t * (2 / p) *
      linePower p x h t ^ (2 / p - 1))) t
  exact hscaled

/-- Away from the scalar singularity, the derivative of
`|u|^(p-2)u` has its expected exact coefficient. -/
lemma hasDerivAt_scalarJ_of_ne_zero {p u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (O3.Experimental.scalarJ p) ((p - 1) * |u| ^ (p - 2)) u := by
  have ha := hasDerivAt_abs hu
  have hap := ha.rpow_const (Or.inl (abs_pos.mpr hu).ne') (p := p - 2)
  have hm := hap.mul (hasDerivAt_id u)
  have hid :
      (↑(SignType.sign u) : ℝ) * (p - 2) * |u| ^ (p - 2 - 1) * u +
          |u| ^ (p - 2) * 1 = (p - 1) * |u| ^ (p - 2) := by
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · have hsign : (↑(SignType.sign u) : ℝ) = -1 := by
        rw [sign_neg huNeg]
        rfl
      rw [hsign, abs_of_neg huNeg]
      have hpow : (-u) ^ (p - 2 - 1) * (-u) = (-u) ^ (p - 2) := by
        calc
          (-u) ^ (p - 2 - 1) * (-u) =
              (-u) ^ (p - 2 - 1) * (-u) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (-u) ^ ((p - 2 - 1) + 1) :=
            (Real.rpow_add (neg_pos.mpr huNeg) _ _).symm
          _ = (-u) ^ (p - 2) := by ring_nf
      have hpowU : (-u) ^ (p - 2 - 1) * u = -((-u) ^ (p - 2)) := by
        calc
          (-u) ^ (p - 2 - 1) * u =
              -((-u) ^ (p - 2 - 1) * (-u)) := by ring
          _ = -((-u) ^ (p - 2)) := by rw [hpow]
      rw [mul_assoc ((-1 : ℝ) * (p - 2)), hpowU]
      ring
    · have hsign : (↑(SignType.sign u) : ℝ) = 1 := by
        rw [sign_pos huPos]
        rfl
      rw [hsign, abs_of_pos huPos]
      simp only [one_mul, mul_one]
      have hpow : u ^ (p - 2 - 1) * u = u ^ (p - 2) := by
        calc
          u ^ (p - 2 - 1) * u = u ^ (p - 2 - 1) * u ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = u ^ ((p - 2 - 1) + 1) := (Real.rpow_add huPos _ _).symm
          _ = u ^ (p - 2) := by ring_nf
      rw [mul_assoc, hpow]
      ring
  rw [← hid]
  change HasDerivAt ((fun y : ℝ ↦ |y| ^ (p - 2)) * id)
    ((↑(SignType.sign u) : ℝ) * (p - 2) * |u| ^ (p - 2 - 1) * id u +
      |u| ^ (p - 2) * 1) u
  exact hm

/-- For exponents above two, the unnormalised duality map is differentiable
also at the scalar zero, with derivative zero. -/
lemma hasDerivAt_scalarJ_zero {q : ℝ} (hq : 2 < q) :
    HasDerivAt (O3.Experimental.scalarJ q) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hcont : Filter.Tendsto (fun t : ℝ ↦ |t| ^ (q - 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    change Filter.Tendsto (fun t : ℝ ↦ |t| ^ (q - 2))
      (nhds 0 ⊓ Filter.principal {0}ᶜ) (nhds 0)
    have hc : ContinuousAt (fun t : ℝ ↦ |t| ^ (q - 2)) 0 :=
      (continuous_abs.continuousAt.rpow_const
        (Or.inr (by linarith : 0 ≤ q - 2)))
    simpa [Real.zero_rpow (by linarith : q - 2 ≠ 0)] using
      hc.tendsto.mono_left inf_le_left
  apply hcont.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  simp only [zero_add, O3.Experimental.scalarJ, abs_zero, smul_eq_mul]
  rw [Real.zero_rpow (by linarith : q - 2 ≠ 0), zero_mul, sub_zero]
  field_simp

lemma hasDerivAt_scalarJ_above_two {q u : ℝ} (hq : 2 < q) :
    HasDerivAt (O3.Experimental.scalarJ q)
      ((q - 1) * |u| ^ (q - 2)) u := by
  by_cases hu : u = 0
  · subst u
    simpa [Real.zero_rpow (by linarith : q - 2 ≠ 0)] using
      hasDerivAt_scalarJ_zero hq
  · exact hasDerivAt_scalarJ_of_ne_zero hu

/-- The weighted quadratic form that appears in the Hessian. -/
noncomputable def weightedSquareSum (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  ∑ i : Fin d, |(x + t • h) i| ^ (p - 2) * (h i) ^ (2 : ℕ)

/-- The unnormalised duality pairing along a line. -/
noncomputable def linePowerPair (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  pairing (powerDualityMap p (x + t • h)) h

lemma hasDerivAt_scalarJ_affine {p a b t : ℝ} (hz : a + t * b ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ O3.Experimental.scalarJ p (a + s * b))
      ((p - 1) * |a + t * b| ^ (p - 2) * b) t := by
  have haff : HasDerivAt (fun s : ℝ ↦ a + s * b) b t := by
    convert ((hasDerivAt_id t).mul_const b).const_add a using 1 <;>
      first | rfl | ring
  change HasDerivAt
    (O3.Experimental.scalarJ p ∘ fun s : ℝ ↦ a + s * b)
    (((p - 1) * |a + t * b| ^ (p - 2)) * b) t
  exact (hasDerivAt_scalarJ_of_ne_zero (p := p) hz).comp t haff

lemma hasDerivAt_linePowerPair_of_coordinates_ne_zero {p : ℝ} {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (linePowerPair p x h)
      ((p - 1) * weightedSquareSum p x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d,
        O3.Experimental.scalarJ p (x i + s * h i) * h i)
      (∑ i : Fin d, ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) t := by
    exact HasDerivAt.fun_sum fun i _ ↦
      (hasDerivAt_scalarJ_affine (p := p) (a := x i) (b := h i) (t := t)
        (by simpa using hz i)).mul_const (h i)
  have hderiv : (∑ i : Fin d,
      ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) =
      (p - 1) * weightedSquareSum p x h t := by
    rw [weightedSquareSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  rw [← hderiv]
  change HasDerivAt
    (fun s : ℝ ↦ ∑ i : Fin d,
      O3.Experimental.scalarJ p (x i + s * h i) * h i)
    (∑ i : Fin d, ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) t
  exact hsum

/-- For `q > 2`, the Hessian's coordinatewise power term is differentiable
even when coordinates cross zero. -/
lemma hasDerivAt_linePowerPair_above_two {q : ℝ} (hq : 2 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    HasDerivAt (linePowerPair q x h)
      ((q - 1) * weightedSquareSum q x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d,
        O3.Experimental.scalarJ q (x i + s * h i) * h i)
      (∑ i : Fin d, ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have haff : HasDerivAt (fun s : ℝ ↦ x i + s * h i) (h i) t := by
      convert ((hasDerivAt_id t).mul_const (h i)).const_add (x i) using 1 <;>
        first | rfl | ring
    have hc := (hasDerivAt_scalarJ_above_two (q := q)
      (u := x i + t * h i) hq).comp t haff
    exact hc.mul_const (h i)
  have hderiv : (∑ i : Fin d,
      ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) =
      (q - 1) * weightedSquareSum q x h t := by
    rw [weightedSquareSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  rw [← hderiv]
  change HasDerivAt
    (fun s : ℝ ↦ ∑ i : Fin d,
      O3.Experimental.scalarJ q (x i + s * h i) * h i)
    (∑ i : Fin d, ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) t
  exact hsum

/-- Exact radial formula for the normalized duality pairing. -/
lemma pairing_dualityMap_smul {q : ℝ} (hq : 1 < q) {d : ℕ}
    (a : ℝ) (h : Point d) :
    pairing (dualityMap q (a • h)) h =
      a * (lpNorm q h) ^ (2 : ℕ) := by
  by_cases ha : a = 0
  · subst a
    simp [O3.Stage2RouteD.dualityMap_zero (by linarith : 0 < q), pairing]
  · have hself := O3.Stage2RouteD.pairing_dualityMap_self hq (a • h)
    rw [O3.Stage2RouteD.pairing_smul_right,
      O3.Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ q)] at hself
    have habs : |a| ^ (2 : ℕ) = a ^ (2 : ℕ) := sq_abs a
    rw [mul_pow, habs] at hself
    apply (mul_left_cancel₀ ha)
    calc
      a * pairing (dualityMap q (a • h)) h =
          a ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ) := hself
      _ = a * (a * (lpNorm q h) ^ (2 : ℕ)) := by ring

/-- At the unique whole-vector zero on an affine line, the actual normalized
duality pairing is locally (indeed globally) affine in the line parameter. -/
lemma line_duality_pair_eq_affine_of_zero {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) =
      fun s : ℝ ↦ (s - t) * (lpNorm q h) ^ (2 : ℕ) := by
  funext s
  have hvec : x + s • h = (s - t) • h := by
    funext i
    have hzi := congrFun hz i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hzi ⊢
    linarith
  rw [hvec, pairing_dualityMap_smul hq]

lemma hasDerivAt_line_duality_pair_at_zero {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h)
      ((lpNorm q h) ^ (2 : ℕ)) t := by
  rw [line_duality_pair_eq_affine_of_zero hq x h t hz]
  convert ((hasDerivAt_id t).sub_const t).mul_const
    ((lpNorm q h) ^ (2 : ℕ)) using 1 <;>
    first | rfl | ring

/-- Algebraic nonzero-vector formula for the directional derivative of the
squared norm.  Unlike `dualityMap`, it has no conditional branch. -/
noncomputable def lineGradientFormula (p : ℝ) {d : ℕ}
    (x h : Point d) (t : ℝ) : ℝ :=
  (linePower p x h t) ^ (2 / p - 1) * linePowerPair p x h t

lemma lineGradientFormula_eq_duality_pair {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    lineGradientFormula p x h t = pairing (dualityMap p (x + t • h)) h := by
  have hnorm : lpNorm p (x + t • h) ≠ 0 :=
    (lpNorm_pos_of_ne_zero hz).ne'
  rw [lineGradientFormula, dualityMap, ite_eq_right hnorm,
    linePower, lpPower_rpow_two_div_sub_one_eq hp hz, linePowerPair]
  unfold pairing powerDualityMap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact Hessian formula at points where the vector and all coordinates avoid
the real-power singularities. -/
lemma hasDerivAt_lineGradientFormula_of_coordinates_ne_zero
    {p : ℝ} (hp : 1 < p) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0)
    (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (lineGradientFormula p x h)
      ((2 - p) * (linePower p x h t) ^ (2 / p - 2) *
          (linePowerPair p x h t) ^ (2 : ℕ) +
        (p - 1) * (linePower p x h t) ^ (2 / p - 1) *
          weightedSquareSum p x h t) t := by
  have hp0 : p ≠ 0 := by linarith
  have hS : linePower p x h t ≠ 0 :=
    (lpPower_pos_of_ne_zero hzvec).ne'
  have hcoeff := (hasDerivAt_linePower hp x h t).rpow_const
    (Or.inl hS) (p := 2 / p - 1)
  have hpair := hasDerivAt_linePowerPair_of_coordinates_ne_zero
    (p := p) x h t hz
  have hprod := hcoeff.mul hpair
  have hraw :
      linePowerDerivative p x h t * (2 / p - 1) *
          linePower p x h t ^ (2 / p - 1 - 1) * linePowerPair p x h t +
        linePower p x h t ^ (2 / p - 1) *
          ((p - 1) * weightedSquareSum p x h t) =
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
          linePowerPair p x h t ^ (2 : ℕ) +
        (p - 1) * linePower p x h t ^ (2 / p - 1) *
          weightedSquareSum p x h t := by
    have hexp : 2 / p - 1 - 1 = 2 / p - 2 := by ring
    rw [hexp, linePowerDerivative]
    unfold linePowerPair
    field_simp
  rw [← hraw]
  change HasDerivAt
    ((fun s : ℝ ↦ linePower p x h s ^ (2 / p - 1)) * linePowerPair p x h)
    (linePowerDerivative p x h t * (2 / p - 1) *
        linePower p x h t ^ (2 / p - 1 - 1) * linePowerPair p x h t +
      linePower p x h t ^ (2 / p - 1) *
        ((p - 1) * weightedSquareSum p x h t)) t
  exact hprod

/-- Above two, the same exact normalized Hessian formula needs only the whole
vector to be nonzero; scalar zero coordinates are covered by
`hasDerivAt_scalarJ_zero`. -/
lemma hasDerivAt_lineGradientFormula_above_two_of_ne_zero
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0) :
    HasDerivAt (lineGradientFormula q x h)
      ((2 - q) * (linePower q x h t) ^ (2 / q - 2) *
          (linePowerPair q x h t) ^ (2 : ℕ) +
        (q - 1) * (linePower q x h t) ^ (2 / q - 1) *
          weightedSquareSum q x h t) t := by
  have hq0 : q ≠ 0 := by linarith
  have hS : linePower q x h t ≠ 0 :=
    (lpPower_pos_of_ne_zero hzvec).ne'
  have hcoeff := (hasDerivAt_linePower (by linarith : 1 < q) x h t).rpow_const
    (Or.inl hS) (p := 2 / q - 1)
  have hpair := hasDerivAt_linePowerPair_above_two (q := q) hq x h t
  have hprod := hcoeff.mul hpair
  have hraw :
      linePowerDerivative q x h t * (2 / q - 1) *
          linePower q x h t ^ (2 / q - 1 - 1) * linePowerPair q x h t +
        linePower q x h t ^ (2 / q - 1) *
          ((q - 1) * weightedSquareSum q x h t) =
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t := by
    have hexp : 2 / q - 1 - 1 = 2 / q - 2 := by ring
    rw [hexp, linePowerDerivative]
    unfold linePowerPair
    field_simp
  rw [← hraw]
  change HasDerivAt
    ((fun s : ℝ ↦ linePower q x h s ^ (2 / q - 1)) * linePowerPair q x h)
    (linePowerDerivative q x h t * (2 / q - 1) *
        linePower q x h t ^ (2 / q - 1 - 1) * linePowerPair q x h t +
      linePower q x h t ^ (2 / q - 1) *
        ((q - 1) * weightedSquareSum q x h t)) t
  exact hprod

lemma lineGradientFormula_deriv_le_above_two {q : ℝ} (hq : 2 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hzvec : x + t • h ≠ 0) :
    (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t ≤
      (q - 1) * (lpNorm q h) ^ (2 : ℕ) := by
  have hfirst :
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
        linePowerPair q x h t ^ (2 : ℕ) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith : 2 - q ≤ 0)
        (Real.rpow_nonneg (lpPower_nonneg q (x + t • h)) _))
      (sq_nonneg _)
  have hw := O3.Stage2RouteD.weightedHolder_upper_power hq
    (x + t • h) h hzvec
  change linePower q x h t ^ (2 / q - 1) *
      weightedSquareSum q x h t ≤ (lpNorm q h) ^ (2 : ℕ) at hw
  have hmul := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ q - 1)
  linarith

/-- Every line parameter admits an exact derivative of the actual normalized
duality pairing, together with the sharp `(q-1)` upper bound.  The proof splits
only on the whole-vector zero; scalar coordinate zeros are already native. -/
lemma exists_hasDerivAt_line_duality_pair_le_above_two
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ) :
    ∃ v : ℝ,
      HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) v t ∧
        v ≤ (q - 1) * (lpNorm q h) ^ (2 : ℕ) := by
  by_cases hz : x + t • h = 0
  · refine ⟨(lpNorm q h) ^ (2 : ℕ),
      hasDerivAt_line_duality_pair_at_zero (by linarith : 1 < q) x h t hz, ?_⟩
    have hn : 0 ≤ (lpNorm q h) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  · let v : ℝ :=
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t
    have hformula : HasDerivAt (lineGradientFormula q x h) v t := by
      exact hasDerivAt_lineGradientFormula_above_two_of_ne_zero hq x h t hz
    have hcont : ContinuousAt (fun s : ℝ ↦ x + s • h) t := by fun_prop
    have hne : ∀ᶠ s in nhds t, x + s • h ≠ 0 := hcont.eventually_ne hz
    have heq :
        (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) =ᶠ[nhds t]
          lineGradientFormula q x h := by
      filter_upwards [hne] with s hs
      exact (lineGradientFormula_eq_duality_pair (by linarith : q ≠ 0)
        x h s hs).symm
    refine ⟨v, hformula.congr_of_eventuallyEq heq, ?_⟩
    exact lineGradientFormula_deriv_le_above_two hq x h t hz

/-- The first Hessian term is nonnegative throughout the frozen range
`p ≤ 2`; hence only the weighted Hölder term remains for the pointwise lower
bound. -/
lemma weightedTerm_le_hessianFormula {p : ℝ} (hp2 : p ≤ 2) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    (p - 1) * linePower p x h t ^ (2 / p - 1) *
        weightedSquareSum p x h t ≤
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
          linePowerPair p x h t ^ (2 : ℕ) +
        (p - 1) * linePower p x h t ^ (2 / p - 1) *
          weightedSquareSum p x h t := by
  have hfirst : 0 ≤
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
        linePowerPair p x h t ^ (2 : ℕ) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hp2)
        (Real.rpow_nonneg (lpPower_nonneg p (x + t • h)) (2 / p - 2)))
      (sq_nonneg (linePowerPair p x h t))
  linarith

/-- At the endpoint `p = 2`, the weighted Hölder bridge is an identity. -/
lemma weightedSquareSum_two_eq {d : ℕ} (x h : Point d) (t : ℝ) :
    weightedSquareSum 2 x h t = (lpNorm 2 h) ^ (2 : ℕ) := by
  rw [lpNorm_sq_eq_lpPower_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  have hexp : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hexp, Real.rpow_one]
  unfold weightedSquareSum lpPower
  apply Finset.sum_congr rfl
  intro i _
  norm_num

/-- The exact remaining pointwise inequality in route A for `1 < p < 2`.
It is kept as a transparent residual proposition, not as an assumption of any
proved declaration. -/
noncomputable def WeightedHolderResidual : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d : ℕ) (z h : Point d),
    (∀ i : Fin d, z i ≠ 0) →
      (lpPower p z) ^ (2 / p - 1) *
          (∑ i : Fin d, |z i| ^ (p - 2) * (h i) ^ (2 : ℕ)) ≥
        (lpNorm p h) ^ (2 : ℕ)

end O3.Stage2RouteA
