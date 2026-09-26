/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchySeries
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Derivatives
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ParametricIntegral

/-!
# Mixed Cauchy coefficients

Higher Cauchy kernels on polydiscs with separate radii. Differentiating the evaluation point
raises the corresponding kernel exponent; the integration contour remains fixed. This identifies
every mixed derivative with the multi-index factorial times its Cauchy coefficient, proves
independence from the contour radii, and yields the sharp mixed-derivative Cauchy estimate.
`PolydiscTaylor` uses these coefficients for convergent Taylor expansions.

## Main definitions

* `cauchyKernel`: The higher Cauchy kernel of multi-index `m`.
* `polydiscCauchyTransform`: The higher Cauchy transform with a fixed contour and variable
  evaluation point.
* `polydiscCauchyCoeffWithRadii`: Multi-index Cauchy coefficients for a polydisc with separate
  radii.

## Main results

* `multiIndexDeriv_eq_factorial_smul_cauchyCoeff`: Mixed derivatives at the center are multi-index
  factorials times the Cauchy coefficients.
* `polydiscCauchyCoeffWithRadii_eq_of_radii`: Changing the positive contour radii does not change
  the Cauchy coefficients.
* `norm_multiIndexDeriv_le`: Cauchy's estimate for every mixed derivative, with the usual
  multi-index factorial and a separate radius in each coordinate.
-/

public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The higher Cauchy kernel of multi-index `m`. -/
@[expose] def cauchyKernel (m : Fin d → ℕ) (w z : Fin d → ℂ) : ℂ :=
  ∏ i, (z i - w i)⁻¹ ^ (m i + 1)

/-- The higher Cauchy transform with a fixed contour and variable
  evaluation point. -/
@[expose] def polydiscCauchyTransform (f : (Fin d → ℂ) → E) (c : Fin d → ℂ) (R : Fin d → ℝ)
    (m : Fin d → ℕ) (w : Fin d → ℂ) : E :=
  ((2 * π * I : ℂ) ^ d)⁻¹ • torusIntegral (fun z => cauchyKernel m w z • f z) c R

/-- Multi-index Cauchy coefficients for a polydisc with separate radii. -/
@[expose] def polydiscCauchyCoeffWithRadii (f : (Fin d → ℂ) → E) (c : Fin d → ℂ)
    (R : Fin d → ℝ) (m : Fin d → ℕ) : E := polydiscCauchyTransform f c R m c

/-- Separate-radius coefficients recover the original equal-radius coefficients. -/
theorem polydiscCauchyCoeffWithRadii_const (f : (Fin d → ℂ) → E) (c : Fin d → ℂ)
    (R : ℝ) (m : Fin d → ℕ) :
    polydiscCauchyCoeffWithRadii f c (fun _ => R) m = polydiscCauchyCoeff f c R m := rfl

/-- Updating the pole in coordinate `i` isolates that factor of the Cauchy kernel. -/
theorem cauchyKernel_update (m : Fin d → ℕ) (w z : Fin d → ℂ) (i : Fin d) (v : ℂ) :
    cauchyKernel m (update w i v) z =
      (∏ j ∈ Finset.univ.erase i, (z j - w j)⁻¹ ^ (m j + 1)) *
        (z i - v)⁻¹ ^ (m i + 1) := by
  rw [cauchyKernel, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  · simp

/-- Differentiating in coordinate `i` raises that kernel exponent by one. -/
theorem hasDerivAt_cauchyKernel_update (m : Fin d → ℕ) (w z : Fin d → ℂ)
    (i : Fin d) (v : ℂ) (hz : z i - v ≠ 0) :
    HasDerivAt (fun a => cauchyKernel m (update w i a) z)
      ((m i + 1 : ℂ) * cauchyKernel (update m i (m i + 1)) (update w i v) z) v := by
  have hprod : (∏ j ∈ Finset.univ.erase i, (z j - w j)⁻¹ ^ (update m i (m i + 1) j + 1)) =
      ∏ j ∈ Finset.univ.erase i, (z j - w j)⁻¹ ^ (m j + 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  simp_rw [cauchyKernel_update]
  convert! ((((hasDerivAt_id v).const_sub (z i)).inv hz).pow (m i + 1)).const_mul
    (∏ j ∈ Finset.univ.erase i, (z j - w j)⁻¹ ^ (m j + 1)) using 1
  rw [hprod]
  simp [pow_succ, div_eq_mul_inv]
  ring

/-- Cauchy's multi-index coefficient estimate with one radius for each coordinate. -/
theorem norm_polydiscCauchyCoeffWithRadii_le {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (m : Fin d → ℕ) :
    ‖polydiscCauchyCoeffWithRadii f c R m‖ ≤ M * ∏ i, (R i)⁻¹ ^ m i := by
  have hker (θ : Fin d → ℝ) : ‖cauchyKernel m c (torusMap c R θ)‖ =
      ∏ i, (R i)⁻¹ ^ (m i + 1) := by
    simp only [cauchyKernel, norm_prod, norm_pow, norm_inv,
      norm_torusMap_sub (fun i => (hR i).le)]
  rw [polydiscCauchyCoeffWithRadii, polydiscCauchyTransform, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_torusIntegral_le_of_norm_le_const
    (C := M * ∏ i, (R i)⁻¹ ^ (m i + 1)) ?_) (norm_nonneg _)).trans_eq ?_
  · intro θ
    rw [norm_smul, hker]
    exact (mul_le_mul_of_nonneg_left
      (hM _ (torusMap_mem_closedPolydisc (fun i => (hR i).le) θ))
      (Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hR i).le) _)).trans_eq
        (mul_comm _ _)
  · simp only [norm_inv, norm_pow, norm_mul, norm_ofNat, norm_real, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (hR _)]
    have hp : (∏ i, R i) * (∏ i, (R i)⁻¹ ^ (m i + 1)) = ∏ i, (R i)⁻¹ ^ m i := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [pow_succ]
      field_simp [(hR i).ne']
    calc
      ((2 * π) ^ d)⁻¹ * (((2 * π) ^ d * ∏ i, R i) * (M * ∏ i, (R i)⁻¹ ^ (m i + 1))) =
          M * ((∏ i, R i) * ∏ i, (R i)⁻¹ ^ (m i + 1)) := by
        field_simp
      _ = _ := by rw [hp]

variable [CompleteSpace E]

/-- Higher Cauchy kernels are jointly continuous in the interior evaluation point and the contour
parameter. -/
theorem continuousOn_cauchyKernel_torus {c : Fin d → ℂ} {R : Fin d → ℝ}
    (hR : ∀ i, 0 < R i) (m : Fin d → ℕ) :
    ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℝ) =>
      cauchyKernel m p.1 (torusMap c R p.2)) (polydisc c R ×ˢ univ) := by
  apply continuousOn_finsetProd
  intro i hi
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀
  · exact ((((continuous_apply i).comp (continuous_torusMap c R)).comp
      continuous_snd).sub ((continuous_apply i).comp continuous_fst)).continuousOn
  · intro p hp
    exact sub_ne_zero.mpr (torusMap_apply_ne_of_norm_sub_lt hR
      (by simpa [dist_eq_norm] using mem_polydisc.mp hp.1 i))

omit [CompleteSpace E] in
/-- Coordinate differentiation under the fixed-contour higher Cauchy integral. -/
theorem hasDerivAt_polydiscCauchyTransform_update {f : (Fin d → ℂ) → E}
    {c w : Fin d → ℂ} {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hw : w ∈ polydisc c R) (m : Fin d → ℕ) (i : Fin d) :
    HasDerivAt (fun a => polydiscCauchyTransform f c R m (update w i a))
      ((m i + 1 : ℂ) • polydiscCauchyTransform f c R (update m i (m i + 1)) w) (w i) := by
  let V : Set ℂ := (update w i) ⁻¹' polydisc c R
  let K : Set (Fin d → ℝ) := Icc 0 (fun _ => 2 * π)
  let J (θ : Fin d → ℝ) : ℂ := ∏ j, R j * exp (θ j * I) * I
  let G (a : ℂ) (θ : Fin d → ℝ) :=
    J θ • cauchyKernel m (update w i a) (torusMap c R θ) • f (torusMap c R θ)
  let G' (a : ℂ) (θ : Fin d → ℝ) :=
    (m i + 1 : ℂ) • J θ • cauchyKernel (update m i (m i + 1))
      (update w i a) (torusMap c R θ) • f (torusMap c R θ)
  have hV : IsOpen V := (isOpen_polydisc c R).preimage
    (continuous_const.update i continuous_id)
  have hwi : w i ∈ V := by simpa [V] using hw
  have hu : Continuous (fun p : ℂ × (Fin d → ℝ) => update w i p.1) :=
    (show Continuous (fun _ : ℂ × (Fin d → ℝ) => w) from continuous_const).update i continuous_fst
  have hker (k : Fin d → ℕ) : ContinuousOn
      (fun p : ℂ × (Fin d → ℝ) => cauchyKernel k (update w i p.1) (torusMap c R p.2))
      (V ×ˢ K) := by
    apply continuousOn_finsetProd
    intro j hj
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · exact ((((continuous_apply j).comp (continuous_torusMap c R)).comp continuous_snd).sub
        ((continuous_apply j).comp hu)).continuousOn
    · intro p hp
      exact sub_ne_zero.mpr (torusMap_apply_ne_of_norm_sub_lt hR
        (by simpa [dist_eq_norm] using mem_polydisc.mp hp.1 j))
  have hfun : ContinuousOn (fun p : ℂ × (Fin d → ℝ) => f (torusMap c R p.2)) (V ×ˢ K) :=
    hfc.comp ((continuous_torusMap c R).comp continuous_snd).continuousOn
      (fun p _ => torusMap_mem_closedPolydisc (fun j => (hR j).le) p.2)
  have hJ : Continuous (fun p : ℂ × (Fin d → ℝ) => J p.2) := by dsimp [J]; fun_prop
  have hG : ContinuousOn (fun p : ℂ × (Fin d → ℝ) => G p.1 p.2) (V ×ˢ K) :=
    hJ.continuousOn.smul ((hker m).smul hfun)
  have hG' : ContinuousOn (fun p : ℂ × (Fin d → ℝ) => G' p.1 p.2) (V ×ˢ K) :=
    continuousOn_const.smul (hJ.continuousOn.smul ((hker _).smul hfun))
  have hd : ∀ a ∈ V, ∀ θ ∈ K, HasDerivAt (fun b => G b θ) (G' a θ) a := by
    intro a ha θ hθ
    have hp : torusMap c R θ i - a ≠ 0 := by
      have H := sub_ne_zero.mpr (torusMap_apply_ne_of_norm_sub_lt
        (c := c) (θ := θ) (i := i) (w := update w i a) hR
        (by simpa [dist_eq_norm] using mem_polydisc.mp ha i))
      simpa using H
    simpa only [G, G', Pi.smul_def, smul_smul, mul_assoc, mul_left_comm] using!
      ((hasDerivAt_cauchyKernel_update m w (torusMap c R θ) i a hp).smul_const
        (f (torusMap c R θ))).const_smul (J θ)
  have H := (hasDerivAt_integral_of_continuousOn_compact (μ := volume)
    (show IsCompact K from isCompact_Icc) hV hwi hG hG' hd).const_smul
      (((2 * π * I : ℂ) ^ d)⁻¹)
  have hval : (∫ θ in K, G' (w i) θ) = (m i + 1 : ℂ) •
      torusIntegral (fun z => cauchyKernel (update m i (m i + 1)) w z • f z) c R := by
    simp only [G', update_eq_self]
    rw [integral_smul]
    rfl
  rw [hval, smul_comm (((2 * π * I : ℂ) ^ d)⁻¹) (m i + 1 : ℂ)] at H
  simpa only [polydiscCauchyTransform, torusIntegral, G, K, J, Pi.smul_def] using! H

/-- The zeroth Cauchy transform equals the original function in the open polydisc. -/
theorem polydiscCauchyTransform_zero_eq {f : (Fin d → ℂ) → E} {c w : Fin d → ℂ} {R : Fin d → ℝ}
    (hR : ∀ i, 0 < R i) (hw : w ∈ polydisc c R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) :
    polydiscCauchyTransform f c R 0 w = f w := by
  simpa [polydiscCauchyTransform, cauchyKernel] using
    two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul
    hR
    (fun i => by simpa [dist_eq_norm] using mem_polydisc.mp hw i) hfc hfa

/-- Prepending an index to a list increments its count there and fixes the other counts. -/
private theorem count_cons_eq_update (is : List (Fin d)) (i : Fin d) :
    (fun j => (i :: is).count j) = update (fun j => is.count j) i (is.count i + 1) := by
  funext j
  by_cases hji : j = i
  · subst j; simp
  · simp [hji, Ne.symm hji]

/-- The product of factorials of the counts after prepending an index. -/
private theorem prod_factorial_count_cons (is : List (Fin d)) (i : Fin d) :
    (∏ j, (((i :: is).count j).factorial : ℂ)) =
      (∏ j, ((is.count j).factorial : ℂ)) * (is.count i + 1 : ℂ) := by
  calc
    (∏ j, (((i :: is).count j).factorial : ℂ)) =
        ∏ j, (if j = i then (is.count i + 1 : ℂ) else 1) * ((is.count j).factorial : ℂ) := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j; simp [Nat.factorial_succ]
      · simp [hji, Ne.symm hji]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [mul_comm]

omit [CompleteSpace E] in
/-- Repeated coordinate differentiation of the zeroth Cauchy transform yields factorials times the
corresponding higher Cauchy transform. -/
theorem iteratedPartialDeriv_polydiscCauchyTransform_zero {f : (Fin d → ℂ) → E}
    {c w : Fin d → ℂ} {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hw : w ∈ polydisc c R) (is : List (Fin d)) :
    iteratedPartialDeriv is (polydiscCauchyTransform f c R 0) w =
      (∏ j, ((is.count j).factorial : ℂ)) •
        polydiscCauchyTransform f c R (fun j => is.count j) w := by
  induction is generalizing w with
  | nil => simp [iteratedPartialDeriv, Pi.zero_def]
  | cons i is ih =>
    change partialDeriv i (iteratedPartialDeriv is (polydiscCauchyTransform f c R 0)) w = _
    have heq : partialDeriv i (iteratedPartialDeriv is (polydiscCauchyTransform f c R 0)) w =
        partialDeriv i (fun v => (∏ j, ((is.count j).factorial : ℂ)) •
          polydiscCauchyTransform f c R (fun j => is.count j) v) w := by
      apply partialDeriv_congr
      filter_upwards [(isOpen_polydisc c R).eventually_mem hw] with v hv
      exact ih hv
    rw [heq, partialDeriv]
    have H :=
      (hasDerivAt_polydiscCauchyTransform_update hR hfc hw (fun j => is.count j) i).const_smul
        (∏ j, ((is.count j).factorial : ℂ))
    have HD := H.deriv
    simp only [Pi.smul_def, smul_smul] at HD
    rw [prod_factorial_count_cons, count_cons_eq_update]
    convert! HD using 1

/-- Mixed derivatives at the center are multi-index factorials times the Cauchy coefficients. -/
theorem multiIndexDeriv_eq_factorial_smul_cauchyCoeff {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) (m : Fin d → ℕ) :
    multiIndexDeriv m f c = (∏ i, (m i).factorial : ℂ) • polydiscCauchyCoeffWithRadii f c R m := by
  have hc : c ∈ polydisc c R := mem_polydisc.mpr (by simpa using hR)
  have hcongr := iteratedPartialDeriv_congrOn (isOpen_polydisc c R)
    (fun z hz => (polydiscCauchyTransform_zero_eq hR hz hfc hfa).symm) (multiIndexList m) hc
  rw [multiIndexDeriv, hcongr, iteratedPartialDeriv_polydiscCauchyTransform_zero hR hfc hc]
  simp only [count_multiIndexList, polydiscCauchyCoeffWithRadii]

/-- Cauchy coefficients are the mixed Taylor coefficients, independent of a contour choice. -/
theorem polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R : Fin d → ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) (m : Fin d → ℕ) :
    polydiscCauchyCoeffWithRadii f c R m =
      (∏ i, (m i).factorial : ℂ)⁻¹ • multiIndexDeriv m f c := by
  rw [multiIndexDeriv_eq_factorial_smul_cauchyCoeff hR hfc hfa m, smul_smul,
    inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun i _ =>
      Nat.cast_ne_zero.mpr (m i).factorial_ne_zero)), one_smul]

/-- Changing the positive contour radii does not change the Cauchy coefficients. -/
theorem polydiscCauchyCoeffWithRadii_eq_of_radii {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R S : Fin d → ℝ} (hR : ∀ i, 0 < R i) (hS : ∀ i, 0 < S i)
    (hfcR : ContinuousOn f (closedPolydisc c R))
    (hfaR : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hfcS : ContinuousOn f (closedPolydisc c S))
    (hfaS : ∀ z ∈ closedPolydisc c S, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i)) (m : Fin d → ℕ) :
    polydiscCauchyCoeffWithRadii f c R m = polydiscCauchyCoeffWithRadii f c S m := by
  rw [polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv hR hfcR hfaR,
    polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv hS hfcS hfaS]

/-- Cauchy's estimate for every mixed derivative, with the usual multi-index factorial and a
separate radius in each coordinate. -/
theorem norm_multiIndexDeriv_le {f : (Fin d → ℂ) → E} {c : Fin d → ℂ}
    {R : Fin d → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun v => f (update z i v)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (m : Fin d → ℕ) :
    ‖multiIndexDeriv m f c‖ ≤ (∏ i, ((m i).factorial : ℝ)) * (M * ∏ i, (R i)⁻¹ ^ m i) := by
  rw [multiIndexDeriv_eq_factorial_smul_cauchyCoeff hR hfc hfa, norm_smul]
  simpa only [norm_prod, norm_natCast] using
    mul_le_mul_of_nonneg_left (norm_polydiscCauchyCoeffWithRadii_le hR hM m)
      (norm_nonneg (∏ i, ((m i).factorial : ℂ)))

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
