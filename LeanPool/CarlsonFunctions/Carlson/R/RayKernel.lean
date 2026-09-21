/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.PositiveRay
public import Mathlib.Analysis.MellinTransform

/-!
# Convergence of Carlson ray kernels

The products of powers in Carlson's single-integral representation (Section 6.8)
have explicit power growth at infinity. These estimates also apply to the primitive
used in the associated-function recurrence of Section 8.4.
-/

open Complex MeasureTheory Filter Asymptotics
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A product of principal powers of affine factors on a positive ray. -/
def carlsonRayProduct (c z : ι → ℂ) (x : ℝ) : ℂ :=
  ∏ i, (1 + (x : ℂ) * z i) ^ (c i)

/-- Extracting the positive real scale from each affine factor is branch-safe. -/
theorem carlsonRayProduct_eq_scaled (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {x : ℝ} (hx : 0 < x) :
    carlsonRayProduct c z x = (x : ℂ) ^ (∑ i, c i) *
      ∏ i, ((x : ℂ)⁻¹ + z i) ^ (c i) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hf (i : ι) : (1 + (x : ℂ) * z i) ^ (c i) =
      (x : ℂ) ^ (c i) * ((x : ℂ)⁻¹ + z i) ^ (c i) := by
    rw [show 1 + (x : ℂ) * z i = (x : ℂ) * ((x : ℂ)⁻¹ + z i) by
      rw [mul_add, mul_inv_cancel₀ hx0]]
    apply ofReal_pos_mul_cpow _ _ hx
    apply slitPlane_ne_zero
    apply carlsonRightHalfPlane_subset_slitPlane
    change 0 < ((x : ℂ)⁻¹ + z i).re
    rw [← ofReal_inv, add_re, ofReal_re]
    exact add_pos (inv_pos.mpr hx) (hz i)
  have hp (s : Finset ι) : (∏ i ∈ s, (x : ℂ) ^ (c i)) = (x : ℂ) ^ (∑ i ∈ s, c i) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, cpow_add _ _ hx0]
  simp only [carlsonRayProduct, hf, Finset.prod_mul_distrib, hp]

/-- After removing its power growth, the ray product has a finite limit. -/
theorem tendsto_carlsonRayProduct_scaled (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    Tendsto (fun x : ℝ => ∏ i, ((x : ℂ)⁻¹ + z i) ^ (c i)) atTop
      (𝓝 (∏ i, (z i) ^ (c i))) := by
  apply tendsto_finsetProd
  intro i _
  have h : Tendsto (fun x : ℝ => (x : ℂ)⁻¹ + z i) atTop (𝓝 (z i)) := by
    simpa using (continuous_ofReal.tendsto 0 |>.comp tendsto_inv_atTop_zero).add_const (z i)
  exact (continuousAt_cpow_const (b := c i)
    (carlsonRightHalfPlane_subset_slitPlane (hz i))).tendsto.comp h

/-- A ray product has the growth predicted by the sum of the real parts of its exponents. -/
theorem isBigO_carlsonRayProduct_atTop (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRayProduct c z =O[atTop] (fun x : ℝ => x ^ (∑ i, c i).re) := by
  have hp : (fun x : ℝ => (x : ℂ) ^ (∑ i, c i)) =O[atTop]
      (fun x : ℝ => x ^ (∑ i, c i).re) := by
    apply isBigO_norm_left.mp
    exact (isBigO_refl _ _).congr'
      (norm_ofReal_cpow_eventually_eq_atTop _).symm Filter.EventuallyEq.rfl
  have H := hp.mul ((tendsto_carlsonRayProduct_scaled c hz).isBigO_one ℝ)
  simp only [mul_one] at H
  exact H.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (carlsonRayProduct_eq_scaled c hz hx).symm) Filter.EventuallyEq.rfl

/-- At zero every affine factor tends to one. -/
theorem continuousAt_carlsonRayProduct_zero (c z : ι → ℂ) :
    ContinuousAt (carlsonRayProduct c z) 0 := by
  unfold carlsonRayProduct
  apply tendsto_finsetProd
  intro i _
  exact (show ContinuousAt (fun x : ℝ => 1 + (x : ℂ) * z i) 0 by fun_prop).cpow
    continuousAt_const (by simp)

/-- Absolute convergence of the Mellin integral of a ray product in its natural strip. -/
theorem mellinConvergent_carlsonRayProduct (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℂ}
    (ha : 0 < a.re) (ha' : a.re + (∑ i, c i).re < 0) :
    MellinConvergent (carlsonRayProduct c z) a := by
  apply mellinConvergent_of_isBigO_rpow (a := -(∑ i, c i).re) (b := 0)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    apply ContinuousAt.continuousWithinAt
    unfold carlsonRayProduct
    apply tendsto_finsetProd
    intro i _
    refine (show ContinuousAt (fun x : ℝ => 1 + (x : ℂ) * z i) x by fun_prop).cpow
      continuousAt_const ?_
    apply carlsonRightHalfPlane_subset_slitPlane
    change 0 < (1 + (x : ℂ) * z i).re
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hi := hz i
    change 0 < (z i).re at hi
    positivity
  · simpa using isBigO_carlsonRayProduct_atTop c hz
  · linarith
  · simpa using ((continuousAt_carlsonRayProduct_zero c z).tendsto.mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  · exact ha

/-- A power times a ray product tends to zero when its total growth exponent is negative. -/
theorem tendsto_cpow_mul_carlsonRayProduct_atTop (a : ℂ) (c : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (ha : a.re + (∑ i, c i).re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * carlsonRayProduct c z x) atTop (𝓝 0) := by
  have hp : (fun x : ℝ => (x : ℂ) ^ a) =O[atTop] (fun x : ℝ => x ^ a.re) := by
    apply isBigO_norm_left.mp
    exact (isBigO_refl _ _).congr'
      (norm_ofReal_cpow_eventually_eq_atTop _).symm Filter.EventuallyEq.rfl
  have H := hp.mul (isBigO_carlsonRayProduct_atTop c hz)
  have H' : (fun x : ℝ => (x : ℂ) ^ a * carlsonRayProduct c z x) =O[atTop]
      (fun x : ℝ => x ^ (a.re + (∑ i, c i).re)) := by
    apply H.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_add hx _ _).symm
  apply H'.trans_tendsto
  simpa using tendsto_rpow_neg_atTop (neg_pos.mpr ha)

/-- The Leibniz derivative of a power times a ray product, with each differentiated
factor represented by lowering just that factor's exponent. -/
def carlsonRayDerivative (a : ℂ) (c z : ι → ℂ) (x : ℝ) : ℂ :=
  a * ((x : ℂ) ^ (a - 1) * carlsonRayProduct c z x) +
    ∑ i, (c i * z i) * ((x : ℂ) ^ a * carlsonRayProduct (c - Pi.single i 1) z x)

/-- Differentiation under the branch-safe positive-ray hypotheses. -/
theorem hasDerivAt_cpow_mul_carlsonRayProduct (a : ℂ) (c : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ a * carlsonRayProduct c z x)
      (carlsonRayDerivative a c z x) x := by
  have hslit (i : ι) : 1 + (x : ℂ) * z i ∈ slitPlane := by
    apply carlsonRightHalfPlane_subset_slitPlane
    change 0 < (1 + (x : ℂ) * z i).re
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hi : 0 < (z i).re := hz i
    positivity
  have hd (i : ι) : HasDerivAt (fun w : ℂ => (1 + w * z i) ^ (c i))
      (c i * (1 + (x : ℂ) * z i) ^ (c i - 1) * z i) (x : ℂ) := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (x : ℂ)).mul_const (z i)).const_add 1).cpow_const (hslit i)
  have H := (((Complex.hasStrictDerivAt_cpow_const (c := a)
    (carlsonRightHalfPlane_subset_slitPlane hx)).hasDerivAt).mul
      (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i))).comp_ofReal
  convert H using 1
  all_goals try rfl
  unfold carlsonRayDerivative carlsonRayProduct
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    have hp : (∏ j, (1 + (x : ℂ) * z j) ^ ((c - Pi.single i 1 : ι → ℂ) j)) =
        (1 + (x : ℂ) * z i) ^ (c i - 1) *
          ∏ j ∈ Finset.univ.erase i, (1 + (x : ℂ) * z j) ^ (c j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Pi.sub_apply, Pi.single_eq_same]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
    rw [hp]
    ring

/-- The ray derivative is absolutely integrable in the boundary-vanishing strip. -/
theorem integrableOn_carlsonRayDerivative (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℂ}
    (ha : 0 < a.re) (ha' : a.re + (∑ i, c i).re < 0) :
    IntegrableOn (carlsonRayDerivative a c z) (Set.Ioi 0) := by
  have h0 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (a - 1) * carlsonRayProduct c z x)
      (Set.Ioi 0) := mellinConvergent_carlsonRayProduct c hz ha ha'
  have hi (i : ι) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ a *
      carlsonRayProduct (c - Pi.single i 1) z x) (Set.Ioi 0) := by
    have hs : ∑ j : ι, (c - Pi.single i 1 : ι → ℂ) j = (∑ j, c j) - 1 := by
      simp [Finset.sum_sub_distrib]
    have H := mellinConvergent_carlsonRayProduct (c - Pi.single i 1) hz
      (a := a + 1) (by simp only [add_re, one_re]; linarith)
      (by rw [hs]; simp only [add_re, sub_re, one_re]; linarith)
    simpa only [MellinConvergent, smul_eq_mul, add_sub_cancel_right] using H
  exact (h0.const_mul a).add (integrable_finsetSum _ (fun i _ => (hi i).const_mul (c i * z i)))

/-- Carlson's ray-kernel integration-by-parts identity. The hypotheses imply both endpoint
values vanish and the derivative is absolutely integrable. -/
theorem integral_carlsonRayDerivative_eq_zero (c : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℂ}
    (ha : 0 < a.re) (ha' : a.re + (∑ i, c i).re < 0) :
    ∫ x in Set.Ioi (0 : ℝ), carlsonRayDerivative a c z x = 0 := by
  have hcont : ContinuousAt (fun x : ℝ => (x : ℂ) ^ a * carlsonRayProduct c z x) 0 :=
    (continuousAt_ofReal_cpow_const 0 a (Or.inl ha)).mul (continuousAt_carlsonRayProduct_zero c z)
  have H := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
    (fun x hx => hasDerivAt_cpow_mul_carlsonRayProduct a c hz hx)
    (integrableOn_carlsonRayDerivative c hz ha ha')
    (tendsto_cpow_mul_carlsonRayProduct_atTop a c hz ha')
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  simpa [ha0] using H

/-- Carlson's Exercise 6.8-8: the ray representation with factors `1 + x zᵢ`.
This is the orientation needed in the proof of the associated-function recurrence. -/
theorem mellin_carlsonRayProduct_eq_rIntegral {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    mellin (carlsonRayProduct (fun i => -b i) z) a =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  let f : ℝ → ℂ := fun x => ∏ i, (z i + (x : ℂ)) ^ (-b i)
  have hpoint (x : ℝ) (hx : 0 < x) :
      carlsonRayProduct (fun i => -b i) z x⁻¹ = (x : ℂ) ^ (∑ i, b i) * f x := by
    rw [carlsonRayProduct_eq_scaled _ hz (inv_pos.mpr hx)]
    simp only [ofReal_inv, inv_inv, Finset.sum_neg_distrib,
      inv_cpow_ofReal_nonneg hx.le, cpow_neg, inv_inv, f, add_comm]
  calc
    _ = mellin (fun x : ℝ => carlsonRayProduct (fun i => -b i) z x⁻¹) (-a) := by
      rw [mellin_comp_inv, neg_neg]
    _ = mellin (fun x : ℝ => (x : ℂ) ^ (∑ i, b i) • f x) (-a) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [hpoint x hx, smul_eq_mul]
    _ = mellin f a' := by rw [mellin_cpow_smul, ← hsum]; congr 1; ring
    _ = carlsonRPositiveRayIntegral a' b z := rfl
    _ = _ := by
      rw [carlsonRPositiveRayIntegral_eq ha' ha (by rw [add_comm, hsum]) hb hz,
        betaIntegral_symm]

end DirichletTransform
end
