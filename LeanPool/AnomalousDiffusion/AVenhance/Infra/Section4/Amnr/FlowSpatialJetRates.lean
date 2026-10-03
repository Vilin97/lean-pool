/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveJacobian

/-! Actual all-order spatial flow estimates from primitive field jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual state restriction equals the actual spatial field Jacobian. -/
theorem amnrStateDerivative_uncurry_eq (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) :
    amnrStateDerivative (Function.uncurry b) (t, x) = jointSpatialFDeriv b t x := rfl

/-- All spatial derivatives of the actual flow curve follow from the actual
Volterra equation and primitive field estimates. No higher flow derivative
or flow variation estimate is supplied as a hypothesis. -/
theorem amnrFlowCurve_iteratedFDeriv_norm_le_of_primitive_jets
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M B C ε : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    {s a c : ℝ} (hac : a ≤ c) (hs : s ∈ Icc a c)
    (hsmall : (c - a) * M ≤ 1 / 2) (hscale : (c - a) * B ≤ C)
    {N : ℕ} (hprimitive : ∀ i, i ≤ N → ∀ t x,
      ‖iteratedFDeriv ℝ i (fun y => jointSpatialFDeriv b t y) x‖ ≤ B * ε⁻¹ ^ i)
    (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) (amnrFlowCurve hX s a c) x‖ ≤
      amnrJacobianJetConstant C n * ε⁻¹ ^ n := by
  let Q := amnrFlowCurve hX s a c
  let V : C(Icc a c, Vec 2) →L[ℝ] C(Icc a c, Vec 2) := amnrCurveIntegral hac s hs
  let η := amnrTimeCurve a c
  let A := amnrCurveJacobianCoefficient (Function.uncurry b) hb.smooth η V
  have hshort : (c - a) * M < 1 := hsmall.trans_lt (by norm_num)
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q :=
    amnrFlowCurve_contDiff_infty_of_short hb hX hM hstate hac hs hshort
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    amnrCurveJacobianCoefficient_contDiff hb.smooth (exists_global_iteratedFDeriv_bound hb) η V
  have hR : ‖ContinuousLinearMap.const ℝ (Icc a c) (M := Vec 2)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg y)).mpr
    intro t
    exact le_rfl
  obtain ⟨C₂, hC₂, hC₂b⟩ := exists_global_iteratedFDeriv_bound hb 2
  have heq := amnrCurveResidual_solution_jacobian_equation hb.smooth hC₂ hC₂b η V hQ
    (amnrFlowCurve_residual_eq_const hb hX hac hs)
  have hsA : ‖A (Q x)‖ ≤ 1 / 2 := by
    have hh := amnrCurveJacobianCoefficient_iteratedFDeriv_norm_le hb.smooth
      (exists_global_iteratedFDeriv_bound hb) η V 0 (Q x) hM
      (fun t y => by
        simpa only [norm_iteratedFDeriv_zero, amnrStateDerivative_uncurry_eq] using
          (hstate (η t) y))
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right (amnrCurveIntegral_norm_le hac s hs) hM).trans
        hsmall)
  have hpA : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i A (Q x)‖ ≤ C * ε⁻¹ ^ i := by
    intro i hi
    have hiB : 0 ≤ B * ε⁻¹ ^ i := by positivity
    have hh := amnrCurveJacobianCoefficient_iteratedFDeriv_norm_le hb.smooth
      (exists_global_iteratedFDeriv_bound hb) η V i (Q x) hiB
      (fun t y => by simpa only [amnrStateDerivative_uncurry_eq] using hprimitive i hi (η t) y)
    refine hh.trans ?_
    calc
      ‖V‖ * (B * ε⁻¹ ^ i) = (‖V‖ * B) * ε⁻¹ ^ i := by ring
      _ ≤ C * ε⁻¹ ^ i := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right (amnrCurveIntegral_norm_le hac s hs) hB).trans hscale) (by
            positivity)
  exact amnrJacobianJet_norm_le_of_scaled_fixed_equation hQ hA _ hR heq hε x hsA hpA n hbudget

/-- Evaluating the actual curve estimate gives the same spatial radius for
 every fixed-time flow operator. -/
theorem amnr_flow_iteratedFDeriv_norm_le_of_primitive_jets
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M B C ε : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    {s a c t : ℝ} (hac : a ≤ c) (hs : s ∈ Icc a c) (ht : t ∈ Icc a c)
    (hsmall : (c - a) * M ≤ 1 / 2) (hscale : (c - a) * B ≤ C)
    {N : ℕ} (hprimitive : ∀ i, i ≤ N → ∀ t x,
      ‖iteratedFDeriv ℝ i (fun y => jointSpatialFDeriv b t y) x‖ ≤ B * ε⁻¹ ^ i)
    (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) (fun y => X t y s) x‖ ≤
      amnrJacobianJetConstant C n * ε⁻¹ ^ n := by
  have hQ := amnrFlowCurve_contDiff_infty_of_short hb hX hM hstate hac hs
    (hsmall.trans_lt (by norm_num))
  let P := ContinuousMap.evalCLM ℝ (M := Vec 2) (⟨t, ht⟩ : Icc a c)
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    change ‖u (⟨t, ht⟩ : Icc a c)‖ ≤ 1 * ‖u‖
    rw [one_mul]
    exact u.norm_coe_le_norm _
  have hh := P.norm_iteratedFDeriv_comp_left (hQ.contDiffAt (x := x)) (n := n + 1) (by simp)
  change ‖iteratedFDeriv ℝ (n + 1) (fun y => X t y s) x‖ ≤ _ at hh
  exact hh.trans ((mul_le_mul hP
    (amnrFlowCurve_iteratedFDeriv_norm_le_of_primitive_jets hb hX hM hB hε hstate hac hs
      hsmall hscale hprimitive n hbudget x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
          (one_mul _))

end AVenhance.Infra.Section4
