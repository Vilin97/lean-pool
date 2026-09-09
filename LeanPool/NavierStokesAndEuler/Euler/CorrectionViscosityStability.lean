/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionStabilityBudget
import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifferenceMetric
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.SquaredMetricStability
import Mathlib.Algebra.Order.Star.Real

/-! Genuine finite-interval Lipschitz comparison of actual correction solutions at different
viscosities. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionViscosityStability

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCylinderSobolevSpace EulerCorrectionOperators EulerQuadraticSource EulerVolterraConvolution
  EulerSobolevHeat EulerCorrectionDifferencePDE EulerCorrectionDifferenceMetric
      EulerCorrectionStabilityConstants
  EulerCorrectionStabilityBudget EulerSquaredMetricStability EulerMetricEnergyEvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance for the actual viscosity comparison. -/
local instance comparisonSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The existing real Sobolev module instance for the actual viscosity comparison. -/
local instance comparisonSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- Two actual zero-initial correction mild solutions obey a pointwise L² Lipschitz estimate in
viscosity.
The differential energy inequality is derived from their literal equations and the actual spatial
cancellations. -/
theorem correction_viscosity_pointwise {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (ν μ : ℝ) (hν : 0 < ν) (hμ : 0 < μ) (hν1 : ν ≤ 1)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (R : ℝ)
    (huR : ‖u‖ ≤ R) (hvR : ‖v‖ ≤ R)
    (hu : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl (D.coefficients period hq) 0 u t)
    (hv : ∀ t, v t = quadraticDuhamel period μ hμ hT le_rfl (D.coefficients period hq) 0 v t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∀ t, ‖value period (u t)-value period (v t)‖ ≤ B.comparisonConstant period R*|ν-μ| := by
  let K := fun s : ℝ => (B.metric (projIcc 0 T hT s)).operator
  let e := fun s : ℝ => value period (extendPath T hT u s)-value period (extendPath T hT v s)
  let E := fun s : ℝ => ⟪K s (e s),e s⟫_ℝ
  have hR : 0 ≤ R := (norm_nonneg u).trans huR
  have hKc : Continuous K := B.continuous.comp continuous_projIcc
  have hec : Continuous e := ((valueOperator period (q+1)).continuous.comp (extendPath_continuous T
      hT u)).sub
    ((valueOperator period (q+1)).continuous.comp (extendPath_continuous T hT v))
  have hEc : Continuous E := (hKc.clm_apply hec).inner (𝕜 := ℝ) hec
  have hKv (t : Icc (0 : ℝ) T) : K t.val=(B.metric t).operator := by
    simp only [K,projIcc_of_mem hT t.property]
  have hev (t : Icc (0 : ℝ) T) : e t.val=value period (u t-v t) := by
    change value period (u (projIcc 0 T hT t.val))-value period (v (projIcc 0 T hT t.val))=_
    rw [projIcc_of_mem hT t.property]
    rfl
  have hzero : E 0 ≤ 0 := by
    have hu0 := hu ⟨0,le_rfl,hT⟩
    have hv0 := hv ⟨0,le_rfl,hT⟩
    simp only [quadraticDuhamel,mul_zero,Real.toNNReal_zero,heatOperator_zero,
      intervalIntegral.integral_same,add_zero] at hu0 hv0
    have he0 : e 0=0 := by rw [hev ⟨0,le_rfl,hT⟩,hu0,hv0,sub_self]; rfl
    simp only [E,he0,map_zero,inner_zero_left,le_refl]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt E (deriv E t) t := by
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have he' := correction_difference_hasDerivAt period hq ν μ hν hμ T hT D u v hu hv t ht
    have hs : ∀ a b, ⟪K t a,b⟫_ℝ=⟪a,K t b⟫_ℝ := by
      rw [hKv τ]
      exact coefficientOperator_inner_swap (B.metric τ).coefficient (B.metric τ).measurable
        (B.metric τ).bound (B.metric τ).norm_bound (B.symmetric τ)
    have hd := metric_energy_hasDerivAt K e t (extendPath T hT B.derivative t)
      (differenceRhs period D hq ν μ τ (u τ) (v τ)) (B.hasDeriv t ht) he' hs
    exact hd.differentiableAt.hasDerivAt
  have hineq (t : ℝ) (ht : t ∈ Ioo 0 T) :
      deriv E t ≤ B.growth period R*E t+defectConstant B.bound R*|ν-μ|^2 := by
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := correction_difference_hasDerivAt period hq ν μ hν hμ T hT D u v hu hv t ht
    have htime : ‖extendPath T hT B.derivative t‖ ≤ B.time := by
      change ‖B.derivative (projIcc 0 T hT t)‖ ≤ _
      exact B.time_le _
    exact difference_metric_deriv_bound period D hq τ (u τ) (v τ) (B.metric τ) K e t ν μ
      B.c B.bound B.first B.time B.linear B.quadratic ‖D.approximation‖ R (extendPath T hT
          B.derivative t)
      B.c_pos hν.le hν1 (hKv τ) (hev τ) (B.hasDeriv t ht) hd (B.bound_le τ) (B.first_le τ) htime
      (B.linear_le τ) (B.quadratic_le τ) (D.approximation.norm_coe_le_norm τ)
      ((u.norm_coe_le_norm τ).trans huR) ((v.norm_coe_le_norm τ).trans hvR)
      (B.symmetric τ) (B.coercive τ) (B.inverse τ) (hz τ) (hud τ) (hvd τ)
  have hbound := linear_growth_bound E (deriv E) (B.growth period R)
    (defectConstant B.bound R*|ν-μ|^2) T (B.growth_nonneg period R hR)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hT hEc.continuousOn hzero hder hineq
  intro t
  have hc : B.c^2*‖value period (u t-v t)‖^2 ≤ E t.val := by
    change _ ≤ ⟪K t.val (e t.val),e t.val⟫_ℝ
    rw [hKv t,hev t]
    exact coefficientOperator_coercive (B.metric t).coefficient (B.metric t).measurable
      (B.metric t).bound (B.metric t).norm_bound (B.c^2) (B.coercive t) _
  let P := defectConstant B.bound R*T*Real.exp (B.growth period R*T)
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (sq_nonneg _) hT) (Real.exp_pos _).le
  have hsqrt := Real.sq_sqrt hP
  have heB : E t.val ≤ P*|ν-μ|^2 := (hbound t.val t.property).trans_eq (by dsimp [P]; ring)
  have hn : B.c*‖value period (u t-v t)‖ ≤ Real.sqrt P*|ν-μ| := by
    have hleft := mul_nonneg B.c_pos.le (norm_nonneg (value period (u t-v t)))
    have hright := mul_nonneg (Real.sqrt_nonneg P) (abs_nonneg (ν-μ))
    nlinarith
  change ‖value period (u t-v t)‖ ≤ B.comparisonConstant period R*|ν-μ|
  have hdiv : ‖value period (u t-v t)‖ ≤ (Real.sqrt P*|ν-μ|)/B.c :=
    (le_div_iff₀ B.c_pos).mpr (by nlinarith only [hn])
  exact hdiv.trans_eq (by unfold StabilityBudget.comparisonConstant; dsimp [P]; ring)

end EulerCorrectionViscosityStability
