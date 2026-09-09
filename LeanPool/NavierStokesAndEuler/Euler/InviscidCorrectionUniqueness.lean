/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionStabilityBudget
import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifferenceMetric
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.InviscidDifferencePDE
import LeanPool.NavierStokesAndEuler.Euler.SquaredMetricStability
import Mathlib.Algebra.Order.Star.Real

/-! Uniqueness of the actual finite-order inviscid correction equation. -/

@[expose] public section


noncomputable section

namespace EulerInviscidCorrectionUniqueness

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCylinderSobolevSpace EulerCorrectionOperators EulerQuadraticSource EulerVolterraConvolution
  EulerSobolevHeat EulerCorrectionDifferencePDE EulerCorrectionDifferenceMetric
      EulerCorrectionStabilityConstants
  EulerCorrectionStabilityBudget EulerSquaredMetricStability EulerMetricEnergyEvolution
      EulerInviscidDifferencePDE
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance for the actual viscosity comparison. -/
local instance comparisonSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The existing real Sobolev module instance for the actual viscosity comparison. -/
local instance comparisonSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- Actual inviscid corrections with equal initial data and the concrete metric/coefficient bounds
are unique.
The squared energy inequality and the zero-difference conclusion are derived from their actual
equations. -/
theorem inviscid_correction_unique {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hi : u ⟨0, le_rfl, hT⟩ = v ⟨0, le_rfl, hT⟩)
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (u
            ⟨t, ht.1.le, ht.2.le⟩))) t)
    (hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (v
            ⟨t, ht.1.le, ht.2.le⟩))) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction) : u = v := by
  let R := max ‖u‖ ‖v‖
  have huR : ‖u‖ ≤ R := le_max_left _ _
  have hvR : ‖v‖ ≤ R := le_max_right _ _
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
    have he0 : e 0=0 := by rw [hev ⟨0,le_rfl,hT⟩,hi,sub_self]; rfl
    simp only [E,he0,map_zero,inner_zero_left,le_refl]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt E (deriv E t) t := by
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have he' := inviscid_difference_hasDerivAt period hq T hT D u v hu hv t ht
    have hs : ∀ a b, ⟪K t a,b⟫_ℝ=⟪a,K t b⟫_ℝ := by
      rw [hKv τ]
      exact coefficientOperator_inner_swap (B.metric τ).coefficient (B.metric τ).measurable
        (B.metric τ).bound (B.metric τ).norm_bound (B.symmetric τ)
    have hd := metric_energy_hasDerivAt K e t (extendPath T hT B.derivative t)
      (differenceRhs period D hq 0 0 τ (u τ) (v τ)) (B.hasDeriv t ht) he' hs
    exact hd.differentiableAt.hasDerivAt
  have hineq (t : ℝ) (ht : t ∈ Ioo 0 T) :
      deriv E t ≤ B.growth period R*E t+0 := by
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := inviscid_difference_hasDerivAt period hq T hT D u v hu hv t ht
    have htime : ‖extendPath T hT B.derivative t‖ ≤ B.time := by
      change ‖B.derivative (projIcc 0 T hT t)‖ ≤ _
      exact B.time_le _
    have hb := difference_metric_deriv_bound period D hq τ (u τ) (v τ) (B.metric τ) K e t 0 0
      B.c B.bound B.first B.time B.linear B.quadratic ‖D.approximation‖ R (extendPath T hT
          B.derivative t)
      B.c_pos (by
          norm_num : (0 : ℝ) ≤ 0) (by
              norm_num : (0 : ℝ) ≤ 1) (hKv τ) (hev τ) (B.hasDeriv t ht) hd (B.bound_le τ)
                  (B.first_le τ) htime
      (B.linear_le τ) (B.quadratic_le τ) (D.approximation.norm_coe_le_norm τ)
      ((u.norm_coe_le_norm τ).trans huR) ((v.norm_coe_le_norm τ).trans hvR)
      (B.symmetric τ) (B.coercive τ) (B.inverse τ) (hz τ) (hud τ) (hvd τ)
    simpa only [E,StabilityBudget.growth,sub_self,abs_zero,zero_pow (by
        decide : (2 : ℕ) ≠ 0),mul_zero] using hb
  have hbound := linear_growth_bound E (deriv E) (B.growth period R)
    0 T (B.growth_nonneg period R hR) (le_refl 0) hT hEc.continuousOn hzero hder hineq
  apply ContinuousMap.ext
  intro t
  have hc : B.c^2*‖value period (u t-v t)‖^2 ≤ E t.val := by
    change _ ≤ ⟪K t.val (e t.val),e t.val⟫_ℝ
    rw [hKv t,hev t]
    exact coefficientOperator_coercive (B.metric t).coefficient (B.metric t).measurable
      (B.metric t).bound (B.metric t).norm_bound (B.c^2) (B.coercive t) _
  have heB : E t.val ≤ 0 := by
    simpa only [zero_mul] using hbound t.val t.property
  have hn : ‖value period (u t-v t)‖ = 0 := by
    have hcpos := sq_pos_of_pos B.c_pos
    have hsq : ‖value period (u t-v t)‖^2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hcpos).mp (by simpa only [mul_zero] using hc.trans heB)
    exact (sq_nonpos_iff _).mp hsq
  apply value_injective period
  exact sub_eq_zero.mp (show value period (u t)-value period (v t)=0 from norm_eq_zero.mp hn)

end EulerInviscidCorrectionUniqueness
