/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionMildEnergy
import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation

/-! The actual correction energy right-hand side has the scalar shrinking-radius form, including its
exact zero initial trace. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionEnergyScalar

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
      EulerCorrectionMildEnergy
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerNonlinearEnergyConstants
      EulerTimeLpSubintervalBound
  EulerTimeLp EulerVolterraConvolution EulerSobolevHeat EulerGevreyMetricComparison
      EulerGevreyDifferentiatedEquation
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual scalar correction right-hand side is bounded by the source's nonlinear
shrinking-radius expression. -/
theorem correctionRhs_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 :
        ℝ)
        T) :
    let X := energyPath period N hN T R (K.operatorPath period) e t
    let Y := lossPath period N hN T R (K.operatorPath period) e t
    let C := combinedConstant period S K
    correctionRhs period S hN K Rdot e t ≤ C*(X+X^2+S.residual) +
      (Rdot t/R t+C*((R t)⁻¹+S.Rc)*(S.B0+X))*Y := by
  obtain ⟨hg0,hg1,hk⟩ := K.constants_nonneg period S.B0 S.B0_nonneg
  exact actual_scalar_bound period (K.growth0 period S.B0) (K.growth1 period) (K.multiplier period)
    S.B S.M S.B0 S.B1 S.A0 S.A2 K.c S.Rc (R t) S.residual
    (energyPath period N hN T R (K.operatorPath period) e t)
    (lossPath period N hN T R (K.operatorPath period) e t) (Rdot t/R t)
    hg0 hg1 hk S.B_nonneg (zero_le_one.trans S.M_one_le) S.B0_nonneg S.B1_nonneg S.A0_nonneg
        S.A2_nonneg K.c_pos
    S.Rc_nonneg (S.radius_pos t) S.residual_pos.le (energy_nonneg period S hN K e t) (loss_nonneg
        period S hN K e t)

/-- Zero is exactly zero in the genuine finite metric energy. -/
theorem energyNorm_zero {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) : energyNorm period N hN ρ K (0 : SobolevSpace period
        q) = 0 := by
  unfold energyNorm weightedMetricSum
  apply Finset.sum_eq_zero
  intro I _
  have hzero : energyValues period 6 N hN (0 : SobolevSpace period q) I = fun _ => 0 := by
    funext a
    rw [← energyWordOperator_apply, map_zero]
  rw [hzero]
  simp [familyMetricNorm, familyEnergy]

/-- The actual zero-initial mild formula has zero trace, without a separately assumed initial-value
identity. -/
theorem zero_mild_trace {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q +
        1)))
    (hsol : ∀ t : Icc (0 : ℝ) T, e t = heatOperator period (q+1) (2*ν*t.val).toNNReal 0 +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    e ⟨0,le_rfl,hT⟩ = 0 := by
  have h := hsol ⟨0,le_rfl,hT⟩
  simpa only [map_zero, intervalIntegral.integral_same, add_zero] using h

/-- A prescribed affine radius has its genuine time derivative at every interior point after clamped
extension. -/
theorem affine_radius_derivative (T : ℝ) (hT : 0 ≤ T) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (ρ0 A : ℝ) (hR : ∀ t, R t = ρ0 - A * t.val) (hRdot : ∀ t, Rdot t = -A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t := by
  have hm : HasDerivAt (fun r : ℝ => A*r) A t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul A
  have ha : HasDerivAt (fun r : ℝ => ρ0-A*r) (-A) t := HasDerivAt.const_sub ρ0 hm
  have he : extendPath T hT R =ᶠ[𝓝 t] fun r => ρ0-A*r := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    change R (projIcc 0 T hT r) = _
    rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
    exact hR ⟨r,hr.1.le,hr.2.le⟩
  exact (ha.congr_of_eventuallyEq he).congr_deriv (hRdot (projIcc 0 T hT t)).symm

end EulerCorrectionEnergyScalar
