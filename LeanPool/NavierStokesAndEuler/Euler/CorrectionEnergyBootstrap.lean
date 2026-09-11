/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionMildEnergy
import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyScalar
import Mathlib.Algebra.Order.Star.Real

/-! The actual nonlinear viscous correction closes its shrinking-radius Gevrey bootstrap from the
constructed mild equation. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionEnergyBootstrap

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerCorrectionMildEnergy
      EulerCorrectionEnergyScalar
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerTimeLp EulerVolterraConvolution
      EulerSobolevHeat
  EulerIntegralEnergyBootstrap
open scoped Topology

/-- Increasing the single scalar coefficient preserves the signed radius term in the genuine energy
estimate. -/
theorem raise_energy_constant (C0 C X Y r b R B : ℝ) (hC : C0 ≤ C)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr : 0 ≤ r) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    C0*(X+X^2+r)+(b+C0*R*(B+X))*Y ≤ C*(X+X^2+r)+(b+C*R*(B+X))*Y := by
  have h1 := mul_le_mul_of_nonneg_right hC (add_nonneg (add_nonneg hX (sq_nonneg X)) hr)
  have h2 := mul_le_mul_of_nonneg_right hC (mul_nonneg (mul_nonneg hR (add_nonneg hB hX)) hY)
  nlinarith only [h1,h2]

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual zero-initial nonlinear correction mild solution satisfies the closed Gevrey
estimate.
The proof derives its full-order all-subinterval energy inequality, source bound, pressure
cancellation, and maximal regularity rather than assuming them. -/
theorem correction_mild_bootstrap {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (S : SpatialBudget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period T hT D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period S K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 < ρ0)
    (hdecay : 2 * C * (S.B0 + Δ) * T ≤ ρ0 / 2) (hscale : ρ0 * S.Rc ≤ 1)
    (hsmall : 2 * S.residual * Real.exp (3 * C * T) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (S.B0 + Δ) * t.val)
    (hRdot : ∀ t, Rdot t = -2 * C * (S.B0 + Δ))
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      e t = heatOperator period (q+1) (2*ν*t.val).toNNReal 0 +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e)
              (t.val-r)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∀ t : Icc (0 : ℝ) T,
      energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ 2*S.residual*Real.exp
          (3*C*t.val) ∧
      energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ Δ/2 := by
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  let A := correctionRhs period S hN K Rdot e
  have hCp : 0 < C := (combinedConstant_pos period S K).trans_le hC
  have hRd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t := by
    intro t ht
    exact affine_radius_derivative T hT R Rdot ρ0 (2*C*(S.B0+Δ)) hR
      (fun τ => (hRdot τ).trans (by ring)) t ht
  have hinit : extendPath T hT X 0 ≤ 2*S.residual := by
    have he0 := zero_mild_trace period ν hν T hT
      (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e) e hsol
    change X (projIcc 0 T hT 0) ≤ _
    rw [projIcc_of_mem hT ⟨le_rfl,hT⟩]
    change energyPath period N hN T R (K.operatorPath period) e ⟨0,le_rfl,hT⟩ ≤ _
    rw [energyPath_apply,he0,energyNorm_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) S.residual_pos.le
  have hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t →
      extendPath T hT X t-extendPath T hT X s ≤ ∫ r in s..t, extendPath T hT A r := by
    intro s hs t ht hst
    have h := correction_mild_integral period hq T hT D KG KL KQ hGq hLq hQq hG N hN R Rdot S K hRd
      ν hν hν1 0 e hsol hz he s t hs.1 hst ht.2
    change X (projIcc 0 T hT t)-X (projIcc 0 T hT s) ≤ _
    rw [projIcc_of_mem hT ht,projIcc_of_mem hT hs]
    exact h
  have hineq : ∀ t ∈ Ico (0 : ℝ) T,
      extendPath T hT A t ≤ C*(extendPath T hT X t+(extendPath T hT X t)^2+S.residual) +
        ((-2*C*(S.B0+Δ))/(ρ0-2*C*(S.B0+Δ)*t) +
          C*((ρ0-2*C*(S.B0+Δ)*t)⁻¹+S.Rc)*(S.B0+extendPath T hT X t))*extendPath T hT Y t := by
    intro t ht
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1,ht.2.le⟩
    have h := correctionRhs_bound period S hN K Rdot e τ
    have h' := raise_energy_constant (combinedConstant period S K) C (X τ) (Y τ) S.residual
      (Rdot τ/R τ) ((R τ)⁻¹+S.Rc) S.B0 hC (energy_nonneg period S hN K e τ)
      (loss_nonneg period S hN K e τ) S.residual_pos.le
      (add_nonneg (inv_nonneg.mpr (S.radius_pos τ).le) S.Rc_nonneg) S.B0_nonneg
    have hh := h.trans h'
    change A (projIcc 0 T hT t) ≤ C*(X (projIcc 0 T hT t)+(X (projIcc 0 T hT t))^2+S.residual) +
      ((-2*C*(S.B0+Δ))/(ρ0-2*C*(S.B0+Δ)*t)+C*((ρ0-2*C*(S.B0+Δ)*t)⁻¹+S.Rc) *
        (S.B0+X (projIcc 0 T hT t)))*Y (projIcc 0 T hT t)
    rw [projIcc_of_mem hT ⟨ht.1,ht.2.le⟩]
    simpa only [hR τ,hRdot τ] using hh
  have hclosed := close_integral_energy_estimate (extendPath T hT X) (extendPath T hT A)
      (extendPath T hT Y)
    C S.B0 Δ S.residual ρ0 T S.Rc hCp S.B0_nonneg hΔ hΔ1 S.residual_pos hρ0 hT S.Rc_nonneg hdecay
        hscale hsmall
    (extendPath_continuous T hT X).continuousOn (extendPath_continuous T hT A).continuousOn hinit
        hint
    (fun t _ => loss_nonneg period S hN K e (projIcc 0 T hT t)) hineq
  intro t
  have h := hclosed t.val t.property
  change X (projIcc 0 T hT t.val) ≤ _ ∧ X (projIcc 0 T hT t.val) ≤ _ at h
  rw [projIcc_of_mem hT t.property] at h
  simpa only [X,energyPath_apply] using h

end EulerCorrectionEnergyBootstrap
