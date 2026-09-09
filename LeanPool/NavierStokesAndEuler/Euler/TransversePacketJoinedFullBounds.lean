/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedCorrectorBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget

@[expose] public section

/-!
# The complete quantitative forced transverse provider

Source-only budgets fixed before the forcing give actual A, A_t, π, dπ,
Q, Q_t, C and C_t bounds linear in its amplitude. All eight outputs use the
same external radius and fixed mixed Sobolev order. They spend at most four
derivative shifts, within the manuscript's ten-shift allowance.
-/

noncomputable section

namespace EulerTransversePacketJoin.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds
open scoped ContDiff

private theorem standard_norm (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {q : ℕ}
  (L : Budget D τ hτ hτT B (Fin 4) q) (N : NormalBudget D q L.R)

def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*L.commonCost)
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*L.commonCost)
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*L.commonCost)
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*L.commonCost)

variable {raw : VectorField} (G : Forcing P D raw) (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block standardDirection q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ A*majorant L.R d
      n)

include hA hforce

theorem velocity_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+3) n :=
  (L.velocity_bound G standardDirection standard_norm A hA d hforce n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem derivative_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+3) n :=
  (L.derivative_bound G standardDirection standard_norm A hA d hforce n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B G))) n 0 ≤
        (L.pressureAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) j 0 ≤ A*majorant L.R
        (d+3) j :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+3) j (by omega)) hA)
  have h := source_pressure_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    standardDirection standard_norm q N.Rc N.C N.C N.Ri L.R A (L.commonCost*A)
    N.Rc_nonneg N.C_nonneg N.C_nonneg hA (mul_nonneg L.commonCost_nonneg hA)
    N.inverse_radius N.pressure_radius N.normal_bound N.strain_bound (d+3) hf
    (L.velocity_common_bound G A hA d hforce) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)

theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (scalarGradientField τ hτ hτT B G).path)) n 0 ≤
        (3*L.pressureAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have h := scalarGradientField_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q L.R (L.pressureAmplitude (P := P) N*A) (d+3) (L.pressure_bound N G A hA d hforce) n
  simpa only [show d+3+1=d+4 by omega,mul_assoc] using h

theorem potential_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialPath τ hτ hτT B G))) n 0 ≤
        (L.potentialAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialPath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (fun j a => (hc.2.2 j a).2.2.1) n
  exact h.trans_eq (by unfold potentialAmplitude NormalBudget.blockAmplitude; ring)

theorem potential_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialTimePath τ hτ hτT B G))) n 0 ≤
        (L.potentialTimeAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialTimePath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (L.derivative_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2) n
  exact h.trans_eq (by unfold potentialTimeAmplitude NormalBudget.blockAmplitude; ring)

theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorPath τ hτ hτT B G))) n 0 ≤
        (L.correctorAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorPath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorAmplitude NormalBudget.blockAmplitude; ring)

theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorTimePath τ hτ hτT B G))) n 0 ≤
        (L.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorTimePath_normalized_bound τ hτ hτT B G L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+3)
    (L.velocity_common_bound G A hA d hforce) (L.derivative_common_bound G A hA d hforce)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorTimeAmplitude NormalBudget.blockAmplitude; ring)

end EulerTransversePacketJoin.Budget
