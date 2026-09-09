/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardNorms
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradientBounds

@[expose] public section

/-!
All eight genuine direct-forward outputs obey one fixed mixed-word Sobolev
budget.  The input radius is retained, both data amplitudes remain outside
the solve, and at most two derivative shifts are spent.  All normalization
uses the literal positive time profile without differentiating that profile.
-/

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds
open scoped ContDiff

private theorem standard_norm (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {q : ℕ} (L : Budget D (Fin 4) q)
  (N : EulerTransversePacketJoin.NormalBudget D q L.R)

def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*L.commonCost)
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*L.commonCost)
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*L.commonCost)
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*L.commonCost)

variable {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block standardDirection q (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ A*majorant L.R d n)
  (hinitial : ∀ n, block standardDirection q
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ A*majorant L.R d n)

include hA hforce hinitial

theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.pressurePath I))) n 0 ≤
        (L.pressureAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hf (j : ℕ) : block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) j 0 ≤ A*majorant L.R (d+1) j :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_one d (d+1) j (by omega)) hA)
  rw [G.pressurePath_normalized_eq_source I L.g L.positive]
  have h := sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    _ _ standardDirection standard_norm q
    (EulerCylinderPotential.weighted_orbit P (reciprocal L.g L.positive) _ G.path_orbit)
    (EulerCylinderPotential.weighted_orbit P (reciprocal L.g L.positive) _ (G.velocityPath_orbit I))
    N.Rc N.C N.C N.Ri L.R A (L.commonCost*A) N.Rc_nonneg N.C_nonneg N.C_nonneg hA
    (mul_nonneg L.commonCost_nonneg hA) N.inverse_radius N.pressure_radius
    N.normal_bound N.strain_bound (d+1) hf
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)

theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.scalarGradientField I).path)) n 0 ≤
        (3*L.pressureAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have h := G.scalarGradientField_normalized_bound I L.g L.positive q L.R
    (L.pressureAmplitude (P := P) N*A) (d+1) (L.pressure_bound N G I A hA d hforce hinitial) n
  simpa only [show d+1+1=d+2 by omega,mul_assoc] using h

theorem potential_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.potentialPath I))) n 0 ≤
        (L.potentialAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hc := N.coefficient_bounds
  have h := G.potentialPath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) n
  exact h.trans_eq (by unfold potentialAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem potential_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.potentialTimePath I))) n 0 ≤
        (L.potentialTimeAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hc := N.coefficient_bounds
  have h := G.potentialTimePath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (L.derivative_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2) n
  exact h.trans_eq (by unfold potentialTimeAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.correctorPath I))) n 0 ≤
        (L.correctorAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have hc := N.coefficient_bounds
  have h := G.correctorPath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+1+1=d+2 by omega] at h
  exact h.trans_eq (by unfold correctorAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.correctorTimePath I))) n 0 ≤
        (L.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have hc := N.coefficient_bounds
  have h := G.correctorTimePath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (L.derivative_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+1+1=d+2 by omega] at h
  exact h.trans_eq (by unfold correctorTimeAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

end EulerTransversePacketForward.Budget
