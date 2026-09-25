/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.FormBoundedGap
public import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded

/-!
# Bounded homogeneous Sylvester uniqueness

A bounded domain-compatible intertwiner between separated self-adjoint closed
operators vanishes.  The proof is deliberately short: every bounded operator
belongs to the operator-norm ideal, so the already established sharp
Davis--Kahan Sylvester estimate applies to the homogeneous equation and gives
`delta * ‖X‖ <= 0`.

This is the uniqueness seam needed by the defect-first Hilbert--Schmidt proof.
It avoids first assuming that the unknown bounded solution belongs to the
square ideal.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

section Complex

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded homogeneous complex Sylvester solution vanishes under any of the
three source gap configurations. -/
theorem closedSylvester_homogeneous_eq_zero_complex
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  let N := KyFanDominantIdealFamily.operatorNorm (𝕜 := ℂ)
  have hzero : N.Mem (0 : F →L[ℂ] E) := by
    rw [FanDominantIdealFamily.mem_iff]
    simp [N]
  have hbound :=
    (davisKahan1970_sylvester_complex N hA hB hδ hgap hEq hzero).2
  change δ * ‖X‖ ≤ ‖(0 : F →L[ℂ] E)‖ at hbound
  have hle : ‖X‖ ≤ 0 := by
    -- The bound is against the norm of zero, which the arithmetic tactics do not
    -- reduce, and the product of the gap with the norm is nonlinear in any case.
    rw [norm_zero] at hbound
    by_contra hpos
    push Not at hpos
    exact absurd hbound (not_le.mpr (mul_pos hδ hpos))
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg X))

/-- Two bounded complex solutions of the same separated closed Sylvester
equation coincide. -/
theorem closedSylvester_solution_unique_complex
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y := by
  have hsub : TauCeti.LinearPMap.SylvesterEquation A B (X - Y) 0 := by
    simpa using hX.sub hY
  have hz := closedSylvester_homogeneous_eq_zero_complex
    hA hB hδ hgap hsub
  exact sub_eq_zero.mp hz

end Complex

section Real

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A bounded homogeneous real Sylvester solution vanishes under any of the
three source gap configurations. -/
theorem closedSylvester_homogeneous_eq_zero_real
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  let N := KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)
  have hzero : N.Mem (0 : F →L[ℝ] E) := by
    rw [FanDominantIdealFamily.mem_iff]
    simp [N]
  have hbound :=
    (davisKahan1970_sylvester_real N hA hB hδ hgap hEq hzero).2
  change δ * ‖X‖ ≤ ‖(0 : F →L[ℝ] E)‖ at hbound
  have hle : ‖X‖ ≤ 0 := by
    -- The bound is against the norm of zero, which the arithmetic tactics do not
    -- reduce, and the product of the gap with the norm is nonlinear in any case.
    rw [norm_zero] at hbound
    by_contra hpos
    push Not at hpos
    exact absurd hbound (not_le.mpr (mul_pos hδ hpos))
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg X))

/-- Two bounded real solutions of the same separated closed Sylvester equation
coincide. -/
theorem closedSylvester_solution_unique_real
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y := by
  have hsub : TauCeti.LinearPMap.SylvesterEquation A B (X - Y) 0 := by
    simpa using hX.sub hY
  have hz := closedSylvester_homogeneous_eq_zero_real
    hA hB hδ hgap hsub
  exact sub_eq_zero.mp hz

end Real

end

end Sylvester
end DavisKahan
end TauCeti
