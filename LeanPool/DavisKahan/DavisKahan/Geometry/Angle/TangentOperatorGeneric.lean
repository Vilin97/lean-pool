/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleGeneric
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TanAngleFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# Tangent angle operators over an arbitrary `RCLike` field

The sine/angle API is already scalar-generic.  Tangent had remained split into
real and complex files because `tan` is not continuous at its poles.  This file
puts the *objects* back at the generic level and makes the continuity domain
explicit in the transport lemmas.

The definitions themselves use Mathlib's total `Real.tan`, just as the existing
fixed-field objects do.  The theorems that identify and transport them require
exactly the source-side pole exclusion that says the displayed tangent exists.
Thus no scalar-specific proof capability leaks into a public theorem.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

noncomputable section

universe u w v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The ambient `tan Θ` at an arbitrary `RCLike` field. -/
def tanAngleOperator : E →L[𝕜] E :=
  cfc Real.tan (angleOperator U V)

/-- The ambient `tan 2Θ` at an arbitrary `RCLike` field. -/
def tanTwoAngleOperator : E →L[𝕜] E :=
  cfc (fun t : ℝ => Real.tan (2 * t)) (angleOperator U V)

/-- The branch-free ambient `|tan 2Θ|` at an arbitrary `RCLike` field. -/
def absTanTwoAngleOperator : E →L[𝕜] E :=
  cfc (fun t : ℝ => |Real.tan (2 * t)|) (angleOperator U V)

/-- The source's definedness condition for the single-angle tangent: no
principal angle reaches `π/2`. -/
def HasDefinedTangent : Prop := U.projectionGap V < 1

/-- The source's pole-exclusion condition for the double-angle tangent. -/
def HasDefinedDoubleTangent : Prop :=
  ∀ t ∈ spectrum ℝ (angleOperator U V), Real.cos (2 * t) ≠ 0

/-- `tan Θ` is self-adjoint whenever its functional calculus is meaningful. -/
theorem isSelfAdjoint_tanAngleOperator : IsSelfAdjoint (tanAngleOperator U V) :=
  cfc_predicate _ (angleOperator U V)

/-- `tan 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_tanTwoAngleOperator : IsSelfAdjoint (tanTwoAngleOperator U V) :=
  cfc_predicate _ (angleOperator U V)

/-- `|tan 2Θ|` is self-adjoint. -/
theorem isSelfAdjoint_absTanTwoAngleOperator : IsSelfAdjoint (absTanTwoAngleOperator U V) :=
  cfc_predicate _ (angleOperator U V)

/-- Under `‖sin Θ‖ < 1`, every angle lies strictly below `π/2`.

This is the scalar-generic form of `spectrum_angleOperatorC_lt_pi_div_two`; its
proof uses only the generic real functional calculus. -/
theorem spectrum_angleOperator_lt_pi_div_two
    (h : HasDefinedTangent U V) {t : ℝ}
    (ht : t ∈ spectrum ℝ (angleOperator U V)) : 0 ≤ t ∧ t < Real.pi / 2 := by
  rw [angleOperator,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := sinAngleOperator U V) (isSelfAdjoint_sinAngleOperator U V)
      Real.continuous_arcsin.continuousOn] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hsi : 0 ≤ s ∧ s ≤ 1 := by
    have hsnonneg := (StarOrderedRing.nonneg_iff_spectrum_nonneg
      (R := ℝ) _ (isSelfAdjoint_sinAngleOperator U V)).mp
        (sinAngleOperator_nonneg U V) s hs
    have hnormK : ‖((s : 𝕜))‖ ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ :=
      spectrum.norm_le_norm_mul_of_mem hs
    have hnorm : |s| ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := by
      rwa [RCLike.norm_ofReal] at hnormK
    have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hsle : s ≤ 1 := by
      have habs : |s| ≤ ‖sinAngleOperator U V‖ := by
        calc
          |s| ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := hnorm
          _ ≤ ‖sinAngleOperator U V‖ * 1 :=
            mul_le_mul_of_nonneg_left hone (norm_nonneg _)
          _ = ‖sinAngleOperator U V‖ := mul_one _
      have hsin : ‖sinAngleOperator U V‖ < 1 := by
        rw [norm_sinAngleOperator]
        exact h
      exact ((le_abs_self s).trans habs).trans (le_of_lt hsin)
    exact ⟨hsnonneg, hsle⟩
  have hnormK : ‖((s : 𝕜))‖ ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hs
  have hnorm : |s| ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := by
    rwa [RCLike.norm_ofReal] at hnormK
  have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hslt : s < 1 := by
    have habs : |s| ≤ ‖sinAngleOperator U V‖ := by
      calc
        |s| ≤ ‖sinAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := hnorm
        _ ≤ ‖sinAngleOperator U V‖ * 1 :=
          mul_le_mul_of_nonneg_left hone (norm_nonneg _)
        _ = ‖sinAngleOperator U V‖ := mul_one _
    have hsle : s ≤ ‖sinAngleOperator U V‖ := (le_abs_self s).trans habs
    have hsin : ‖sinAngleOperator U V‖ < 1 := by
      rw [norm_sinAngleOperator]
      exact h
    exact hsle.trans_lt hsin
  exact ⟨Real.arcsin_nonneg.mpr hsi.1, Real.arcsin_lt_pi_div_two.mpr hslt⟩

/-- A defined single-angle tangent makes `tan` continuous on the angle spectrum. -/
theorem continuousOn_tan_spectrum (h : HasDefinedTangent U V) :
    ContinuousOn Real.tan (spectrum ℝ (angleOperator U V)) := by
  exact Real.continuousOn_tan.mono (by
    intro t ht
    obtain ⟨ht0, ht2⟩ := spectrum_angleOperator_lt_pi_div_two U V h ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht0], ht2⟩))

/-- A strict ambient `sin 2Θ` contraction excludes every quarter-turn pole.

This is the scalar-generic converse companion to the fixed-field lemma that pole
exclusion makes the double-angle sine a strict contraction.  It is useful when
a real proof naturally controls approximation number zero rather than the angle
spectrum directly. -/
theorem hasDefinedDoubleTangent_of_norm_sinTwoAngleOperator_lt_one
    (h : ‖sinTwoAngleOperator U V‖ < 1) : HasDefinedDoubleTangent U V := by
  intro t ht hcos
  have hs : Real.sin (2 * t) ∈ spectrum ℝ (sinTwoAngleOperator U V) := by
    rw [sinTwoAngleOperator,
      cfc_map_spectrum (R := ℝ) (f := fun s : ℝ => Real.sin (2 * s))
        (a := angleOperator U V) (isSelfAdjoint_angleOperator U V)
        (by fun_prop : ContinuousOn (fun s : ℝ => Real.sin (2 * s)) _)]
    exact ⟨t, ht, rfl⟩
  have hspec : |Real.sin (2 * t)| ≤ ‖sinTwoAngleOperator U V‖ := by
    have h0K : ‖((Real.sin (2 * t) : 𝕜))‖ ≤
        ‖sinTwoAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ :=
      spectrum.norm_le_norm_mul_of_mem hs
    have h0 : |Real.sin (2 * t)| ≤
        ‖sinTwoAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := by
      rwa [RCLike.norm_ofReal] at h0K
    have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc
      |Real.sin (2 * t)|
          ≤ ‖sinTwoAngleOperator U V‖ * ‖(1 : E →L[𝕜] E)‖ := h0
      _ ≤ ‖sinTwoAngleOperator U V‖ * 1 :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖sinTwoAngleOperator U V‖ := mul_one _
  have hpyth := Real.sin_sq_add_cos_sq (2 * t)
  rw [hcos] at hpyth
  norm_num at hpyth
  have habs : |Real.sin (2 * t)| = 1 := by
    rcases hpyth with hsin | hsin <;> rw [hsin] <;> norm_num
  rw [habs] at hspec
  exact (not_le_of_gt h) hspec

/-- Pole exclusion makes the branch-free doubled tangent continuous on the angle spectrum. -/
theorem continuousOn_absTanTwo_spectrum (h : HasDefinedDoubleTangent U V) :
    ContinuousOn (fun t : ℝ => |Real.tan (2 * t)|)
      (spectrum ℝ (angleOperator U V)) := by
  refine ContinuousOn.abs (Real.continuousOn_tan.comp (by fun_prop) ?_)
  intro t ht
  exact h t ht

/-! ## Fixed-field identifications -/

section Complex
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U V : Submodule ℂ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

@[simp] theorem tanAngleOperator_complex : tanAngleOperator U V = tanAngleOperatorC U V := rfl
@[simp] theorem tanTwoAngleOperator_complex : tanTwoAngleOperator U V = tanTwoAngleOperatorC U V := rfl
@[simp] theorem absTanTwoAngleOperator_complex :
    absTanTwoAngleOperator U V = absTanTwoAngleOperatorC U V := rfl
end Complex

section Real
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (U V : Submodule ℝ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- On its source-defined domain, the generic real tangent is the existing descended tangent. -/
theorem tanAngleOperator_real (h : HasDefinedTangent U V) :
    tanAngleOperator U V = tanAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_tanAngleOperatorR]
  change complexify (cfc Real.tan (angleOperator U V)) = _
  rw [complexify_cfc Real.tan (isSelfAdjoint_angleOperator U V)
      (continuousOn_tan_spectrum U V h), angleOperator_real, complexify_angleOperatorR]
  rfl

/-- Under pole exclusion, the generic real branch-free double tangent is the existing one. -/
theorem absTanTwoAngleOperator_real (h : HasDefinedDoubleTangent U V) :
    absTanTwoAngleOperator U V = absTanTwoAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_absTanTwoAngleOperatorR]
  change complexify (cfc (fun t : ℝ => |Real.tan (2 * t)|) (angleOperator U V)) = _
  rw [complexify_cfc _ (isSelfAdjoint_angleOperator U V)
      (continuousOn_absTanTwo_spectrum U V h), angleOperator_real, complexify_angleOperatorR]
  rfl
end Real

/-! ## Scalar transport -/

section Transport
variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
open TauCeti.ScalarTransport

/-- Definedness of `tan Θ` is invariant under scalar transport. -/
theorem hasDefinedTangent_submodule :
    HasDefinedTangent (submodule (e := e) U) (submodule (e := e) V) ↔
      HasDefinedTangent U V := by
  unfold HasDefinedTangent
  rw [← norm_sinAngleOperator (submodule (e := e) U) (submodule (e := e) V),
    ← norm_sinAngleOperator U V, ← clm_sinAngleOperator (e := e) U V, clm_norm]

/-- Scalar transport carries `tan Θ` on the domain where the tangent exists. -/
theorem clm_tanAngleOperator (h : HasDefinedTangent U V) :
    clm (e := e) (tanAngleOperator U V) =
      tanAngleOperator (submodule (e := e) U) (submodule (e := e) V) := by
  change clm (e := e) (cfc Real.tan (angleOperator U V)) = _
  rw [clm_cfc Real.tan (isSelfAdjoint_angleOperator U V)
      (continuousOn_tan_spectrum U V h), clm_angleOperator]
  rfl

/-- Double-tangent pole exclusion is invariant under scalar transport. -/
theorem hasDefinedDoubleTangent_submodule :
    HasDefinedDoubleTangent (submodule (e := e) U) (submodule (e := e) V) ↔
      HasDefinedDoubleTangent U V := by
  unfold HasDefinedDoubleTangent
  rw [← clm_angleOperator (e := e) U V, ScalarTransport.spectrum_clm]

/-- Scalar transport carries the branch-free doubled tangent once the pole is excluded. -/
theorem clm_absTanTwoAngleOperator (h : HasDefinedDoubleTangent U V) :
    clm (e := e) (absTanTwoAngleOperator U V) =
      absTanTwoAngleOperator (submodule (e := e) U) (submodule (e := e) V) := by
  change clm (e := e) (cfc (fun t : ℝ => |Real.tan (2 * t)|) (angleOperator U V)) = _
  rw [clm_cfc _ (isSelfAdjoint_angleOperator U V)
      (continuousOn_absTanTwo_spectrum U V h), clm_angleOperator]
  rfl

end Transport

end
end DavisKahan.Angle
end TauCeti
