/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.Proposition35Nonacute
import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.TrigonometricSeries

/-!
# Dimension-free exponential form of the Section 3 direct rotation

This module combines the nonacute polar geometry with the Banach-algebra Euler identity.  For a
chosen completed direct rotation, its paper quarter turn `J` commutes with the bounded operator
angle `Theta` and satisfies `J^2 Theta = -Theta`.  The general functional-calculus Euler theorem
therefore gives

`exp (J Theta) = cos Theta + J sin Theta`,

which is exactly the already established polar resolution of the direct rotation.

No finite-dimensionality, compactness, spectral discreteness, or global identity `J^2 = -1` is
used.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Proposition35

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The real algebra structure on bounded operators obtained by restricting scalars. -/
local instance realAlgebra : Algebra ℝ (H →L[𝕜] H) :=
  ContinuousLinearMap.realAlgebra (𝕜 := 𝕜) (E := H)

local instance realIsScalarTower : IsScalarTower ℝ 𝕜 (H →L[𝕜] H) :=
  ContinuousLinearMap.realIsScalarTower (𝕜 := 𝕜) (E := H)

/-- The operator norm makes the algebra of bounded operators a real normed algebra. -/
local instance realNormedAlgebra : NormedAlgebra ℝ (H →L[𝕜] H) :=
  { realAlgebra with
    norm_smul_le := by
      intro r T
      rw [← IsScalarTower.algebraMap_smul 𝕜]
      simpa using norm_smul_le (algebraMap ℝ 𝕜 r) T }

local instance realContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint :=
  ContinuousLinearMap.continuousFunctionalCalculusReal (𝕜 := 𝕜) (E := H)


variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The operator angle takes values in the polar initial space of the acute skew part. -/
theorem section3AngleOperator_apply_mem_skewPolarInitial
    (hacute : TauCeti.IsAcute U V) (x : H) :
    section3AngleOperator U V x ∈
      (section3DirectRotation U V - section3CosAngleOperator U V).polarInitial := by
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hmod := modulus_section3DirectRotation_sub_cosine U V hacute
  have hkerDsin : LinearMap.ker D.toLinearMap =
      LinearMap.ker (section3SinAngleOperator U V).toLinearMap := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have hz := D.modulus_apply_eq_zero_iff z
    simpa [D, hmod] using hz.symm
  have hkerDtheta : LinearMap.ker D.toLinearMap =
      LinearMap.ker (section3AngleOperator U V).toLinearMap :=
    hkerDsin.trans (ker_section3AngleOperator_eq_ker_sine U V).symm
  rw [D.polarInitial_eq_orthogonal_ker, hkerDtheta]
  have hself : (section3AngleOperator U V).adjoint = section3AngleOperator U V :=
    (section3AngleOperator_isSelfAdjoint U V).adjoint_eq
  have horth : (section3AngleOperator U V).rangeᗮ =
      (section3AngleOperator U V).ker := by
    rw [(section3AngleOperator U V).orthogonal_range, hself]
  have horthEq : (section3AngleOperator U V).kerᗮ =
      (section3AngleOperator U V).range.topologicalClosure := by
    calc
      (section3AngleOperator U V).kerᗮ =
          (section3AngleOperator U V).rangeᗮᗮ := by rw [horth]
      _ = (section3AngleOperator U V).range.topologicalClosure :=
        Submodule.orthogonal_orthogonal_eq_closure _
  rw [horthEq]
  exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- On the support reached by the acute operator angle, the paper quarter turn squares to `-1`. -/
theorem section3QuarterTurn_sq_comp_angleOperator
    (hacute : TauCeti.IsAcute U V) :
    section3QuarterTurn U V ∘L section3QuarterTurn U V ∘L
        section3AngleOperator U V =
      -section3AngleOperator U V := by
  let D := section3DirectRotation U V - section3CosAngleOperator U V
  have hskewStar := star_section3DirectRotation_sub_cosine U V
  have hskew : D.adjoint = -D := by
    simpa [D, ContinuousLinearMap.star_eq_adjoint] using hskewStar
  ext x
  have hx := section3AngleOperator_apply_mem_skewPolarInitial U V hacute x
  have hquarter :=
    ContinuousLinearMap.polarPartial_apply_polarPartial_apply_of_mem_of_adjoint_eq_neg
      (M := D) hskew hx
  simpa [D, section3QuarterTurn, ContinuousLinearMap.comp_apply] using hquarter

/-- The supported Euler identity for the acute paper quarter turn and operator angle. -/
theorem exp_quarterTurn_mul_angleOperator (hacute : TauCeti.IsAcute U V) :
    NormedSpace.exp (section3QuarterTurn U V * section3AngleOperator U V) =
      section3CosAngleOperator U V +
        section3QuarterTurn U V * section3SinAngleOperator U V := by
  have hcomm : Commute (section3QuarterTurn U V) (section3AngleOperator U V) :=
    (section3AngleOperator_comm_quarterTurn U V hacute).symm
  have hsq :
      section3QuarterTurn U V * section3QuarterTurn U V * section3AngleOperator U V =
        -section3AngleOperator U V := by
    rw [mul_assoc]
    simpa only [ContinuousLinearMap.mul_def] using
      section3QuarterTurn_sq_comp_angleOperator U V hacute
  have heuler := exp_mul_eq_cfc_real_cos_add_mul_cfc_real_sin
    (hT := section3AngleOperator_isSelfAdjoint U V) hcomm hsq
  rw [cfc_sin_section3AngleOperator U V] at heuler
  simpa only [section3CosAngleOperator] using heuler

/-- Davis--Kahan's exponential formula for the canonical direct rotation of an acute pair. -/
theorem section3DirectRotation_eq_exp_quarterTurn_mul_angleOperator
    (hacute : TauCeti.IsAcute U V) :
    section3DirectRotation U V =
      NormedSpace.exp (section3QuarterTurn U V * section3AngleOperator U V) := by
  rw [section3DirectRotation_eq_cos_add_quarterTurn_sin U V hacute]
  have hexp := exp_quarterTurn_mul_angleOperator U V hacute
  simpa only [ContinuousLinearMap.mul_def] using hexp.symm

/-- The supported Euler identity for the nonacute paper quarter turn and operator angle. -/
theorem exp_nonacuteQuarterTurn_mul_angleOperator
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    NormedSpace.exp
        (section3NonacuteQuarterTurn U V J * section3AngleOperator U V) =
      section3CosAngleOperator U V +
        section3NonacuteQuarterTurn U V J * section3SinAngleOperator U V := by
  have hcomm : Commute
      (section3NonacuteQuarterTurn U V J) (section3AngleOperator U V) :=
    (section3AngleOperator_comm_nonacuteQuarterTurn U V J).symm
  have hsq :
      section3NonacuteQuarterTurn U V J * section3NonacuteQuarterTurn U V J *
          section3AngleOperator U V =
        -section3AngleOperator U V := by
    rw [mul_assoc]
    simpa only [ContinuousLinearMap.mul_def] using
      section3NonacuteQuarterTurn_sq_comp_angleOperator U V J
  have heuler := exp_mul_eq_cfc_real_cos_add_mul_cfc_real_sin
    (hT := section3AngleOperator_isSelfAdjoint U V) hcomm hsq
  rw [cfc_sin_section3AngleOperator U V] at heuler
  simpa only [section3CosAngleOperator] using heuler

/-- Davis--Kahan's direct-rotation exponential formula for every chosen completed rotation. -/
theorem nonacuteDirectRotation_eq_exp_nonacuteQuarterTurn_mul_angleOperator
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      NormedSpace.exp
        (section3NonacuteQuarterTurn U V J * section3AngleOperator U V) := by
  rw [nonacuteDirectRotation_eq_cos_add_quarterTurn_sin U V J]
  have hexp := exp_nonacuteQuarterTurn_mul_angleOperator U V J
  simpa only [ContinuousLinearMap.mul_def] using hexp.symm

end

end Proposition35
end DavisKahan
end TauCeti
