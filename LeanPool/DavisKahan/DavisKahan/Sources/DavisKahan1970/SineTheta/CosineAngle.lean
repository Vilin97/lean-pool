/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.OperatorAngleBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Cosine Angle -/

open TauCeti.DavisKahan.Angle


/-!
# The source definition of the directed Davis--Kahan angle

The paper defines `Theta_0` from the cosine block, not from a previously named
sine block.  If `U` is the trial subspace and `V` is the exact subspace, the
cosine block is the overlap map from `U` to `V`; its positive source modulus is
`cos Theta_0`.  The angle is `arccos (cos Theta_0)` on the coordinate Hilbert
space `U`.

This module keeps the coordinate space explicit.  In particular, it does not
extend the cosine modulus by zero to the ambient orthogonal complement, where
`arccos 0 = pi/2` would create spurious angles.  It then proves that applying
sine to the source-defined angle has the complete singular-value sequence of
the cross projection into `V`'s orthogonal complement.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded operators on a subspace coordinate space, as a C⋆-algebra.

This is `inferInstance`, but stating it in the submodule shape is load-bearing.
Searching for `ContinuousFunctionalCalculus` on `↥U →L[ℂ] ↥U` does not find the
C⋆-algebra structure on its own, even though the very same search succeeds for
an abstract complete complex inner-product space and the C⋆-algebra instance is
found when requested directly.  Recording it here as a local instance lets the
functional calculus below elaborate; without it every `cfc` in this module
fails. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateCosineAngle
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

/-- The overlap block whose singular values are the principal cosines. -/
noncomputable def cosineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] V :=
  V.subtypeL.adjoint ∘L U.subtypeL

/-- The complementary overlap block whose singular values are the directed
principal sines. -/
noncomputable def sineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] Vᗮ :=
  Vᗮ.subtypeL.adjoint ∘L U.subtypeL

/-- The positive cosine operator on the trial coordinate space. -/
noncomputable def cosineBlockModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  ContinuousLinearMap.modulus (cosineBlockC U V)

/-- The positive directed sine modulus on the trial coordinate space. -/
noncomputable def sineBlockModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  ContinuousLinearMap.modulus (sineBlockC U V)

/-- The cosine modulus is a positive contraction. -/
theorem norm_cosineBlockModulusC_le_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosineBlockModulusC U V‖ ≤ 1 := by
  rw [cosineBlockModulusC]
  calc
    ‖ContinuousLinearMap.modulus (cosineBlockC U V)‖ =
        ‖cosineBlockC U V‖ := ContinuousLinearMap.norm_modulus _
    _ ≤ ‖V.subtypeL.adjoint‖ * ‖U.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      have hV : ‖V.subtypeL.adjoint‖ ≤ 1 := by
        rw [Submodule.adjoint_subtypeL]
        exact V.orthogonalProjectionOnto_norm_le
      exact mul_le_mul hV U.norm_subtypeL_le
        (norm_nonneg U.subtypeL) zero_le_one
    _ = 1 := by ring

/-- The real spectrum of the cosine modulus lies in `[0,1]`. -/
theorem spectrum_cosineBlockModulusC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (cosineBlockModulusC U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg
    (ContinuousLinearMap.modulus_nonneg (cosineBlockC U V)) hx, ?_⟩
  -- `spectrum.norm_le_norm_of_mem` would need `NormOneClass`, i.e. `‖id‖ = 1`,
  -- which fails when `U` is the zero subspace.  The `mul` form carries no such
  -- instance, and `norm_id_le` bounds the unit without nontriviality.
  have hone : ‖(1 : ↥U →L[ℂ] ↥U)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habs : ‖x‖ ≤ ‖cosineBlockModulusC U V‖ * ‖(1 : ↥U →L[ℂ] ↥U)‖ :=
    spectrum.norm_le_norm_mul_of_mem hx
  rw [Real.norm_eq_abs] at habs
  refine (le_abs_self x).trans (habs.trans ?_)
  calc
    ‖cosineBlockModulusC U V‖ * ‖(1 : ↥U →L[ℂ] ↥U)‖ ≤ 1 * 1 :=
      mul_le_mul (norm_cosineBlockModulusC_le_one U V) hone
        (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The literal directed angle of Section 1 and Section 6 of the paper. -/
noncomputable def directedAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.arccos (cosineBlockModulusC U V)

/-- The paper's literal `cos Theta_0`. -/
noncomputable def directedCosAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.cos (directedAngleBlockC U V)

/-- The paper's literal `sin Theta_0`. -/
noncomputable def directedSinAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.sin (directedAngleBlockC U V)

/-- Applying cosine to the source-defined angle recovers the overlap modulus. -/
theorem sourceDirectedCosC_eq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedCosAngleBlockC U V = cosineBlockModulusC U V := by
  have hsa : IsSelfAdjoint (cosineBlockModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  rw [directedCosAngleBlockC, directedAngleBlockC,
    ← cfc_comp Real.cos Real.arccos (cosineBlockModulusC U V)
      hsa Real.continuous_cos.continuousOn
      Real.continuous_arccos.continuousOn]
  calc
    cfc (Real.cos ∘ Real.arccos) (cosineBlockModulusC U V) =
        cfc (fun x : ℝ => x) (cosineBlockModulusC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_cosineBlockModulusC_subset_Icc U V hx
      exact Real.cos_arccos (by linarith [hxi.1]) hxi.2
    _ = cosineBlockModulusC U V := cfc_id' ℝ _

/-- Operator Pythagoras on the trial coordinate space. -/
theorem sineBlockModulus_sq_add_cosineBlockModulus_sq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sineBlockModulusC U V * sineBlockModulusC U V +
      cosineBlockModulusC U V * cosineBlockModulusC U V =
        ContinuousLinearMap.id ℂ U := by
  rw [sineBlockModulusC, cosineBlockModulusC,
    ContinuousLinearMap.modulus_mul_self,
    ContinuousLinearMap.modulus_mul_self]
  ext x
  -- The adjoint of a projection onto the subtype is the inclusion.
  have hadjPerp : (Vᗮ.orthogonalProjectionOnto).adjoint = Vᗮ.subtypeL := by
    rw [← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  have hadjV : (V.orthogonalProjectionOnto).adjoint = V.subtypeL := by
    rw [← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  have hsplit : Vᗮ.starProjection (x : E) + V.starProjection (x : E) = (x : E) := by
    simp [add_comm]
  have hUx : U.starProjection (x : E) = (x : E) :=
    Submodule.starProjection_eq_self_iff.mpr x.2
  simp only [sineBlockC, cosineBlockC, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.id_apply, Submodule.adjoint_subtypeL,
    hadjPerp, hadjV, Submodule.coe_add]
  -- Both summands are `U`'s projection of a piece of the `V`/`Vᗮ` splitting.
  change U.starProjection (Vᗮ.starProjection (x : E)) +
      U.starProjection (V.starProjection (x : E)) = (x : E)
  rw [← map_add, hsplit, hUx]
/-- The source-defined sine is the positive square root complementary to the
cosine modulus. -/
theorem directedSinAngleBlockC_eq_sineBlockModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSinAngleBlockC U V = sineBlockModulusC U V := by
  have hsaCos : IsSelfAdjoint (cosineBlockModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  -- The spectrum of the angle is the arccosine image of the modulus spectrum,
  -- by the spectral mapping theorem.
  have hspec : spectrum ℝ (directedAngleBlockC U V) =
      Real.arccos '' spectrum ℝ (cosineBlockModulusC U V) := by
    rw [directedAngleBlockC]
    exact cfc_map_spectrum Real.arccos (cosineBlockModulusC U V) hsaCos
      Real.continuous_arccos.continuousOn
  have hnonneg : 0 ≤ directedSinAngleBlockC U V := by
    rw [directedSinAngleBlockC]
    apply cfc_nonneg
    intro x hx
    rw [hspec] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arccos_nonneg y) (Real.arccos_le_pi y)
  have hsquare :
      directedSinAngleBlockC U V * directedSinAngleBlockC U V =
        (sineBlockC U V).adjoint ∘L sineBlockC U V := by
    rw [directedSinAngleBlockC, ← cfc_mul _ _ _
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn]
    have htrig :
        cfc (fun x : ℝ => Real.sin x * Real.sin x)
            (directedAngleBlockC U V) =
          ContinuousLinearMap.id ℂ U -
            cosineBlockModulusC U V * cosineBlockModulusC U V := by
      have hangle : IsSelfAdjoint (directedAngleBlockC U V) :=
        cfc_predicate Real.arccos (cosineBlockModulusC U V)
      -- Name both functions in eta-expanded form: supplying only the
      -- continuity proofs would pin `g` to `Real.cos * Real.cos`, which does
      -- not match the eta-expanded `fun x => Real.cos x * Real.cos x` in the
      -- goal, and the rewrite would not fire.
      have hcos : cosineBlockModulusC U V * cosineBlockModulusC U V =
          cfc (fun x : ℝ => Real.cos x * Real.cos x)
            (directedAngleBlockC U V) := by
        rw [← sourceDirectedCosC_eq U V, directedCosAngleBlockC]
        exact (cfc_mul Real.cos Real.cos (directedAngleBlockC U V)
          Real.continuous_cos.continuousOn
          Real.continuous_cos.continuousOn).symm
      have hone : (ContinuousLinearMap.id ℂ U) =
          cfc (fun _ : ℝ => (1 : ℝ)) (directedAngleBlockC U V) :=
        (cfc_const_one ℝ (directedAngleBlockC U V) hangle).symm
      have hsplit :
          cfc (fun x : ℝ => (1 : ℝ) - Real.cos x * Real.cos x)
              (directedAngleBlockC U V) =
            cfc (fun _ : ℝ => (1 : ℝ)) (directedAngleBlockC U V) -
              cfc (fun x : ℝ => Real.cos x * Real.cos x)
                (directedAngleBlockC U V) :=
        cfc_sub (fun _ : ℝ => (1 : ℝ))
          (fun x : ℝ => Real.cos x * Real.cos x)
          (directedAngleBlockC U V)
          continuous_const.continuousOn
          (Real.continuous_cos.mul Real.continuous_cos).continuousOn
      rw [hcos, hone, ← hsplit]
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [htrig]
    have hp := sineBlockModulus_sq_add_cosineBlockModulus_sq U V
    have hs := ContinuousLinearMap.modulus_mul_self (sineBlockC U V)
    rw [← hs]
    exact (eq_sub_of_add_eq hp).symm
  show directedSinAngleBlockC U V =
    CFC.sqrt ((sineBlockC U V).adjoint ∘L sineBlockC U V)
  exact (CFC.sqrt_unique hsquare hnonneg).symm

/-- The literal source `sin Theta_0` has exactly the singular values of the
cross projection printed in the paper.

The source sine acts on the trial coordinate space `U` while the cross block
maps `U` into `Vᗮ`, so this is the heterogeneous singular-sequence relation;
`SameApproximationSingularValues` is the special case of it in which the two
operators happen to share a codomain, and cannot be stated here. -/
theorem directedSinAngleBlock_same_sineBlock
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (directedSinAngleBlockC U V) (sineBlockC U V) := by
  rw [directedSinAngleBlockC_eq_sineBlockModulusC]
  exact modulus_hasSameApproximationNumbers _


end

end ExactSinTheta
end DavisKahan
end TauCeti
