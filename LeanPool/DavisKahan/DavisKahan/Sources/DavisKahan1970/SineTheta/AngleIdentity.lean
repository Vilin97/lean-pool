/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngleReal

/-! # Angle Identity -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Equality of the cosine-defined and sine-defined directed angles

Davis and Kahan define the directed angle from the positive cosine overlap.
A modern projection formulation often starts from the positive complementary
sine modulus.  On the canonical range `[0, pi/2]` these are not merely
operators with matching singular data: functional calculus shows that they
produce exactly the same angle operator.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded operators on a subspace coordinate space, as a C⋆-algebra.

Recording this in the submodule shape is load-bearing: the functional-calculus
search does not find the C⋆-algebra structure on `↥U →L[ℂ] ↥U` by itself.  See
the companion instance in `PaperCosineAngle`. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateAngleIdentity
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

/-- The source cosine-defined directed angle has spectrum in `[0, pi/2]`. -/
theorem spectrum_directedAngleBlockC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (directedAngleBlockC U V) ⊆
      Set.Icc 0 (Real.pi / 2) := by
  have hsa : IsSelfAdjoint (cosineBlockModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  intro y hy
  rw [directedAngleBlockC,
    cfc_map_spectrum (R := ℝ) Real.arccos (cosineBlockModulusC U V)
      hsa Real.continuous_arccos.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_cosineBlockModulusC_subset_Icc U V hx
  exact ⟨Real.arccos_nonneg x,
    (Real.arccos_le_pi_div_two).2 hxi.1⟩

/-- The angle reconstructed from the positive sine modulus. -/
noncomputable def sineDefinedDirectedAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection]  : U →L[ℂ] U :=
  cfc Real.arcsin (sineBlockModulusC U V)

/-- The angle reconstructed from the sine modulus is exactly the source
cosine-defined angle. -/
theorem sineDefinedDirectedAngleC_eq_directedAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sineDefinedDirectedAngleC U V = directedAngleBlockC U V := by
  have hangle : IsSelfAdjoint (directedAngleBlockC U V) :=
    cfc_predicate Real.arccos (cosineBlockModulusC U V)
  rw [sineDefinedDirectedAngleC,
    ← directedSinAngleBlockC_eq_sineBlockModulusC U V,
    directedSinAngleBlockC,
    ← cfc_comp Real.arcsin Real.sin (directedAngleBlockC U V)
      hangle Real.continuous_arcsin.continuousOn
      Real.continuous_sin.continuousOn]
  calc
    cfc (Real.arcsin ∘ Real.sin) (directedAngleBlockC U V) =
        cfc (fun x : ℝ => x) (directedAngleBlockC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_directedAngleBlockC_subset_Icc U V hx
      exact Real.arcsin_sin
        (by linarith [hxi.1, Real.pi_pos]) hxi.2
    _ = directedAngleBlockC U V := cfc_id' ℝ _

/-- Equivalent formulation with the source angle on the left. -/
theorem sourceDirectedAngleC_eq_arcsin_sineModulus
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedAngleBlockC U V =
      cfc Real.arcsin (sineBlockModulusC U V) :=
  (sineDefinedDirectedAngleC_eq_directedAngleBlockC U V).symm

section Real

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- For real subspaces, the sine-reconstructed angle on the canonical
complexification equals the source cosine-defined angle.

The right-hand side is written through `sineDefinedDirectedAngleC`, which
is *by definition* `cfc Real.arcsin (sineBlockModulusC ..)`, so this is the same
statement as the spelled-out functional calculus.  Writing it out here would not
elaborate: in statement position there is no way to pin the C⋆-algebra instance
on the complexified subspace coordinates, and the functional-calculus search
does not find it unaided even though the C⋆-algebra structure itself resolves. -/
theorem sourceDirectedAngleR_eq_arcsin_sineModulus
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sourceDirectedAngleR U V =
      sineDefinedDirectedAngleC
        (complexifySubmodule U)
        (complexifySubmodule V) :=
  (sineDefinedDirectedAngleC_eq_directedAngleBlockC _ _).symm

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
