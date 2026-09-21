/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.LinearPMapSpectralDescent
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.UnitaryTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# The reducing restriction commutes with complexification

The block of a complexified real partial map on a complexified real reducing
subspace is, through the canonical coordinate change
`complexifySubmoduleEquiv`, the complexification of the real block.

This is the transport a real unbounded perturbation theorem needs when it wants
to run its complex counterpart on complexified data and read the conclusion back:
the printed spectral placements are statements about `realSpectrum` of the two
blocks, and `realSpectrum_reducingRestriction_complexifyReal` says the placement
survives the passage unchanged.
-/

open scoped InnerProductSpace
open TauCeti.RealComplexification

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- **The complexified block is the block of the complexification.** -/
theorem unitaryConj_complexifyReal_reducingRestriction
    {A : E →ₗ.[ℝ] E} {P : Submodule ℝ E} [P.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hredC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P)) :
    TauCeti.LinearPMap.unitaryConj (complexifySubmoduleEquiv P)
        (TauCeti.LinearPMap.complexifyReal
          (TauCeti.LinearPMap.reducingRestriction A P hred))
      = TauCeti.LinearPMap.reducingRestriction
          (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P) hredC := by
  refine LinearPMap.ext ?_ ?_
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2⟩
  · intro x y hxy
    rfl

omit [CompleteSpace E] in
/-- **The printed spectral placement survives complexification.** -/
theorem realSpectrum_reducingRestriction_complexifyReal
    {A : E →ₗ.[ℝ] E} {P : Submodule ℝ E} [P.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hredC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P)) :
    TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction
          (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P) hredC)
      = TauCeti.LinearPMap.realSpectrum
          (TauCeti.LinearPMap.reducingRestriction A P hred) := by
  rw [← unitaryConj_complexifyReal_reducingRestriction hred hredC,
    TauCeti.LinearPMap.realSpectrum_unitaryConj,
    TauCeti.LinearPMap.realSpectrum_complexifyReal]

omit [CompleteSpace E] in
/-- The same, for a subspace merely *presented* as a complexification.  The
equation is on a variable so that `subst` handles it; that is what lets a caller
use `(complexifySubmodule Q)ᗮ` without transporting a partial map along an
equality of submodules. -/
theorem realSpectrum_reducingRestriction_complexifyReal_of_eq
    {A : E →ₗ.[ℝ] E} {P : Submodule ℝ E} [P.HasOrthogonalProjection]
    {W : Submodule ℂ (TauCeti.RealComplexification E)} [W.HasOrthogonalProjection]
    (hW : W = complexifySubmodule P)
    (hred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hredC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) W) :
    TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction
          (TauCeti.LinearPMap.complexifyReal A) W hredC)
      = TauCeti.LinearPMap.realSpectrum
          (TauCeti.LinearPMap.reducingRestriction A P hred) := by
  subst hW
  exact realSpectrum_reducingRestriction_complexifyReal hred hredC

omit [CompleteSpace E] in
/-- **The residual norm survives complexification.** -/
theorem norm_complexify_comp_subtypeL (T : E →L[ℝ] E) (P : Submodule ℝ E)
    [P.HasOrthogonalProjection] [CompleteSpace P]
    [CompleteSpace (complexifySubmodule P)] :
    ‖TauCeti.RealComplexification.complexify T ∘L
        ((complexifySubmodule P).subtypeL :
          complexifySubmodule P →L[ℂ] TauCeti.RealComplexification E)‖
      = ‖T ∘L (P.subtypeL : P →L[ℝ] E)‖ := by
  rw [TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection,
    TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection,
    starProjection_complexifySubmodule,
    ← TauCeti.RealComplexification.complexify_comp,
    TauCeti.RealComplexification.norm_complexify]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Separability survives complexification.**

The complexification is `WithLp 2 (E × E)`, homeomorphic to the product; a
separable metric space is second countable, the product of two second countable
spaces is, and a second countable space is separable. -/
theorem separableSpace_realComplexification
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (TauCeti.RealComplexification E) := by
  let _ : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  let _ : SecondCountableTopology (TauCeti.RealComplexification E) :=
    (WithLp.homeomorphProd 2 E E).secondCountableTopology
  infer_instance

end

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
