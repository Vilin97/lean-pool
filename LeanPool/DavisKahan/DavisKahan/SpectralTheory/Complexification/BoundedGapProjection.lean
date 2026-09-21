/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Spectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralGapFormBounds
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Complexification.SpectralDescent


/-!
# Real bounded spectral branches across a gap

Mathlib's bounded Borel spectral projection is presently a complex-Hilbert-space
construction in the Davis--Kahan layer.  A real self-adjoint bounded operator
nevertheless has a canonical real spectral branch whenever the selected cut
lies in a genuine spectral gap.

The gap is the important abstraction seam.  On the spectrum, the indicator of
`Iic alpha` agrees with the continuous real-valued `spectralGapSymbol`, so the
bounded spectral projection is a continuous-functional-calculus value.  The
complexification of a real operator is fixed by canonical conjugation; the
real-valued functional calculus is therefore fixed as well.  Taking its real
part descends the *actual bounded spectral projection*, not merely an arbitrary
reducing projection.

The resulting real range complexifies exactly to the complex bounded spectral
subspace.  This is the bridge needed by real forms of Davis--Kahan Section 8,
and it deliberately lives in spectral complexification rather than in the
source theorem.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

open Set
open scoped InnerProductSpace
open TauCeti.RealComplexification
open TauCeti.DavisKahanExt

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]


/-- The complex bounded low spectral projection of a real operator is fixed by
canonical conjugation whenever the cut lies in a spectral gap. -/
theorem conjugateOperator_boundedSelfAdjointSpectralProjection_Iic_complexify
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    conjugateOperator
        (boundedSelfAdjointSpectralProjection (complexify B)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            ((complexify_isSelfAdjoint_iff B).2 hB))
          (Set.Iic alpha) measurableSet_Iic) =
      boundedSelfAdjointSpectralProjection (complexify B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          ((complexify_isSelfAdjoint_iff B).2 hB))
        (Set.Iic alpha) measurableSet_Iic := by
  have hBc : IsSelfAdjoint (complexify B) := (complexify_isSelfAdjoint_iff B).2 hB
  have hBcop : (complexify B).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hBc
  have hgapC : realSpectrum (complexify B) ⊆
      Set.Iic alpha ∪ Set.Ici (alpha + delta) := by
    rw [realSpectrum_complexify]
    exact hgap
  have hconjStar : conjugateOperator (complexify B) = star (complexify B) := by
    rw [conjugateOperator_complexify, hBc.star_eq]
  rw [boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom
    (complexify B) hBcop hdelta hgapC]
  simpa only [TauCeti.BorelCalculus.star_ofRealLM] using
    (TauCeti.LinearPMap.conjugateOperator_cfcHom_of_adjoint
      hBc.isStarNormal hconjStar
      (TauCeti.BorelCalculus.ofRealLM
        (spectralGapSymbol (complexify B) alpha delta)))

/-- The real bounded spectral projection for the lower side of a genuine gap,
obtained by descending the actual complex bounded spectral projection. -/
noncomputable def realBoundedSpectralProjectionIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (_hdelta : 0 < delta)
    (_hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    E →L[ℝ] E :=
  realPartOperator
    (boundedSelfAdjointSpectralProjection (complexify B)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        ((complexify_isSelfAdjoint_iff B).2 hB))
      (Set.Iic alpha) measurableSet_Iic)

/-- Complexifying the descended real gap projection recovers the actual bounded
complex spectral projection. -/
theorem complexify_realBoundedSpectralProjectionIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    complexify (realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap) =
      boundedSelfAdjointSpectralProjection (complexify B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          ((complexify_isSelfAdjoint_iff B).2 hB))
        (Set.Iic alpha) measurableSet_Iic := by
  exact complexify_realPartOperator
    (conjugateOperator_boundedSelfAdjointSpectralProjection_Iic_complexify
      B hB hdelta hgap)

/-- The descended real gap projection is idempotent. -/
theorem realBoundedSpectralProjectionIicOfGap_idem
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap *
        realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap =
      realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap := by
  apply complexify_injective
  rw [complexify_mul,
    complexify_realBoundedSpectralProjectionIicOfGap]
  exact (boundedSelfAdjointSpectralPVM (complexify B)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff B).2 hB))).proj_idem
        (Set.Iic alpha) measurableSet_Iic

/-- The real lower spectral branch selected across the gap. -/
noncomputable def realBoundedSpectralSubspaceIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    Submodule ℝ E :=
  (realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap).range

/-- The descended real gap branch is closed and hence has its orthogonal
projection. -/
noncomputable instance realBoundedSpectralSubspaceIicOfGap_hasOrthogonalProjection
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    (realBoundedSpectralSubspaceIicOfGap B hB alpha delta hdelta hgap).HasOrthogonalProjection := by
  unfold realBoundedSpectralSubspaceIicOfGap
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem
      (realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap) from
        realBoundedSpectralProjectionIicOfGap_idem B hB alpha delta hdelta hgap)

/-- The descended real branch is not merely some real reducing subspace: its
complexification is exactly the genuine bounded complex spectral subspace used
by the Section 8 theorem. -/
theorem complexifySubmodule_realBoundedSpectralSubspaceIicOfGap
    (B : E →L[ℝ] E) (hB : IsSelfAdjoint B)
    (alpha delta : ℝ) (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    complexifySubmodule
        (realBoundedSpectralSubspaceIicOfGap B hB alpha delta hdelta hgap) =
      boundedSelfAdjointSpectralSubspace (complexify B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          ((complexify_isSelfAdjoint_iff B).2 hB))
        (Set.Iic alpha) measurableSet_Iic := by
  change complexifySubmodule
      (LinearMap.range
        (realBoundedSpectralProjectionIicOfGap B hB alpha delta hdelta hgap).toLinearMap) =
    LinearMap.range
      (boundedSelfAdjointSpectralProjection (complexify B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          ((complexify_isSelfAdjoint_iff B).2 hB))
        (Set.Iic alpha) measurableSet_Iic).toLinearMap
  rw [← range_complexify,
    complexify_realBoundedSpectralProjectionIicOfGap]

end

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
