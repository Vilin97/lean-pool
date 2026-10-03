/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalReverseGap
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Degenerate coordinate blocks in the bounded off-diagonal estimate

The ordered-gap estimate was first proved under nontriviality of both
coordinate Hilbert spaces.  This leaf removes those auxiliary assumptions.
If either the source subspace or its orthogonal complement is subsingleton,
the rectangular angular coordinate is the zero operator and the sharp
contractive Riccati inequality is immediate.  Otherwise the nontrivial
ordered-gap theorem applies.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The sharp contractive Riccati inequality from an ordered internal gap,
with no nontriviality assumptions on either coordinate subspace. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_orderedInternalGap
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : OrderedInternalGap A U d)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  classical
  rcases subsingleton_or_nontrivial U with hUsub | hUnt
  · let : Subsingleton U := hUsub
    have hXzero : quarterAcuteAngularCoordinate U V hquarter = 0 := by
      ext u
      have hu : u = 0 := Subsingleton.elim _ _
      subst u
      simp
    have hXnorm : ‖quarterAcuteAngularCoordinate U V hquarter‖ = 0 := by
      rw [hXzero]
      simp
    rw [hXnorm]
    nlinarith [norm_nonneg H]
  · let : Nontrivial U := hUnt
    rcases subsingleton_or_nontrivial Uᗮ with hUcsub | hUcnt
    · let : Subsingleton Uᗮ := hUcsub
      have hXzero : quarterAcuteAngularCoordinate U V hquarter = 0 := by
        apply ContinuousLinearMap.ext
        intro u
        exact Subsingleton.elim _ _
      have hXnorm : ‖quarterAcuteAngularCoordinate U V hquarter‖ = 0 := by
        rw [hXzero]
        exact ContinuousLinearMap.opNorm_zero
      rw [hXnorm]
      nlinarith [norm_nonneg H]
    · let : Nontrivial Uᗮ := hUcnt
      exact
        quarterAcuteAngularCoordinate_sharp_bound_of_orderedInternalGap_nontrivial
          A H hA hH U V hU hV hoff hd hgap hquarter

end DavisKahanExt
end TauCeti
