/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit

/-!
# Spectral containments from Hilbert-space form bounds

A uniform real quadratic-form bound on a bounded operator excludes real
spectrum beyond the same bound.  The argument is scalar-generic over `RCLike`:
a real shift outside the form interval is coercive, hence invertible by the
operator Lax--Milgram theorem.

The restricted-subspace corollaries package the same argument in the
`SpectrumIn` vocabulary used by Davis--Kahan.  Keeping these lemmas here avoids
making the real Section 8 development depend on a complex-only spectral
calculus merely to convert sharp form bounds into the printed spectral
orientation.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A global upper quadratic-form bound excludes real spectrum above the same
threshold. -/
theorem realSpectrum_subset_Iic_of_re_inner_le_generic
    {T : E →L[𝕜] E} {c : ℝ}
    (hform : ∀ z : E, RCLike.re ⟪T z, z⟫_𝕜 ≤ c * ‖z‖ ^ 2) :
    realSpectrum T ⊆ Set.Iic c := by
  intro r hr
  by_contra hnot
  have hlt : c < r := lt_of_not_ge hnot
  have hcoer : ∀ z : E, (r - c) * ‖z‖ ^ 2 ≤
      RCLike.re ⟪(((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - T) z, z⟫_𝕜 := by
    intro z
    have hz := hform z
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, RCLike.conj_ofReal, map_sub, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
    linarith
  have hunit : IsUnit (((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - T) :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive (by linarith) hcoer
  have hspec : (r : 𝕜) ∈ spectrum 𝕜 T := hr
  rw [spectrum.mem_iff] at hspec
  apply hspec
  rw [Algebra.algebraMap_eq_smul_one]
  exact hunit

/-- A global lower quadratic-form bound excludes real spectrum below the same
threshold. -/
theorem realSpectrum_subset_Ici_of_le_re_inner_generic
    {T : E →L[𝕜] E} {c : ℝ}
    (hform : ∀ z : E, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪T z, z⟫_𝕜) :
    realSpectrum T ⊆ Set.Ici c := by
  intro r hr
  by_contra hnot
  have hlt : r < c := lt_of_not_ge hnot
  have hcoer : ∀ z : E, (c - r) * ‖z‖ ^ 2 ≤
      RCLike.re ⟪(T - ((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E)) z, z⟫_𝕜 := by
    intro z
    have hz := hform z
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, RCLike.conj_ofReal, map_sub, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
    linarith
  have hunit : IsUnit (T - ((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E)) :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive (by linarith) hcoer
  have hspec : (r : 𝕜) ∈ spectrum 𝕜 T := hr
  rw [spectrum.mem_iff] at hspec
  apply hspec
  rw [Algebra.algebraMap_eq_smul_one]
  have hneg : ((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - T =
      -(T - ((r : ℝ) : 𝕜) • (1 : E →L[𝕜] E)) := by
    module
  rw [hneg]
  exact hunit.neg

/-- An upper form bound on an invariant orthogonally complemented subspace
places its restricted real spectrum below the same threshold. -/
theorem spectrumIn_Iic_of_re_inner_le_generic
    {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : ∀ x ∈ U, T x ∈ U) {c : ℝ}
    (hform : ∀ x ∈ U, RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    SpectrumIn T U (Set.Iic c) := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  refine ⟨hU, ?_⟩
  rw [restrictedSpectrum_eq_restrictionSpectrum T U hU]
  exact realSpectrum_subset_Iic_of_re_inner_le_generic
    (fun z => hform (z : E) z.2)

/-- A lower form bound on an invariant orthogonally complemented subspace
places its restricted real spectrum above the same threshold. -/
theorem spectrumIn_Ici_of_le_re_inner_generic
    {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : ∀ x ∈ U, T x ∈ U) {c : ℝ}
    (hform : ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜) :
    SpectrumIn T U (Set.Ici c) := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  refine ⟨hU, ?_⟩
  rw [restrictedSpectrum_eq_restrictionSpectrum T U hU]
  exact realSpectrum_subset_Ici_of_le_re_inner_generic
    (fun z => hform (z : E) z.2)

end Foundation
end DavisKahan
end TauCeti
