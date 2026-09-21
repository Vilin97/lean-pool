/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.BoundedGapProjection
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.FormTransport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormSpectrumBounds

/-! # Theorem81Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1 over a real Hilbert space

The complex source theorem already proves the hard perturbation theory.  This
file descends its canonical Section 8 branch to a real Hilbert space without
re-running the spectral argument.

The nontrivial point is branch selection: after complexification, the complex
branch must itself be the complexification of a real subspace.  The bounded-gap
spectral descent layer proves exactly that for the genuine bounded spectral
projection.  Once this branch is identified, reduction, sharp form bounds and
quarter-acuteness transport without loss.  The printed restricted-spectrum
orientation is recovered natively over `ℝ` from the transported sharp form
bounds using the scalar-generic coercive resolvent lemmas.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Real-scalar counterpart of `Theorem81Conclusion`. -/
structure Theorem81ConclusionReal
    (A H : E →L[ℝ] E) (P Q : Submodule ℝ E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (alpha delta : ℝ) : Prop where
  /-- The open gap contains no real spectrum of the perturbed operator. -/
  spectral_repulsion :
    realSpectrum (A + H) ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)
  /-- The descended branch reduces the real perturbed operator. -/
  branch_reduces : (A + H).Reduces Q
  /-- Sharp upper form bound on the low branch. -/
  branch_form_low : ∀ x ∈ Q, ⟪(A + H) x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2
  /-- Sharp lower form bound on the complementary branch. -/
  branch_form_high :
    ∀ x ∈ Qᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪(A + H) x, x⟫_ℝ
  /-- The printed low spectral orientation. -/
  branch_spectrum_low : SpectrumIn (A + H) Q (Set.Iic alpha)
  /-- The printed high spectral orientation. -/
  branch_spectrum_high : SpectrumIn (A + H) Qᗮ (Set.Ici (alpha + delta))
  /-- The selected branch is strictly inside the quarter turn. -/
  quarter_acute : IsQuarterAcute P Q
  /-- Equivalent scalar maximal-angle statement. -/
  maximal_angle_lt_pi_div_four : maximalAngle P Q < Real.pi / 4

/-- **Davis--Kahan 1970, Theorem 8.1, existence over a REAL Hilbert space.**

From the printed real-scalar hypotheses alone there exists an orthogonally
complemented real branch carrying the complete Theorem 8.1 existence
conclusion.  The witness is the real descent of the actual bounded complex
spectral branch; no contour or extra branch-selection hypothesis is supplied
by the caller. -/
theorem theorem8_1_canonicalBranch_real
    (A H : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P) :
    ∃ (Q : Submodule ℝ E) (hQ : Q.HasOrthogonalProjection),
      haveI : Q.HasOrthogonalProjection := hQ
      Theorem81ConclusionReal A H P Q alpha delta := by
  classical
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hHc : IsSelfAdjoint (complexify H) := (complexify_isSelfAdjoint_iff H).2 hH
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  have hconcC := theorem8_1_canonicalBranch
    (E := RealComplexification E)
    (complexify A) (complexify H) (complexifySubmodule P) hdelta hAc hHc
    (fun z hz => mapsTo_complexifySubmodule hAP hz)
    (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
    (fun z hz => by
      rw [← complexifySubmodule_orthogonal P] at hz
      exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
    (fun z hz => mapsTo_orthogonal_complexifySubmodule P hHP hz)
    (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hHPperp hz)
  have hrep : realSpectrum (A + H) ⊆
      Set.Iic alpha ∪ Set.Ici (alpha + delta) := by
    rw [← realSpectrum_complexify (A + H), ← hsum]
    exact hconcC.spectral_repulsion
  let Q : Submodule ℝ E :=
    realBoundedSpectralSubspaceIicOfGap (A + H) (hA.add hH)
      alpha delta hdelta hrep
  let hQ : Q.HasOrthogonalProjection :=
    realBoundedSpectralSubspaceIicOfGap_hasOrthogonalProjection
      (A + H) (hA.add hH) alpha delta hdelta hrep
  have : Q.HasOrthogonalProjection := hQ
  have hQc : complexifySubmodule Q =
      canonicalLowBranch (complexify A + complexify H)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hHc)) alpha := by
    unfold Q
    simpa only [canonicalLowBranch, hsum] using
      (complexifySubmodule_realBoundedSpectralSubspaceIicOfGap
        (A + H) (hA.add hH) alpha delta hdelta hrep)
  have hreducesC : (complexify (A + H)).Reduces (complexifySubmodule Q) := by
    rw [← hsum, hQc]
    exact hconcC.branch_reduces
  have hreduces : (A + H).Reduces Q :=
    (complexify_reduces_iff (A + H) Q).1 hreducesC
  have hlow : ∀ x ∈ Q, ⟪(A + H) x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2 := by
    intro x hx
    have hxC : ofReal x ∈ complexifySubmodule Q :=
      (ofReal_mem_complexifySubmodule_iff Q x).2 hx
    have hc := hconcC.branch_form_low (ofReal x) (hQc ▸ hxC)
    rw [hsum] at hc
    simpa [re_inner_complexify] using hc
  have hhigh : ∀ x ∈ Qᗮ,
      (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪(A + H) x, x⟫_ℝ := by
    intro x hx
    have hxC : ofReal x ∈ (complexifySubmodule Q)ᗮ := by
      rw [← complexifySubmodule_orthogonal Q]
      exact (ofReal_mem_complexifySubmodule_iff Qᗮ x).2 hx
    have hc := hconcC.branch_form_high (ofReal x) (by simpa only [hQc] using hxC)
    rw [hsum] at hc
    simpa [re_inner_complexify] using hc
  have hquarterC : IsQuarterAcute (complexifySubmodule P) (complexifySubmodule Q) := by
    simpa only [hQc] using hconcC.quarter_acute
  have hquarter : IsQuarterAcute P Q :=
    (isQuarterAcute_complexifySubmodule_iff P Q).1 hquarterC
  have hangle : maximalAngle P Q < Real.pi / 4 := by
    have hmem : Real.pi / 4 ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    change Real.arcsin (P.projectionGap Q) < Real.pi / 4
    rw [Real.arcsin_lt_iff_lt_sin' hmem, Real.sin_pi_div_four]
    exact hquarter
  refine ⟨Q, hQ, ?_⟩
  exact
    { spectral_repulsion := hrep
      branch_reduces := hreduces
      branch_form_low := hlow
      branch_form_high := hhigh
      branch_spectrum_low :=
        spectrumIn_Iic_of_re_inner_le_generic hreduces.1 hlow
      branch_spectrum_high :=
        spectrumIn_Ici_of_le_re_inner_generic hreduces.2 hhigh
      quarter_acute := hquarter
      maximal_angle_lt_pi_div_four := hangle }


/-- **Davis--Kahan 1970, Theorem 8.1, uniqueness over a REAL Hilbert space.**

Any two reducing real subspaces satisfying the printed closed quarter-angle
condition are equal.  The proof complexifies both candidates, applies the
already-proved complex uniqueness theorem to identify both with the same
canonical spectral branch, and reflects subspace equality back to `ℝ`. -/
theorem theorem8_1_eq_of_maximalAngle_le_real
    (A H : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P)
    (M N : Submodule ℝ E) [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    (hMreduces : (A + H).Reduces M) (hNreduces : (A + H).Reduces N)
    (hMangle : maximalAngle P M ≤ Real.pi / 4)
    (hNangle : maximalAngle P N ≤ Real.pi / 4) :
    M = N := by
  classical
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hHc : IsSelfAdjoint (complexify H) := (complexify_isSelfAdjoint_iff H).2 hH
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  have hMreducesC : (complexify A + complexify H).Reduces (complexifySubmodule M) := by
    rw [hsum]
    exact (complexify_reduces_iff (A + H) M).2 hMreduces
  have hNreducesC : (complexify A + complexify H).Reduces (complexifySubmodule N) := by
    rw [hsum]
    exact (complexify_reduces_iff (A + H) N).2 hNreduces
  have hMangleC :
      maximalAngle (complexifySubmodule P) (complexifySubmodule M) ≤ Real.pi / 4 := by
    simpa only [maximalAngle, subspaceGap_complexifySubmodule] using hMangle
  have hNangleC :
      maximalAngle (complexifySubmodule P) (complexifySubmodule N) ≤ Real.pi / 4 := by
    simpa only [maximalAngle, subspaceGap_complexifySubmodule] using hNangle
  have hMcanon := theorem8_1_eq_canonicalBranch_of_maximalAngle_le
    (E := RealComplexification E)
    (complexify A) (complexify H) (complexifySubmodule P)
    hdelta hAc hHc
    (fun z hz => mapsTo_complexifySubmodule hAP hz)
    (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
    (fun z hz => by
      rw [← complexifySubmodule_orthogonal P] at hz
      exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
    (fun z hz => mapsTo_orthogonal_complexifySubmodule P hHP hz)
    (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hHPperp hz)
    (complexifySubmodule M) hMreducesC hMangleC
  have hNcanon := theorem8_1_eq_canonicalBranch_of_maximalAngle_le
    (E := RealComplexification E)
    (complexify A) (complexify H) (complexifySubmodule P)
    hdelta hAc hHc
    (fun z hz => mapsTo_complexifySubmodule hAP hz)
    (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
    (fun z hz => by
      rw [← complexifySubmodule_orthogonal P] at hz
      exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
    (fun z hz => mapsTo_orthogonal_complexifySubmodule P hHP hz)
    (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hHPperp hz)
    (complexifySubmodule N) hNreducesC hNangleC
  exact complexifySubmodule_injective (hMcanon.trans hNcanon.symm)

/-- **Davis--Kahan 1970, Theorem 8.1, printed characterization over `ℝ`.**

For a reducing real subspace of the perturbed operator, the closed quarter-angle
condition is equivalent to the two printed restricted-spectrum orientations.
Both directions are inherited exactly from the complex theorem through
restriction-spectrum complexification; no finite-dimensionality assumption is
introduced. -/
theorem theorem8_1_maximalAngle_le_iff_spectrumIn_real
    (A H : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P)
    (M : Submodule ℝ E) [M.HasOrthogonalProjection]
    (hMreduces : (A + H).Reduces M) :
    maximalAngle P M ≤ Real.pi / 4 ↔
      (SpectrumIn (A + H) M (Set.Iic alpha) ∧
        SpectrumIn (A + H) Mᗮ (Set.Ici (alpha + delta))) := by
  classical
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hHc : IsSelfAdjoint (complexify H) := (complexify_isSelfAdjoint_iff H).2 hH
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  have hMreducesC : (complexify A + complexify H).Reduces (complexifySubmodule M) := by
    rw [hsum]
    exact (complexify_reduces_iff (A + H) M).2 hMreduces
  have hcharC := theorem8_1_maximalAngle_le_iff_spectrumIn
    (E := RealComplexification E)
    (complexify A) (complexify H) (complexifySubmodule P)
    hdelta hAc hHc
    (fun z hz => mapsTo_complexifySubmodule hAP hz)
    (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
    (fun z hz => by
      rw [← complexifySubmodule_orthogonal P] at hz
      exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
    (fun z hz => mapsTo_orthogonal_complexifySubmodule P hHP hz)
    (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hHPperp hz)
    (complexifySubmodule M) hMreducesC
  have hangle_iff :
      maximalAngle (complexifySubmodule P) (complexifySubmodule M) ≤ Real.pi / 4 ↔
        maximalAngle P M ≤ Real.pi / 4 := by
    simp only [maximalAngle, subspaceGap_complexifySubmodule]
  constructor
  · intro hangle
    rcases hcharC.1 (hangle_iff.2 hangle) with ⟨hlowC, hhighC⟩
    have hlowC' : SpectrumIn (complexify (A + H)) (complexifySubmodule M)
        (Set.Iic alpha) := by
      simpa only [hsum] using hlowC
    have hhighC' : SpectrumIn (complexify (A + H)) (complexifySubmodule (Mᗮ))
        (Set.Ici (alpha + delta)) := by
      simpa only [hsum, complexifySubmodule_orthogonal M] using hhighC
    exact
      ⟨(spectrumIn_complexifySubmodule_iff M (A + H) (Set.Iic alpha)).1 hlowC',
        (spectrumIn_complexifySubmodule_iff (Mᗮ) (A + H)
          (Set.Ici (alpha + delta))).1 hhighC'⟩
  · rintro ⟨hlow, hhigh⟩
    have hlowC0 := spectrumIn_complexifySubmodule M (A + H) (Set.Iic alpha) hlow
    have hhighC0 := spectrumIn_complexifySubmodule (Mᗮ) (A + H)
      (Set.Ici (alpha + delta)) hhigh
    have hlowC : SpectrumIn (complexify A + complexify H) (complexifySubmodule M)
        (Set.Iic alpha) := by
      simpa only [hsum] using hlowC0
    have hhighC : SpectrumIn (complexify A + complexify H) (complexifySubmodule M)ᗮ
        (Set.Ici (alpha + delta)) := by
      simpa only [hsum, complexifySubmodule_orthogonal M] using hhighC0
    exact hangle_iff.1 (hcharC.2 ⟨hlowC, hhighC⟩)

end

end Section8
end DavisKahan1970
end TauCeti
