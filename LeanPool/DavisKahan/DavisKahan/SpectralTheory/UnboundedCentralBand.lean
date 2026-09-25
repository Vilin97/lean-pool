/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionLocalization
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GapResolvent
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CentralBand
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RayleighRitz

/-!
# The central band of an unbounded self-adjoint operator

The unbounded counterpart of `CentralBand.lean`.  For a self-adjoint partial map
whose real spectrum lies in `[l, r] ∪ exterior(l, r, d)`, the spectral range of
the **closed interval** `[l, r]` carries the band block and its orthogonal
complement carries the exterior block, with the two spectra separated by `d`.

Taking the selecting set to be the closed interval rather than the open central
band is what makes the band side immediate: every point outside `[l, r]` keeps a
positive distance from it, so
`selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty` applies
directly.

The complement side needs one step.  `((Icc l r)ᶜ` is not the exterior — it also
contains the two open gaps `(l - d, l)` and `(r, r + d)` — but those consist of
resolvent points, so `specProjection_eq_zero_of_subset_resolventSet` kills them
and the two spectral ranges coincide.  `specProjection_eq_of_diff_eq_zero` below
is the bookkeeping that combines the two sets; there is no general
`specProjection (S ∪ T)` additivity lemma, and none is needed.

This is step (b) of the unbounded Theorem 8.2 path recorded in `GOAL.md` §10.4.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **A null set may be removed from a spectral selection.**

If `specProjection A S = 0` and `U ∩ Sᶜ = T`, then `U` and `T` select the same
spectral projection.  With `S` a set of resolvent points this says that the
spectral range does not see the part of the selecting set that carries no
spectrum. -/
theorem specProjection_eq_of_diff_eq_zero
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {U T S : Set ℝ}
    (hU : MeasurableSet U) (hT : MeasurableSet T) (hS : MeasurableSet S)
    (hzero : TauCeti.LinearPMap.specProjection hA S hS = 0)
    (heq : U ∩ Sᶜ = T) :
    TauCeti.LinearPMap.specProjection hA U hU
      = TauCeti.LinearPMap.specProjection hA T hT := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hSx : TauCeti.LinearPMap.specProjection hA S hS x = 0 := by rw [hzero]; rfl
  have hcompl : TauCeti.LinearPMap.specProjection hA Sᶜ hS.compl x = x := by
    have h := TauCeti.LinearPMap.specProjection_add_compl_apply hA hS x
    rw [hSx, zero_add] at h
    exact h
  have hinter := TauCeti.LinearPMap.specProjection_apply_specProjection hA hU hS.compl x
  rw [hcompl] at hinter
  rw [hinter]
  subst heq
  rfl

/-- The two open gaps flanking the band consist of resolvent points, so their
spectral projection vanishes. -/
theorem specProjection_gaps_eq_zero
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r d : ℝ}
    (hlr : l ≤ r) (hd : 0 < d)
    (hspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ {x : ℝ | x ≤ l - d ∨ r + d ≤ x}) :
    TauCeti.LinearPMap.specProjection hA
        (Set.Ioo (l - d) l ∪ Set.Ioo r (r + d))
        (measurableSet_Ioo.union measurableSet_Ioo) = 0 := by
  refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _ _ ?_
  intro lam hlam
  have hnot : lam ∉ TauCeti.LinearPMap.realSpectrum A := by
    intro hmem
    rcases hspec hmem with h | h
    · rcases hlam with h' | h'
      · linarith [h.1, h'.2]
      · linarith [h.2, h'.1]
    · rcases hlam with h' | h'
      · rcases h with h | h
        · linarith [h'.1]
        · linarith [h'.2, h]
      · rcases h with h | h
        · linarith [h'.1]
        · linarith [h'.2]
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, not_not] at hnot
  have := (realSpectrum_eq_spectraSpectrum A)
  by_contra hcon
  exact (by
    have : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
      rw [this, Set.mem_preimage, TauCeti.LinearPMap.mem_spectrum_iff]
      exact hcon
    rw [TauCeti.LinearPMap.mem_realSpectrum_iff] at this
    exact this hnot)

/-- The exterior of the band, as a set. -/
def bandExterior (l r d : ℝ) : Set ℝ := {x : ℝ | x ≤ l - d ∨ r + d ≤ x}

/-- The exterior of the band is measurable, being a union of two closed rays. -/
theorem measurableSet_bandExterior (l r d : ℝ) : MeasurableSet (bandExterior l r d) := by
  have : bandExterior l r d = Set.Iic (l - d) ∪ Set.Ici (r + d) := rfl
  rw [this]
  exact measurableSet_Iic.union measurableSet_Ici

/-- **The complement of the closed band selects the exterior.**

`(Icc l r)ᶜ` also contains the two open gaps, but they carry no spectrum, so the
two spectral ranges coincide.  Combined with `specRange_compl` this identifies
the orthogonal complement of the band range with the exterior range. -/
theorem specRange_bandExterior_eq_orthogonal
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r d : ℝ}
    (hlr : l ≤ r) (hd : 0 < d)
    (hspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ bandExterior l r d) :
    TauCeti.LinearPMap.specRange hA (bandExterior l r d)
        (measurableSet_bandExterior l r d)
      = (TauCeti.LinearPMap.specRange hA (Set.Icc l r) measurableSet_Icc)ᗮ := by
  have hgapsz := specProjection_gaps_eq_zero hA hlr hd hspec
  have hsplit : (Set.Icc l r)ᶜ ∩ (Set.Ioo (l - d) l ∪ Set.Ioo r (r + d))ᶜ
      = bandExterior l r d := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
      Set.mem_Ioo, bandExterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt x (l - d) with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        by_contra hcon
        push Not at hcon
        rcases lt_or_ge x l with hxl | hxl
        · exact h2 (Or.inl ⟨h, hxl⟩)
        · rcases lt_or_ge r x with hxr | hxr
          · exact h2 (Or.inr ⟨hxr, hcon⟩)
          · exact h1 ⟨hxl, hxr⟩
    · rintro (h | h)
      · refine ⟨fun hc => by linarith [hc.1], fun hc => ?_⟩
        rcases hc with hc | hc
        · linarith [hc.1]
        · linarith [hc.1]
      · refine ⟨fun hc => by linarith [hc.2], fun hc => ?_⟩
        rcases hc with hc | hc
        · linarith [hc.2]
        · linarith [hc.2]
  have hproj : TauCeti.LinearPMap.specProjection hA ((Set.Icc l r)ᶜ)
        measurableSet_Icc.compl
      = TauCeti.LinearPMap.specProjection hA (bandExterior l r d)
        (measurableSet_bandExterior l r d) :=
    specProjection_eq_of_diff_eq_zero hA measurableSet_Icc.compl
      (measurableSet_bandExterior l r d)
      (measurableSet_Ioo.union measurableSet_Ioo) hgapsz hsplit
  have hrange : TauCeti.LinearPMap.specRange hA ((Set.Icc l r)ᶜ) measurableSet_Icc.compl
      = TauCeti.LinearPMap.specRange hA (bandExterior l r d)
        (measurableSet_bandExterior l r d) := by
    unfold TauCeti.LinearPMap.specRange
    rw [hproj]
  rw [← hrange]
  exact TauCeti.LinearPMap.specRange_compl hA (Set.Icc l r) measurableSet_Icc

/-- **The band block's real spectrum lies in the band.** -/
theorem realSpectrum_specRestrict_Icc_subset
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r : ℝ} :
    TauCeti.LinearPMap.realSpectrum
        (selfAdjointSpectralRestriction A hA (Set.Icc l r) measurableSet_Icc)
      ⊆ Set.Icc l r := by
  intro lam hlam
  by_contra hcon
  rw [Set.mem_Icc] at hcon
  push Not at hcon
  have havoid : ∀ a b : ℝ, Set.Icc l r ∩ Set.Ioo a b = ∅ → lam ∈ Set.Ioo a b → False := by
    intro a b hdisj hmem
    have := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA (Set.Icc l r) measurableSet_Icc hdisj lam hmem
    rw [realSpectrum_eq_spectraSpectrum] at hlam
    exact this hlam
  rcases lt_or_ge lam l with h | h
  · refine havoid (lam - 1) l ?_ ⟨by linarith, h⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx1, -⟩, -, hx4⟩
    linarith
  · have hr : r < lam := hcon h
    refine havoid r (lam + 1) ?_ ⟨hr, by linarith⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hx2⟩, hx3, -⟩
    linarith

/-- **The exterior block's real spectrum lies in the exterior.** -/
theorem realSpectrum_specRestrict_bandExterior_subset
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r d : ℝ} :
    TauCeti.LinearPMap.realSpectrum
        (selfAdjointSpectralRestriction A hA (bandExterior l r d)
          (measurableSet_bandExterior l r d))
      ⊆ bandExterior l r d := by
  intro lam hlam
  by_contra hcon
  simp only [bandExterior, Set.mem_ofPred_eq] at hcon
  push Not at hcon
  have hdisj : bandExterior l r d ∩ Set.Ioo (l - d) (r + d) = ∅ := by
    ext x
    simp only [bandExterior, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨h | h, hx1, hx2⟩
    · linarith
    · linarith
  have := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    A hA (bandExterior l r d) (measurableSet_bandExterior l r d) hdisj lam
    ⟨hcon.1, hcon.2⟩
  rw [realSpectrum_eq_spectraSpectrum] at hlam
  exact this hlam

/-! ## Transport to an arbitrary reducing subspace

`selfAdjointSpectralRestriction A hA B hB` and
`reducingRestriction A (specRange hA B hB) _` are definitionally equal, so the
two containments above transfer to any subspace *presented* as a spectral range.
Stating them this way is what lets a caller name the band subspace once and use
its orthogonal complement without transporting a partial map along an equality of
submodules. -/

/-- The band containment, for a subspace presented as the band spectral range. -/
theorem realSpectrum_reducingRestriction_band_subset
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r : ℝ}
    {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : W = TauCeti.LinearPMap.specRange hA (Set.Icc l r) measurableSet_Icc)
    (hred : TauCeti.LinearPMap.ReducesSubspace A W) :
    TauCeti.LinearPMap.realSpectrum (TauCeti.LinearPMap.reducingRestriction A W hred)
      ⊆ Set.Icc l r := by
  subst hW
  exact realSpectrum_specRestrict_Icc_subset hA

/-- The exterior containment, for a subspace presented as the exterior spectral
range. -/
theorem realSpectrum_reducingRestriction_bandExterior_subset
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r d : ℝ}
    {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : W = TauCeti.LinearPMap.specRange hA (bandExterior l r d)
      (measurableSet_bandExterior l r d))
    (hred : TauCeti.LinearPMap.ReducesSubspace A W) :
    TauCeti.LinearPMap.realSpectrum (TauCeti.LinearPMap.reducingRestriction A W hred)
      ⊆ bandExterior l r d := by
  subst hW
  exact realSpectrum_specRestrict_bandExterior_subset hA

/-- **The band configuration is a source separation.**

The band block of one operator and the exterior block of another are separated by
`d`, which is exactly `FormBoundedSylvesterGap.intervalExterior`.  This is the
hypothesis the unbounded `sin Θ` and `sin 2Θ` endpoints take, so it is what the
moving spectral branch supplies at each parameter. -/
theorem formBoundedSylvesterGap_band_exterior
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {l r d : ℝ}
    (hlr : l ≤ r)
    {W W' : Submodule ℂ H} [W.HasOrthogonalProjection] [W'.HasOrthogonalProjection]
    (hW : W = TauCeti.LinearPMap.specRange hA (Set.Icc l r) measurableSet_Icc)
    (hW' : W' = TauCeti.LinearPMap.specRange hB (bandExterior l r d)
      (measurableSet_bandExterior l r d))
    (hredA : TauCeti.LinearPMap.ReducesSubspace A W)
    (hredB : TauCeti.LinearPMap.ReducesSubspace B W') :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A W hredA)
      (TauCeti.LinearPMap.reducingRestriction B W' hredB) d :=
  .intervalExterior hlr
    (Or.inl ⟨realSpectrum_reducingRestriction_band_subset hA hW hredA,
      realSpectrum_reducingRestriction_bandExterior_subset hB hW' hredB⟩)

/-- **The real-spectrum reading of `spectrum_addBounded_subset_of_gap`.**

The same stability statement with `realSpectrum` on both sides, which is the
spelling the band machinery and `FormBoundedSylvesterGap` use. -/
theorem realSpectrum_addBounded_subset_of_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (K : H →L[ℂ] H)
    {alpha beta delta gam : ℝ} (hab : beta ≤ alpha) (hdelta : 0 < delta)
    (hgam : ‖K‖ ≤ gam) (hgamlt : 2 * gam < delta)
    (hgap : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc beta alpha ∪ bandExterior beta alpha delta) :
    TauCeti.LinearPMap.realSpectrum (TauCeti.LinearPMap.addBounded A K) ⊆
      Set.Icc (beta - gam) (alpha + gam) ∪
        bandExterior (beta - gam) (alpha + gam) (delta - 2 * gam) := by
  intro lam hlam
  refine spectrum_addBounded_subset_of_gap hA K hab hdelta hgam hgamlt ?_ lam ?_
  · intro mu hmu
    exact hgap (by rw [realSpectrum_eq_spectraSpectrum]; exact hmu)
  · rw [realSpectrum_eq_spectraSpectrum] at hlam
    exact hlam

/-! ## Half-line spectrum gives a form bound

The printed spectral placements of Section 8 are half-line containments; the
theorems that consume them want form bounds.  A point outside the closed
half-line is a resolvent point, so its spectral projection vanishes, and the
half-line energy bounds of the spectral measure do the rest. -/

/-- **Spectrum in `Iic c` gives the upper form bound.** -/
theorem re_inner_le_of_realSpectrum_subset_Iic
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c : ℝ}
    (h : TauCeti.LinearPMap.realSpectrum A ⊆ Set.Iic c) (x : A.domain) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  refine TauCeti.LinearPMap.re_inner_le_of_specProjection_Ioi_eq_zero hA ?_ x
  refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _ _ ?_
  intro lam hlam
  have hnot : lam ∉ TauCeti.LinearPMap.realSpectrum A := fun hmem => absurd (h hmem) (by
    simp only [Set.mem_Iic, not_le]
    exact hlam)
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, not_not] at hnot
  by_contra hcon
  have : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
    rw [realSpectrum_eq_spectraSpectrum, Set.mem_preimage,
      TauCeti.LinearPMap.mem_spectrum_iff]
    exact hcon
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff] at this
  exact this hnot

/-- **Spectrum in `Ici c` gives the lower form bound.** -/
theorem le_re_inner_of_realSpectrum_subset_Ici
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c : ℝ}
    (h : TauCeti.LinearPMap.realSpectrum A ⊆ Set.Ici c) (x : A.domain) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  refine TauCeti.LinearPMap.le_re_inner_of_specProjection_Iio_eq_zero hA ?_ x
  refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _ _ ?_
  intro lam hlam
  have hnot : lam ∉ TauCeti.LinearPMap.realSpectrum A := fun hmem => absurd (h hmem) (by
    simp only [Set.mem_Ici, not_le]
    exact hlam)
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, not_not] at hnot
  by_contra hcon
  have : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
    rw [realSpectrum_eq_spectraSpectrum, Set.mem_preimage,
      TauCeti.LinearPMap.mem_spectrum_iff]
    exact hcon
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff] at this
  exact this hnot

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete. -/
noncomputable local instance instCompleteSpaceCoeBandForm
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- **A block placed in `Iic c` bounds the ambient form on that block.** -/
theorem re_inner_le_of_reducingRestriction_realSpectrum_subset_Iic
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) {c : ℝ}
    (h : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A U hred) ⊆ Set.Iic c)
    (x : A.domain) (hx : (x : H) ∈ U) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  have hres : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A U hred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred hA.dense_domain hA
  have hxdom : (⟨(x : H), hx⟩ : U) ∈
      (TauCeti.LinearPMap.reducingRestriction A U hred).domain := x.2
  have hb := re_inner_le_of_realSpectrum_subset_Iic hres h
    (⟨⟨(x : H), hx⟩, hxdom⟩ :
      (TauCeti.LinearPMap.reducingRestriction A U hred).domain)
  exact hb

/-- **A block placed in `Ici c` bounds the ambient form on that block from
below.** -/
theorem le_re_inner_of_reducingRestriction_realSpectrum_subset_Ici
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) {c : ℝ}
    (h : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A U hred) ⊆ Set.Ici c)
    (x : A.domain) (hx : (x : H) ∈ U) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  have hres : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A U hred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred hA.dense_domain hA
  have hxdom : (⟨(x : H), hx⟩ : U) ∈
      (TauCeti.LinearPMap.reducingRestriction A U hred).domain := x.2
  have hb := le_re_inner_of_realSpectrum_subset_Ici hres h
    (⟨⟨(x : H), hx⟩, hxdom⟩ :
      (TauCeti.LinearPMap.reducingRestriction A U hred).domain)
  exact hb

end DavisKahan
end TauCeti
