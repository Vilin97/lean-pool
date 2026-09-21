/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionOperator
import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Spectral Restriction Localization -/

open TauCeti.DavisKahan.Sylvester

/-!
# Spectral localization of the restriction to a spectral range

The restriction of `A` to the range of `E_A(B)` must inherit the spectral
localization encoded by `B`:

* if `B ⊆ [β, α]`, the restriction has quadratic form in `[β, α]`;
* if `B` is disjoint from an open interval, every point of that interval lies
  in the resolvent set of the restriction.

These are the final analytic localization inputs needed by the independent
bounded-perturbation sine-theta path.

## Provenance

Until 2026-07-29 both statements were routed through `vendor/Spectra`'s Stone
theory: the restricted operator was the generator of the restricted unitary
group, and the two facts came from that group's *scalar* Borel measure —
identified with the ambient one by Fourier uniqueness
(`Spectra.Fourier.measure_ext_of_fourier`), then restricted to `B` because the
vector is fixed by `E_A(B)`, after which `weak_first_moment` and
`mem_resolventSet_of_spectralProjection_Ioo_eq_zero` finished the job.

The native replacements come from the Borel calculus of the Cayley transform
(`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean`):

* `re_inner_apply_bounds_of_subset_Icc` — the quadratic form of `A` on a
  spectral range is confined to any interval containing `B`;
* `mem_resolventSet_specRestrict_of_gap` — a gap between `B` and `lam` makes
  `lam` a resolvent point, the inverse being the Borel calculus of
  `(κ - lam)⁻¹ 1_B`.

The two exported statements are unchanged; the scalar-measure machinery that
supported them is gone, and with it this module's dependency on Spectra.
-/

open scoped InnerProductSpace ENNReal
open Complex Filter MeasureTheory Topology

namespace TauCeti
namespace DavisKahan


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The restriction to `E_A(B)H` inherits interval form bounds from the set
containment `B ⊆ [β, α]`. -/
theorem selfAdjointSpectralRestriction_semibounded_of_subset_Icc
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {β α : ℝ} (hBsub : B ⊆ Set.Icc β α) :
    TauCeti.LinearPMap.SemiboundedBelow (selfAdjointSpectralRestriction A hA B hB) β ∧
      TauCeti.LinearPMap.SemiboundedAbove (selfAdjointSpectralRestriction A hA B hB) α := by
  constructor
  · intro x
    exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc hA B hB hBsub
      x.1.2 x.2).1
  · intro x
    exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc hA B hB hBsub
      x.1.2 x.2).2

/-- If the selecting set is disjoint from an open interval, the spectrum of the
restriction avoids that interval. -/
theorem selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {a b : ℝ} (hdisj : B ∩ Set.Ioo a b = ∅) :
    ∀ lam ∈ Set.Ioo a b,
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA B hB) := by
  intro lam hlam
  have hleft : 0 < lam - a := by linarith [hlam.1]
  have hright : 0 < b - lam := by linarith [hlam.2]
  set ε : ℝ := min (lam - a) (b - lam) / 2 with hεdef
  have hmin : 0 < min (lam - a) (b - lam) := lt_min hleft hright
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hmin (by norm_num)
  have hεleft : ε ≤ lam - a := by
    rw [hεdef]
    have := min_le_left (lam - a) (b - lam)
    linarith
  have hεright : ε ≤ b - lam := by
    rw [hεdef]
    have := min_le_right (lam - a) (b - lam)
    linarith
  -- every point of `B` is at least `ε` away from `lam`
  have hgap : ∀ s ∈ B, ε ≤ |s - lam| := by
    intro s hs
    by_contra hcon
    rw [not_le, abs_lt] at hcon
    have hsIoo : s ∈ Set.Ioo a b := by
      constructor <;> [linarith [hcon.1]; linarith [hcon.2]]
    have : s ∈ B ∩ Set.Ioo a b := ⟨hs, hsIoo⟩
    rw [hdisj] at this
    exact this
  intro hnot
  exact hnot (TauCeti.LinearPMap.mem_resolventSet_specRestrict_of_gap hA B hB hε hgap)

end DavisKahan
end TauCeti
