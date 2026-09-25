/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# The `ε`-grid on the line, and which of its cells carry spectrum

A block argument cuts the line into cells of width `ε` and works cell by cell.
This module supplies the grid — `gridCell ε k = [kε, (k+1)ε)` for `k : ℤ` — with
the three facts a spectral decomposition needs (measurable, pairwise disjoint,
covering), the two estimates a block estimate needs (each cell is bounded, and
within `ε` of its left endpoint), and the observation that lets empty cells be
discarded:

`exists_mem_spectrum_of_specProjection_ne_zero` — a cell carrying a **nonzero**
spectral projection must meet the spectrum.

That last one is what licenses the separation hypothesis on the surviving
blocks: if `E_A(I) ≠ 0` and `E_B(J) ≠ 0` then `I` and `J` contain actual
spectral points, which the pairwise gap separates by `δ`, so their representatives
are separated by at least `δ - 2ε`.

The grid is indexed by `ℤ`, hence countable but not finite — the spectra need not
be bounded.  This is why the reassembly lemmas were stated for an arbitrary index
type rather than a `Finset`.

## Sources

*Follows nothing in particular*: the `ε`-grid a block argument cuts the line into, with
exactly the three facts (measurable, disjoint, covering) the decomposition uses.

## Provenance

*New.*  Mathlib has the unit grid (`iUnion_Ico_intCast`,
`pairwise_disjoint_Ico_intCast`); these are the `ε`-scaled versions, proved
directly from `Int.floor` rather than transported.
-/

@[expose] public section

open Set

namespace TauCeti
namespace LinearPMap

variable {ε : ℝ}

/-- The `k`-th cell of the `ε`-grid on the line. -/
def gridCell (ε : ℝ) (k : ℤ) : Set ℝ := Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)

/-- Grid cells are measurable, being half-open intervals, so each admits a spectral projection. -/
theorem measurableSet_gridCell (ε : ℝ) (k : ℤ) : MeasurableSet (gridCell ε k) :=
  measurableSet_Ico

/-- Distinct cells are disjoint. -/
theorem pairwise_disjoint_gridCell (hε : 0 < ε) :
    Pairwise (Function.onFun Disjoint (gridCell ε)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxk hxl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hkl' : ((k : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    have : ((k : ℝ) + 1) * ε ≤ (l : ℝ) * ε := by nlinarith [hε.le]
    exact absurd (lt_of_lt_of_le hxk.2 this) (not_lt.mpr hxl.1)
  · have hlk' : ((l : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    have : ((l : ℝ) + 1) * ε ≤ (k : ℝ) * ε := by nlinarith [hε.le]
    exact absurd (lt_of_lt_of_le hxl.2 this) (not_lt.mpr hxk.1)

/-- The cells cover the line. -/
theorem iUnion_gridCell (hε : 0 < ε) : (⋃ k : ℤ, gridCell ε k) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true, gridCell, mem_Ico]
  refine ⟨⌊x / ε⌋, ?_, ?_⟩
  · rw [← le_div_iff₀ hε]
    exact Int.floor_le _
  · rw [← div_lt_iff₀ hε]
    exact Int.lt_floor_add_one _

/-- Each cell is bounded. -/
theorem abs_le_of_mem_gridCell (hε : 0 < ε) (k : ℤ) {s : ℝ} (hs : s ∈ gridCell ε k) :
    |s| ≤ (|(k : ℝ)| + 1) * ε := by
  obtain ⟨h1, h2⟩ := hs
  have hk : -|(k : ℝ)| ≤ (k : ℝ) := neg_abs_le _
  have hk' : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  rw [abs_le]
  constructor <;> nlinarith [hε.le, abs_nonneg ((k : ℝ))]

/-- Each cell lies within `ε` of its left endpoint. -/
theorem abs_sub_le_of_mem_gridCell (hε : 0 < ε) (k : ℤ) {s : ℝ} (hs : s ∈ gridCell ε k) :
    |s - (k : ℝ) * ε| ≤ ε := by
  obtain ⟨h1, h2⟩ := hs
  rw [abs_le]
  constructor <;> nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **The grid's spectral projections split norms.**  This is the hypothesis the
reassembly lemmas take, instantiated at the `ε`-grid. -/
theorem tsum_enorm_sq_specProjection_gridCell (hε : 0 < ε) (v : H) :
    ∑' k : ℤ, ‖specProjection hA (gridCell ε k) (measurableSet_gridCell ε k) v‖ₑ ^ 2
      = ‖v‖ₑ ^ 2 := by
  simp only [specProjection_def]
  exact (spectralPVM hA).tsum_enorm_sq_proj (gridCell ε) (measurableSet_gridCell ε)
    (pairwise_disjoint_gridCell hε) (iUnion_gridCell hε) v

/-- The same, for the adjoints — which is the form the *right*-hand reassembly
takes.  Spectral projections are self-adjoint, so it is the same statement. -/
theorem tsum_enorm_sq_adjoint_specProjection_gridCell (hε : 0 < ε) (v : H) :
    ∑' k : ℤ,
        ‖(specProjection hA (gridCell ε k) (measurableSet_gridCell ε k)).adjoint v‖ₑ ^ 2
      = ‖v‖ₑ ^ 2 := by
  have hsa : ∀ k : ℤ,
      (specProjection hA (gridCell ε k) (measurableSet_gridCell ε k)).adjoint
        = specProjection hA (gridCell ε k) (measurableSet_gridCell ε k) := fun k => by
    simp only [specProjection_def]
    exact ((spectralPVM hA).isSelfAdjoint_proj _ _).adjoint_eq
  simp_rw [hsa]
  exact tsum_enorm_sq_specProjection_gridCell hA hε v

/-- Spectral projections are idempotent, in the composition form the block
lemmas take. -/
theorem specProjection_comp_self (Bset : Set ℝ) (hBset : MeasurableSet Bset) :
    (specProjection hA Bset hBset).comp (specProjection hA Bset hBset)
      = specProjection hA Bset hBset := by
  simp only [specProjection_def]
  exact (spectralPVM hA).proj_idem Bset hBset


/-- **A cell carrying a nonzero projection meets the spectrum.**  Contrapositive
of `specProjection_eq_zero_of_subset_resolventSet`; it is what lets empty cells
be discarded and the separation hypothesis be used on the survivors. -/
theorem exists_mem_spectrum_of_specProjection_ne_zero (B : Set ℝ) (hB : MeasurableSet B)
    (h : specProjection hA B hB ≠ 0) :
    ∃ lam ∈ B, (lam : ℂ) ∈ spectrum A := by
  by_contra hcon
  push Not at hcon
  refine h (specProjection_eq_zero_of_subset_resolventSet hA B hB fun lam hlam => ?_)
  have := hcon lam hlam
  rwa [spectrum, Set.mem_compl_iff, not_not] at this

end LinearPMap
end TauCeti
