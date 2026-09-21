/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Algebra of Lower Semianalytic Functions

  Closure properties of lower semianalytic functions: addition, constant
  functions, and composition with continuous maps.

  Reference: Bertsekas–Shreve, Lemma 7.30
-/
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.KernelIntegral

open Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The sum of two lower semianalytic functions is lower semianalytic.
    (BS, Lemma 7.30) Proof: in `ℝ≥0∞` (with truncated subtraction),
    `{f + g < c} = ⋃ (q : ℚ), ({f < q} ∩ {g < c - q})`, a countable union of
    binary intersections of analytic sets. -/
theorem IsLowerSemianalytic.add [T2Space X] {f g : X → ℝ≥0∞}
    (hf : IsLowerSemianalytic f) (hg : IsLowerSemianalytic g) :
    IsLowerSemianalytic (fun x => f x + g x) := by
  intro c
  show AnalyticSet {x | f x + g x < c}
  have hdecomp : {x | f x + g x < c}
      = ⋃ q : ℚ, ({x | f x < (Real.toNNReal q : ℝ≥0∞)}
          ∩ {x | g x < c - (Real.toNNReal q : ℝ≥0∞)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp
        (lt_tsub_iff_right.mpr h)
      exact ⟨q, hq1, lt_tsub_iff_left.mpr (lt_tsub_iff_right.mp hq2)⟩
    · rintro ⟨q, hq1, hq2⟩
      exact lt_trans (ENNReal.add_lt_add_right (ne_top_of_lt hq2) hq1)
        (lt_tsub_iff_left.mp hq2)
  rw [hdecomp]
  exact AnalyticSet.iUnion fun q => (hf _).inter' (hg _)

/-- Constant functions are lower semianalytic: every strict sublevel set is
    `univ` or `∅`. -/
theorem IsLowerSemianalytic.const [PolishSpace X] (c : ℝ≥0∞) :
    IsLowerSemianalytic (fun _ : X => c) := by
  intro d
  by_cases hcd : c < d
  · have h : {x : X | (fun _ : X => c) x < d} = univ :=
      eq_univ_of_forall fun _ => hcd
    rw [h]
    exact isClosed_univ.analyticSet
  · have h : {x : X | (fun _ : X => c) x < d} = ∅ := by
      ext x
      simp [hcd]
    rw [h]
    exact analyticSet_empty

/-- Precomposition with a continuous map preserves lower semianalyticity:
    sublevel sets pull back to preimages of analytic sets, which are analytic
    by `MeasureTheory.AnalyticSet.preimage_of_continuous`. -/
theorem IsLowerSemianalytic.comp_continuous [PolishSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Y → ℝ≥0∞} (hf : IsLowerSemianalytic f)
    {g : X → Y} (hg : Continuous g) :
    IsLowerSemianalytic (f ∘ g) := by
  intro c
  have h : {x | (f ∘ g) x < c} = g ⁻¹' {y | f y < c} := rfl
  rw [h]
  exact (hf c).preimage_of_continuous hg

end
