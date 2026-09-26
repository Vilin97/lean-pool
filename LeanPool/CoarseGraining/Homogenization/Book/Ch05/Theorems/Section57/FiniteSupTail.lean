/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleUnion

/-! # Finite Sup Tail -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped BigOperators ENNReal

/-!
# Finite supremum tail bounds without logarithmic scale inflation

The no-loss minimal-scale proof uses finite union bounds directly at the
probability level.  This avoids first packaging a finite maximum as an
`O_{\Gamma}` random variable with a logarithmic scale factor, which is the
source of the non-note-facing exponent loss in the discarded route.
-/

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

omit [MeasurableSpace Ω] [DecidableEq ι] in
/-- A finite supremum tail is contained in the union of the individual tails. -/
theorem finiteSupTail_subset_iUnion
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ} {T : ℝ} :
    {ω | T < s.sup' hs (fun i => X i ω)} ⊆
      ⋃ i : {i // i ∈ s}, {ω | T < X i.1 ω} := by
  intro ω hω
  change T < s.sup' hs (fun i => X i ω) at hω
  obtain ⟨i, hi, hTi⟩ := (Finset.lt_sup'_iff hs).1 hω
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hTi⟩

omit [DecidableEq ι] in
/-- Union-bound tail estimate for a finite supremum. -/
theorem measureReal_finiteSupTail_le_sum
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ} {T : ℝ} :
    μ.real {ω | T < s.sup' hs (fun i => X i ω)} ≤
      ∑ i : {i // i ∈ s}, μ.real {ω | T < X i.1 ω} := by
  calc
    μ.real {ω | T < s.sup' hs (fun i => X i ω)}
        ≤ μ.real (⋃ i : {i // i ∈ s}, {ω | T < X i.1 ω}) :=
          measureReal_mono (μ := μ)
            (finiteSupTail_subset_iUnion (Ω := Ω) hs)
    _ ≤ ∑ i : {i // i ∈ s}, μ.real {ω | T < X i.1 ω} :=
          measureReal_iUnion_fintype_le (μ := μ)
            (f := fun i : {i // i ∈ s} => {ω | T < X i.1 ω})

omit [DecidableEq ι] in
/-- Common-tail version of `measureReal_finiteSupTail_le_sum`. -/
theorem measureReal_finiteSupTail_le_card_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ} {T R : ℝ}
    (hR :
      ∀ i ∈ s, μ.real {ω | T < X i ω} ≤ R) :
    μ.real {ω | T < s.sup' hs (fun i => X i ω)} ≤
      (s.card : ℝ) * R := by
  calc
    μ.real {ω | T < s.sup' hs (fun i => X i ω)}
        ≤ ∑ i : {i // i ∈ s}, μ.real {ω | T < X i.1 ω} :=
          measureReal_finiteSupTail_le_sum (μ := μ) hs
    _ ≤ ∑ _i : {i // i ∈ s}, R := by
          exact Finset.sum_le_sum fun i _hi => hR i.1 i.2
    _ = (s.card : ℝ) * R := by
          simp

omit [DecidableEq ι] in
/-- A finite supremum of centered `Γσ` variables has a probability-level union
bound with the cardinality as a prefactor.  No logarithmic scale factor is
introduced. -/
theorem measureReal_finiteSup_sub_const_tail_le_card_mul_exp
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ}
    {c A lam σ : ℝ}
    (hlam : 1 ≤ lam)
    (hX :
      ∀ i ∈ s,
        IsBigOWith μ (gammaSigma σ) (fun ω => X i ω - c) A) :
    μ.real {ω | c + A * lam < s.sup' hs (fun i => X i ω)} ≤
      (s.card : ℝ) * Real.exp (-(lam ^ σ)) := by
  refine measureReal_finiteSupTail_le_card_mul (μ := μ) hs ?_
  intro i hi
  exact
    measureReal_le_exp_of_subset_upperTail_gammaSigma
      (μ := μ) (σ := σ) (X := fun ω => X i ω - c)
      (A := A) (s := lam) (E := {ω | c + A * lam < X i ω})
      (hX i hi) hlam
      (by
        intro ω hω
        change c + A * lam < X i ω at hω
        change A * lam < X i ω - c
        linarith)

omit [DecidableEq ι] in
/-- Symmetric-tail version of `measureReal_finiteSup_sub_const_tail_le_card_mul_exp`.
It keeps the finite maximum as a probability-level cardinality prefactor. -/
theorem measureReal_finiteSup_tail_le_card_mul_exp_of_isBigO
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ}
    {A lam σ : ℝ}
    (hlam : 1 ≤ lam)
    (hX :
      ∀ i ∈ s,
        IsBigO μ (gammaSigma σ) (X i) A) :
    μ.real {ω | A * lam < s.sup' hs (fun i => X i ω)} ≤
      (s.card : ℝ) * Real.exp (-(lam ^ σ)) := by
  refine measureReal_finiteSupTail_le_card_mul (μ := μ) hs ?_
  intro i hi
  have htail :
      μ.real (absTailEvent (X i) (A * lam)) ≤
        Real.exp (-(lam ^ σ)) := by
    simpa using
      (Ch04.isBigO_gammaSigma_iff (μ := μ) (X := X i) (A := A)
        (σ := σ)).1 (hX i hi) hlam
  exact
    (measureReal_mono (μ := μ)
      (by
        intro ω hω
        change A * lam < X i ω at hω
        change A * lam < |X i ω|
        exact lt_of_lt_of_le hω (le_abs_self (X i ω)))).trans htail

end

end Section57
end Ch05
end Book
end Homogenization
