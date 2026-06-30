/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Elementary finite probability

This file avoids measure-theory overhead for the upper-bound proof.  All random
objects used there are uniform on finite types, so probability and expectation
are just normalized finite sums.
-/

namespace PebblingLean

namespace FiniteProbability

variable {Ω ι : Type*}

/-- Uniform probability of an event on a finite sample space, as a rational
number. -/
noncomputable def uniformProbability [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) / (Fintype.card Ω : ℚ)

/-- Uniform expectation of a natural-valued random variable on a finite sample
space, as a rational number. -/
noncomputable def uniformExpectation [Fintype Ω] (X : Ω → ℕ) : ℚ :=
  (∑ ω : Ω, (X ω : ℚ)) / (Fintype.card Ω : ℚ)

theorem exists_not_of_uniformProbability_lt_one [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (hprob : uniformProbability P < 1) :
    ∃ ω : Ω, ¬ P ω := by
  classical
  by_contra hnone
  have hall : ∀ ω : Ω, P ω := by
    intro ω
    by_contra hω
    exact hnone ⟨ω, hω⟩
  have hfilter :
      (Finset.univ.filter P).card = Fintype.card Ω := by
    rw [Finset.card_eq_iff_eq_univ]
    exact Finset.filter_eq_self.mpr fun ω _ => hall ω
  have hcard_ne : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hprob_eq : uniformProbability P = 1 := by
    unfold uniformProbability
    rw [hfilter]
    field_simp [hcard_ne]
  linarith

/-- Union bound for finite uniform probabilities. -/
theorem uniformProbability_exists_le_sum [Fintype Ω] [Nonempty Ω]
    [Fintype ι] (P : ι → Ω → Prop)
    [∀ i, DecidablePred (P i)]
    [DecidablePred fun ω => ∃ i : ι, P i ω] :
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω) ≤
      ∑ i : ι, uniformProbability (P i) := by
  classical
  let bad : Finset Ω := Finset.univ.filter fun ω : Ω => ∃ i : ι, P i ω
  let badAt : ι → Finset Ω := fun i => Finset.univ.filter fun ω : Ω => P i ω
  have hsubset : bad ⊆ Finset.univ.biUnion badAt := by
    intro ω hω
    have hex : ∃ i : ι, P i ω := by
      simpa [bad] using hω
    rcases hex with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [badAt, hi]⟩
  have hcard :
      bad.card ≤ ∑ i : ι, (badAt i).card := by
    exact (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hden_nonneg : 0 ≤ (Fintype.card Ω : ℚ) := by positivity
  calc
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω)
        = (bad.card : ℚ) / (Fintype.card Ω : ℚ) := by
          rfl
    _ ≤ ((∑ i : ι, (badAt i).card : ℕ) : ℚ) / (Fintype.card Ω : ℚ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden_nonneg
    _ = ∑ i : ι, uniformProbability (P i) := by
          simp [uniformProbability, badAt, Finset.sum_div]

end FiniteProbability

end PebblingLean
