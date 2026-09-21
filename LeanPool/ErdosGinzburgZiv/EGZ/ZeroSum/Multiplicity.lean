/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Constants
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass

/-!
# Zero sums in natural-valued multiplicities

The decomposition and expansion arguments use multiplicity functions.  The
EGZ constant uses sequences with distinct selected positions.  This file
supplies the bridge between these two models.
-/

open scoped BigOperators

namespace EGZ

/-- A submultiset of exactly `p` vectors whose sum vanishes. -/
def HasZeroSumMultiplicity {p d : ℕ} [NeZero p]
    (f : FpCoord p d → ℕ) : Prop :=
  ∃ a : FpCoord p d → ℕ,
    a ≤ f ∧ natMass a = p ∧ (∑ v, a v • v) = 0

theorem HasZeroSumMultiplicity.mono {p d : ℕ} [NeZero p]
    {f g : FpCoord p d → ℕ} (h : HasZeroSumMultiplicity f)
    (hfg : f ≤ g) : HasZeroSumMultiplicity g := by
  obtain ⟨a, ha, hm, hz⟩ := h
  exact ⟨a, ha.trans hfg, hm, hz⟩

/-- The multiplicity of a vector in a finite indexed sequence. -/
noncomputable def sequenceMultiplicity {p d : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → FpCoord p d) (q : FpCoord p d) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ v i = q).card

theorem natMass_sequenceMultiplicity {p d : ℕ} [NeZero p]
    {ι : Type*} [Fintype ι] (v : ι → FpCoord p d) :
    natMass (sequenceMultiplicity v) = Fintype.card ι := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset ι))
    (t := (Finset.univ : Finset (FpCoord p d)))
    (f := v) (by simp)).symm

/-- Selecting bounded multiplicities selects distinct sequence positions,
even when the vectors at those positions coincide. -/
theorem hasZeroSumSubsequence_of_multiplicity {p d : ℕ} [NeZero p]
    {ι : Type*} [Fintype ι] (v : ι → FpCoord p d)
    (h : HasZeroSumMultiplicity (sequenceMultiplicity v)) :
    HasZeroSumSubsequence p v := by
  classical
  obtain ⟨a, ha, hm, hz⟩ := h
  have hex (q : FpCoord p d) : ∃ I : Finset ι,
      I ⊆ Finset.univ.filter (fun i ↦ v i = q) ∧ I.card = a q :=
    Finset.exists_subset_card_eq (ha q)
  choose I hI hcard using hex
  have hdisj : (↑(Finset.univ : Finset (FpCoord p d)) : Set (FpCoord p d)).PairwiseDisjoint I := by
    intro q _ r _ hqr
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hqr ((Finset.mem_filter.mp (hI q hi)).2.symm.trans
      (Finset.mem_filter.mp (hI r hj)).2)
  refine ⟨Finset.univ.biUnion I, ?_, ?_⟩
  · rw [Finset.card_biUnion hdisj]
    simpa only [hcard, natMass] using hm
  · rw [Finset.sum_biUnion hdisj]
    calc
      (∑ q, ∑ i ∈ I q, v i) = ∑ q, a q • q := by
        apply Finset.sum_congr rfl
        intro q _
        calc
          (∑ i ∈ I q, v i) = ∑ _i ∈ I q, q :=
            Finset.sum_congr rfl fun i hi ↦ (Finset.mem_filter.mp (hI q hi)).2
          _ = a q • q := by rw [Finset.sum_const, hcard]
      _ = 0 := hz

/-- A multiplicity-form estimate at an exact length gives the EGZ property
at that length. -/
theorem egzProperty_of_multiplicity {p d n : ℕ} [NeZero p]
    (h : ∀ f : FpCoord p d → ℕ, natMass f = n → HasZeroSumMultiplicity f) :
    EGZProperty p d n := by
  intro v
  apply hasZeroSumSubsequence_of_multiplicity v
  apply h
  simpa using natMass_sequenceMultiplicity v

/-- A zero sum in a cumulative node is a zero sum in the original input. -/
theorem FlagDecomposition.hasZeroSum_of_cumulative {p d : ℕ} [NeZero p]
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (h : HasZeroSumMultiplicity (Φ.cumulativeWeight x)) : HasZeroSumMultiplicity f := by
  classical
  apply h.mono
  intro v
  apply le_trans _ (Φ.retained_le v)
  apply Finset.sum_le_sum
  intro y _
  change (if y ≤ x then Φ.localWeight y v else 0) ≤ Φ.localWeight y v
  split_ifs <;> omega

end EGZ
