/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.TriangularPreprocess
import Mathlib.Data.Rat.Cardinal

/-!
# Triangular preprocessing for the rational direct sum

This module repeats only the coefficient-dependent part of the triangular bookkeeping for
`ContinuumIndex →₀ ℚ`.  It enumerates all injective rational sequences, assigns each code a
fresh coordinate strictly above the support of its sequence, and applies the generic bounded
independence selector from `Wallace.TriangularPreprocess`.

No topology or character is assumed.
-/

open Set
open scoped Cardinal

namespace Wallace
namespace RationalTriangularPreprocess

noncomputable section

open FiniteCombinatorics

abbrev ContinuumIndex := TriangularPreprocess.ContinuumIndex

/-- The direct sum of continuum many copies of the additive group of rationals. -/
abbrev ContinuumRationalGroup := ContinuumIndex →₀ ℚ

/-- All injective sequences in the rational direct sum. -/
abbrev RationalInjectiveSequences :=
  {s : ℕ → ContinuumRationalGroup // Function.Injective s}

/-- The triangular support condition for rational-valued finitely supported sequences. -/
def RationalSupportedBelow (s : ℕ → ContinuumRationalGroup) (i : ContinuumIndex) : Prop :=
  ∀ n j, j ∈ (s n).support → j < i

@[simp]
theorem mk_continuumIndex : #ContinuumIndex = 𝔠 :=
  TriangularPreprocess.mk_continuumIndex

theorem continuumIndex_infinite : Infinite ContinuumIndex :=
  TriangularPreprocess.continuumIndex_infinite

theorem mk_continuumRationalGroup : #ContinuumRationalGroup = 𝔠 := by
  letI : Infinite ContinuumIndex := continuumIndex_infinite
  change #(ContinuumIndex →₀ ℚ) = 𝔠
  rw [Cardinal.mk_finsupp_of_infinite, mk_continuumIndex, Cardinal.mkRat]
  exact max_eq_left Cardinal.aleph0_le_continuum

theorem mk_continuumRationalGroup_sequences :
    #(ℕ → ContinuumRationalGroup) = 𝔠 := by
  rw [Cardinal.mk_arrow, mk_continuumRationalGroup, Cardinal.mk_nat]
  simpa only [Cardinal.lift_id] using Cardinal.continuum_power_aleph0

/-- An injective ray in a rational basis coordinate. -/
def rationalBasisRay (i : ContinuumIndex) (n : ℕ) : ContinuumRationalGroup :=
  Finsupp.single i (n : ℚ)

theorem rationalBasisRay_injective (i : ContinuumIndex) :
    Function.Injective (rationalBasisRay i) := by
  intro m n h
  have hi := congrArg (fun z : ContinuumRationalGroup => z i) h
  exact_mod_cast (by simpa [rationalBasisRay] using hi)

theorem rationalBasisRay_family_injective :
    Function.Injective (fun i : ContinuumIndex =>
      (⟨rationalBasisRay i, rationalBasisRay_injective i⟩ : RationalInjectiveSequences)) := by
  intro i j hij
  have hfun : rationalBasisRay i = rationalBasisRay j := congrArg Subtype.val hij
  have hi := congrArg (fun s : ℕ → ContinuumRationalGroup => s 1 i) hfun
  by_contra hne
  simp [rationalBasisRay, hne] at hi

theorem mk_rationalInjectiveSequences : #RationalInjectiveSequences = 𝔠 := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq mk_continuumRationalGroup_sequences
  · rw [← mk_continuumIndex]
    exact Cardinal.mk_le_of_injective rationalBasisRay_family_injective

/-- A fixed enumeration of every injective rational sequence. -/
def rationalSequenceCodeEquiv : ContinuumIndex ≃ RationalInjectiveSequences :=
  Classical.choice <| Cardinal.eq.mp <|
    mk_continuumIndex.trans mk_rationalInjectiveSequences.symm

def codedSequence (a : ContinuumIndex) : ℕ → ContinuumRationalGroup :=
  (rationalSequenceCodeEquiv a).1

theorem codedSequence_injective (a : ContinuumIndex) :
    Function.Injective (codedSequence a) :=
  (rationalSequenceCodeEquiv a).2

/-- The union of the finite supports of a rational sequence. -/
def sequenceSupport (s : ℕ → ContinuumRationalGroup) : Set ContinuumIndex :=
  {i | ∃ n, i ∈ (s n).support}

theorem sequenceSupport_countable (s : ℕ → ContinuumRationalGroup) :
    (sequenceSupport s).Countable := by
  rw [show sequenceSupport s = ⋃ n, ((s n).support : Set ContinuumIndex) by
    ext i
    simp [sequenceSupport]]
  exact Set.countable_iUnion fun n => (s n).support.finite_toSet.countable

/-- A strict bound for every coordinate occurring in the coded sequence. -/
def supportBound (a : ContinuumIndex) : ContinuumIndex :=
  Classical.choose <| TriangularPreprocess.exists_strict_upperBound_of_countable
    (sequenceSupport_countable (codedSequence a))

theorem support_lt_supportBound (a : ContinuumIndex) {n : ℕ} {i : ContinuumIndex}
    (hi : i ∈ (codedSequence a n).support) : i < supportBound a := by
  exact (Classical.choose_spec <|
    TriangularPreprocess.exists_strict_upperBound_of_countable
      (sequenceSupport_countable (codedSequence a))) i ⟨n, hi⟩

/-- The fresh-coordinate embedding for rational sequence codes. -/
def codeIndex : ContinuumIndex ↪ ContinuumIndex :=
  ⟨TriangularPreprocess.freshIndex supportBound,
    TriangularPreprocess.freshIndex_injective supportBound⟩

theorem codedSequence_supportedBelow (a : ContinuumIndex) :
    RationalSupportedBelow (codedSequence a) (codeIndex a) := by
  intro n i hi
  exact (support_lt_supportBound a hi).trans
    (TriangularPreprocess.freshIndex_spec supportBound a).1

/-- The rational basis point assigned to a code. -/
def codeBasisVector (a : ContinuumIndex) : ContinuumRationalGroup :=
  Finsupp.single (codeIndex a) 1

/-- The translated sequence used for bounded-independence preprocessing. -/
def codedDifference (a : ContinuumIndex) (n : ℕ) : ContinuumRationalGroup :=
  codedSequence a n - codeBasisVector a

theorem codedDifference_injective (a : ContinuumIndex) :
    Function.Injective (codedDifference a) := by
  intro m n hmn
  apply codedSequence_injective a
  have h := congrArg (fun z => z + codeBasisVector a) hmn
  simpa [codedDifference] using h

/-- Full block preprocessing for rational sequences. -/
theorem triangular_block_preprocess
    (a : ContinuumIndex)
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ l, (TriangularPreprocess.blockPositions N hN l).card = N l ∧
        BoundedIndependent (M l)
          ((TriangularPreprocess.blockPositions N hN l).image fun n =>
            codedSequence a (φ n) - codeBasisVector a)) ∧
      RationalSupportedBelow (codedSequence a ∘ φ) (codeIndex a) := by
  obtain ⟨φ, hφ, hblocks⟩ :=
    TriangularPreprocess.exists_boundedIndependent_subsequence_for_sizes
      (codedDifference a) (codedDifference_injective a) N hN M
  refine ⟨φ, hφ, ?_, ?_⟩
  · simpa only [codedDifference] using hblocks
  · intro n i hi
    exact codedSequence_supportedBelow a (φ n) i hi

end

end RationalTriangularPreprocess
end Wallace
