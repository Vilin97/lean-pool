/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
import LeanPool.FourAP.Extension
import LeanPool.FourAP.Limit
import Mathlib.Data.PNat.Basic

/-!
# The permutation of the positive integers

This file formalizes the final proof and computability remark in the paper
“A 4AP-free permutation of the positive integers”. Starting from the empty
word, stage `n + 1` extends stage `n` with target `{n}`. These safe words give
an explicit bijection of `ℕ`, proved 4AP-free by `permutationOfSafeStages_apFree`.
Adding one to each value gives the positive sequence; shifting the positions
as well gives the positive permutation in the paper's indexing convention.

The numerical prefixes from the remark are checked separately in
its upstream numerical examples module, using the stabilization results proved here.
-/

namespace FourAP

/-- The initial stage `P⁽⁰⁾ = []` in the final proof is safe, since its
completion is the 3AP-free binary order. -/
theorem empty_safe : Safe bits [] := by
  constructor
  · simp
  · simpa [APFree, Completion] using bits_apFree

/-- The singleton-target stages `P⁽ⁿ⁾` from the proof of the theorem and the
final remark: start empty, then force `0`, `1`, `2`, ... in succession. -/
def algorithmStage : ℕ → List ℕ
  | 0 => []
  | n + 1 => extendAlgorithm (algorithmStage n) {n}

/-- Every stage of the executable construction is safe, as asserted in the
proof of the main theorem. -/
theorem algorithmStage_safe (n : ℕ) : Safe bits (algorithmStage n) := by
  induction n with
  | zero => simpa only [algorithmStage] using empty_safe
  | succ n ih => exact (extendAlgorithm_spec _ _ ih).1

/-- The executable stages retain every entry already placed (main proof). -/
theorem algorithmStage_prefix (n : ℕ) :
    (algorithmStage n).IsPrefix (algorithmStage (n + 1)) :=
  (extendAlgorithm_spec _ _ (algorithmStage_safe n)).2.1

/-- By stage `n`, all integers below `n` have appeared. This supplies the
exhaustion statement in the main proof and the termination guarantee in the
final remark's procedure for computing any given entry. -/
theorem algorithmStage_covers (n : ℕ) : ∀ t < n, t ∈ algorithmStage n := by
  induction n with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    intro t ht
    by_cases heq : t = n
    · subst t
      exact (extendAlgorithm_spec _ _ (algorithmStage_safe n)).2.2 n (by simp)
    · exact (algorithmStage_prefix n).sublist.subset (ih t (by omega))

/-- The particular computable permutation of `ℕ₀` specified by the singleton
targets in the final remark. Both this map and its inverse are executable. -/
def explicitPermutation : ℕ ≃ ℕ :=
  permutationOfSafeStages bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers

/-- The permutation computed in the final remark is 4AP-free. This connects
the executable algorithm to the theorem, rather than merely checking examples. -/
theorem explicitPermutation_apFree : SequenceAPFree explicitPermutation :=
  permutationOfSafeStages_apFree bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers

/-- The stopping criterion in the final remark: any stage long enough to
contain a position already gives the final value at that position. -/
theorem explicitPermutation_eq_getElem (n i : ℕ)
    (hi : i < (algorithmStage n).length) :
    explicitPermutation i = (algorithmStage n)[i] :=
  permutationOfSafeStages_eq_getElem bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers n i hi

/-- Reading a finite initial segment from a sufficiently long stage agrees
with the actual infinite permutation. This is the list form of the stopping
criterion and justifies the displayed numerical example in the remark. -/
theorem explicitPermutation_prefix (n m : ℕ) (hm : m ≤ (algorithmStage n).length) :
    (List.range m).map explicitPermutation = (algorithmStage n).take m := by
  apply List.ext_getElem
  · simp [List.length_take, hm]
  · intro i hi hj
    have hi' : i < m := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact explicitPermutation_eq_getElem n i (lt_of_lt_of_le hi' hm)

/-- Add one to the executable permutation, as in the last sentence of the
proof and the second displayed prefix in the final remark. Positions remain
zero-based here so the sequence can be read directly using Lean lists. -/
def explicitPositiveSequence : ℕ ≃ ℕ+ :=
  explicitPermutation.trans Equiv.pnatEquivNat.symm

/-- The positive sequence is the nonnegative permutation shifted by one,
exactly as stated in the paper. -/
@[simp] theorem explicitPositiveSequence_apply (i : ℕ) :
    (explicitPositiveSequence i : ℕ) = explicitPermutation i + 1 := rfl

/-- The explicit positive sequence avoids every nonconstant four-term AP,
including negative integer differences. This is the theorem's conclusion
for the particular computable construction in the final remark. -/
theorem explicitPositiveSequence_apFree : ∀ i j k l : ℕ,
    i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
    ¬ (((explicitPositiveSequence i : ℕ) : ℤ) = a ∧
       ((explicitPositiveSequence j : ℕ) : ℤ) = a + r ∧
       ((explicitPositiveSequence k : ℕ) : ℤ) = a + 2 * r ∧
       ((explicitPositiveSequence l : ℕ) : ℤ) = a + 3 * r) := by
  intro i j k l hij hjk hkl a r hr h
  simp only [explicitPositiveSequence_apply] at h
  apply explicitPermutation_apFree hij hjk hkl
  rcases h with ⟨ha, hb, hc, hd⟩
  unfold IsAP4
  constructor
  · intro hab
    have : (explicitPermutation i : ℤ) = explicitPermutation j :=
      congrArg (fun n : ℕ => (n : ℤ)) hab
    omega
  · constructor <;> omega

/-- The actual computable permutation of positive integers, with both values
and positions indexed by `ℕ+`, matching the paper's `a₁ a₂ …` convention. -/
def explicitPositivePermutation : ℕ+ ≃ ℕ+ :=
  Equiv.pnatEquivNat.trans explicitPositiveSequence

/-- The paper's main theorem for the explicitly constructed positive
permutation, now also with positive-integer positions. -/
theorem explicitPositivePermutation_apFree : ∀ i j k l : ℕ+,
    i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
    ¬ (((explicitPositivePermutation i : ℕ) : ℤ) = a ∧
       ((explicitPositivePermutation j : ℕ) : ℤ) = a + r ∧
       ((explicitPositivePermutation k : ℕ) : ℤ) = a + 2 * r ∧
       ((explicitPositivePermutation l : ℕ) : ℤ) = a + 3 * r) := by
  intro i j k l hij hjk hkl a r hr
  exact explicitPositiveSequence_apFree i.natPred j.natPred k.natPred l.natPred
    (PNat.natPred_strictMono hij) (PNat.natPred_strictMono hjk)
    (PNat.natPred_strictMono hkl) a r hr

end FourAP
