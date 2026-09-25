/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineCertifiedPairEligibility
public import LeanPool.BeyondBethe.BeyondBethe.MachineListReverse

/-!
# Disjointness from an encoded row-pair list

An ordered row pair is encoded as a pair of unary row rulers.  The scanner
tests whether a candidate pair shares an endpoint with any selected pair.
It iterates for the bit-length of the selected-list encoding, so malformed
inputs remain polynomially bounded; after the encoded list is exhausted the
step stutters.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

def orderedRowPairCode {n : ℕ} (q : Fin n × Fin n) : List Bool :=
  pair (finUnaryCode q.1) (finUnaryCode q.2)

def machineDisjointCandidateFirst (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDisjointRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineDisjointCandidateSecond (word : List Bool) : List Bool :=
  machinePairFirst (machineDisjointRest word)

def machineDisjointSelectedList (word : List Bool) : List Bool :=
  machinePairSecond (machineDisjointRest word)

def machineDisjointPack
    (remaining conflict source : List Bool) : List Bool :=
  pair remaining (pair conflict source)

def machineDisjointRemaining (state : List Bool) : List Bool :=
  machinePairFirst state

def machineDisjointConflict (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineDisjointSource (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond state)

def machineDisjointCurrentPair (state : List Bool) : List Bool :=
  machineListHead (machineDisjointRemaining state)

def machineDisjointCurrentFirst (state : List Bool) : List Bool :=
  machinePairFirst (machineDisjointCurrentPair state)

def machineDisjointCurrentSecond (state : List Bool) : List Bool :=
  machinePairSecond (machineDisjointCurrentPair state)

def machineUnaryRulersEqualBit (lhs rhs : List Bool) : List Bool :=
  machineBinaryNatEqBit (pair (machineLengthBits lhs) (machineLengthBits rhs))

def machineDisjointIFirstBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit
    (machineDisjointCandidateFirst (machineDisjointSource state))
    (machineDisjointCurrentFirst state)

def machineDisjointISecondBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit
    (machineDisjointCandidateFirst (machineDisjointSource state))
    (machineDisjointCurrentSecond state)

def machineDisjointJFirstBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit
    (machineDisjointCandidateSecond (machineDisjointSource state))
    (machineDisjointCurrentFirst state)

def machineDisjointJSecondBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit
    (machineDisjointCandidateSecond (machineDisjointSource state))
    (machineDisjointCurrentSecond state)

def machineDisjointCurrentConflictBit (state : List Bool) : List Bool :=
  machineOrBit (machineDisjointIFirstBit state)
    (machineOrBit (machineDisjointISecondBit state)
      (machineOrBit (machineDisjointJFirstBit state)
        (machineDisjointJSecondBit state)))

def machineDisjointInputBound (word : List Bool) : List Bool :=
  pair [false] word

def machineDisjointNextConflict (state : List Bool) : List Bool :=
  (machineOrBit (machineDisjointConflict state)
      (machineDisjointCurrentConflictBit state)).take
    (machineDisjointInputBound (machineDisjointSource state)).length

def machineDisjointProcess (state : List Bool) : List Bool :=
  machineDisjointPack (machineListTail (machineDisjointRemaining state))
    (machineDisjointNextConflict state) (machineDisjointSource state)

def machineDisjointStep (state : List Bool) : List Bool :=
  machineIfEmpty (machineDisjointRemaining state) state
    (machineDisjointProcess state)

def machineDisjointInit (word : List Bool) : List Bool :=
  machineDisjointPack (machineDisjointSelectedList word) [false] word

def machineDisjointWidth (word : List Bool) : List Bool :=
  let bound := machineDisjointInputBound word
  machineDisjointPack bound bound bound

def machineDisjointFinalState (word : List Bool) : List Bool :=
  (machineDisjointStep)^[(machineDisjointSelectedList word).length]
    (machineDisjointInit word)

def machineRowPairConflictBit (word : List Bool) : List Bool :=
  machineDisjointConflict (machineDisjointFinalState word)

/-- One bit, true exactly when the candidate is disjoint from every encoded
selected pair on canonical inputs. -/
def machineRowPairDisjointBit (word : List Bool) : List Bool :=
  machineNotBit (machineRowPairConflictBit word)

theorem machineDisjointCandidateFirst_mem_FP :
    machineDisjointCandidateFirst ∈ FP := machinePairFirst_mem_FP

theorem machineDisjointRest_mem_FP : machineDisjointRest ∈ FP :=
  machinePairSecond_mem_FP

theorem machineDisjointCandidateSecond_mem_FP :
    machineDisjointCandidateSecond ∈ FP := by
  simpa only [machineDisjointCandidateSecond] using! machineCompose_mem_FP
    machineDisjointRest_mem_FP machinePairFirst_mem_FP

theorem machineDisjointSelectedList_mem_FP :
    machineDisjointSelectedList ∈ FP := by
  simpa only [machineDisjointSelectedList] using! machineCompose_mem_FP
    machineDisjointRest_mem_FP machinePairSecond_mem_FP

theorem machineDisjointRemaining_mem_FP : machineDisjointRemaining ∈ FP :=
  machinePairFirst_mem_FP

theorem machineDisjointConflict_mem_FP : machineDisjointConflict ∈ FP := by
  simpa only [machineDisjointConflict] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineDisjointSource_mem_FP : machineDisjointSource ∈ FP := by
  simpa only [machineDisjointSource] using! machineCompose_mem_FP
    machinePairSecond_mem_FP machinePairSecond_mem_FP

theorem machineDisjointCurrentPair_mem_FP :
    machineDisjointCurrentPair ∈ FP := by
  simpa only [machineDisjointCurrentPair] using! machineCompose_mem_FP
    machineDisjointRemaining_mem_FP machineListHead_mem_FP

theorem machineDisjointCurrentFirst_mem_FP :
    machineDisjointCurrentFirst ∈ FP := by
  simpa only [machineDisjointCurrentFirst] using! machineCompose_mem_FP
    machineDisjointCurrentPair_mem_FP machinePairFirst_mem_FP

theorem machineDisjointCurrentSecond_mem_FP :
    machineDisjointCurrentSecond ∈ FP := by
  simpa only [machineDisjointCurrentSecond] using! machineCompose_mem_FP
    machineDisjointCurrentPair_mem_FP machinePairSecond_mem_FP

theorem machineUnaryRulersEqualBit_mem_FP
    {lhs rhs : List Bool → List Bool} (hlhs : lhs ∈ FP) (hrhs : rhs ∈ FP) :
    (fun word ↦ machineUnaryRulersEqualBit (lhs word) (rhs word)) ∈ FP := by
  have hl := machineCompose_mem_FP hlhs machineLengthBits_mem_FP
  have hr := machineCompose_mem_FP hrhs machineLengthBits_mem_FP
  have hinput := machinePair_mem_FP hl hr
  simpa only [machineUnaryRulersEqualBit] using! machineCompose_mem_FP hinput
    machineBinaryNatEqBit_mem_FP

theorem machineDisjointIFirstBit_mem_FP : machineDisjointIFirstBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    (machineCompose_mem_FP machineDisjointSource_mem_FP
      machineDisjointCandidateFirst_mem_FP)
    machineDisjointCurrentFirst_mem_FP

theorem machineDisjointISecondBit_mem_FP : machineDisjointISecondBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    (machineCompose_mem_FP machineDisjointSource_mem_FP
      machineDisjointCandidateFirst_mem_FP)
    machineDisjointCurrentSecond_mem_FP

theorem machineDisjointJFirstBit_mem_FP : machineDisjointJFirstBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    (machineCompose_mem_FP machineDisjointSource_mem_FP
      machineDisjointCandidateSecond_mem_FP)
    machineDisjointCurrentFirst_mem_FP

theorem machineDisjointJSecondBit_mem_FP : machineDisjointJSecondBit ∈ FP := by
  exact machineUnaryRulersEqualBit_mem_FP
    (machineCompose_mem_FP machineDisjointSource_mem_FP
      machineDisjointCandidateSecond_mem_FP)
    machineDisjointCurrentSecond_mem_FP

theorem machineDisjointCurrentConflictBit_mem_FP :
    machineDisjointCurrentConflictBit ∈ FP := by
  exact machineOrBit_mem_FP machineDisjointIFirstBit_mem_FP
    (machineOrBit_mem_FP machineDisjointISecondBit_mem_FP
      (machineOrBit_mem_FP machineDisjointJFirstBit_mem_FP
        machineDisjointJSecondBit_mem_FP))

theorem machineDisjointInputBound_mem_FP : machineDisjointInputBound ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP

theorem machineDisjointNextConflict_mem_FP :
    machineDisjointNextConflict ∈ FP := by
  have hdata := machineOrBit_mem_FP machineDisjointConflict_mem_FP
    machineDisjointCurrentConflictBit_mem_FP
  have hbound := machineCompose_mem_FP machineDisjointSource_mem_FP
    machineDisjointInputBound_mem_FP
  simpa only [machineDisjointNextConflict] using! machineTake_mem_FP hbound hdata

theorem machineDisjointProcess_mem_FP : machineDisjointProcess ∈ FP := by
  have htail := machineCompose_mem_FP machineDisjointRemaining_mem_FP
    machineListTail_mem_FP
  exact machinePair_mem_FP htail
    (machinePair_mem_FP machineDisjointNextConflict_mem_FP
      machineDisjointSource_mem_FP)

theorem machineDisjointStep_mem_FP : machineDisjointStep ∈ FP := by
  simpa only [machineDisjointStep] using! machineIfEmpty_mem_FP
    machineDisjointRemaining_mem_FP id_mem_FP machineDisjointProcess_mem_FP

theorem machineDisjointInit_mem_FP : machineDisjointInit ∈ FP :=
  machinePair_mem_FP machineDisjointSelectedList_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP)

theorem machineDisjointWidth_mem_FP : machineDisjointWidth ∈ FP :=
  machinePair_mem_FP machineDisjointInputBound_mem_FP
    (machinePair_mem_FP machineDisjointInputBound_mem_FP
      machineDisjointInputBound_mem_FP)

@[simp] theorem machineDisjointRemaining_pack (remaining conflict source) :
    machineDisjointRemaining (machineDisjointPack remaining conflict source) =
      remaining := by simp [machineDisjointRemaining, machineDisjointPack]

@[simp] theorem machineDisjointConflict_pack (remaining conflict source) :
    machineDisjointConflict (machineDisjointPack remaining conflict source) =
      conflict := by simp [machineDisjointConflict, machineDisjointPack]

@[simp] theorem machineDisjointSource_pack (remaining conflict source) :
    machineDisjointSource (machineDisjointPack remaining conflict source) =
      source := by simp [machineDisjointSource, machineDisjointPack]

def MachineDisjointStateBound (word state : List Bool) : Prop :=
  let B := (machineDisjointInputBound word).length
  state = machineDisjointPack (machineDisjointRemaining state)
      (machineDisjointConflict state) (machineDisjointSource state) ∧
    (machineDisjointRemaining state).length ≤ B ∧
    (machineDisjointConflict state).length ≤ B ∧
    machineDisjointSource state = word

theorem machineDisjointSelected_length_le (word : List Bool) :
    (machineDisjointSelectedList word).length ≤
      (machineDisjointInputBound word).length := by
  exact ((machinePairSecond_length_le (machineDisjointRest word)).trans
    (machinePairSecond_length_le word)).trans
      (by
        simp only [machineDisjointInputBound, pair_length]
        omega)

theorem machineDisjoint_one_le_bound (word : List Bool) :
    1 ≤ (machineDisjointInputBound word).length := by
  simp only [machineDisjointInputBound, pair_length]
  omega

theorem machineDisjoint_source_le_bound (word : List Bool) :
    word.length ≤ (machineDisjointInputBound word).length := by
  simp only [machineDisjointInputBound, pair_length]
  omega

theorem machineDisjointInit_bound (word : List Bool) :
    MachineDisjointStateBound word (machineDisjointInit word) := by
  simp only [MachineDisjointStateBound, machineDisjointInit,
    machineDisjointRemaining_pack, machineDisjointConflict_pack,
    machineDisjointSource_pack]
  exact ⟨trivial, machineDisjointSelected_length_le word,
    machineDisjoint_one_le_bound word, trivial⟩

theorem machineDisjointStep_bound {word state : List Bool}
    (hstate : MachineDisjointStateBound word state) :
    MachineDisjointStateBound word (machineDisjointStep state) := by
  rcases hstate with ⟨hpack, hremaining, hconflict, hsource⟩
  by_cases hrem : machineDisjointRemaining state = []
  · rw [machineDisjointStep, hrem, machineIfEmpty_nil]
    exact ⟨hpack, hremaining, hconflict, hsource⟩
  · rw [machineDisjointStep]
    cases hcode : machineDisjointRemaining state with
    | nil => exact False.elim (hrem hcode)
    | cons bit tail =>
        rw [machineIfEmpty_cons, machineDisjointProcess]
        simp only [MachineDisjointStateBound, machineDisjointRemaining_pack,
          machineDisjointConflict_pack, machineDisjointSource_pack]
        refine ⟨trivial, ?_, ?_, hsource⟩
        · exact (machinePairSecond_length_le
            (machineDisjointRemaining state)).trans hremaining
        · simp only [machineDisjointNextConflict, List.length_take]
          rw [hsource]
          exact Nat.min_le_left _ _

theorem machineDisjointIterate_bound (word : List Bool) : ∀ k,
    MachineDisjointStateBound word
      ((machineDisjointStep)^[k] (machineDisjointInit word)) := by
  intro k
  induction k with
  | zero => exact machineDisjointInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineDisjointStep_bound ih

theorem machineDisjointIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineDisjointSelectedList word).length) :
    ((machineDisjointStep)^[iterations] (machineDisjointInit word)).length ≤
      (machineDisjointWidth word).length := by
  rcases machineDisjointIterate_bound word iterations with
    ⟨hpack, hremaining, hconflict, hsource⟩
  have hsourceLength : (machineDisjointSource
      ((machineDisjointStep)^[iterations] (machineDisjointInit word))).length ≤
      (machineDisjointInputBound word).length := by
    rw [hsource]
    exact machineDisjoint_source_le_bound word
  rw [hpack]
  simp only [machineDisjointPack, machineDisjointWidth, pair_length]
  omega

theorem machineDisjointFinalState_mem_FP : machineDisjointFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineDisjointStep_mem_FP
    machineDisjointInit_mem_FP machineDisjointSelectedList_mem_FP
    machineDisjointWidth_mem_FP machineDisjointIterate_length_le_width

theorem machineRowPairConflictBit_mem_FP : machineRowPairConflictBit ∈ FP := by
  simpa only [machineRowPairConflictBit] using! machineCompose_mem_FP
    machineDisjointFinalState_mem_FP machineDisjointConflict_mem_FP

theorem machineRowPairDisjointBit_mem_FP : machineRowPairDisjointBit ∈ FP :=
  machineNotBit_mem_FP machineRowPairConflictBit_mem_FP

/-! ## Exact semantics -/

def orderedPairsConflict {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) : Bool :=
  selected.any fun q ↦ decide (i = q.1 ∨ i = q.2 ∨ j = q.1 ∨ j = q.2)

def machineDisjointInput {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) : List Bool :=
  pair (finUnaryCode i)
    (pair (finUnaryCode j) (binaryListCode orderedRowPairCode selected))

@[simp] theorem machineUnaryRulersEqualBit_encode {n : ℕ}
    (i j : Fin n) :
    machineUnaryRulersEqualBit (finUnaryCode i) (finUnaryCode j) =
      [decide (i = j)] := by
  rw [machineUnaryRulersEqualBit]
  simp only [machineLengthBits_encode, finUnaryCode, List.length_replicate,
    machineBinaryNatEqBit_pair_natBits]
  by_cases hval : i.1 = j.1
  · have h : i = j := Fin.ext hval
    simp [hval, h]
  · have h : i ≠ j := fun hij ↦ hval (congrArg Fin.val hij)
    simp [hval, h]

@[simp] theorem machineDisjointCurrentConflictBit_encode {n : ℕ}
    (i j x y : Fin n) (qs sourceSelected : List (Fin n × Fin n))
    (conflict : Bool) :
    machineDisjointCurrentConflictBit
        (machineDisjointPack
          (binaryListCode orderedRowPairCode ((x, y) :: qs)) [conflict]
          (machineDisjointInput i j sourceSelected)) =
      [decide (i = x ∨ i = y ∨ j = x ∨ j = y)] := by
  simp only [machineDisjointCurrentConflictBit, machineDisjointIFirstBit,
    machineDisjointISecondBit, machineDisjointJFirstBit,
    machineDisjointJSecondBit, machineDisjointSource_pack,
    machineDisjointCurrentFirst, machineDisjointCurrentSecond,
    machineDisjointCurrentPair, machineDisjointRemaining_pack,
    machineListHead_cons, orderedRowPairCode, machinePairFirst_pair,
    machinePairSecond_pair, machineDisjointCandidateFirst,
    machineDisjointCandidateSecond, machineDisjointRest,
    machineDisjointInput, machineUnaryRulersEqualBit_encode,
    machineOrBit_one]
  by_cases hix : i = x <;> by_cases hiy : i = y <;>
    by_cases hjx : j = x <;> by_cases hjy : j = y <;>
    simp [hix, hiy, hjx, hjy]

def machineDisjointSemanticState {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) (k : ℕ) : List Bool :=
  machineDisjointPack
    (binaryListCode orderedRowPairCode (selected.drop k))
    [orderedPairsConflict i j (selected.take k)]
    (machineDisjointInput i j selected)

@[simp] theorem machineDisjointSemanticState_zero {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) :
    machineDisjointSemanticState i j selected 0 =
      machineDisjointInit (machineDisjointInput i j selected) := by
  simp [machineDisjointSemanticState, machineDisjointInit,
    machineDisjointInput, machineDisjointSelectedList,
    machineDisjointRest, orderedPairsConflict]

theorem machineDisjointSemanticState_step {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n))
    (k : ℕ) (hk : k < selected.length) :
    machineDisjointStep (machineDisjointSemanticState i j selected k) =
      machineDisjointSemanticState i j selected (k + 1) := by
  rw [machineDisjointSemanticState, List.drop_eq_getElem_cons hk,
    machineDisjointStep]
  simp only [machineDisjointRemaining_pack]
  rw [machineIfEmpty_of_ne_nil_matrix _ _ _
    (binaryListCode_cons_ne_nil orderedRowPairCode selected[k]
      (selected.drop (k + 1)))]
  rw [machineDisjointProcess]
  simp only [machineDisjointRemaining_pack, machineListTail_cons,
    machineDisjointSource_pack, machineDisjointNextConflict,
    machineDisjointConflict_pack]
  rcases hp : selected[k] with ⟨x, y⟩
  rw [machineDisjointCurrentConflictBit_encode]
  simp only [machineOrBit_one]
  have hbound : 1 ≤
      (machineDisjointInputBound (machineDisjointInput i j selected)).length :=
    machineDisjoint_one_le_bound _
  rw [(List.take_eq_self_iff _).2 (by simpa using! hbound)]
  rw [machineDisjointSemanticState]
  apply congrArg (fun z : Bool ↦ machineDisjointPack
    (binaryListCode orderedRowPairCode (selected.drop (k + 1))) [z]
    (machineDisjointInput i j selected))
  rw [orderedPairsConflict, orderedPairsConflict,
    ← List.take_concat_get hk, List.concat_eq_append, List.any_append]
  simp [hp]

theorem machineDisjointIterate_semantics {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) : ∀ k ≤ selected.length,
    (machineDisjointStep)^[k]
        (machineDisjointInit (machineDisjointInput i j selected)) =
      machineDisjointSemanticState i j selected k := by
  intro k hk
  induction k with
  | zero => exact (machineDisjointSemanticState_zero i j selected).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact machineDisjointSemanticState_step i j selected k (by omega)

theorem machineDisjoint_done_iterate
    (extra : ℕ) (conflict source : List Bool) :
    (machineDisjointStep)^[extra]
        (machineDisjointPack [] conflict source) =
      machineDisjointPack [] conflict source := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineDisjointStep]

@[simp] theorem machineDisjointSelectedList_input {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) :
    machineDisjointSelectedList (machineDisjointInput i j selected) =
      binaryListCode orderedRowPairCode selected := by
  simp [machineDisjointSelectedList, machineDisjointRest,
    machineDisjointInput]

@[simp] theorem machineRowPairConflictBit_encode {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) :
    machineRowPairConflictBit (machineDisjointInput i j selected) =
      [orderedPairsConflict i j selected] := by
  rw [machineRowPairConflictBit, machineDisjointFinalState,
    machineDisjointSelectedList_input]
  let word := binaryListCode orderedRowPairCode selected
  have hle : selected.length ≤ word.length :=
    binaryListCode_listLength_le orderedRowPairCode selected
  have hsplit : word.length = (word.length - selected.length) + selected.length := by
    omega
  rw [hsplit, Function.iterate_add_apply,
    machineDisjointIterate_semantics i j selected selected.length le_rfl]
  simp only [machineDisjointSemanticState, List.drop_length, List.take_length]
  change machineDisjointConflict
      ((machineDisjointStep)^[word.length - selected.length]
        (machineDisjointPack [] [orderedPairsConflict i j selected]
          (machineDisjointInput i j selected))) = _
  rw [machineDisjoint_done_iterate]
  simp only [machineDisjointConflict_pack]

@[simp] theorem machineRowPairDisjointBit_encode {n : ℕ}
    (i j : Fin n) (selected : List (Fin n × Fin n)) :
    machineRowPairDisjointBit (machineDisjointInput i j selected) =
      [!orderedPairsConflict i j selected] := by
  rw [machineRowPairDisjointBit, machineRowPairConflictBit_encode,
    machineNotBit_one]

end BeyondBethe
