/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Defs
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Finite-state structured RAM scanners — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace Scanner

open Internal

private abbrev StoreBound (spec : Spec) (inputLength : ℕ) (store : Store) : Prop :=
  StoreEnvelope (inputLength + inputBase spec) (inputLength + inputBase spec) store

private abbrev width (spec : Spec) (inputLength : ℕ) : ℕ :=
  valueWidth (inputLength + inputBase spec)

private abbrev resourceSpace (spec : Spec) (inputLength : ℕ) : ℕ :=
  envelopeSpace (inputLength + inputBase spec) (inputLength + inputBase spec)

private theorem envelopeSpace_eq_spaceBound (spec : Spec) (inputLength : ℕ) :
    resourceSpace spec inputLength = spaceBound spec inputLength := by
  simp [resourceSpace, envelopeSpace, spaceBound, two_mul]

private theorem inputStore_bound (spec : Spec) (bits : List Bool) :
    StoreBound spec bits.length (inputStore spec bits) := by
  apply Internal.Input.bitStoreEnvelope
  · simp [lengthReg, inputBase, transitionBase]
  · simp [inputBase, transitionBase]
    omega
  · exact Nat.le_add_right _ _
  · have hinitial := spec.initial_lt
    have hpositive : 0 < spec.stateCount := by omega
    simp [inputBase, transitionBase]
    omega

private theorem setupIndices_nodup (spec : Spec) :
    (setupIndices spec).Nodup := by
  rw [setupIndices, List.nodup_append']
  refine ⟨by decide, List.nodup_range', ?_⟩
  rw [List.disjoint_left]
  intro index hfixed htable
  have hlt : index < transitionBase := by
    simp [fixedSetupIndices, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg,
      acceptBaseReg] at hfixed
    simp [transitionBase]
    omega
  have hle : transitionBase ≤ index :=
    List.left_le_of_mem_range' htable
  omega

private theorem setupWrites_nodup (spec : Spec) :
    ((setupWrites spec).map Prod.fst).Nodup := by
  have hmap : (setupWrites spec).map Prod.fst = setupIndices spec := by
    simp [setupWrites, List.map_map, Function.comp_def]
  rw [hmap]
  exact setupIndices_nodup spec

private theorem setupOps_length (spec : Spec) :
    (setupOps spec).length = 6 + 3 * spec.stateCount := by
  simp [setupOps, setupWrites, setupIndices, fixedSetupIndices, tableIndices]
  ring

private theorem transitionAddress_mem (spec : Spec) (state : ℕ)
    (hstate : state < spec.stateCount) (bit : Bool) :
    transitionAddress state bit ∈ setupIndices spec := by
  rw [setupIndices, List.mem_append]
  right
  rw [tableIndices]
  apply List.mem_range'.mpr
  refine ⟨2 * state + Input.bitValue bit, ?_, ?_⟩
  · cases bit <;> simp [Input.bitValue]
    all_goals omega
  · simp [transitionAddress]
    omega

private theorem acceptAddress_mem (spec : Spec) (state : ℕ)
    (hstate : state < spec.stateCount) :
    acceptAddress spec state ∈ setupIndices spec := by
  rw [setupIndices, List.mem_append]
  right
  rw [tableIndices]
  apply List.mem_range'.mpr
  refine ⟨2 * spec.stateCount + state, by omega, ?_⟩
  simp [acceptAddress, acceptBase]
  omega

private theorem setupValue_transition (spec : Spec) (state : ℕ)
    (hstate : state < spec.stateCount) (bit : Bool) :
    setupValue spec (transitionAddress state bit) = spec.step state bit := by
  have hlt : transitionAddress state bit < acceptBase spec := by
    cases bit <;> simp [transitionAddress, Input.bitValue, acceptBase]
    all_goals omega
  have hdiv : (transitionAddress state bit - transitionBase) / 2 = state := by
    cases bit <;> simp [transitionAddress, Input.bitValue, transitionBase]
    all_goals omega
  have hbit : decide ((transitionAddress state bit - transitionBase) % 2 = 1) = bit := by
    cases bit <;> simp [transitionAddress, Input.bitValue, transitionBase]
    all_goals omega
  unfold setupValue
  split_ifs with hs hp ho ht htr ha
  · simp [transitionAddress, Input.bitValue, stateReg, transitionBase] at hs
    omega
  · simp [transitionAddress, Input.bitValue, pointerReg, transitionBase] at hp
    omega
  · simp [transitionAddress, Input.bitValue, oneReg, transitionBase] at ho
    omega
  · simp [transitionAddress, Input.bitValue, twoReg, transitionBase] at ht
    omega
  · simp [transitionAddress, Input.bitValue, transitionBaseReg, transitionBase] at htr
    omega
  · simp [transitionAddress, Input.bitValue, acceptBaseReg, transitionBase] at ha
    omega
  · dsimp only
    rw [hdiv, hbit]

private theorem setupValue_accept (spec : Spec) (state : ℕ)
    (hstate : state < spec.stateCount) :
    setupValue spec (acceptAddress spec state) = Input.bitValue (spec.accept state) := by
  have hnotLt : ¬acceptAddress spec state < acceptBase spec := by
    simp [acceptAddress]
  have hdiff : acceptAddress spec state - acceptBase spec = state := by
    simp [acceptAddress]
  unfold setupValue
  split_ifs with hs hp ho ht htr ha
  · simp [acceptAddress, acceptBase, stateReg, transitionBase] at hs
    omega
  · simp [acceptAddress, acceptBase, pointerReg, transitionBase] at hp
    omega
  · simp [acceptAddress, acceptBase, oneReg, transitionBase] at ho
    omega
  · simp [acceptAddress, acceptBase, twoReg, transitionBase] at ht
    omega
  · simp [acceptAddress, acceptBase, transitionBaseReg, transitionBase] at htr
    omega
  · simp [acceptAddress, acceptBase, acceptBaseReg, transitionBase] at ha
    omega
  · rw [hdiff]

private theorem setupValue_le_inputBase (spec : Spec) (index : ℕ)
    (hindex : index ∈ setupIndices spec) :
    setupValue spec index ≤ inputBase spec := by
  rcases List.mem_append.mp hindex with hfixed | htable
  · simp [fixedSetupIndices] at hfixed
    rcases hfixed with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals have hinitial := spec.initial_lt
    all_goals simp [setupValue, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg,
      acceptBaseReg, inputBase, acceptBase, transitionBase] <;> omega
  · obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp htable
    unfold setupValue
    split_ifs with hs hp ho ht htr ha htableLt
    · simp [stateReg, transitionBase] at hs
      omega
    · simp [pointerReg, transitionBase] at hp
      omega
    · simp [oneReg, transitionBase] at ho
      omega
    · simp [twoReg, transitionBase] at ht
      omega
    · simp [transitionBaseReg, transitionBase] at htr
      omega
    · simp [acceptBaseReg, transitionBase] at ha
      omega
    · have hstate : offset / 2 < spec.stateCount := by
        simp [acceptBase, transitionBase] at htableLt
        omega
      have hbase : spec.stateCount ≤ inputBase spec := by
        simp [inputBase, transitionBase]
        omega
      dsimp only
      simp only [Nat.add_sub_cancel_left, one_mul]
      change spec.step (offset / 2) (decide (offset % 2 = 1)) ≤ inputBase spec
      exact (spec.step_lt (offset / 2) hstate _).le.trans hbase
    · have hpositive : 1 ≤ inputBase spec := by
        have hinitial := spec.initial_lt
        simp [inputBase, transitionBase]
        omega
      simp only [Input.bitValue]
      split <;> omega

private def setupStore (spec : Spec) (bits : List Bool) : Store :=
  Basic.execList (setupOps spec) (inputStore spec bits)

private theorem setupStore_apply (spec : Spec) (bits : List Bool) (index : ℕ)
    (hindex : index ∈ setupIndices spec) :
    setupStore spec bits index = setupValue spec index := by
  apply Basic.execList_imm_apply_of_mem (setupWrites spec) (inputStore spec bits)
    (setupWrites_nodup spec)
  simp [setupWrites, hindex]

private theorem setupStore_unwritten (spec : Spec) (bits : List Bool) (index : ℕ)
    (hindex : index ∉ setupIndices spec) :
    setupStore spec bits index = inputStore spec bits index := by
  apply Basic.execList_imm_apply_of_not_mem (setupWrites spec)
  simpa [setupWrites, List.map_map, Function.comp_def] using hindex

private theorem setupStore_high (spec : Spec) (bits : List Bool) (index : ℕ)
    (hindex : inputBase spec ≤ index) :
    setupStore spec bits index = inputStore spec bits index := by
  apply Basic.execList_imm_apply_of_not_mem (setupWrites spec)
  simp only [setupWrites, List.map_map]
  intro hmem
  have hsetup : index ∈ setupIndices spec := by simpa using hmem
  rcases List.mem_append.mp hsetup with hfixed | htable
  · have hlt : index < inputBase spec := by
      simp [fixedSetupIndices, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg,
        acceptBaseReg] at hfixed
      simp [inputBase, transitionBase]
      omega
    omega
  · rcases List.mem_range'.mp htable with ⟨offset, hoffset, heq⟩
    have hlt : index < inputBase spec := by
      calc
        index = transitionBase + 1 * offset := heq
        _ < inputBase spec := by
          simp [inputBase, transitionBase]
          omega
    omega

private theorem setup_measured (spec : Spec) (bits : List Bool) :
    MeasuredRuns (setup spec) (inputStore spec bits) (setupStore spec bits)
        (setupOps spec).length
        (4 * (setupOps spec).length * width spec bits.length)
        (resourceSpace spec bits.length) ∧
      StoreBound spec bits.length (setupStore spec bits) := by
  have hinitial := inputStore_bound spec bits
  have hpreserve : ∀ op, op ∈ setupOps spec → ∀ current,
      StoreBound spec bits.length current →
      StoreBound spec bits.length (op.exec current) := by
    intro op hop current hcurrent
    rw [setupOps] at hop
    obtain ⟨write, hwrite, rfl⟩ := List.mem_map.mp hop
    rw [setupWrites] at hwrite
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hwrite
    apply hcurrent.execBasic (.imm index (setupValue spec index))
    · have hlt : index < inputBase spec := by
        rcases List.mem_append.mp hindex with hfixed | htable
        · simp [fixedSetupIndices, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg,
            acceptBaseReg] at hfixed
          simp [inputBase, transitionBase]
          omega
        · rcases List.mem_range'.mp htable with ⟨offset, hoffset, heq⟩
          calc
            index = transitionBase + 1 * offset := heq
            _ < inputBase spec := by
              simp [inputBase, transitionBase]
              omega
      exact hlt.trans_le (Nat.le_add_left _ bits.length)
    · exact (setupValue_le_inputBase spec index hindex).trans
        (Nat.le_add_left _ bits.length)
  simpa [setup, setupStore] using
    MeasuredRuns.basicsEnvelope (setupOps spec) (inputStore spec bits)
      hinitial hpreserve

private structure LoopInv (spec : Spec) (inputLength : ℕ)
    (remaining : List Bool) (state consumed : ℕ) (store : Store) : Prop where
  total_eq : consumed + remaining.length = inputLength
  state_lt : state < spec.stateCount
  store_bound : StoreBound spec inputLength store
  length_eq : store lengthReg = remaining.length
  state_eq : store stateReg = state
  pointer_eq : store pointerReg = inputBase spec + consumed
  one_eq : store oneReg = 1
  two_eq : store twoReg = 2
  transitionBase_eq : store transitionBaseReg = transitionBase
  acceptBase_eq : store acceptBaseReg = acceptBase spec
  transition_eq : ∀ automaton, automaton < spec.stateCount → ∀ bit,
    store (transitionAddress automaton bit) = spec.step automaton bit
  accept_eq : ∀ automaton, automaton < spec.stateCount →
    store (acceptAddress spec automaton) = Input.bitValue (spec.accept automaton)
  input_eq : ∀ offset,
    store (inputBase spec + consumed + offset) =
      match remaining[offset]? with
      | some bit => Input.bitValue bit
      | none => 0

private theorem setup_inv (spec : Spec) (bits : List Bool)
    (hbound : StoreBound spec bits.length (setupStore spec bits)) :
    LoopInv spec bits.length bits spec.initial 0 (setupStore spec bits) := by
  constructor
  · simp
  · exact spec.initial_lt
  · exact hbound
  · rw [setupStore_unwritten]
    · simp [inputStore, Input.bitStore, lengthReg]
    · simp [setupIndices, fixedSetupIndices, tableIndices, lengthReg, stateReg,
        pointerReg, oneReg, twoReg, transitionBaseReg, acceptBaseReg,
        transitionBase]
  · rw [setupStore_apply spec bits stateReg]
    · simp [setupValue, stateReg]
    · simp [setupIndices, fixedSetupIndices]
  · rw [setupStore_apply spec bits pointerReg]
    · simp [setupValue, stateReg, pointerReg]
    · simp [setupIndices, fixedSetupIndices]
  · rw [setupStore_apply spec bits oneReg]
    · simp [setupValue, stateReg, pointerReg, oneReg]
    · simp [setupIndices, fixedSetupIndices]
  · rw [setupStore_apply spec bits twoReg]
    · simp [setupValue, stateReg, pointerReg, oneReg, twoReg]
    · simp [setupIndices, fixedSetupIndices]
  · rw [setupStore_apply spec bits transitionBaseReg]
    · simp [setupValue, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg]
    · simp [setupIndices, fixedSetupIndices]
  · rw [setupStore_apply spec bits acceptBaseReg]
    · simp [setupValue, stateReg, pointerReg, oneReg, twoReg, transitionBaseReg,
        acceptBaseReg]
    · simp [setupIndices, fixedSetupIndices]
  · intro state hstate bit
    rw [setupStore_apply spec bits _ (transitionAddress_mem spec state hstate bit)]
    exact setupValue_transition spec state hstate bit
  · intro state hstate
    rw [setupStore_apply spec bits _ (acceptAddress_mem spec state hstate)]
    exact setupValue_accept spec state hstate
  · intro offset
    rw [setupStore_high spec bits _ (by omega)]
    simp [inputStore, Input.bitStore, Input.bitValue, lengthReg, inputBase]
    rfl

private def loaded (store : Store) : Store :=
  (Basic.load bitReg pointerReg).exec store

private def multiplied (store : Store) : Store :=
  (Basic.mul addressReg stateReg twoReg).exec (loaded store)

private def indexed (store : Store) : Store :=
  (Basic.add addressReg addressReg bitReg).exec (multiplied store)

private def addressed (store : Store) : Store :=
  (Basic.add addressReg addressReg transitionBaseReg).exec (indexed store)

private def transitioned (store : Store) : Store :=
  (Basic.load stateReg addressReg).exec (addressed store)

private def advanced (store : Store) : Store :=
  (Basic.add pointerReg pointerReg oneReg).exec (transitioned store)

private def iterated (store : Store) : Store :=
  (Basic.sub lengthReg lengthReg oneReg).exec (advanced store)

private theorem addressed_high (store : Store) (index : ℕ)
    (hindex : transitionBase ≤ index) :
    addressed store index = store index := by
  have hbit : index ≠ bitReg := by
    simp [transitionBase, bitReg] at hindex ⊢
    omega
  have haddress : index ≠ addressReg := by
    simp [transitionBase, addressReg] at hindex ⊢
    omega
  simp [addressed, indexed, multiplied, loaded, Basic.exec,
    Function.update_of_ne, hbit, haddress]

private theorem iterated_high (store : Store) (index : ℕ)
    (hindex : twoReg ≤ index) :
    iterated store index = store index := by
  have hlength : index ≠ lengthReg := by
    simp [twoReg, lengthReg] at hindex ⊢
    omega
  have hstate : index ≠ stateReg := by
    simp [twoReg, stateReg] at hindex ⊢
    omega
  have hpointer : index ≠ pointerReg := by
    simp [twoReg, pointerReg] at hindex ⊢
    omega
  have hbit : index ≠ bitReg := by
    simp [twoReg, bitReg] at hindex ⊢
    omega
  have haddress : index ≠ addressReg := by
    simp [twoReg, addressReg] at hindex ⊢
    omega
  simp [iterated, advanced, transitioned, addressed, indexed, multiplied,
    loaded, Basic.exec, Function.update_of_ne, hlength, hstate, hpointer,
    hbit, haddress]

private theorem body_measured {spec : Spec} {bit : Bool} {rest : List Bool}
    {inputLength consumed state : ℕ} {store : Store}
    (hinv : LoopInv spec inputLength (bit :: rest) state consumed store) :
    MeasuredRuns body store (iterated store) 7 (28 * width spec inputLength)
      (resourceSpace spec inputLength) ∧
    StoreBound spec inputLength (iterated store) := by
  have hstateLt := hinv.state_lt
  have hpositive := spec.initial_lt
  have htotal := hinv.total_eq
  have hloaded : StoreBound spec inputLength (loaded store) := by
    apply hinv.store_bound.execBasic (.load bitReg pointerReg)
    · simp [bitReg, inputBase, transitionBase]
      omega
    · simpa [Internal.Basic.writeValue] using
        hinv.store_bound.value_le (store pointerReg)
  have hloadedBit : loaded store bitReg = Input.bitValue bit := by
    simp only [loaded, Basic.exec, Function.update_self]
    rw [hinv.pointer_eq]
    simpa using hinv.input_eq 0
  have hloadedState : loaded store stateReg = state := by
    have hne : stateReg ≠ bitReg := by decide
    simpa [loaded, Basic.exec, stateReg, bitReg, Function.update_of_ne hne] using
      hinv.state_eq
  have hloadedTwo : loaded store twoReg = 2 := by
    have hne : twoReg ≠ bitReg := by decide
    simpa [loaded, Basic.exec, twoReg, bitReg, Function.update_of_ne hne] using
      hinv.two_eq
  have hmultiplied : StoreBound spec inputLength (multiplied store) := by
    apply hloaded.execBasic (.mul addressReg stateReg twoReg)
    · simp [addressReg, inputBase, transitionBase]
      omega
    · change loaded store stateReg * loaded store twoReg ≤
        inputLength + inputBase spec
      rw [hloadedState, hloadedTwo]
      simp [inputBase, transitionBase]
      omega
  have hmultipliedAddress : multiplied store addressReg = 2 * state := by
    simp [multiplied, Basic.exec, hloadedState, hloadedTwo]
    ring
  have hmultipliedBit : multiplied store bitReg = Input.bitValue bit := by
    have hne : bitReg ≠ addressReg := by decide
    simpa [multiplied, Basic.exec, Function.update_of_ne hne] using hloadedBit
  have hindexed : StoreBound spec inputLength (indexed store) := by
    apply hmultiplied.execBasic (.add addressReg addressReg bitReg)
    · simp [addressReg, inputBase, transitionBase]
      omega
    · change multiplied store addressReg + multiplied store bitReg ≤
        inputLength + inputBase spec
      rw [hmultipliedAddress, hmultipliedBit]
      cases bit <;> simp [Input.bitValue, inputBase, transitionBase] <;> omega
  have hindexedAddress : indexed store addressReg =
      2 * state + Input.bitValue bit := by
    simp [indexed, Basic.exec, hmultipliedAddress, hmultipliedBit]
  have hindexedBase : indexed store transitionBaseReg = transitionBase := by
    have hne : transitionBaseReg ≠ addressReg := by decide
    simpa [indexed, multiplied, loaded, Basic.exec, Function.update_of_ne hne,
      transitionBaseReg, addressReg, bitReg] using hinv.transitionBase_eq
  have haddressed : StoreBound spec inputLength (addressed store) := by
    apply hindexed.execBasic (.add addressReg addressReg transitionBaseReg)
    · simp [addressReg, inputBase, transitionBase]
      omega
    · change indexed store addressReg + indexed store transitionBaseReg ≤
        inputLength + inputBase spec
      rw [hindexedAddress, hindexedBase]
      cases bit <;> simp [Input.bitValue, inputBase, transitionBase] <;> omega
  have haddressedAddress : addressed store addressReg =
      transitionAddress state bit := by
    simp [addressed, Basic.exec, hindexedAddress, hindexedBase,
      transitionAddress]
    ring
  have htransitioned : StoreBound spec inputLength (transitioned store) := by
    apply haddressed.execBasic (.load stateReg addressReg)
    · simp [stateReg, inputBase, transitionBase]
      omega
    · change addressed store (addressed store addressReg) ≤
        inputLength + inputBase spec
      rw [haddressedAddress, addressed_high store _ (by
        simp [transitionAddress, transitionBase]
        omega)]
      rw [hinv.transition_eq state hinv.state_lt bit]
      have hstep := spec.step_lt state hinv.state_lt bit
      simp [inputBase, transitionBase]
      omega
  have htransitionedPointer : transitioned store pointerReg =
      inputBase spec + consumed := by
    have hne : pointerReg ≠ stateReg := by decide
    simpa [transitioned, addressed, indexed, multiplied, loaded, Basic.exec,
      pointerReg, stateReg, addressReg, bitReg, Function.update_of_ne hne] using
      hinv.pointer_eq
  have htransitionedOne : transitioned store oneReg = 1 := by
    have hne : oneReg ≠ stateReg := by decide
    simpa [transitioned, addressed, indexed, multiplied, loaded, Basic.exec,
      oneReg, stateReg, addressReg, bitReg, Function.update_of_ne hne] using
      hinv.one_eq
  have hadvanced : StoreBound spec inputLength (advanced store) := by
    apply htransitioned.execBasic (.add pointerReg pointerReg oneReg)
    · simp [pointerReg, inputBase, transitionBase]
      omega
    · change transitioned store pointerReg + transitioned store oneReg ≤
        inputLength + inputBase spec
      rw [htransitionedPointer, htransitionedOne]
      have htotal := hinv.total_eq
      simp only [List.length_cons] at htotal
      omega
  have hadvancedLength : advanced store lengthReg = (bit :: rest).length := by
    have hlength : store lengthReg = (bit :: rest).length := hinv.length_eq
    simpa [advanced, transitioned, addressed, indexed, multiplied, loaded,
      Basic.exec, lengthReg, pointerReg, stateReg, addressReg, bitReg] using hlength
  have hadvancedOne : advanced store oneReg = 1 := by
    simpa [advanced, transitioned, addressed, indexed, multiplied, loaded,
      Basic.exec, oneReg, pointerReg, stateReg, addressReg, bitReg] using hinv.one_eq
  have hiterated : StoreBound spec inputLength (iterated store) := by
    apply hadvanced.execBasic (.sub lengthReg lengthReg oneReg)
    · simp [lengthReg, inputBase, transitionBase]
    · change advanced store lengthReg - advanced store oneReg ≤
        inputLength + inputBase spec
      rw [hadvancedLength, hadvancedOne]
      have htotal := hinv.total_eq
      omega
  have hload := MeasuredRuns.basicEnvelope (.load bitReg pointerReg) store
    hinv.store_bound hloaded
  have hmul := MeasuredRuns.basicEnvelope (.mul addressReg stateReg twoReg)
    (loaded store) hloaded hmultiplied
  have hindex := MeasuredRuns.basicEnvelope (.add addressReg addressReg bitReg)
    (multiplied store) hmultiplied hindexed
  have haddress := MeasuredRuns.basicEnvelope
    (.add addressReg addressReg transitionBaseReg) (indexed store) hindexed haddressed
  have htransition := MeasuredRuns.basicEnvelope (.load stateReg addressReg)
    (addressed store) haddressed htransitioned
  have hadvance := MeasuredRuns.basicEnvelope (.add pointerReg pointerReg oneReg)
    (transitioned store) htransitioned hadvanced
  have hdecrement := MeasuredRuns.basicEnvelope (.sub lengthReg lengthReg oneReg)
    (advanced store) hadvanced hiterated
  have hrun := hload.seq (hmul.seq
    (hindex.seq (haddress.seq (htransition.seq (hadvance.seq hdecrement)))))
  constructor
  · simp only [body, Cmd.basics, bodyOps, List.map_cons, List.map_nil, Cmd.seqList]
    convert! hrun using 1
    ring
  · exact hiterated

private theorem addressed_address_of_inv {spec : Spec} {bit : Bool}
    {rest : List Bool} {inputLength consumed state : ℕ} {store : Store}
    (hinv : LoopInv spec inputLength (bit :: rest) state consumed store) :
    addressed store addressReg = transitionAddress state bit := by
  have hbit : loaded store bitReg = Input.bitValue bit := by
    simp only [loaded, Basic.exec, Function.update_self]
    rw [hinv.pointer_eq]
    simpa using hinv.input_eq 0
  have hstate : loaded store stateReg = state := by
    have hne : stateReg ≠ bitReg := by decide
    simpa [loaded, Basic.exec, stateReg, bitReg, Function.update_of_ne hne] using
      hinv.state_eq
  have htwo : loaded store twoReg = 2 := by
    have hne : twoReg ≠ bitReg := by decide
    simpa [loaded, Basic.exec, twoReg, bitReg, Function.update_of_ne hne] using
      hinv.two_eq
  have hbase : indexed store transitionBaseReg = transitionBase := by
    have hne : transitionBaseReg ≠ addressReg := by decide
    simpa [indexed, multiplied, loaded, Basic.exec, Function.update_of_ne hne,
      transitionBaseReg, addressReg, bitReg] using hinv.transitionBase_eq
  have hmultipliedAddress : multiplied store addressReg = 2 * state := by
    simp [multiplied, Basic.exec, hstate, htwo]
    ring
  have hmultipliedBit : multiplied store bitReg = Input.bitValue bit := by
    have hne : bitReg ≠ addressReg := by decide
    simpa [multiplied, Basic.exec, Function.update_of_ne hne] using hbit
  have hindexedAddress : indexed store addressReg =
      2 * state + Input.bitValue bit := by
    simp [indexed, Basic.exec, hmultipliedAddress, hmultipliedBit]
  simp [addressed, Basic.exec, hindexedAddress, hbase, transitionAddress]
  ring

private theorem iterated_state {spec : Spec} {bit : Bool} {rest : List Bool}
    {inputLength consumed state : ℕ} {store : Store}
    (hinv : LoopInv spec inputLength (bit :: rest) state consumed store) :
    iterated store stateReg = spec.step state bit := by
  have haddress := addressed_address_of_inv hinv
  have htable : addressed store (transitionAddress state bit) =
      spec.step state bit := by
    rw [addressed_high store _ (by
      cases bit <;> simp [transitionAddress, transitionBase, Input.bitValue]
      all_goals omega)]
    exact hinv.transition_eq state hinv.state_lt bit
  simp [iterated, advanced, transitioned, Basic.exec, lengthReg, pointerReg,
    stateReg, haddress, htable]

private theorem iterated_inv {spec : Spec} {bit : Bool} {rest : List Bool}
    {inputLength consumed state : ℕ} {store : Store}
    (hinv : LoopInv spec inputLength (bit :: rest) state consumed store) :
    LoopInv spec inputLength rest (spec.step state bit) (consumed + 1)
      (iterated store) := by
  constructor
  · have htotal := hinv.total_eq
    simp only [List.length_cons] at htotal
    omega
  · exact spec.step_lt state hinv.state_lt bit
  · exact (body_measured hinv).2
  · have hlength : store 0 = (bit :: rest).length := by
      simpa [lengthReg] using hinv.length_eq
    have hone : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
    simp [iterated, advanced, transitioned, addressed, indexed, multiplied,
      loaded, Basic.exec, lengthReg, pointerReg, stateReg, addressReg, bitReg,
      oneReg]
    rw [hlength, hone]
    simp
  · exact iterated_state hinv
  · have hpointer : store 2 = inputBase spec + consumed := by
      simpa [pointerReg] using hinv.pointer_eq
    have hone : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
    simp [iterated, advanced, transitioned, addressed, indexed, multiplied,
      loaded, Basic.exec, lengthReg, pointerReg, stateReg, addressReg, bitReg,
      oneReg]
    rw [hpointer, hone]
    omega
  · simpa [iterated, advanced, transitioned, addressed, indexed, multiplied,
      loaded, Basic.exec, lengthReg, pointerReg, stateReg, addressReg, bitReg,
      oneReg] using hinv.one_eq
  · rw [iterated_high store twoReg (by simp)]
    exact hinv.two_eq
  · rw [iterated_high store transitionBaseReg (by
      simp [twoReg, transitionBaseReg])]
    exact hinv.transitionBase_eq
  · rw [iterated_high store acceptBaseReg (by simp [twoReg, acceptBaseReg])]
    exact hinv.acceptBase_eq
  · intro automaton hautomaton value
    rw [iterated_high store _ (by
      simp [transitionAddress, transitionBase, twoReg]
      omega)]
    exact hinv.transition_eq automaton hautomaton value
  · intro automaton hautomaton
    rw [iterated_high store _ (by
      simp [acceptAddress, acceptBase, transitionBase, twoReg]
      omega)]
    exact hinv.accept_eq automaton hautomaton
  · intro offset
    rw [iterated_high store _ (by
      simp [inputBase, transitionBase, twoReg]
      omega)]
    have hinput := hinv.input_eq (offset + 1)
    convert! hinput using 1
    all_goals simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private def loopAdvance (spec : Spec) (state : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  (spec.step state.1 bit, state.2 + 1)

private theorem foldl_loopAdvance (spec : Spec) (bits : List Bool)
    (state consumed : ℕ) :
    bits.foldl (loopAdvance spec) (state, consumed) =
      (bits.foldl spec.step state, consumed + bits.length) := by
  induction bits generalizing state consumed with
  | nil => simp
  | cons bit rest ih =>
      simp only [List.foldl_cons, loopAdvance]
      rw [ih]
      simp
      omega

private theorem whileFoldSteps_eq (bits : List Bool) :
    MeasuredRuns.whileFoldSteps (fun _ : Bool => 7) bits =
      1 + 9 * bits.length := by
  induction bits with
  | nil => simp [MeasuredRuns.whileFoldSteps]
  | cons bit rest ih =>
      rw [MeasuredRuns.whileFoldSteps, ih]
      simp
      omega

private theorem whileFoldCost_eq (bits : List Bool) (w : ℕ) :
    MeasuredRuns.whileFoldCost w (fun _ : Bool => 28 * w) bits =
      (31 * bits.length + 1) * w := by
  induction bits with
  | nil => simp [MeasuredRuns.whileFoldCost]
  | cons bit rest ih =>
      rw [MeasuredRuns.whileFoldCost, ih]
      simp only [List.length_cons]
      ring

private theorem loop_measured {spec : Spec} {remaining : List Bool}
    {inputLength consumed state : ℕ} {store : Store}
    (hinv : LoopInv spec inputLength remaining state consumed store) :
    ∃ final,
      MeasuredRuns mainLoop store final (1 + 9 * remaining.length)
        ((31 * remaining.length + 1) * width spec inputLength)
        (resourceSpace spec inputLength) ∧
      LoopInv spec inputLength [] (remaining.foldl spec.step state)
        (consumed + remaining.length) final := by
  let bodySteps : Bool → ℕ := fun _ => 7
  let bodyCost : Bool → ℕ := fun _ => 28 * width spec inputLength
  have hrun := MeasuredRuns.whileFoldEnvelope
    (Inv := fun items foldState current =>
      LoopInv spec inputLength items foldState.1 foldState.2 current)
    (advance := loopAdvance spec) (bodySteps := bodySteps) (bodyCost := bodyCost)
    (test := lengthReg) (body := body)
    (hstore := by intro _ _ _ h; exact h.store_bound)
    (hnil := by intro _ _ h; simpa using h.length_eq)
    (hcons := by intro _ _ _ _ h; rw [h.length_eq]; simp)
    (hbody := by
      intro bit rest foldState current h
      exact ⟨iterated current, (body_measured h).1, by
        simpa [loopAdvance] using iterated_inv h⟩)
    (items := remaining) (state := (state, consumed)) (initial := store) hinv
  obtain ⟨final, hloop, hfinal⟩ := hrun
  have hsteps : MeasuredRuns.whileFoldSteps bodySteps remaining =
      1 + 9 * remaining.length := by
    simpa [bodySteps] using whileFoldSteps_eq remaining
  have hcost : MeasuredRuns.whileFoldCost (width spec inputLength)
      bodyCost remaining =
      (31 * remaining.length + 1) * width spec inputLength := by
    simpa [bodyCost] using whileFoldCost_eq remaining (width spec inputLength)
  have hstate := foldl_loopAdvance spec remaining state consumed
  rw [hstate] at hfinal
  refine ⟨final, ?_, hfinal⟩
  simpa [mainLoop, hsteps, hcost] using hloop

private def finalStore (store : Store) : Store :=
  Basic.execList finalizeOps store

private theorem finalize_measured {spec : Spec} {inputLength state : ℕ}
    {store : Store} (hinv : LoopInv spec inputLength [] state inputLength store) :
    MeasuredRuns finalize store (finalStore store) 2
        (8 * width spec inputLength) (resourceSpace spec inputLength) ∧
      finalStore store lengthReg = Input.bitValue (spec.accept state) := by
  let indexed := (Basic.add addressReg stateReg acceptBaseReg).exec store
  have hstate : store stateReg = state := hinv.state_eq
  have hbase : store acceptBaseReg = acceptBase spec := hinv.acceptBase_eq
  have hpositive := spec.initial_lt
  have hstateLt := hinv.state_lt
  have hindexed : StoreBound spec inputLength indexed := by
    apply hinv.store_bound.execBasic (.add addressReg stateReg acceptBaseReg)
    · simp [addressReg, inputBase, transitionBase]
      omega
    · change store stateReg + store acceptBaseReg ≤
        inputLength + inputBase spec
      rw [hstate, hbase]
      simp [acceptBase, inputBase, transitionBase]
      omega
  have haddress : indexed addressReg = acceptAddress spec state := by
    simp [indexed, Basic.exec, hstate, hbase, acceptAddress]
    ring
  have htable : indexed (acceptAddress spec state) =
      Input.bitValue (spec.accept state) := by
    have hne : acceptAddress spec state ≠ addressReg := by
      simp [acceptAddress, acceptBase, transitionBase, addressReg]
      omega
    rw [show indexed (acceptAddress spec state) =
        store (acceptAddress spec state) by
      simp [indexed, Basic.exec, Function.update_of_ne hne]]
    exact hinv.accept_eq state hinv.state_lt
  have hfinal : StoreBound spec inputLength (finalStore store) := by
    change StoreBound spec inputLength
      ((Basic.load lengthReg addressReg).exec indexed)
    apply hindexed.execBasic (.load lengthReg addressReg)
    · simp [lengthReg, inputBase, transitionBase]
    · change indexed (indexed addressReg) ≤ inputLength + inputBase spec
      rw [haddress, htable]
      cases spec.accept state <;> simp [Input.bitValue, inputBase, transitionBase]
      all_goals omega
  have hfirst := MeasuredRuns.basicEnvelope
    (.add addressReg stateReg acceptBaseReg) store hinv.store_bound hindexed
  have hsecond := MeasuredRuns.basicEnvelope (.load lengthReg addressReg)
    indexed hindexed hfinal
  have hrun := hfirst.seq hsecond
  constructor
  · simp only [finalize, Cmd.basics, finalizeOps, List.map_cons, List.map_nil,
      Cmd.seqList]
    convert! hrun using 1
    ring
  · change ((Basic.load lengthReg addressReg).exec indexed) lengthReg = _
    simp [Basic.exec, haddress, htable]

theorem program_measured_internal (spec : Spec) (bits : List Bool) :
    ∃ final cost space,
      Exec (program spec) (inputStore spec bits) final
          (stepCount spec bits.length) cost space ∧
      cost ≤ timeBound spec bits.length ∧
      space ≤ spaceBound spec bits.length ∧
      final lengthReg = Input.bitValue
        (spec.accept (bits.foldl spec.step spec.initial)) := by
  obtain ⟨hsetup, hsetupBound⟩ := setup_measured spec bits
  have hsetupInv := setup_inv spec bits hsetupBound
  obtain ⟨loopFinal, hloop, hloopInv⟩ := loop_measured hsetupInv
  have hloopInv' : LoopInv spec bits.length []
      (bits.foldl spec.step spec.initial) bits.length loopFinal := by
    simpa using hloopInv
  obtain ⟨hfinalize, hresult⟩ := finalize_measured hloopInv'
  have hseq := hsetup.seq (hloop.seq hfinalize)
  have hcostLe :
      4 * (setupOps spec).length * width spec bits.length +
          ((31 * bits.length + 1) * width spec bits.length +
            8 * width spec bits.length) ≤ timeBound spec bits.length := by
    rw [timeBound]
    change _ ≤ 64 * (bits.length + spec.stateCount + 1) * width spec bits.length
    calc
      4 * (setupOps spec).length * width spec bits.length +
            ((31 * bits.length + 1) * width spec bits.length +
              8 * width spec bits.length)
          = (31 * bits.length + 12 * spec.stateCount + 33) *
              width spec bits.length := by
              rw [setupOps_length]
              ring
      _ ≤ (64 * (bits.length + spec.stateCount + 1)) *
          width spec bits.length :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 64 * (bits.length + spec.stateCount + 1) *
          width spec bits.length := by ring
  have hwide := hseq.weakenCost hcostLe
  have hprogram : MeasuredRuns (program spec) (inputStore spec bits)
      (finalStore loopFinal) (stepCount spec bits.length)
      (timeBound spec bits.length) (resourceSpace spec bits.length) := by
    rw [program]
    convert! hwide using 1
    rw [setupOps_length]
    simp [stepCount]
    ring
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hprogram
  have hspace' : space ≤ spaceBound spec bits.length := by
    rw [← envelopeSpace_eq_spaceBound]
    exact hspace
  exact ⟨finalStore loopFinal, cost, space, hexec, hcost, hspace', hresult⟩

private theorem TypedSpec.numeric_step_code {State : Type} [FinEnum State]
    (typed : TypedSpec State) (state : State) (bit : Bool) :
    typed.numeric.step (TypedSpec.code state) bit =
      TypedSpec.code (typed.step state bit) := by
  simp [TypedSpec.numeric, TypedSpec.code]

private theorem TypedSpec.numeric_accept_code {State : Type} [FinEnum State]
    (typed : TypedSpec State) (state : State) :
    typed.numeric.accept (TypedSpec.code state) = typed.accept state := by
  simp [TypedSpec.numeric, TypedSpec.code]

private theorem TypedSpec.foldl_numeric_step {State : Type} [FinEnum State]
    (typed : TypedSpec State) (bits : List Bool) (state : State) :
    bits.foldl typed.numeric.step (TypedSpec.code state) =
      TypedSpec.code (bits.foldl typed.step state) := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.foldl_cons]
      rw [typed.numeric_step_code, ih]

theorem typed_program_measured_internal {State : Type} [FinEnum State]
    (typed : TypedSpec State) (bits : List Bool) :
    ∃ final cost space,
      Exec (program typed.numeric) (inputStore typed.numeric bits) final
          (stepCount typed.numeric bits.length) cost space ∧
      cost ≤ timeBound typed.numeric bits.length ∧
      space ≤ spaceBound typed.numeric bits.length ∧
      final lengthReg = Input.bitValue
        (typed.accept (bits.foldl typed.step typed.initial)) := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hresult⟩ :=
    program_measured_internal typed.numeric bits
  refine ⟨final, cost, space, hexec, hcost, hspace, ?_⟩
  change final lengthReg = Input.bitValue
    (typed.numeric.accept
      (bits.foldl typed.numeric.step (TypedSpec.code typed.initial))) at hresult
  rw [typed.foldl_numeric_step, typed.numeric_accept_code] at hresult
  exact hresult

end Scanner

end Structured

end RAM

end Complexity
