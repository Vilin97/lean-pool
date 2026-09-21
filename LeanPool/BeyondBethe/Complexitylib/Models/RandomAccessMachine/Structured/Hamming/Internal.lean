/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Hamming.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources

/-!
# Structured RAM Hamming-weight program — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace Hamming

open Internal

private abbrev StoreBound (inputLength : ℕ) (store : Store) : Prop :=
  StoreEnvelope (inputLength + 5) (inputLength + 5) store

private abbrev width (inputLength : ℕ) : ℕ :=
  valueWidth (inputLength + 5)

private abbrev resourceSpace (inputLength : ℕ) : ℕ :=
  envelopeSpace (inputLength + 5) (inputLength + 5)

private theorem envelopeSpace_eq_spaceBound (inputLength : ℕ) :
    envelopeSpace (inputLength + 5) (inputLength + 5) = spaceBound inputLength := by
  simp [envelopeSpace, spaceBound, two_mul]

private theorem inputStore_bound (bits : List Bool) :
    StoreBound bits.length (inputStore bits) := by
  apply Internal.Input.bitStoreEnvelope
  · simp [lengthReg]
  · simp [inputBase]
    omega
  · omega
  · omega

private structure LoopInv (inputLength : ℕ) (remaining : List Bool)
    (consumed acc : ℕ) (store : Store) : Prop where
  total_eq : consumed + remaining.length = inputLength
  acc_le : acc ≤ consumed
  store_bound : StoreBound inputLength store
  length_eq : store lengthReg = remaining.length
  count_eq : store countReg = acc
  pointer_eq : store pointerReg = inputBase + consumed
  one_eq : store oneReg = 1
  input_eq : ∀ offset,
    store (inputBase + consumed + offset) =
      match remaining[offset]? with
      | some bit => bitValue bit
      | none => 0

private def loaded (store : Store) : Store :=
  (Basic.load scratchReg pointerReg).exec store

private def branched (bit : Bool) (store : Store) : Store :=
  if bit then (Basic.add countReg countReg oneReg).exec (loaded store)
  else loaded store

private def advanced (bit : Bool) (store : Store) : Store :=
  (Basic.add pointerReg pointerReg oneReg).exec (branched bit store)

private def iterated (bit : Bool) (store : Store) : Store :=
  (Basic.sub lengthReg lengthReg oneReg).exec (advanced bit store)

private theorem bitValue_le_one (bit : Bool) : bitValue bit ≤ 1 := by
  cases bit <;> simp [bitValue]

private theorem loaded_bound {inputLength : ℕ} {store : Store}
    (hstore : StoreBound inputLength store) :
    StoreBound inputLength (loaded store) := by
  apply hstore.execBasic (.load scratchReg pointerReg)
  · simp [scratchReg]
  · simpa [Internal.Basic.writeValue] using hstore.value_le (store pointerReg)

private theorem branched_bound {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    StoreBound inputLength (branched bit store) := by
  cases bit with
  | false => simpa [branched] using loaded_bound hinv.store_bound
  | true =>
      rw [branched, ite_eq_left rfl]
      apply (loaded_bound hinv.store_bound).execBasic
        (.add countReg countReg oneReg)
      · simp [countReg]
      · have hcount : loaded store countReg = acc := by
          have hcount₀ : store 1 = acc := by
            simpa [countReg] using hinv.count_eq
          simp [loaded, Basic.exec, countReg, scratchReg, hcount₀]
        have hone : loaded store oneReg = 1 := by
          have hone₀ : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
          simp [loaded, Basic.exec, oneReg, scratchReg, hone₀]
        change loaded store countReg + loaded store oneReg ≤ inputLength + 5
        rw [hcount, hone]
        have htotal := hinv.total_eq
        have hacc := hinv.acc_le
        omega

private theorem advanced_bound {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    StoreBound inputLength (advanced bit store) := by
  apply (branched_bound hinv).execBasic (.add pointerReg pointerReg oneReg)
  · simp [pointerReg]
  · have hpointer : branched bit store pointerReg = inputBase + consumed := by
      have hpointer₀ : store 2 = inputBase + consumed := by
        simpa [pointerReg] using hinv.pointer_eq
      cases bit <;>
        simp [branched, loaded, Basic.exec, pointerReg, oneReg, scratchReg,
          countReg, hpointer₀]
    have hone : branched bit store oneReg = 1 := by
      have hone₀ : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
      cases bit <;>
        simp [branched, loaded, Basic.exec, pointerReg, oneReg, scratchReg,
          countReg, hone₀]
    change branched bit store pointerReg + branched bit store oneReg ≤ inputLength + 5
    rw [hpointer, hone]
    have htotal := hinv.total_eq
    simp [inputBase] at htotal ⊢
    omega

private theorem iterated_bound {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    StoreBound inputLength (iterated bit store) := by
  apply (advanced_bound hinv).execBasic (.sub lengthReg lengthReg oneReg)
  · simp [lengthReg]
  · have hlength : advanced bit store lengthReg = (bit :: rest).length := by
      have hlength₀ : store 0 = rest.length + 1 := by
        simpa [lengthReg] using hinv.length_eq
      cases bit <;>
        simp [advanced, branched, loaded, Basic.exec, lengthReg, pointerReg,
          oneReg, scratchReg, countReg, hlength₀]
    have hone : advanced bit store oneReg = 1 := by
      have hone₀ : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
      cases bit <;>
        simp [advanced, branched, loaded, Basic.exec, pointerReg,
          oneReg, scratchReg, countReg, hone₀]
    change advanced bit store lengthReg - advanced bit store oneReg ≤ inputLength + 5
    rw [hlength, hone]
    have htotal := hinv.total_eq
    omega

private theorem loaded_scratch {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    loaded store scratchReg = bitValue bit := by
  simp only [loaded, Basic.exec, Function.update_self]
  rw [hinv.pointer_eq]
  simpa using hinv.input_eq 0

private theorem body_measured {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    MeasuredRuns body store (iterated bit store) (4 + 2 * bitValue bit)
      (20 * width inputLength) (resourceSpace inputLength) := by
  have hloadedBound := loaded_bound hinv.store_bound
  have hbranchedBound := branched_bound hinv
  have hadvancedBound := advanced_bound hinv
  have hiteratedBound := iterated_bound hinv
  have hload : MeasuredRuns (.basic (.load scratchReg pointerReg))
      store (loaded store) 1 (4 * width inputLength) (resourceSpace inputLength) :=
    MeasuredRuns.basicEnvelope _ _ hinv.store_bound hloadedBound
  have hbranch : MeasuredRuns
      (.ifZero scratchReg Cmd.skip (.basic (.add countReg countReg oneReg)))
      (loaded store) (branched bit store) (1 + 2 * bitValue bit)
      (8 * width inputLength) (resourceSpace inputLength) := by
    cases bit with
    | false =>
        have hzero : loaded store scratchReg = 0 := by
          simpa [bitValue] using loaded_scratch hinv
        have hrun := MeasuredRuns.ifZeroEnvelope
          (onNonzero := .basic (.add countReg countReg oneReg)) hzero hloadedBound
          (MeasuredRuns.skipEnvelope hloadedBound)
        apply MeasuredRuns.weakenCost (by simpa [branched, bitValue] using hrun)
        change width inputLength ≤ 8 * width inputLength
        omega
    | true =>
        have hnonzero : loaded store scratchReg ≠ 0 := by
          have hscratch := loaded_scratch hinv
          simp [bitValue, hscratch]
        let op := Basic.add countReg countReg oneReg
        have hop : op.exec (loaded store) = branched true store := by
          simp [op, branched]
        have hadd := MeasuredRuns.basicEnvelope op (loaded store) hloadedBound
          (by simpa [hop] using hbranchedBound)
        have hrun := MeasuredRuns.ifNonzeroEnvelope (onZero := Cmd.skip)
          hnonzero hloadedBound hadd
        apply MeasuredRuns.weakenCost (by simpa [branched, bitValue, op] using hrun)
        change 3 * width inputLength + 4 * width inputLength ≤
          8 * width inputLength
        omega
  have hadvance : MeasuredRuns (.basic (.add pointerReg pointerReg oneReg))
      (branched bit store) (advanced bit store) 1 (4 * width inputLength)
      (resourceSpace inputLength) :=
    MeasuredRuns.basicEnvelope _ _ hbranchedBound hadvancedBound
  have hdecrement : MeasuredRuns (.basic (.sub lengthReg lengthReg oneReg))
      (advanced bit store) (iterated bit store) 1 (4 * width inputLength)
      (resourceSpace inputLength) :=
    MeasuredRuns.basicEnvelope _ _ hadvancedBound hiteratedBound
  have hrun := hload.seq (hbranch.seq (hadvance.seq hdecrement))
  rw [body, Cmd.seqList]
  convert hrun using 1
  · cases bit <;> simp [bitValue]
  · ring

private theorem iterated_high (bit : Bool) (store : Store) (index : ℕ)
    (hindex : inputBase ≤ index) : iterated bit store index = store index := by
  have hlength : index ≠ lengthReg := by
    simp [inputBase, lengthReg] at hindex ⊢
    omega
  have hcount : index ≠ countReg := by
    simp [inputBase, countReg] at hindex ⊢
    omega
  have hpointer : index ≠ pointerReg := by
    simp [inputBase, pointerReg] at hindex ⊢
    omega
  have hscratch : index ≠ scratchReg := by
    simp [inputBase, scratchReg] at hindex ⊢
    omega
  cases bit <;> simp [iterated, advanced, branched, loaded, Basic.exec,
    Function.update_of_ne, hlength, hcount, hpointer, hscratch]

private theorem iterated_inv {bit : Bool} {rest : List Bool}
    {inputLength consumed acc : ℕ} {store : Store}
    (hinv : LoopInv inputLength (bit :: rest) consumed acc store) :
    LoopInv inputLength rest (consumed + 1) (acc + bitValue bit)
      (iterated bit store) := by
  constructor
  · have htotal := hinv.total_eq
    simp only [List.length_cons] at htotal
    omega
  · have hbit := bitValue_le_one bit
    have hacc := hinv.acc_le
    omega
  · exact iterated_bound hinv
  · cases bit <;>
      simp [iterated, advanced, branched, loaded, Basic.exec, lengthReg,
        countReg, pointerReg, oneReg, scratchReg]
    all_goals
      have hlength : store 0 = (Bool.false :: rest).length := by
        simpa [lengthReg] using hinv.length_eq
      have hone : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
      rw [hlength, hone]
      simp
  · cases bit <;>
      simp [iterated, advanced, branched, loaded, Basic.exec, lengthReg,
        countReg, pointerReg, oneReg, scratchReg, bitValue]
    all_goals
      have hcount : store 1 = acc := by simpa [countReg] using hinv.count_eq
      have hone : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
      simp [hcount, hone]
  · cases bit <;>
      simp [iterated, advanced, branched, loaded, Basic.exec, lengthReg,
        countReg, pointerReg, oneReg, scratchReg, inputBase]
    all_goals
      have hpointer : store 2 = 5 + consumed := by
        simpa [pointerReg, inputBase] using hinv.pointer_eq
      have hone : store 3 = 1 := by simpa [oneReg] using hinv.one_eq
      rw [hpointer, hone]
      omega
  · cases bit <;>
      simp [iterated, advanced, branched, loaded, Basic.exec, lengthReg,
        countReg, pointerReg, oneReg, scratchReg] <;> exact hinv.one_eq
  · intro offset
    rw [iterated_high bit store _ (by simp [inputBase]; omega)]
    have hinput := hinv.input_eq (offset + 1)
    convert hinput using 1
    all_goals simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private def loopAdvance (state : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  (state.1 + 1, state.2 + bitValue bit)

private theorem foldl_loopAdvance (bits : List Bool) (consumed acc : ℕ) :
    bits.foldl loopAdvance (consumed, acc) =
      (consumed + bits.length, acc + weight bits) := by
  induction bits generalizing consumed acc with
  | nil => simp [weight]
  | cons bit rest ih =>
      simp only [List.foldl_cons, loopAdvance]
      rw [ih]
      simp only [List.length_cons, weight]
      cases bit <;> simp [bitValue] <;> omega

private theorem whileFoldSteps_eq (bits : List Bool) :
    MeasuredRuns.whileFoldSteps (fun bit => 4 + 2 * bitValue bit) bits =
      1 + 6 * bits.length + 2 * weight bits := by
  induction bits with
  | nil => simp [MeasuredRuns.whileFoldSteps, weight]
  | cons bit rest ih =>
      rw [MeasuredRuns.whileFoldSteps, ih]
      cases bit <;> simp [weight, bitValue] <;> omega

private theorem whileFoldCost_eq (bits : List Bool) (w : ℕ) :
    MeasuredRuns.whileFoldCost w (fun _ : Bool => 20 * w) bits =
      (23 * bits.length + 1) * w := by
  induction bits with
  | nil => simp [MeasuredRuns.whileFoldCost]
  | cons bit rest ih =>
      rw [MeasuredRuns.whileFoldCost, ih]
      simp only [List.length_cons]
      ring

private theorem loop_measured {remaining : List Bool} {inputLength consumed acc : ℕ}
    {store : Store} (hinv : LoopInv inputLength remaining consumed acc store) :
    ∃ final,
      MeasuredRuns mainLoop store final
        (1 + 6 * remaining.length + 2 * weight remaining)
        ((23 * remaining.length + 1) * width inputLength)
        (resourceSpace inputLength) ∧
      final countReg = acc + weight remaining ∧ final lengthReg = 0 ∧
      StoreBound inputLength final := by
  let bodySteps : Bool → ℕ := fun bit => 4 + 2 * bitValue bit
  let bodyCost : Bool → ℕ := fun _ => 20 * width inputLength
  have hrun := MeasuredRuns.whileFoldEnvelope
    (Inv := fun items state store =>
      LoopInv inputLength items state.1 state.2 store)
    (advance := loopAdvance) (bodySteps := bodySteps) (bodyCost := bodyCost)
    (test := lengthReg) (body := body)
    (hstore := by intro _ _ _ h; exact h.store_bound)
    (hnil := by intro _ _ h; simpa using h.length_eq)
    (hcons := by intro _ _ _ _ h; rw [h.length_eq]; simp)
    (hbody := by
      intro bit rest state current h
      exact ⟨iterated bit current, body_measured h, by
        simpa [loopAdvance] using iterated_inv h⟩)
    (items := remaining) (state := (consumed, acc)) (initial := store) hinv
  obtain ⟨final, hloop, hfinal⟩ := hrun
  have hsteps : MeasuredRuns.whileFoldSteps bodySteps remaining =
      1 + 6 * remaining.length + 2 * weight remaining := by
    simpa [bodySteps] using whileFoldSteps_eq remaining
  have hcost : MeasuredRuns.whileFoldCost (width inputLength) bodyCost remaining =
      (23 * remaining.length + 1) * width inputLength := by
    simpa [bodyCost] using whileFoldCost_eq remaining (width inputLength)
  have hstate := foldl_loopAdvance remaining consumed acc
  rw [hstate] at hfinal
  refine ⟨final, ?_, hfinal.count_eq, hfinal.length_eq, hfinal.store_bound⟩
  simpa [mainLoop, hsteps, hcost] using hloop

private def setupStore (bits : List Bool) : Store :=
  Basic.execList setupOps (inputStore bits)

private theorem setup_measured (bits : List Bool) :
    MeasuredRuns setup (inputStore bits) (setupStore bits) 3
        (12 * width bits.length) (resourceSpace bits.length) ∧
      StoreBound bits.length (setupStore bits) := by
  have hinitial := inputStore_bound bits
  have hpreserve : ∀ op, op ∈ setupOps → ∀ current,
      StoreBound bits.length current →
      StoreBound bits.length (op.exec current) := by
    intro op hop current hcurrent
    simp [setupOps] at hop
    rcases hop with rfl | rfl | rfl
    · apply hcurrent.execBasic (.imm countReg 0) <;> simp [countReg]
    · apply hcurrent.execBasic (.imm pointerReg inputBase)
      · simp [pointerReg]
      · simp [inputBase]
    · apply hcurrent.execBasic (.imm oneReg 1) <;> simp [oneReg]
  obtain ⟨hrun, hfinal⟩ :=
    MeasuredRuns.basicsEnvelope setupOps (inputStore bits) hinitial hpreserve
  constructor
  · simpa [setup, setupStore, setupOps] using hrun
  · simpa [setupStore] using hfinal

private theorem setup_inv (bits : List Bool)
    (hbound : StoreBound bits.length (setupStore bits)) :
    LoopInv bits.length bits 0 0 (setupStore bits) := by
  constructor
  · simp
  · simp
  · exact hbound
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, inputStore,
      Input.bitStore, lengthReg, countReg, pointerReg, oneReg, inputBase]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, countReg, pointerReg, oneReg]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, pointerReg, oneReg, inputBase]
  · simp [setupStore, setupOps, Basic.execList, Basic.exec, oneReg]
  · intro offset
    have hcount : 5 + offset ≠ 1 := by omega
    have hpointer : 5 + offset ≠ 2 := by omega
    have hone : 5 + offset ≠ 3 := by omega
    simp [setupStore, setupOps, Basic.execList, Basic.exec, Function.update_of_ne,
      hcount, hpointer, hone, inputStore, Input.bitStore, bitValue, lengthReg,
      countReg, pointerReg, oneReg, inputBase]
    rfl

private def finalStore (store : Store) : Store :=
  (Basic.add lengthReg countReg oneReg).exec
    ((Basic.imm oneReg 0).exec store)

private theorem finalize_measured {inputLength : ℕ} {store : Store}
    (hstore : StoreBound inputLength store) :
    MeasuredRuns finalize store (finalStore store) 2
      (8 * width inputLength) (resourceSpace inputLength) := by
  let zeroed := (Basic.imm oneReg 0).exec store
  have hzeroed : StoreBound inputLength zeroed := by
    apply hstore.execBasic (.imm oneReg 0)
    · simp [oneReg]
    · simp [Internal.Basic.writeValue]
  have hfinal : StoreBound inputLength (finalStore store) := by
    apply hzeroed.execBasic (.add lengthReg countReg oneReg)
    · simp [lengthReg]
    · have hcount := hstore.value_le countReg
      simpa [zeroed, Basic.exec, countReg, oneReg] using hcount
  have hzero : MeasuredRuns (.basic (.imm oneReg 0)) store zeroed 1
      (4 * width inputLength) (resourceSpace inputLength) :=
    MeasuredRuns.basicEnvelope _ _ hstore hzeroed
  have hadd : MeasuredRuns (.basic (.add lengthReg countReg oneReg)) zeroed
      (finalStore store) 1 (4 * width inputLength) (resourceSpace inputLength) :=
    MeasuredRuns.basicEnvelope _ _ hzeroed hfinal
  have hrun := hzero.seq hadd
  rw [finalize, Cmd.seqList]
  convert hrun using 1
  all_goals ring

theorem program_measured_internal (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      final lengthReg = weight bits := by
  obtain ⟨hsetup, hsetupStore⟩ := setup_measured bits
  have hsetupInv := setup_inv bits hsetupStore
  obtain ⟨loopFinal, hloop, hcount, hlength, hloopStore⟩ :=
    loop_measured hsetupInv
  have hfinalize := finalize_measured hloopStore
  have hseq := hsetup.seq (hloop.seq hfinalize)
  have hcostLe :
      12 * width bits.length +
          ((23 * bits.length + 1) * width bits.length + 8 * width bits.length)
        ≤ timeBound bits.length := by
    rw [timeBound]
    change _ ≤ 64 * (bits.length + 1) * width bits.length
    calc
      12 * width bits.length +
            ((23 * bits.length + 1) * width bits.length + 8 * width bits.length)
          = (23 * bits.length + 21) * width bits.length := by ring
      _ ≤ (64 * (bits.length + 1)) * width bits.length :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 64 * (bits.length + 1) * width bits.length := by ring
  have hprogram := hseq.weakenCost hcostLe
  rw [program]
  have hprogram' : MeasuredRuns (setup.seq (mainLoop.seq finalize))
      (inputStore bits) (finalStore loopFinal) (stepCount bits)
      (timeBound bits.length) (resourceSpace bits.length) := by
    convert hprogram using 1
    unfold stepCount
    ring
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hprogram'
  have hspace' : space ≤ spaceBound bits.length := by
    rw [← envelopeSpace_eq_spaceBound]
    exact hspace
  refine ⟨finalStore loopFinal, cost, space, hexec, hcost, hspace', ?_⟩
  have hcount' : loopFinal 1 = weight bits := by
    simpa [countReg] using hcount
  simp [finalStore, Basic.exec, hcount', lengthReg, countReg, oneReg]

end Hamming

end Structured

end RAM

end Complexity
