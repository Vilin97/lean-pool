/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Direct
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Load
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Immediate
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Store
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Control

/-!
# Concrete sparse-store arithmetic instruction kernel

This surface exposes the first complete instruction-level composition in the
RAM-to-TM direction: two canonical operands are combined by a width-efficient
binary machine and the result is committed by the fixed encoded-store update
controller. A redirected form writes the new store to a fresh work buffer.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Uniform framed contract for the selected arithmetic operation. -/
theorem binaryInstructionArithmeticTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ tapes.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ tapes.rhs).HasBinaryNat rhs)
    (hresult : (work₀ tapes.update.replacement).HasBinaryNat 0)
    (hshift : (work₀ tapes.shift).HasBinaryNat 0)
    (htmp : (work₀ tapes.tmp).HasBinaryNat 0)
    (hdbl : (work₀ tapes.dbl).HasBinaryNat 0)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (binaryInstructionArithmeticTM tapes op).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionArithmeticResult tapes op lhs rhs work₀ work ∧
        out = out₀)
      (binaryInstructionArithmeticTime op lhs rhs) :=
  binaryInstructionArithmeticTM_hoareTime_frame_internal tapes op lhs rhs
    inp₀ work₀ out₀ hlhs hrhs hresult hshift htmp hdbl hinput hwork
    houtput

/-- Width-efficient arithmetic followed by a semantics-exact sparse write. -/
theorem binaryInstructionUpdateTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (address lhs rhs : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hready : EntryScanReady tapes.update.entry
      (store.flatMap Entry.encode) address.bits initialWork initialWork)
    (hlhs : (initialWork tapes.lhs).HasBinaryNat lhs)
    (hrhs : (initialWork tapes.rhs).HasBinaryNat rhs)
    (hresult : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hshift : (initialWork tapes.shift).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (hremaining :
      (initialWork tapes.update.remaining).HasBinaryNat store.length)
    (hfound : (initialWork tapes.update.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.update.resultCount).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (initialWork i))
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (binaryInstructionUpdateTM tapes op).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionUpdateResult tapes op store address lhs rhs
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address (op.eval lhs rhs)).flatMap
              Entry.encode))
      (binaryInstructionUpdateTime tapes op store address lhs rhs) :=
  binaryInstructionUpdateTM_hoareTime_frame_internal tapes op store address
    lhs rhs emittedBits initialWork inp₀ out₀ hcanonical hready hlhs hrhs
    hresult hshift htmp hdbl hremaining hfound hresultCount hinput hwork
    houtput

/-- Redirect the updated encoded store into a fresh last work tape while the
real output remains the standard blank parked tape. -/
theorem binaryInstructionUpdateTM_retargetOutput_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (address lhs rhs : ℕ)
    (emittedBits : List Bool) (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (hcanonical : Canonical store)
    (hready : EntryScanReady tapes.update.entry
      (store.flatMap Entry.encode) address.bits
        (fun i => initialWork (Fin.castSucc i))
        (fun i => initialWork (Fin.castSucc i)))
    (hlhs : (initialWork (Fin.castSucc tapes.lhs)).HasBinaryNat lhs)
    (hrhs : (initialWork (Fin.castSucc tapes.rhs)).HasBinaryNat rhs)
    (hresult :
      (initialWork (Fin.castSucc tapes.update.replacement)).HasBinaryNat 0)
    (hshift : (initialWork (Fin.castSucc tapes.shift)).HasBinaryNat 0)
    (htmp : (initialWork (Fin.castSucc tapes.tmp)).HasBinaryNat 0)
    (hdbl : (initialWork (Fin.castSucc tapes.dbl)).HasBinaryNat 0)
    (hremaining :
      (initialWork (Fin.castSucc tapes.update.remaining)).HasBinaryNat
        store.length)
    (hfound :
      (initialWork (Fin.castSucc tapes.update.found)).HasBinaryNat 0)
    (hresultCount :
      (initialWork (Fin.castSucc tapes.update.resultCount)).HasBinaryNat
        store.length)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i : Fin n, TM.Parked (initialWork (Fin.castSucc i)))
    (hbuffer :
      (initialWork (Fin.last n)).HasBinaryPrefix emittedBits) :
    (binaryInstructionUpdateTM tapes op).retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionUpdateResult tapes op store address lhs rhs
          (fun i => initialWork (Fin.castSucc i))
          (fun i => work (Fin.castSucc i)) ∧
        (work (Fin.last n)).HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address (op.eval lhs rhs)).flatMap
              Entry.encode) ∧
        out = (Tape.init []).move Dir3.right)
      (binaryInstructionUpdateTime tapes op store address lhs rhs) := by
  let baseWork : Fin n → Tape := fun i => initialWork (Fin.castSucc i)
  let buffer := initialWork (Fin.last n)
  have hbase := binaryInstructionUpdateTM_hoareTime_frame tapes op store
    address lhs rhs emittedBits baseWork inp₀ buffer hcanonical hready hlhs
    hrhs hresult hshift htmp hdbl hremaining hfound hresultCount hinput hwork
    hbuffer
  have hlift := TM.retargetOutput_hoareTime
    (binaryInstructionUpdateTM tapes op) hbase
  apply hlift.consequence
  · rintro inp work out ⟨hinp, hworkEq, hout⟩
    subst inp
    subst work
    exact ⟨⟨rfl, rfl, rfl⟩, hout⟩
  · rintro inp work out ⟨⟨hinp, hresult, hbuffer'⟩, hout⟩
    exact ⟨hinp, hresult, hbuffer', hout⟩
  · exact le_rfl

/-- Arithmetic and sparse update are both one-way-output machines. -/
theorem binaryInstructionUpdateTM_isTransducer {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp) :
    (binaryInstructionUpdateTM tapes op).IsTransducer := by
  apply TM.IsTransducer.seqTM
  · cases op with
    | add => exact TM.binaryRippleAddTM_isTransducer _ _ _
    | sub => exact TM.binaryRippleSubTM_isTransducer _ _ _
    | mul => exact TM.binaryShiftMulTM_isTransducer _
  · exact entryUpdateTM_isTransducer tapes.update

/-- Two direct sparse-register reads, arithmetic, and the destination write
realize one complete direct `add`, `sub`, or `mul` instruction. -/
theorem directBinaryInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (directBinaryInstructionTM tapes op destination source₀ source₁).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryInstructionResult tapes op store destination source₀
          source₁ initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (op.eval (RegisterStore.read store source₀)
                (RegisterStore.read store source₁))).flatMap Entry.encode))
      (directBinaryInstructionTime tapes op store destination source₀
        source₁) :=
  directBinaryInstructionTM_hoareTime_frame_internal tapes op store
    destination source₀ source₁ emittedBits initialWork inp₀ out₀
    hcanonical hinitial hrhs₀ hreplacement htmp hdbl hinput houtput

/-- Direct arithmetic instruction simulation never moves the output head left. -/
theorem directBinaryInstructionTM_isTransducer {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (destination source₀ source₁ : ℕ) :
    (directBinaryInstructionTM tapes op destination source₀
      source₁).IsTransducer := by
  exact
    (entryLookupStaticTM_isTransducer tapes.lhsLookup source₀).seqTM
      ((entryLookupStaticTM_isTransducer tapes.rhsLookup source₁).seqTM
        ((TM.binaryAddConstTM_isTransducer tapes.update.entry.query
          destination).seqTM
          (binaryInstructionUpdateTM_isTransducer tapes op)))

/-- Every prefix of a direct arithmetic instruction respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem directBinaryInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (directBinaryInstructionTM tapes op destination source₀ source₁).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (directBinaryInstructionTM tapes op destination source₀
      source₁).reachesIn time start current)
    (htime : time ≤ directBinaryInstructionTime tapes op store destination
      source₀ source₁) :
    current.WithinAuxSpace inputLength
      (initialSpace + directBinaryInstructionTime tapes op store destination
        source₀ source₁) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- A fixed-address lookup followed by a loaded runtime-address lookup and
sparse update realizes one indirect `load`. -/
theorem indirectLoadInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination addressRegister : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (indirectLoadInstructionTM tapes destination addressRegister).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectLoadInstructionResult tapes store destination addressRegister
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (RegisterStore.read store
                (RegisterStore.read store addressRegister))).flatMap
              Entry.encode))
      (indirectLoadInstructionTime tapes store destination addressRegister) :=
  indirectLoadInstructionTM_hoareTime_frame_internal tapes store destination
    addressRegister emittedBits initialWork inp₀ out₀ hcanonical hinitial
    hreplacement hinput houtput

/-- Indirect-load simulation never moves the output head left. -/
theorem indirectLoadInstructionTM_isTransducer {n : ℕ}
    (tapes : BinaryInstructionTapes n) (destination addressRegister : ℕ) :
    (indirectLoadInstructionTM tapes destination
      addressRegister).IsTransducer := by
  exact
    (entryLookupStaticTM_isTransducer tapes.lhsLookup addressRegister).seqTM
      ((entryLookupLoadedTM_isTransducer tapes.indirectLoadLookup).seqTM
        ((TM.binaryAddConstTM_isTransducer tapes.update.entry.query
          destination).seqTM
          (entryUpdateTM_isTransducer tapes.update)))

/-- Every indirect-load prefix respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem indirectLoadInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination addressRegister inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (indirectLoadInstructionTM tapes destination addressRegister).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (indirectLoadInstructionTM tapes destination
      addressRegister).reachesIn time start current)
    (htime : time ≤ indirectLoadInstructionTime tapes store destination
      addressRegister) :
    current.WithinAuxSpace inputLength
      (initialSpace + indirectLoadInstructionTime tapes store destination
        addressRegister) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Immediate-value and destination synthesis followed by sparse update
realizes one `imm` instruction. -/
theorem immediateInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (immediateInstructionTM tapes destination value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ImmediateInstructionResult tapes store destination value initialWork
          work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination value).flatMap Entry.encode))
      (immediateInstructionTime tapes store destination value) :=
  immediateInstructionTM_hoareTime_frame_internal tapes store destination value
    emittedBits initialWork inp₀ out₀ hcanonical hinitial hreplacement
    hinput houtput

/-- Immediate-instruction simulation never moves the output head left. -/
theorem immediateInstructionTM_isTransducer {n : ℕ}
    (tapes : BinaryInstructionTapes n) (destination value : ℕ) :
    (immediateInstructionTM tapes destination value).IsTransducer := by
  exact
    (TM.binaryAddConstTM_isTransducer tapes.update.replacement value).seqTM
      ((TM.binaryAddConstTM_isTransducer tapes.update.entry.query
        destination).seqTM
        (entryUpdateTM_isTransducer tapes.update))

/-- Every immediate-instruction prefix respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem immediateInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (immediateInstructionTM tapes destination value).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (immediateInstructionTM tapes destination value).reachesIn time
      start current)
    (htime : time ≤ immediateInstructionTime tapes store destination value) :
    current.WithinAuxSpace inputLength
      (initialSpace + immediateInstructionTime tapes store destination value) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Two direct lookups followed by framed binary copies into the update ABI
realize one indirect `store`. -/
theorem indirectStoreInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (indirectStoreInstructionTM tapes addressRegister source).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectStoreInstructionResult tapes store addressRegister source
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store
              (RegisterStore.read store addressRegister)
              (RegisterStore.read store source)).flatMap Entry.encode))
      (indirectStoreInstructionTime tapes store addressRegister source) :=
  indirectStoreInstructionTM_hoareTime_frame_internal tapes store
    addressRegister source emittedBits initialWork inp₀ out₀ hcanonical
    hinitial hrhs₀ hreplacement hinput houtput

/-- Indirect-store simulation never moves the output head left. -/
theorem indirectStoreInstructionTM_isTransducer {n : ℕ}
    (tapes : BinaryInstructionTapes n) (addressRegister source : ℕ) :
    (indirectStoreInstructionTM tapes addressRegister source).IsTransducer := by
  exact
    ((entryLookupStaticTM_isTransducer tapes.lhsLookup
      addressRegister).seqTM
      (entryLookupStaticTM_isTransducer tapes.rhsLookup source)).seqTM
    ((TM.binaryCopyIntoTM_isTransducer tapes.lhs tapes.update.entry.query
      tapes.update.found).seqTM
      ((TM.binaryCopyIntoTM_isTransducer tapes.rhs tapes.update.replacement
        tapes.update.found).seqTM
        (entryUpdateTM_isTransducer tapes.update)))

/-- Every indirect-store prefix respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem indirectStoreInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (indirectStoreInstructionTM tapes addressRegister source).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (indirectStoreInstructionTM tapes addressRegister
      source).reachesIn time start current)
    (htime : time ≤ indirectStoreInstructionTime tapes store addressRegister
      source) :
    current.WithinAuxSpace inputLength
      (initialSpace + indirectStoreInstructionTime tapes store addressRegister
        source) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Reset and replace a canonical binary program counter by a fixed literal. -/
theorem setProgramCounterTM_hoareTime_frame {n : ℕ}
    (pc : Fin n) (pcValue target : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hpc : (work₀ pc).HasBinaryNat pcValue)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (setProgramCounterTM pc target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ pc
          ((Tape.init (target.bits.map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (setProgramCounterTime pcValue target) :=
  setProgramCounterTM_hoareTime_frame_internal pc pcValue target inp₀ work₀
    out₀ hpc hinput hwork houtput

/-- Conditional-zero control realizes sparse `jz` and restores its loaded
operand to the clean lookup ABI. -/
theorem zeroJumpInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue source target : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (zeroJumpInstructionTM tapes source target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store
          (if RegisterStore.read store source = 0 then target
            else pcValue + 1)
          initialWork work ∧
        out = out₀)
      (zeroJumpInstructionTime tapes store pcValue source target) :=
  zeroJumpInstructionTM_hoareTime_frame_internal tapes store pcValue source
    target initialWork inp₀ out₀ hready hinput houtput

/-- Unconditional control replaces the program counter by its jump target. -/
theorem jumpInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue target : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (jumpInstructionTM tapes target).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store target initialWork work ∧
        out = out₀)
      (jumpInstructionTime pcValue target) :=
  jumpInstructionTM_hoareTime_frame_internal tapes store pcValue target
    initialWork inp₀ out₀ hready hinput houtput

/-- Halt is an exact no-op at the clean control boundary. -/
theorem haltInstructionTM_hoareTime_frame {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hready : ControlInstructionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (haltInstructionTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ControlInstructionResult tapes store pcValue initialWork work ∧
        out = out₀)
      haltInstructionTime :=
  haltInstructionTM_hoareTime_frame_internal tapes store pcValue initialWork
    inp₀ out₀ hready hinput houtput

/-- Program-counter replacement never moves the output head left. -/
theorem setProgramCounterTM_isTransducer {n : ℕ} (pc : Fin n)
    (target : ℕ) : (setProgramCounterTM pc target).IsTransducer :=
  (TM.resetBinaryWorkTM_isTransducer pc).seqTM
    (TM.binaryAddConstTM_isTransducer pc target)

/-- Conditional-zero control never moves the output head left. -/
theorem zeroJumpInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (source target : ℕ) :
    (zeroJumpInstructionTM tapes source target).IsTransducer := by
  exact
    (entryLookupStaticTM_isTransducer tapes.data.lhsLookup source).seqTM
      (((setProgramCounterTM_isTransducer tapes.pc target).branchWorkBlankTM
        (TM.binarySuccTM_isTransducer tapes.pc)).seqTM
        (TM.resetBinaryWorkTM_isTransducer tapes.data.lhs))

/-- Unconditional jump control never moves the output head left. -/
theorem jumpInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (target : ℕ) :
    (jumpInstructionTM tapes target).IsTransducer :=
  setProgramCounterTM_isTransducer tapes.pc target

/-- Halt control never moves the output head left. -/
theorem haltInstructionTM_isTransducer {n : ℕ} :
    (haltInstructionTM (n := n)).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> cases oHead <;> simp [haltInstructionTM, TM.skipTM,
    TM.idleDir]

/-- Every conditional-zero prefix respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem zeroJumpInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : ControlInstructionTapes n) (store : Store)
    (pcValue source target inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (zeroJumpInstructionTM tapes source target).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (zeroJumpInstructionTM tapes source target).reachesIn time start
      current)
    (htime : time ≤
      zeroJumpInstructionTime tapes store pcValue source target) :
    current.WithinAuxSpace inputLength
      (initialSpace +
        zeroJumpInstructionTime tapes store pcValue source target) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Every unconditional-jump prefix respects the coarse
initial-space-plus-total-time auxiliary-space envelope. -/
theorem jumpInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : ControlInstructionTapes n)
    (pcValue target inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (jumpInstructionTM tapes target).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (jumpInstructionTM tapes target).reachesIn time start current)
    (htime : time ≤ jumpInstructionTime pcValue target) :
    current.WithinAuxSpace inputLength
      (initialSpace + jumpInstructionTime pcValue target) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Every halt prefix respects its one-step auxiliary-space envelope. -/
theorem haltInstructionTM_prefix_withinAuxSpace {n : ℕ}
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (haltInstructionTM (n := n)).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (haltInstructionTM (n := n)).reachesIn time start current)
    (htime : time ≤ haltInstructionTime) :
    current.WithinAuxSpace inputLength
      (initialSpace + haltInstructionTime) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
