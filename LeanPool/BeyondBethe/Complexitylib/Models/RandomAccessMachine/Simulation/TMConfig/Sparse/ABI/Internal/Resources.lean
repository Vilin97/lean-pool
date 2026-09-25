/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Internal.Decision
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Resources

/-!
# Resource bounds for the public sparse-simulator ABI -- proof internals

The simulation core uses `StepEnvelope`. During the backward input copy only
the writable value scratch register can temporarily exceed the core word bound;
`MarshalEnvelope` records that exception while retaining the same finite index
support. The first captured-position repair reloads that scratch register from
the sparse data region, returning to the core envelope before simulation.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Temporary marshalling envelope. Every register except `valueReg` already
fits the core word bound; the value scratch may use the larger `valueLimit`. -/
structure MarshalEnvelope (tm : TM n) (bound valueLimit : ℕ)
    (store : Structured.Store) : Prop where
  index_lt : ∀ index, store index ≠ 0 → index < registerBound n (bound + 1)
  value_le : ∀ index, store index ≤ valueLimit
  value_le_of_ne : ∀ index, index ≠ valueReg n →
    store index ≤ wordBound tm bound

theorem MarshalEnvelope.storeEnvelope {tm : TM n} {bound valueLimit : ℕ}
    {store : Structured.Store} (henvelope : MarshalEnvelope tm bound valueLimit store) :
    Structured.Internal.StoreEnvelope (registerBound n (bound + 1))
      valueLimit store :=
  ⟨henvelope.index_lt, henvelope.value_le⟩

theorem StepEnvelope.toMarshalEnvelope {tm : TM n} {bound valueLimit : ℕ}
    {store : Structured.Store} (henvelope : StepEnvelope tm bound store)
    (hlimit : wordBound tm bound ≤ valueLimit) :
    MarshalEnvelope tm bound valueLimit store where
  index_lt := henvelope.index_lt
  value_le index := le_trans (henvelope.value_le index) hlimit
  value_le_of_ne index _ := henvelope.value_le index

private theorem control_lt_registerBound (n bound : ℕ) :
    cellBase n < registerBound n (bound + 1) :=
  control_lt_registerBound_internal n bound

private theorem smallValue_le_wordBound (tm : TM n) (bound value : ℕ)
    (hvalue : value ≤ 4) : value ≤ wordBound tm bound := by
  have hfour : 4 ≤ registerBound n (bound + 1) := by
    have hcontrol := control_lt_registerBound n bound
    simp [cellBase] at hcontrol
    omega
  exact le_trans hvalue
    (le_trans hfour (registerBound_le_wordBound_internal tm bound))

private theorem cellReg_le_wordBound (tm : TM n) (bound : ℕ)
    (tape : Fin (n + 2)) {position : ℕ} (hposition : position ≤ bound + 1) :
    cellReg n tape position ≤ wordBound tm bound :=
  le_trans (Nat.le_of_lt
    (cellReg_lt_registerBound_internal tape (bound := bound) hposition))
    (registerBound_le_wordBound_internal tm bound)

private theorem registerBound_mono (n : ℕ) {bound larger : ℕ}
    (hle : bound ≤ larger) :
    registerBound n bound ≤ registerBound n larger := by
  have hmul := Nat.mul_le_mul_right (n + 2) hle
  simp only [registerBound, cellReg, outputTape, Fin.val_mk]
  omega

private theorem wordBound_mono (tm : TM n) {bound larger : ℕ}
    (hle : bound ≤ larger) : wordBound tm bound ≤ wordBound tm larger := by
  simp only [wordBound]
  apply Nat.max_le.mpr
  constructor
  · exact le_trans (registerBound_mono n (Nat.add_le_add_right hle 1))
      (Nat.le_max_left _ _)
  · apply Nat.max_le.mpr
    constructor
    · exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · exact le_trans (Nat.add_le_add_right hle 1)
        (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

private theorem StepEnvelope.monoBound {tm : TM n} {bound larger : ℕ}
    {store : Structured.Store} (henvelope : StepEnvelope tm bound store)
    (hle : bound ≤ larger) : StepEnvelope tm larger store :=
  henvelope.mono
    (registerBound_mono n (Nat.add_le_add_right hle 1))
    (wordBound_mono tm hle)

private theorem spaceBound_mono (tm : TM n) {bound larger : ℕ}
    (hle : bound ≤ larger) : spaceBound tm bound ≤ spaceBound tm larger := by
  have hregister := registerBound_mono n (Nat.add_le_add_right hle 1)
  have hword := wordBound_mono tm hle
  have hregisterSize := Nat.size_le_size hregister
  have hwordSize := Nat.size_le_size hword
  simp only [spaceBound, bitlen]
  exact Nat.mul_le_mul hregister
    (Nat.add_le_add hregisterSize hwordSize)

theorem decisionTimeBound_mono_steps_internal (tm : TM n)
    (inputLength : ℕ) {steps larger : ℕ} (hle : steps ≤ larger) :
    decisionTimeBound tm inputLength steps ≤
      decisionTimeBound tm inputLength larger := by
  have hbound : marshalBound n inputLength + steps ≤
      marshalBound n inputLength + larger := Nat.add_le_add_left hle _
  have hword := wordBound_mono tm hbound
  have hwidth : wordWidth tm (marshalBound n inputLength + steps) ≤
      wordWidth tm (marshalBound n inputLength + larger) := by
    have hsize := Nat.size_le_size hword
    simpa [wordWidth, bitlen] using! Nat.add_le_add_right hsize 1
  have hfactor : (steps + 1) * runFactor tm ≤
      (larger + 1) * runFactor tm :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hle 1)
  simp only [decisionTimeBound]
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul hfactor hwidth) _)
    (Nat.mul_le_mul_left (4 * (extractVerdictOps n).length) hwidth)

private theorem inputLength_succ_le_marshalBaseBound (n inputLength : ℕ) :
    inputLength + 1 ≤ marshalBaseBound n inputLength := by
  have hmul : inputLength + 1 ≤ (inputLength + 1) * (n + 2) :=
    le_mul_of_one_le_right (Nat.zero_le _) (by omega)
  simp only [marshalBaseBound, registerBound, cellReg, outputTape,
    Fin.val_mk]
  omega

private theorem cellBase_le_marshalBaseBound (n inputLength : ℕ) :
    cellBase n ≤ marshalBaseBound n inputLength := by
  simp only [marshalBaseBound, registerBound, cellReg, outputTape,
    Fin.val_mk]
  omega

private theorem marshalBaseBound_le_wordBound (tm : TM n)
    (inputLength : ℕ) :
    marshalBaseBound n inputLength ≤ wordBound tm (marshalBound n inputLength) := by
  apply le_trans (show marshalBaseBound n inputLength ≤
      marshalBound n inputLength + 1 by simp [marshalBound]; omega)
  exact bound_succ_le_wordBound_internal tm (marshalBound n inputLength)

private theorem marshalValue_le_wordBound (tm : TM n)
    {inputLength processed : ℕ} (hprocessed : processed ≤ inputLength) :
    marshalBaseBound n inputLength + processed ≤
      wordBound tm (marshalBound n inputLength) := by
  apply le_trans (show marshalBaseBound n inputLength + processed ≤
      marshalBound n inputLength + 1 by simp [marshalBound]; omega)
  exact bound_succ_le_wordBound_internal tm (marshalBound n inputLength)

private theorem initRegs_marshalEnvelope (n : ℕ) (x : List Bool) :
    Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length) (initRegs x) := by
  have hinput := Structured.Internal.Input.bitStoreEnvelope
    (lengthReg := 0) (inputBase := 1)
    (indexBound := registerBound n (marshalBound n x.length + 1))
    (valueBound := marshalBaseBound n x.length) x
    (by
      have hbound := bound_lt_registerBound_internal n
        (marshalBound n x.length)
      omega)
    (by
      have hlength := inputLength_succ_le_marshalBaseBound n x.length
      have hbound := bound_lt_registerBound_internal n
        (marshalBound n x.length)
      have hmarshal : 1 + x.length ≤ marshalBound n x.length := by
        simp only [marshalBound]
        omega
      exact Nat.le_of_lt (lt_of_le_of_lt hmarshal hbound))
    (by
      have := inputLength_succ_le_marshalBaseBound n x.length
      omega)
    (by
      have := inputLength_succ_le_marshalBaseBound n x.length
      omega)
  have hinit : initRegs x = Structured.Input.bitStore 0 1 x := by
    funext index
    by_cases hzero : index = 0
    · subst index
      simp [initRegs, Structured.Input.bitStore]
    · have hone : 1 ≤ index := Nat.one_le_iff_ne_zero.mpr hzero
      simp [initRegs, Structured.Input.bitStore, Structured.Input.bitValue,
        hzero, hone]
      rfl
  rw [hinit]
  exact hinput

/-- Installing the four copy-loop constants has a uniform marshalling
envelope and establishes the semantic loop invariant. -/
theorem marshalConstants_measured_internal (tm : TM n) (x : List Bool) :
    Structured.Internal.MeasuredRuns (.basics (marshalConstants n))
      (initRegs x) (marshalStart n x) (marshalConstants n).length
      (4 * (marshalConstants n).length *
        Structured.Internal.valueWidth (marshalBaseBound n x.length))
      (Structured.Internal.envelopeSpace
        (registerBound n (marshalBound n x.length + 1))
        (marshalBaseBound n x.length)) ∧
    MarshalEnvelope tm (marshalBound n x.length)
      (marshalBaseBound n x.length) (marshalStart n x) ∧
    MarshalInvariant n x x.length (marshalStart n x) := by
  have hinitial := initRegs_marshalEnvelope n x
  have hpreserve : ∀ op, op ∈ marshalConstants n →
      ∀ store, Structured.Internal.StoreEnvelope
        (registerBound n (marshalBound n x.length + 1))
        (marshalBaseBound n x.length) store →
      Structured.Internal.StoreEnvelope
        (registerBound n (marshalBound n x.length + 1))
        (marshalBaseBound n x.length) (op.exec store) := by
    intro op hop store henvelope
    simp [marshalConstants] at hop
    rcases hop with rfl | rfl | rfl | rfl
    · apply henvelope.execBasic
      · exact lt_trans (scratch_range_internal n).1.2
          (control_lt_registerBound n (marshalBound n x.length))
      · simp
    · apply henvelope.execBasic
      · exact lt_trans (scratch_range_internal n).2.1.2
          (control_lt_registerBound n (marshalBound n x.length))
      · have hbase := cellBase_le_marshalBaseBound n x.length
        simp [cellBase] at hbase ⊢
        omega
    · apply henvelope.execBasic
      · exact lt_trans (scratch_range_internal n).2.2.1.2
          (control_lt_registerBound n (marshalBound n x.length))
      · exact le_trans (by simp [cellBase]; omega)
          (cellBase_le_marshalBaseBound n x.length)
    · apply henvelope.execBasic
      · exact lt_trans (scratch_range_internal n).2.2.2.1.2
          (control_lt_registerBound n (marshalBound n x.length))
      · exact cellBase_le_marshalBaseBound n x.length
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelope
    (marshalConstants n) (initRegs x) hinitial hpreserve
  have hbaseWord := marshalBaseBound_le_wordBound tm x.length
  have hmarshal : MarshalEnvelope tm (marshalBound n x.length)
      (marshalBaseBound n x.length) (marshalStart n x) := by
    have hfinal := hmeasured.2
    exact ⟨hfinal.index_lt, hfinal.value_le,
      fun index _ => le_trans (hfinal.value_le index) hbaseWord⟩
  simpa [marshalStart] using! And.intro hmeasured.1
    (And.intro hmarshal (marshalStart_invariant_internal n x))

/-- Loading, clearing, and encoding a positive source cursor retain the cursor register. -/
private theorem marshalLoop_encodedState (n : ℕ) (store : Structured.Store) (cursor : ℕ)
    (hcursor : 0 < cursor) (hstate : store stateReg = cursor) :
    let sourceAddressed :=
      (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
    let sourceLoaded :=
      (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
    let sourceCleared :=
      (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
    let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
    let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
    let counted :=
      (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
    let based :=
      (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
    let encoded :=
      (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
    sourceLoaded (addressReg n) = cursor → encoded stateReg = cursor := by
  dsimp only
  intro hloadedAddress
  let sourceAddressed :=
    (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
  let sourceLoaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
  let sourceCleared :=
    (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
  let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
  let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
  let counted :=
    (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
  let based :=
    (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
  let encoded :=
    (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
  have hsourceAddressedState : sourceAddressed stateReg = cursor := by
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, addressReg])]
    exact hstate
  have hsourceLoadedState : sourceLoaded stateReg = cursor := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    exact hsourceAddressedState
  have hsourceClearedState : sourceCleared stateReg = cursor := by
    simp only [sourceCleared, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · exact hsourceLoadedState
    · rw [hloadedAddress]
      simp [stateReg]
      omega
  have hbasedState : based stateReg = cursor := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, stateScratchReg]),
      Function.update_of_ne (by simp [stateReg, tapeCountReg]),
      Function.update_of_ne (by simp [stateReg, oneReg]),
      Function.update_of_ne (by simp [stateReg, zeroReg])]
    exact hsourceClearedState
  have hencodedState : encoded stateReg = cursor := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    exact hbasedState
  exact hencodedState

private theorem marshalLoopOps_envelopeChain (n : ℕ) (x : List Bool)
    {cursor processed : ℕ} {store : Structured.Store}
    (hcursor : 0 < cursor)
    (hinvariant : MarshalInvariant n x cursor store)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) store) :
    Structured.Internal.Basic.EnvelopeChain
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed + 1)
      (marshalLoopOps n) store := by
  let limit := marshalBaseBound n x.length + processed + 1
  let sourceAddressed :=
    (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
  let sourceLoaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
  let sourceCleared :=
    (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
  let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
  let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
  let counted :=
    (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
  let based :=
    (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
  let encoded :=
    (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
  let multiplied :=
    (Structured.Basic.mul (addressReg n) stateReg (tapeCountReg n)).exec encoded
  let destinationAddressed :=
    (Structured.Basic.add (addressReg n) (addressReg n)
      (stateScratchReg n)).exec multiplied
  let destinationStored :=
    (Structured.Basic.store (addressReg n) (valueReg n)).exec
      destinationAddressed
  let final :=
    (Structured.Basic.sub stateReg stateReg (oneReg n)).exec destinationStored
  have hindexControl := control_lt_registerBound n (marshalBound n x.length)
  have hstore : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit store :=
    henvelope.mono le_rfl (by omega)
  have hstate : store stateReg = cursor := hinvariant.1
  have hcursorLength : cursor ≤ x.length := hinvariant.2.1
  have hzero : store (zeroReg n) = 0 := hinvariant.2.2.1
  have hsourceAddressedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed)
      sourceAddressed := by
    apply henvelope.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.2.1.2 hindexControl
    · simp [Structured.Internal.Basic.writeValue, hstate, hzero]
      exact le_trans hcursorLength
        (le_trans (show x.length ≤ marshalBaseBound n x.length by
          have := inputLength_succ_le_marshalBaseBound n x.length
          omega) (by omega))
  have hsourceAddress : sourceAddressed (addressReg n) = cursor := by
    simp [sourceAddressed, Structured.Basic.exec, hstate, hzero]
  have hsourceAddressed : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit sourceAddressed :=
    hsourceAddressedCurrent.mono le_rfl (by omega)
  have hsourceLoadedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed)
      sourceLoaded := by
    apply hsourceAddressedCurrent.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.2.2.1.2 hindexControl
    · exact hsourceAddressedCurrent.value_le _
  have hsourceLoaded : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit sourceLoaded :=
    hsourceLoadedCurrent.mono le_rfl (by omega)
  have hloadedAddress : sourceLoaded (addressReg n) = cursor := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [addressReg, valueReg])]
    exact hsourceAddress
  have hloadedZero : sourceLoaded (zeroReg n) = 0 := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, valueReg])]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hzero
  have hsourceClearedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed)
      sourceCleared := by
    apply hsourceLoadedCurrent.execBasic
    · simp only [Structured.Internal.Basic.writeIndex]
      rw [hloadedAddress]
      apply lt_of_le_of_lt hcursorLength
      apply lt_of_le_of_lt (show x.length ≤ marshalBound n x.length by
        simp [marshalBound])
      exact bound_lt_registerBound_internal n (marshalBound n x.length)
    · simp [Structured.Internal.Basic.writeValue, hloadedZero]
  have hsourceCleared : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit sourceCleared :=
    hsourceClearedCurrent.mono le_rfl (by omega)
  have hzeroedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) zeroed := by
    apply hsourceClearedCurrent.execBasic
    · exact lt_trans (scratch_range_internal n).1.2 hindexControl
    · simp
  have hzeroed : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit zeroed :=
    hzeroedCurrent.mono le_rfl (by omega)
  have honedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) oned := by
    apply hzeroedCurrent.execBasic
    · exact lt_trans (scratch_range_internal n).2.1.2 hindexControl
    · have hbase := inputLength_succ_le_marshalBaseBound n x.length
      simp
      omega
  have honed : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit oned :=
    honedCurrent.mono le_rfl (by omega)
  have hcountedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) counted := by
    apply honedCurrent.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.1.2 hindexControl
    · have hbase := cellBase_le_marshalBaseBound n x.length
      simp [Structured.Internal.Basic.writeValue, cellBase] at hbase ⊢
      omega
  have hcounted : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit counted :=
    hcountedCurrent.mono le_rfl (by omega)
  have hbasedCurrent : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) based := by
    apply hcountedCurrent.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.1.2 hindexControl
    · exact le_trans (cellBase_le_marshalBaseBound n x.length) (by
        simp)
  have hbased : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit based :=
    hbasedCurrent.mono le_rfl (by omega)
  have hbasedValue : based (valueReg n) ≤
      marshalBaseBound n x.length + processed :=
    hbasedCurrent.value_le _
  have hbasedOne : based (oneReg n) = 1 := by
    simp [based, counted, oned, Structured.Basic.exec, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hencoded : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit encoded := by
    apply hbased.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.2.2.1.2 hindexControl
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hbasedOne]
      exact Nat.add_le_add_right hbasedValue 1
  have hencodedState : encoded stateReg = cursor :=
    marshalLoop_encodedState n store cursor hcursor hstate hloadedAddress
  have hencodedCount : encoded (tapeCountReg n) = n + 2 := by
    simp [encoded, based, counted, Structured.Basic.exec, tapeCountReg,
      stateScratchReg, valueReg, Function.update_of_ne]
  have hcursorCellBase : cursor * (n + 2) + cellBase n ≤
      marshalBaseBound n x.length := by
    have hmul := Nat.mul_le_mul_right (n + 2) hcursorLength
    have hmulSucc := Nat.mul_le_mul_right (n + 2)
      (show x.length ≤ x.length + 1 by omega)
    simp only [marshalBaseBound, registerBound, cellReg, outputTape,
      Fin.val_mk]
    omega
  have hmultiplied : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit multiplied := by
    apply hencoded.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.2.1.2 hindexControl
    · change encoded stateReg * encoded (tapeCountReg n) ≤ limit
      rw [hencodedState, hencodedCount]
      exact le_trans (show cursor * (n + 2) ≤
          cursor * (n + 2) + cellBase n by omega)
        (le_trans hcursorCellBase (by omega))
  have hmultipliedAddress : multiplied (addressReg n) = cursor * (n + 2) := by
    simp [multiplied, Structured.Basic.exec, hencodedState, hencodedCount]
  have hmultipliedBase : multiplied (stateScratchReg n) = cellBase n := by
    simp [multiplied, encoded, based, Structured.Basic.exec,
      stateScratchReg, addressReg, valueReg, Function.update_of_ne]
  have hdestinationAddressed : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit
      destinationAddressed := by
    apply hmultiplied.execBasic
    · exact lt_trans (scratch_range_internal n).2.2.2.2.1.2 hindexControl
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hmultipliedAddress, hmultipliedBase]
      exact le_trans hcursorCellBase (by omega)
  have hdestinationAddress : destinationAddressed (addressReg n) =
      cellReg n (inputTape n) cursor := by
    simp [destinationAddressed, Structured.Basic.exec, hmultipliedAddress,
      hmultipliedBase, cellReg, inputTape, Nat.add_comm]
  have hdestinationStored : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit
      destinationStored := by
    apply hdestinationAddressed.execBasic
    · simp only [Structured.Internal.Basic.writeIndex]
      rw [hdestinationAddress]
      exact cellReg_lt_registerBound_internal (inputTape n)
        (show cursor ≤ marshalBound n x.length + 1 by
          simp [marshalBound]
          omega)
    · exact hdestinationAddressed.value_le _
  have hfinal : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1)) limit final := by
    apply hdestinationStored.execBasic
    · simp [stateReg, registerBound, cellReg, outputTape, cellBase]
    · exact le_trans (Nat.sub_le _ _)
        (hdestinationStored.value_le stateReg)
  simp only [marshalLoopOps, Structured.Internal.Basic.EnvelopeChain]
  exact ⟨hstore, hsourceAddressed, hsourceLoaded, hsourceCleared, hzeroed,
    honed, hcounted, hbased, hencoded, hmultiplied,
    hdestinationAddressed, hdestinationStored, hfinal⟩

private theorem envelopeChain_monoValue {indexBound valueBound largerValue : ℕ}
    {ops : List Structured.Basic} {store : Structured.Store}
    (hchain : Structured.Internal.Basic.EnvelopeChain
      indexBound valueBound ops store)
    (hvalue : valueBound ≤ largerValue) :
    Structured.Internal.Basic.EnvelopeChain
      indexBound largerValue ops store := by
  induction ops generalizing store with
  | nil => exact hchain.mono le_rfl hvalue
  | cons op rest ih =>
      exact ⟨hchain.1.mono le_rfl hvalue, ih hchain.2⟩

private theorem marshalLoop_measured_aux (n : ℕ) (x : List Bool)
    {cursor processed : ℕ} {store : Structured.Store}
    (hbalance : processed + cursor = x.length)
    (hinvariant : MarshalInvariant n x cursor store)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerBound n (marshalBound n x.length + 1))
      (marshalBaseBound n x.length + processed) store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (marshalLoop n) store final
        (marshalLoopSteps n cursor)
        ((cursor * (3 + 4 * (marshalLoopOps n).length) + 1) *
          marshalWidth n x.length)
        (marshalSpaceBound n x.length) ∧
      MarshalInvariant n x 0 final ∧
      Structured.Internal.StoreEnvelope
        (registerBound n (marshalBound n x.length + 1))
        (marshalBaseBound n x.length + processed + cursor) final := by
  induction cursor generalizing processed store with
  | zero =>
      have hzero : store stateReg = 0 := hinvariant.1
      have hglobal : Structured.Internal.StoreEnvelope
          (registerBound n (marshalBound n x.length + 1))
          (marshalBound n x.length) store := by
        have hp : processed = x.length := by omega
        simpa [marshalBound, hp] using! henvelope
      have hrun := Structured.Internal.MeasuredRuns.whileZeroEnvelope
        (body := .basics (marshalLoopOps n)) hzero hglobal
      refine ⟨store, ?_, hinvariant, ?_⟩
      · simpa [marshalLoop, marshalLoopSteps, marshalLoopTimeBound,
          marshalWidth, marshalSpaceBound,
          Structured.Internal.valueWidth,
          Structured.Internal.envelopeSpace] using! hrun
      · simpa using! henvelope
  | succ cursor ih =>
      have hpositive : 0 < cursor + 1 := by omega
      have hnonzero : store stateReg ≠ 0 := by
        rw [hinvariant.1]
        omega
      have hprocessed : processed + 1 ≤ x.length := by omega
      have hchain := marshalLoopOps_envelopeChain n x hpositive hinvariant
        henvelope
      have hchainGlobal := envelopeChain_monoValue hchain
        (show marshalBaseBound n x.length + processed + 1 ≤
            marshalBound n x.length by
          simp [marshalBound]
          omega)
      let middle := Structured.Basic.execList (marshalLoopOps n) store
      have hbody := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
        (marshalLoopOps n) store hchainGlobal |>.1
      have hmiddleInvariant : MarshalInvariant n x cursor middle := by
        have hstep := marshalLoopOps_invariant_internal n x (cursor + 1)
          store hpositive hinvariant
        simpa [middle] using! hstep
      have hmiddleEnvelope : Structured.Internal.StoreEnvelope
          (registerBound n (marshalBound n x.length + 1))
          (marshalBaseBound n x.length + (processed + 1)) middle := by
        have hfinal := hchain.final
        simpa [middle, Nat.add_assoc] using! hfinal
      obtain ⟨final, hloop, hfinalInvariant, hfinalEnvelope⟩ :=
        ih (processed := processed + 1) (store := middle)
          (by omega) hmiddleInvariant hmiddleEnvelope
      have hinitialGlobal : Structured.Internal.StoreEnvelope
          (registerBound n (marshalBound n x.length + 1))
          (marshalBound n x.length) store :=
        henvelope.mono le_rfl (by simp [marshalBound]; omega)
      have hrun := Structured.Internal.MeasuredRuns.whileNonzeroEnvelope
        hnonzero hinitialGlobal hbody hloop
      refine ⟨final, ?_, hfinalInvariant, ?_⟩
      · convert! hrun using 1
        all_goals simp [marshalLoopSteps, marshalWidth,
          Structured.Internal.valueWidth, Nat.succ_mul]
        all_goals ring
      · convert! hfinalEnvelope using 1
        omega

/-- The backward-copy loop has an exact source-step count, linear logarithmic
cost, and a finite sparse-store envelope. -/
theorem marshalLoop_measured_internal {tm : TM n} (x : List Bool) :
    ∃ final,
      Structured.Internal.MeasuredRuns (marshalLoop n) (marshalStart n x) final
        (marshalLoopSteps n x.length) (marshalLoopTimeBound n x.length)
        (marshalSpaceBound n x.length) ∧
      MarshalInvariant n x 0 final ∧
      StepEnvelope tm (marshalBound n x.length) final := by
  obtain ⟨_hconstants, hmarshal, hinvariant⟩ :=
    marshalConstants_measured_internal tm x
  obtain ⟨final, hrun, hfinalInvariant, hfinalEnvelope⟩ :=
    marshalLoop_measured_aux n x (processed := 0) (store := marshalStart n x)
      (by simp) hinvariant hmarshal.storeEnvelope
  refine ⟨final, ?_, hfinalInvariant, ?_⟩
  · simpa using! hrun
  · apply hfinalEnvelope.mono le_rfl
      (show marshalBaseBound n x.length + 0 + x.length ≤
          wordBound tm (marshalBound n x.length) by
        simpa [marshalBound] using!
          (marshalValue_le_wordBound tm (processed := x.length) le_rfl))

/-- The verdict extractor stays in the core envelope and has the standard
four-width-per-basic-instruction cost bound. -/
theorem extractVerdict_measured_internal {tm : TM n} {bound : ℕ}
    {halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm halted store)
    (henvelope : StepEnvelope tm bound store) :
    let final := Structured.Basic.execList (extractVerdictOps n) store
    Structured.Internal.MeasuredRuns (.basics (extractVerdictOps n)) store final
      (extractVerdictOps n).length
      (4 * (extractVerdictOps n).length * wordWidth tm bound)
      (spaceBound tm bound) ∧
    StepEnvelope tm bound final ∧
    final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  let addressed := (Structured.Basic.imm (addressReg n)
    (cellReg n (outputTape n) 1)).exec store
  let loaded := (Structured.Basic.load stateReg (addressReg n)).exec addressed
  let oned := (Structured.Basic.imm (oneReg n) 1).exec loaded
  let final := (Structured.Basic.sub stateReg stateReg (oneReg n)).exec oned
  have hrange := scratch_range_internal n
  have haddressValue := cellReg_le_wordBound tm bound (outputTape n)
    (position := 1) (by omega)
  have haddressed : StepEnvelope tm bound addressed := by
    apply henvelope.execBasic
    · exact lt_trans hrange.2.2.2.2.1.2
        (control_lt_registerBound n bound)
    · simpa [Structured.Internal.Basic.writeValue] using! haddressValue
  have hloaded : StepEnvelope tm bound loaded := by
    apply haddressed.execBasic
    · simp [stateReg, registerBound, cellReg, outputTape, cellBase]
    · exact haddressed.value_le (addressed (addressReg n))
  have honeBound : 1 ≤ wordBound tm bound :=
    smallValue_le_wordBound tm bound 1 (by omega)
  have honed : StepEnvelope tm bound oned := by
    apply hloaded.execBasic
    · exact lt_trans hrange.2.1.2 (control_lt_registerBound n bound)
    · simpa [Structured.Internal.Basic.writeValue] using! honeBound
  have hfinal : StepEnvelope tm bound final := by
    apply honed.execBasic
    · simp [stateReg, registerBound, cellReg, outputTape, cellBase]
    · exact le_trans (Nat.sub_le _ _) (honed.value_le stateReg)
  have hchain : Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (extractVerdictOps n) store := by
    simpa [extractVerdictOps, addressed, loaded, oned, final] using!
      And.intro henvelope
        (And.intro haddressed (And.intro hloaded (And.intro honed hfinal)))
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (extractVerdictOps n) store hchain
  have hverdict := extractVerdict_exec_internal hrepresents
  refine ⟨?_, hfinal, ?_⟩
  · simpa [wordWidth, spaceBound, Structured.Internal.valueWidth,
      Structured.Internal.envelopeSpace] using! hmeasured.1
  · obtain ⟨_cost, _space, _hexec, hvalue⟩ := hverdict
    simpa [final] using! hvalue

private theorem repairBit_measured_internal {tm : TM n} {bound valueLimit : ℕ}
    {entry : ℕ × ℕ} {store : Structured.Store}
    (hposition : entry.1 ≤ bound + 1) (hvalue : entry.2 ≤ 1)
    (henvelope : MarshalEnvelope tm bound valueLimit store)
    (hwordLimit : wordBound tm bound ≤ valueLimit) :
    ∃ steps,
      Structured.Internal.MeasuredRuns (repairBit n entry) store
        (repairBitStore n entry store) steps
        (27 * (bitlen valueLimit + 1))
        (Structured.Internal.envelopeSpace
          (registerBound n (bound + 1)) valueLimit) ∧
      StepEnvelope tm bound (repairBitStore n entry store) := by
  let addressed := (Structured.Basic.imm (addressReg n)
    (cellReg n (inputTape n) entry.1)).exec store
  let loaded := (Structured.Basic.load (valueReg n) (addressReg n)).exec addressed
  have hrange := scratch_range_internal n
  have haddressBound := cellReg_le_wordBound tm bound (inputTape n) hposition
  have haddressedMarshal : MarshalEnvelope tm bound valueLimit addressed := by
    refine ⟨?_, ?_, ?_⟩
    · intro index hnonzero
      by_cases heq : index = addressReg n
      · subst index
        exact lt_trans hrange.2.2.2.2.1.2
          (control_lt_registerBound n bound)
      · exact henvelope.index_lt index (by
          simpa [addressed, Structured.Basic.exec,
            Function.update_of_ne heq] using! hnonzero)
    · intro index
      by_cases heq : index = addressReg n
      · subst index
        simpa [addressed, Structured.Basic.exec] using!
          le_trans haddressBound hwordLimit
      · simpa [addressed, Structured.Basic.exec,
          Function.update_of_ne heq] using! henvelope.value_le index
    · intro index hne
      by_cases heq : index = addressReg n
      · subst index
        simpa [addressed, Structured.Basic.exec] using! haddressBound
      · simpa [addressed, Structured.Basic.exec,
          Function.update_of_ne heq] using! henvelope.value_le_of_ne index hne
  have haddressedStore := haddressedMarshal.storeEnvelope
  have haddress : addressed (addressReg n) =
      cellReg n (inputTape n) entry.1 := by
    simp [addressed, Structured.Basic.exec]
  have haddressNeValue : addressed (addressReg n) ≠ valueReg n := by
    rw [haddress]
    simp [cellReg, inputTape, cellBase, valueReg]
    omega
  have hloadedEnvelope : StepEnvelope tm bound loaded := by
    constructor
    · intro index hnonzero
      by_cases heq : index = valueReg n
      · subst index
        exact lt_trans hrange.2.2.2.2.2.1.2
          (control_lt_registerBound n bound)
      · exact haddressedMarshal.index_lt index (by
          simpa [loaded, Structured.Basic.exec,
            Function.update_of_ne heq] using! hnonzero)
    · intro index
      by_cases heq : index = valueReg n
      · subst index
        simp only [loaded, Structured.Basic.exec, Function.update_self]
        exact haddressedMarshal.value_le_of_ne
          (addressed (addressReg n)) haddressNeValue
      · simpa [loaded, Structured.Basic.exec,
          Function.update_of_ne heq] using!
          haddressedMarshal.value_le_of_ne index heq
  have hloadedLarge := hloadedEnvelope.mono le_rfl hwordLimit
  have hsetupChain : Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) valueLimit
      [.imm (addressReg n) (cellReg n (inputTape n) entry.1),
        .load (valueReg n) (addressReg n)] store := by
    exact ⟨henvelope.storeEnvelope, haddressedStore, hloadedLarge⟩
  have hsetup := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    [.imm (addressReg n) (cellReg n (inputTape n) entry.1),
      .load (valueReg n) (addressReg n)] store hsetupChain |>.1
  by_cases hzero : loaded (valueReg n) = 0
  · have hskip := Structured.Internal.MeasuredRuns.skipEnvelope hloadedLarge
    have hbranch := Structured.Internal.MeasuredRuns.ifZeroEnvelope
      (onNonzero := .basics
        [.imm (valueReg n) (entry.2 + 1),
          .store (addressReg n) (valueReg n)])
      hzero hloadedLarge hskip
    have hrun := hsetup.seq hbranch
    have hrun' := hrun.weakenCost (show
      8 * (bitlen valueLimit + 1) + (bitlen valueLimit + 1) ≤
        27 * (bitlen valueLimit + 1) by omega)
    have hrepairStore : repairBitStore n entry store = loaded := by
      unfold repairBitStore
      change (if loaded (valueReg n) = 0 then loaded else _) = loaded
      rw [ite_eq_left hzero]
    refine ⟨3, ?_, ?_⟩
    · rw [hrepairStore]
      simpa [repairBit] using! hrun'
    · rw [hrepairStore]
      exact hloadedEnvelope
  · let valued := (Structured.Basic.imm (valueReg n) (entry.2 + 1)).exec loaded
    let final := (Structured.Basic.store (addressReg n) (valueReg n)).exec valued
    have hsmall : entry.2 + 1 ≤ wordBound tm bound := by
      apply smallValue_le_wordBound tm bound
      omega
    have hvalued : StepEnvelope tm bound valued := by
      apply hloadedEnvelope.execBasic
      · exact lt_trans hrange.2.2.2.2.2.1.2
          (control_lt_registerBound n bound)
      · simpa [Structured.Internal.Basic.writeValue] using! hsmall
    have hvaluedAddress : valued (addressReg n) =
        cellReg n (inputTape n) entry.1 := by
      simp [valued, loaded, addressed, Structured.Basic.exec, addressReg,
        valueReg, Function.update_of_ne]
    have hvaluedValue : valued (valueReg n) = entry.2 + 1 := by
      simp [valued, Structured.Basic.exec]
    have hfinal : StepEnvelope tm bound final := by
      apply hvalued.execBasic
      · simp only [Structured.Internal.Basic.writeIndex]
        rw [hvaluedAddress]
        exact cellReg_lt_registerBound_internal (inputTape n) hposition
      · simp only [Structured.Internal.Basic.writeValue]
        rw [hvaluedValue]
        exact hsmall
    have hwritesChain : Structured.Internal.Basic.EnvelopeChain
        (registerBound n (bound + 1)) valueLimit
        [.imm (valueReg n) (entry.2 + 1),
          .store (addressReg n) (valueReg n)] loaded := by
      exact ⟨hloadedLarge, hvalued.mono le_rfl hwordLimit,
        hfinal.mono le_rfl hwordLimit⟩
    have hwrites := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
      [.imm (valueReg n) (entry.2 + 1),
        .store (addressReg n) (valueReg n)] loaded hwritesChain |>.1
    have hbranch := Structured.Internal.MeasuredRuns.ifNonzeroEnvelope
      (onZero := .skip) hzero hloadedLarge hwrites
    have hrun := hsetup.seq hbranch
    have hrun' := hrun.weakenCost (show
      8 * (bitlen valueLimit + 1) +
          (3 * (bitlen valueLimit + 1) +
            8 * (bitlen valueLimit + 1)) ≤
        27 * (bitlen valueLimit + 1) by omega)
    have hrepairStore : repairBitStore n entry store = final := by
      unfold repairBitStore
      change (if loaded (valueReg n) = 0 then loaded else
        Structured.Basic.execList
          [.imm (valueReg n) (entry.2 + 1),
            .store (addressReg n) (valueReg n)] loaded) = final
      rw [ite_eq_right hzero]
      rfl
    refine ⟨6, ?_, ?_⟩
    · rw [hrepairStore]
      simpa [repairBit] using! hrun'
    · rw [hrepairStore]
      exact hfinal

private theorem repairCaptured_fromStep_measured {tm : TM n}
    {bound valueLimit : ℕ} (captured : List (ℕ × ℕ))
    {store : Structured.Store}
    (hentries : ∀ entry, entry ∈ captured →
      entry.1 ≤ bound + 1 ∧ entry.2 ≤ 1)
    (henvelope : StepEnvelope tm bound store)
    (hwordLimit : wordBound tm bound ≤ valueLimit) :
    ∃ final steps,
      Structured.Internal.MeasuredRuns (repairCaptured n captured) store final
        steps (captured.length * (27 * (bitlen valueLimit + 1)))
        (Structured.Internal.envelopeSpace
          (registerBound n (bound + 1)) valueLimit) ∧
      final = repairStore n captured store ∧ StepEnvelope tm bound final := by
  induction captured generalizing store with
  | nil =>
      have hskip := Structured.Internal.MeasuredRuns.skipEnvelope
        (henvelope.mono le_rfl hwordLimit)
      exact ⟨store, 0, by simpa [repairCaptured] using! hskip, rfl, henvelope⟩
  | cons entry rest ih =>
      have hentry := hentries entry (by simp)
      obtain ⟨firstSteps, hfirst, hfirstEnvelope⟩ :=
        repairBit_measured_internal hentry.1 hentry.2
          (henvelope.toMarshalEnvelope hwordLimit) hwordLimit
      let first := repairBitStore n entry store
      have hrestEntries : ∀ candidate, candidate ∈ rest →
          candidate.1 ≤ bound + 1 ∧ candidate.2 ≤ 1 := by
        intro candidate hmem
        exact hentries candidate (by simp [hmem])
      obtain ⟨final, restSteps, hrest, hrestStore, hfinalEnvelope⟩ :=
        ih hrestEntries (by simpa [first] using! hfirstEnvelope)
      have hrun := hfirst.seq hrest
      refine ⟨final, firstSteps + restSteps, ?_, ?_, hfinalEnvelope⟩
      · convert! hrun using 1
        simp only [List.length_cons]
        ring
      · simp [repairStore] at hrestStore ⊢
        exact hrestStore

theorem repairCaptured_measured_internal {tm : TM n} {bound valueLimit : ℕ}
    {captured : List (ℕ × ℕ)} {store : Structured.Store}
    (hentries : ∀ entry, entry ∈ captured →
      entry.1 ≤ bound + 1 ∧ entry.2 ≤ 1)
    (hnonempty : captured ≠ [])
    (henvelope : MarshalEnvelope tm bound valueLimit store)
    (hwordLimit : wordBound tm bound ≤ valueLimit) :
    ∃ final steps,
      Structured.Internal.MeasuredRuns (repairCaptured n captured) store final
        steps (captured.length * (27 * (bitlen valueLimit + 1)))
        (Structured.Internal.envelopeSpace
          (registerBound n (bound + 1)) valueLimit) ∧
      final = repairStore n captured store ∧ StepEnvelope tm bound final := by
  obtain ⟨entry, rest, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
  have hentry := hentries entry (by simp)
  obtain ⟨firstSteps, hfirst, hfirstEnvelope⟩ :=
    repairBit_measured_internal hentry.1 hentry.2 henvelope hwordLimit
  have hrestEntries : ∀ candidate, candidate ∈ rest →
      candidate.1 ≤ bound + 1 ∧ candidate.2 ≤ 1 := by
    intro candidate hmem
    exact hentries candidate (by simp [hmem])
  obtain ⟨final, restSteps, hrest, hrestStore, hfinalEnvelope⟩ :=
    repairCaptured_fromStep_measured rest hrestEntries hfirstEnvelope hwordLimit
  have hrun := hfirst.seq hrest
  refine ⟨final, firstSteps + restSteps, ?_, ?_, hfinalEnvelope⟩
  · convert! hrun using 1
    simp only [List.length_cons]
    ring
  · simp [repairStore] at hrestStore ⊢
    exact hrestStore

private theorem immWrites_envelopeChain {tm : TM n} {bound : ℕ}
    (writes : List (ℕ × ℕ)) {store : Structured.Store}
    (hfits : ∀ write, write ∈ writes →
      write.1 < registerBound n (bound + 1) ∧
        write.2 ≤ wordBound tm bound)
    (henvelope : StepEnvelope tm bound store) :
    Structured.Internal.Basic.EnvelopeChain
      (registerBound n (bound + 1)) (wordBound tm bound)
      (writes.map fun write => Structured.Basic.imm write.1 write.2) store := by
  induction writes generalizing store with
  | nil => exact henvelope
  | cons write rest ih =>
      have hwrite := hfits write (by simp)
      have hnext : StepEnvelope tm bound
          ((Structured.Basic.imm write.1 write.2).exec store) := by
        apply henvelope.execBasic
        · exact hwrite.1
        · simpa [Structured.Internal.Basic.writeValue] using! hwrite.2
      have hrestFits : ∀ candidate, candidate ∈ rest →
          candidate.1 < registerBound n (bound + 1) ∧
            candidate.2 ≤ wordBound tm bound := by
        intro candidate hmem
        exact hfits candidate (by simp [hmem])
      exact ⟨henvelope, ih hrestFits hnext⟩

private theorem initializeConfigWrite_fits (tm : TM n) (bound : ℕ)
    {write : ℕ × ℕ} (hmem : write ∈ initializeConfigWrites tm) :
    write.1 < registerBound n (bound + 1) ∧
      write.2 ≤ wordBound tm bound := by
  simp only [initializeConfigWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hmem
  rcases hmem with hstateOrHead | hstart
  · rcases hstateOrHead with hstate | hhead
    · subst write
      constructor
      · simp [stateReg, registerBound, cellReg, outputTape, cellBase]
      · have hcode : stateCode tm tm.qstart < Fintype.card tm.Q := by
          simp [stateCode]
        exact le_trans (Nat.le_of_lt hcode)
          (card_le_wordBound_internal tm bound)
    · obtain ⟨tape, _hfin, rfl⟩ := hhead
      constructor
      · have hcontrol := headReg_lt_control_internal tape
        exact lt_of_lt_of_le hcontrol
          (le_trans (by simp [cellBase]; omega)
            (Nat.le_of_lt (control_lt_registerBound n bound)))
      · exact Nat.zero_le _
  · obtain ⟨tape, _hfin, rfl⟩ := hstart
    constructor
    · exact cellReg_lt_registerBound_internal tape (position := 0) (by omega)
    · change symbolCode Γ.start ≤ wordBound tm bound
      exact smallValue_le_wordBound tm bound _ (by decide)

theorem initializeConfigOps_measured_internal {tm : TM n} {bound : ℕ}
    {store : Structured.Store} (henvelope : StepEnvelope tm bound store) :
    let final := Structured.Basic.execList (initializeConfigOps tm) store
    Structured.Internal.MeasuredRuns (.basics (initializeConfigOps tm)) store final
      (initializeConfigOps tm).length
      (4 * (initializeConfigOps tm).length * wordWidth tm bound)
      (spaceBound tm bound) ∧ StepEnvelope tm bound final := by
  have hchain := immWrites_envelopeChain (tm := tm) (bound := bound)
    (initializeConfigWrites tm) (fun write hmem =>
      initializeConfigWrite_fits tm bound hmem) henvelope
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (initializeConfigOps tm) store (by
      simpa [initializeConfigOps] using! hchain)
  simpa [wordWidth, spaceBound, Structured.Internal.valueWidth,
    Structured.Internal.envelopeSpace] using! hmeasured

private theorem captureValues_eq_reverse_append (store : Structured.Store)
    (regs : List ℕ) (captured : List (ℕ × ℕ)) :
    captureValues store regs captured =
      (regs.map (fun reg => (reg, store reg))).reverse ++ captured := by
  induction regs generalizing captured with
  | nil => simp [captureValues]
  | cons reg rest ih =>
      rw [captureValues, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem capturedInput_entry (n : ℕ) (x : List Bool)
    {entry : ℕ × ℕ} (hmem : entry ∈ capturedInput n x) :
    entry.1 ∈ captureRegs n ∧ entry.2 = initRegs x entry.1 := by
  rw [capturedInput, captureValues_eq_reverse_append] at hmem
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at hmem
  obtain ⟨reg, hreg, rfl⟩ := hmem
  exact ⟨hreg, rfl⟩

private theorem capturedInput_entries_fit (n : ℕ) (x : List Bool)
    {bound : ℕ} (hcontrol : valueReg n ≤ bound + 1) :
    ∀ entry, entry ∈ capturedInput n x →
      entry.1 ≤ bound + 1 ∧ entry.2 ≤ 1 := by
  intro entry hmem
  have hentry := capturedInput_entry n x hmem
  have hposition : entry.1 ≤ valueReg n := by
    have hreg := hentry.1
    simp [captureRegs, zeroReg, oneReg, tapeCountReg, stateScratchReg,
      addressReg, valueReg] at hreg
    rcases hreg with h | h | h | h | h | h
    all_goals rw [h]
    all_goals simp [valueReg]
  have hpositive := captureRegs_positive_internal n hentry.1
  have hbit := initRegs_bool_of_pos_internal x hpositive
  constructor
  · exact le_trans hposition hcontrol
  · rw [hentry.2]
    omega

private theorem capturedInput_nonempty (n : ℕ) (x : List Bool) :
    capturedInput n x ≠ [] := by
  rw [capturedInput, captureValues_eq_reverse_append]
  simp [captureRegs]

private theorem marshalBaseSpace_le_spaceBound (tm : TM n)
    (inputLength : ℕ) :
    Structured.Internal.envelopeSpace
        (registerBound n (marshalBound n inputLength + 1))
        (marshalBaseBound n inputLength) ≤
      spaceBound tm (marshalBound n inputLength) := by
  have hvalue := marshalBaseBound_le_wordBound tm inputLength
  have hsize := Nat.size_le_size hvalue
  simp only [Structured.Internal.envelopeSpace, spaceBound, bitlen]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hsize _)

private theorem marshalSpace_le_spaceBound (tm : TM n)
    (inputLength : ℕ) :
    marshalSpaceBound n inputLength ≤
      spaceBound tm (marshalBound n inputLength) := by
  have hvalue := marshalValue_le_wordBound tm
    (inputLength := inputLength) (processed := inputLength) le_rfl
  have hsize := Nat.size_le_size (by
    simpa [marshalBound] using! hvalue)
  simp only [marshalSpaceBound, spaceBound, bitlen]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hsize _)

/-- A selected capture-tree leaf carries the public input through copy,
repair, and initialization within one concrete resource envelope. -/
theorem marshalLeaf_measured_internal (tm : TM n) (x : List Bool) :
    ∃ final steps,
      Structured.Internal.MeasuredRuns
        (marshalLeaf tm (capturedInput n x)) (initRegs x) final steps
        (marshalLeafTimeBound tm x.length)
        (spaceBound tm (marshalBound n x.length)) ∧
      Represents tm (tm.initCfg x) final ∧
      StepEnvelope tm (marshalBound n x.length) final := by
  obtain ⟨hconstants, _hmarshal, _hstartInvariant⟩ :=
    marshalConstants_measured_internal tm x
  have hconstants' := hconstants.weakenSpace
    (marshalBaseSpace_le_spaceBound tm x.length)
  obtain ⟨looped, hloop, hloopInvariant, hloopEnvelope⟩ :=
    marshalLoop_measured_internal (tm := tm) x
  have hloop' := hloop.weakenSpace (marshalSpace_le_spaceBound tm x.length)
  have hcontrol : valueReg n ≤ marshalBound n x.length + 1 := by
    have hrange := (scratch_range_internal n).2.2.2.2.2.1.2
    have hbase := cellBase_le_marshalBaseBound n x.length
    simp [marshalBound] at *
    omega
  have hentries := capturedInput_entries_fit n x hcontrol
  have hnonempty := capturedInput_nonempty n x
  obtain ⟨repaired, repairSteps, hrepair, hrepairStore,
      hrepairEnvelope⟩ :=
    repairCaptured_measured_internal hentries hnonempty
      (hloopEnvelope.toMarshalEnvelope le_rfl) le_rfl
  have hrepair' : Structured.Internal.MeasuredRuns
      (repairCaptured n (capturedInput n x)) looped repaired repairSteps
      ((capturedInput n x).length *
        (27 * wordWidth tm (marshalBound n x.length)))
      (spaceBound tm (marshalBound n x.length)) := by
    simpa [wordWidth, spaceBound, Structured.Internal.envelopeSpace] using!
      hrepair
  subst repaired
  let final := Structured.Basic.execList (initializeConfigOps tm)
    (repairStore n (capturedInput n x) looped)
  obtain ⟨hinitialize, hinitializeEnvelope⟩ :=
    initializeConfigOps_measured_internal hrepairEnvelope
  have hrepresents := initializeStore_represents_internal tm x looped
    hloopInvariant
  have hrun := hconstants'.seq (hloop'.seq (hrepair'.seq hinitialize))
  refine ⟨final,
    (marshalConstants n).length +
      (marshalLoopSteps n x.length +
        (repairSteps + (initializeConfigOps tm).length)), ?_, ?_, ?_⟩
  · convert! hrun using 1
    simp [marshalLeafTimeBound, marshalBaseWidth,
      Structured.Internal.valueWidth, capturedInput,
      captureValues_eq_reverse_append]
    ring
  · simpa [final, initializeStore] using! hrepresents
  · simpa [final] using! hinitializeEnvelope

private theorem captureInput_measured_of_leaf {tm : TM n} (x : List Bool)
    (regs : List ℕ) (captured : List (ℕ × ℕ))
    {final : Structured.Store} {leafSteps leafCost : ℕ}
    (hbits : ∀ reg, reg ∈ regs →
      initRegs x reg = 0 ∨ initRegs x reg = 1)
    (hleaf : Structured.Internal.MeasuredRuns
      (marshalLeaf tm (captureValues (initRegs x) regs captured))
      (initRegs x) final leafSteps leafCost
      (spaceBound tm (marshalBound n x.length))) :
    ∃ steps,
      Structured.Internal.MeasuredRuns
        (captureInput tm regs captured) (initRegs x) final steps
        (3 * regs.length * wordWidth tm (marshalBound n x.length) + leafCost)
        (spaceBound tm (marshalBound n x.length)) := by
  induction regs generalizing captured with
  | nil =>
      exact ⟨leafSteps, by simpa [captureInput, captureValues] using! hleaf⟩
  | cons reg rest ih =>
      have hrestBits : ∀ candidate, candidate ∈ rest →
          initRegs x candidate = 0 ∨ initRegs x candidate = 1 := by
        intro candidate hmem
        exact hbits candidate (by simp [hmem])
      simp only [captureValues] at hleaf
      obtain ⟨restSteps, hrest⟩ := ih ((reg, initRegs x reg) :: captured)
        hrestBits hleaf
      have henvelope := initRegs_envelope_internal tm x
        (marshalBound n x.length) (by simp [marshalBound])
      rcases hbits reg (by simp) with hzero | hone
      · have hbranch := Structured.Internal.MeasuredRuns.ifZeroEnvelope
          (onNonzero := captureInput tm rest ((reg, 1) :: captured))
          hzero henvelope hrest
        have hweakened := hbranch.weakenCost (show
          wordWidth tm (marshalBound n x.length) +
              (3 * rest.length * wordWidth tm (marshalBound n x.length) +
                leafCost) ≤
            3 * (reg :: rest).length *
                wordWidth tm (marshalBound n x.length) + leafCost by
          simp only [List.length_cons]
          have hw : 1 ≤ wordWidth tm (marshalBound n x.length) := by
            simp [wordWidth]
          calc
            wordWidth tm (marshalBound n x.length) +
                (3 * rest.length * wordWidth tm (marshalBound n x.length) +
                  leafCost) ≤
              3 * wordWidth tm (marshalBound n x.length) +
                (3 * rest.length * wordWidth tm (marshalBound n x.length) +
                  leafCost) := Nat.add_le_add_right (by omega) _
            _ = 3 * (rest.length + 1) *
                wordWidth tm (marshalBound n x.length) + leafCost := by ring)
        exact ⟨restSteps + 1, by
          simpa [captureInput, hzero, spaceBound,
            Structured.Internal.envelopeSpace] using! hweakened⟩
      · have hnonzero : initRegs x reg ≠ 0 := by omega
        have hbranch := Structured.Internal.MeasuredRuns.ifNonzeroEnvelope
          (onZero := captureInput tm rest ((reg, 0) :: captured))
          hnonzero henvelope hrest
        refine ⟨restSteps + 2, ?_⟩
        convert! hbranch using 1
        all_goals simp [captureInput, hone, wordWidth,
          Structured.Internal.valueWidth]
        all_goals ring

/-- The full public-input marshaller has a concrete resource certificate and
hands the simulation core an exact sparse representation. -/
theorem marshalInput_measured_internal (tm : TM n) (x : List Bool) :
    ∃ final steps,
      Structured.Internal.MeasuredRuns (marshalInput tm) (initRegs x) final
        steps (marshalTimeBound tm x.length)
        (spaceBound tm (marshalBound n x.length)) ∧
      Represents tm (tm.initCfg x) final ∧
      StepEnvelope tm (marshalBound n x.length) final := by
  obtain ⟨final, leafSteps, hleaf, hrepresents, henvelope⟩ :=
    marshalLeaf_measured_internal tm x
  have hselected : Structured.Internal.MeasuredRuns
      (marshalLeaf tm
        (captureValues (initRegs x) (captureRegs n) []))
      (initRegs x) final leafSteps (marshalLeafTimeBound tm x.length)
      (spaceBound tm (marshalBound n x.length)) := by
    simpa [capturedInput] using! hleaf
  have hbits : ∀ reg, reg ∈ captureRegs n →
      initRegs x reg = 0 ∨ initRegs x reg = 1 := by
    intro reg hmem
    have hpositive := captureRegs_positive_internal n hmem
    have hbit := initRegs_bool_of_pos_internal x hpositive
    omega
  obtain ⟨steps, hrun⟩ := captureInput_measured_of_leaf x
    (captureRegs n) [] hbits hselected
  refine ⟨final, steps, ?_, hrepresents, henvelope⟩
  simpa [marshalInput, marshalTimeBound, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using! hrun

/-- End-to-end public-ABI execution with concrete time and space bounds. -/
theorem decisionProgram_measured_internal {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps,
      Structured.Internal.MeasuredRuns (decisionProgram tm) (initRegs x) final
        sourceSteps (decisionTimeBound tm x.length steps)
        (spaceBound tm (marshalBound n x.length + steps)) ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  obtain ⟨marshaled, marshalSteps, hmarshal, hrepresents,
      hmarshalEnvelope⟩ := marshalInput_measured_internal tm x
  have hbaseLe : marshalBound n x.length ≤
      marshalBound n x.length + steps := Nat.le_add_right _ _
  have hmarshal' := hmarshal.weakenSpace (spaceBound_mono tm hbaseLe)
  have hheads : HeadsBounded (tm.initCfg x) (marshalBound n x.length) := by
    intro tape
    simp only [tapeAt]
    split <;> simp [Tape.init]
  have hworkStart : ∀ i, ((tm.initCfg x).work i).cells 0 = Γ.start := by
    intro i
    simp [Tape.init]
  have houtputStart : (tm.initCfg x).output.cells 0 = Γ.start := by
    simp [Tape.init]
  have hlargeEnvelope := hmarshalEnvelope.monoBound hbaseLe
  obtain ⟨simulated, hsimulation, hhaltedRepresents,
      hsimulationEnvelope⟩ :=
    runUntilHalt_measured_internal hreach hhalted hrepresents hheads
      hworkStart houtputStart hlargeEnvelope
  have hsimulation' := hsimulation.weakenCost
    (runTimeBound_le_linear_internal tm (marshalBound n x.length) steps
      (tm.initCfg x))
  obtain ⟨hextract, _hextractEnvelope, hverdict⟩ :=
    extractVerdict_measured_internal hhaltedRepresents hsimulationEnvelope
  have hrun := hmarshal'.seq (hsimulation'.seq hextract)
  refine ⟨Structured.Basic.execList (extractVerdictOps n) simulated,
    marshalSteps +
      (runSteps tm steps (tm.initCfg x) + (extractVerdictOps n).length),
    ?_, hverdict⟩
  convert! hrun using 1
  simp [decisionTimeBound]
  ring

/-- Concrete compiled-RAM transfer of the end-to-end resource certificate. -/
theorem compiledDecision_resourceBound_internal {tm : TM n} {steps : ℕ}
    {x : List Bool} {halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg x) halted)
    (hhalted : tm.halted halted) :
    ∃ final sourceSteps cost space,
      Structured.Exec (decisionProgram tm) (initRegs x) final
        sourceSteps cost space ∧
      cost ≤ decisionTimeBound tm x.length steps ∧
      space ≤ spaceBound tm (marshalBound n x.length + steps) ∧
      run (compiledDecision tm) sourceSteps (initCfg x) =
        { pc := (decisionProgram tm).codeSize, regs := final } ∧
      Halted (compiledDecision tm)
        (run (compiledDecision tm) sourceSteps (initCfg x)) ∧
      logTimeUpto (compiledDecision tm) sourceSteps (initCfg x) = cost ∧
      spaceUpto (compiledDecision tm) sourceSteps (initCfg x) = space ∧
      final stateReg = symbolCode (halted.output.cells 1) - 1 := by
  obtain ⟨final, sourceSteps, hrun, hverdict⟩ :=
    decisionProgram_measured_internal hreach hhalted
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hrun
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, sourceSteps, cost, space, hexec, hcost, hspace, ?_, ?_, ?_,
    ?_, hverdict⟩
  · simpa [compiledDecision, initCfg] using! hcompiled.1
  · simpa [compiledDecision, initCfg] using!
      Structured.Exec.compile_halted hexec
  · simpa [compiledDecision, initCfg] using! hcompiled.2.1
  · simpa [compiledDecision, initCfg] using! hcompiled.2.2

end Sparse

end TMConfig

end RAM

end Complexity
