/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Layout
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources

/-!
# Loading represented TM states and head symbols -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Step


private theorem execList_append (first second : List Structured.Basic)
    (store : Structured.Store) :
    Structured.Basic.execList (first ++ second) store =
      Structured.Basic.execList second (Structured.Basic.execList first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons op rest ih =>
      simp [Structured.Basic.execList, ih]

private theorem loadTapeOps_apply_of_ne (n bound : ℕ)
    (tape : Fin (n + 2)) (store : Structured.Store) (reg : ℕ)
    (haddress : reg ≠ addressReg n bound)
    (hsymbol : reg ≠ symbolReg n bound tape) :
    Structured.Basic.execList (loadTapeOps n bound tape) store reg = store reg := by
  simp [loadTapeOps, Structured.Basic.execList, Structured.Basic.exec,
    Function.update_of_ne haddress, Function.update_of_ne hsymbol]

private theorem symbolReg_injective (n bound : ℕ) :
    Function.Injective (symbolReg n bound) := by
  intro first second heq
  apply Fin.ext
  simp [symbolReg] at heq
  omega

/-- Semantic facts established for a processed prefix of named tapes. -/
private structure LoadedPrefix (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (processed : List (Fin (n + 2)))
    (store : Structured.Store) : Prop where
  represents : Represents tm bound cfg store
  zero : store (zeroReg n bound) = 0
  one : store (oneReg n bound) = 1
  state : store (stateScratchReg n bound) = stateCode tm cfg.state
  symbols : ∀ tape, tape ∈ processed →
    store (symbolReg n bound tape) = symbolCode (readSymbols cfg tape)

private theorem setup_loadedPrefix {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store) :
    LoadedPrefix tm bound cfg []
      (Structured.Basic.execList (setupOps n bound) store) := by
  have hstate := hrepresents (stateField (n := n) (bound := bound))
  rw [fieldReg_state_internal] at hstate
  change store 0 = stateCode tm cfg.state at hstate
  let first := (Structured.Basic.imm (zeroReg n bound) 0).exec store
  let second := (Structured.Basic.imm (oneReg n bound) 1).exec first
  let final := (Structured.Basic.add (stateScratchReg n bound) 0
    (zeroReg n bound)).exec second
  have hzeroOne : zeroReg n bound ≠ oneReg n bound := by
    simp [zeroReg, oneReg]
  have hzeroState : zeroReg n bound ≠ stateScratchReg n bound := by
    simp [zeroReg, stateScratchReg]
  have honeState : oneReg n bound ≠ stateScratchReg n bound := by
    simp [oneReg, stateScratchReg]
  have hzeroNonzero : zeroReg n bound ≠ 0 := by
    simp [zeroReg, scratchBase, registerCount]
  have honeNonzero : oneReg n bound ≠ 0 := by
    simp [oneReg, scratchBase, registerCount]
  have hrepFirst : Represents tm bound cfg first := by
    exact hrepresents.update_outside_internal (zeroReg_ge_internal n bound)
  have hrepSecond : Represents tm bound cfg second := by
    exact hrepFirst.update_outside_internal (oneReg_ge_internal n bound)
  have hrepFinal : Represents tm bound cfg final := by
    exact hrepSecond.update_outside_internal (stateScratchReg_ge_internal n bound)
  have hzeroFinal : final (zeroReg n bound) = 0 := by
    simp [final, second, first, Structured.Basic.exec,
      Function.update_of_ne hzeroState,
      Function.update_of_ne hzeroOne]
  have honeFinal : final (oneReg n bound) = 1 := by
    simp [final, second, first, Structured.Basic.exec,
      Function.update_of_ne honeState]
  have hstateFinal : final (stateScratchReg n bound) = stateCode tm cfg.state := by
    have hsecondSource : second 0 = store 0 := by
      simp [second, first, Structured.Basic.exec,
        Function.update_of_ne (Ne.symm hzeroNonzero),
        Function.update_of_ne (Ne.symm honeNonzero)]
    have hsecondZero : second (zeroReg n bound) = 0 := by
      simp [second, first, Structured.Basic.exec,
        Function.update_of_ne hzeroOne]
    simp only [final, Structured.Basic.exec, Function.update_self]
    rw [hsecondSource, hsecondZero, hstate]
    rfl
  simpa [setupOps, Structured.Basic.execList, first, second, final] using
    LoadedPrefix.mk hrepFinal hzeroFinal honeFinal hstateFinal (by simp)

private theorem loadTape_loadedPrefix {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {processed : List (Fin (n + 2))}
    {store : Structured.Store} (hloaded : LoadedPrefix tm bound cfg processed store)
    (tape : Fin (n + 2))
    (hhead : (tapeAt cfg tape).head ≤ bound) :
    LoadedPrefix tm bound cfg (tape :: processed)
      (Structured.Basic.execList (loadTapeOps n bound tape) store) := by
  let final := Structured.Basic.execList (loadTapeOps n bound tape) store
  have haddressZero : zeroReg n bound ≠ addressReg n bound := by
    simp [zeroReg, addressReg]
  have hsymbolZero : zeroReg n bound ≠ symbolReg n bound tape := by
    simp [zeroReg, symbolReg]
    omega
  have haddressOne : oneReg n bound ≠ addressReg n bound := by
    simp [oneReg, addressReg]
  have hsymbolOne : oneReg n bound ≠ symbolReg n bound tape := by
    simp [oneReg, symbolReg]
    omega
  have haddressState : stateScratchReg n bound ≠ addressReg n bound := by
    simp [stateScratchReg, addressReg]
  have hsymbolState : stateScratchReg n bound ≠ symbolReg n bound tape := by
    simp [stateScratchReg, symbolReg]
    omega
  refine ⟨loadTapeOps_represents_internal hloaded.represents tape,
    loadTapeOps_apply_of_ne n bound tape store (zeroReg n bound)
      haddressZero hsymbolZero ▸ hloaded.zero,
    loadTapeOps_apply_of_ne n bound tape store (oneReg n bound)
      haddressOne hsymbolOne ▸ hloaded.one,
    loadTapeOps_apply_of_ne n bound tape store (stateScratchReg n bound)
      haddressState hsymbolState ▸ hloaded.state, ?_⟩
  intro candidate hmem
  rcases List.mem_cons.mp hmem with heq | hprocessed
  · subst candidate
    exact loadTapeOps_symbol_internal hloaded.represents hhead
  · by_cases heq : candidate = tape
    · subst candidate
      exact loadTapeOps_symbol_internal hloaded.represents hhead
    · rw [loadTapeOps_apply_of_ne n bound tape store (symbolReg n bound candidate)]
      · exact hloaded.symbols candidate hprocessed
      · simp [symbolReg, addressReg]
        omega
      · exact fun hregs => heq (symbolReg_injective n bound hregs)

private theorem loadTapes_loadedPrefix {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} (tapes processed : List (Fin (n + 2)))
    {store : Structured.Store} (hloaded : LoadedPrefix tm bound cfg processed store)
    (hheads : HeadsBounded cfg bound) :
    LoadedPrefix tm bound cfg (tapes.reverse ++ processed)
      (Structured.Basic.execList (tapes.flatMap (loadTapeOps n bound)) store) := by
  induction tapes generalizing processed store with
  | nil => simpa using! hloaded
  | cons tape rest ih =>
      have hnext := loadTape_loadedPrefix hloaded tape (hheads tape)
      have hfinal := ih (processed := tape :: processed) hnext
      simpa [List.flatMap_cons, Structured.Basic.execList, execList_append,
        List.reverse_cons, List.append_assoc] using hfinal

theorem loadOps_loaded_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound) :
    let final := Structured.Basic.execList (loadOps n bound) store
    Represents tm bound cfg final ∧
      final (zeroReg n bound) = 0 ∧
      final (oneReg n bound) = 1 ∧
      final (stateScratchReg n bound) = stateCode tm cfg.state ∧
      ∀ tape, final (symbolReg n bound tape) =
        symbolCode (readSymbols cfg tape) := by
  let setup := Structured.Basic.execList (setupOps n bound) store
  have hsetup := setup_loadedPrefix hrepresents
  have hloaded := loadTapes_loadedPrefix (List.finRange (n + 2)) [] hsetup
    hheads
  rw [loadOps, execList_append]
  exact ⟨hloaded.represents, hloaded.zero, hloaded.one, hloaded.state,
    fun tape => hloaded.symbols tape (by simp)⟩

private theorem registerCount_lt_registerLimit (n bound : ℕ) :
    registerCount n bound < registerLimit n bound := by
  simp [registerLimit, scratchBase]
  omega

private theorem registerLimit_le_wordBound (tm : TM n) (bound : ℕ) :
    registerLimit n bound ≤ wordBound tm bound :=
  le_max_left _ _

private theorem setupOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    Structured.Internal.Basic.EnvelopeChain (registerLimit n bound)
      (wordBound tm bound) (setupOps n bound) store := by
  let first := (Structured.Basic.imm (zeroReg n bound) 0).exec store
  let second := (Structured.Basic.imm (oneReg n bound) 1).exec first
  let final := (Structured.Basic.add (stateScratchReg n bound) 0
    (zeroReg n bound)).exec second
  have hscratch := scratch_lt_registerLimit_internal n bound
  have hfirst : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) first := by
    apply henvelope.execBasic
    · exact hscratch.1
    · simp [Structured.Internal.Basic.writeValue]
  have honeValue : 1 ≤ wordBound tm bound := by
    have hpositive : 1 ≤ registerLimit n bound := by
      simp [registerLimit, scratchBase, registerCount]
    exact le_trans hpositive (registerLimit_le_wordBound tm bound)
  have hsecond : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) second := by
    apply hfirst.execBasic
    · exact hscratch.2.1
    · simpa [Structured.Internal.Basic.writeValue] using honeValue
  have hstateStore : store 0 = stateCode tm cfg.state := by
    have hstate := hrepresents (stateField (n := n) (bound := bound))
    simpa [fieldReg_state_internal, fieldValue] using! hstate
  have hsecondSource : second 0 = store 0 := by
    simp [second, first, Structured.Basic.exec, zeroReg, oneReg, scratchBase,
      registerCount, Function.update_of_ne]
  have hsecondZero : second (zeroReg n bound) = 0 := by
    simp [second, first, Structured.Basic.exec, zeroReg, oneReg,
      Function.update_of_ne]
  have hstateBound : stateCode tm cfg.state ≤ wordBound tm bound := by
    exact le_trans (Nat.le_of_lt (stateCode_lt_internal tm cfg.state))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hfinal : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) final := by
    apply hsecond.execBasic
    · exact hscratch.2.2.1
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hsecondSource, hsecondZero, hstateStore, Nat.add_zero]
      exact hstateBound
  simpa [setupOps, first, second, final] using!
    And.intro henvelope (And.intro hfirst (And.intro hsecond hfinal))

private theorem loadTapeOps_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (tape : Fin (n + 2)) (hhead : (tapeAt cfg tape).head ≤ bound)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    Structured.Internal.Basic.EnvelopeChain (registerLimit n bound)
      (wordBound tm bound) (loadTapeOps n bound tape) store := by
  let first :=
    (Structured.Basic.imm (addressReg n bound) (cellBase n bound tape)).exec store
  let addressed :=
    (Structured.Basic.add (addressReg n bound) (addressReg n bound)
      (headReg tape)).exec first
  let final :=
    (Structured.Basic.load (symbolReg n bound tape) (addressReg n bound)).exec addressed
  have hscratch := scratch_lt_registerLimit_internal n bound
  have hbaseLt : cellBase n bound tape < registerCount n bound := by
    have hfield := fieldReg_lt_internal
      (cellField tape (⟨0, by omega⟩ : Fin (bound + 1)))
    rw [← cellBase_add_eq_fieldReg_internal] at hfield
    simpa using hfield
  have hbaseBound : cellBase n bound tape ≤ wordBound tm bound := by
    exact le_trans (Nat.le_of_lt hbaseLt)
      (le_trans (Nat.le_of_lt (registerCount_lt_registerLimit n bound))
        (registerLimit_le_wordBound tm bound))
  have hfirst : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) first := by
    apply henvelope.execBasic
    · exact hscratch.2.2.2.1
    · simpa [Structured.Internal.Basic.writeValue] using hbaseBound
  have hstoreHead : store (headReg tape) = (tapeAt cfg tape).head := by
    have hvalue := hrepresents (headField (bound := bound) tape)
    rwa [← headReg_eq_fieldReg_internal] at hvalue
  have hfirstAddress : first (addressReg n bound) = cellBase n bound tape := by
    simp [first, Structured.Basic.exec]
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    have hne : headReg tape ≠ addressReg n bound := by
      intro heq
      have hheadReg := fieldReg_lt_internal (headField (bound := bound) tape)
      rw [← headReg_eq_fieldReg_internal] at hheadReg
      have haddress := addressReg_ge_internal n bound
      omega
    simp [first, Structured.Basic.exec, Function.update_of_ne hne]
  let position : Fin (bound + 1) := ⟨(tapeAt cfg tape).head, by omega⟩
  have haddressedLt :
      cellBase n bound tape + (tapeAt cfg tape).head < registerCount n bound := by
    change cellBase n bound tape + position.val < registerCount n bound
    rw [cellBase_add_eq_fieldReg_internal]
    exact fieldReg_lt_internal _
  have haddressedBound :
      cellBase n bound tape + (tapeAt cfg tape).head ≤ wordBound tm bound := by
    exact le_trans (Nat.le_of_lt haddressedLt)
      (le_trans (Nat.le_of_lt (registerCount_lt_registerLimit n bound))
        (registerLimit_le_wordBound tm bound))
  have haddressed : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) addressed := by
    apply hfirst.execBasic
    · exact hscratch.2.2.2.1
    · simp only [Structured.Internal.Basic.writeValue]
      rw [hfirstAddress, hfirstHead, hstoreHead]
      exact haddressedBound
  have hfinal : Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) final := by
    apply haddressed.execBasic
    · exact hscratch.2.2.2.2.2 tape
    · exact haddressed.value_le (addressed (addressReg n bound))
  simpa [loadTapeOps, first, addressed, final] using!
    And.intro henvelope (And.intro hfirst (And.intro haddressed hfinal))

private theorem loadTapes_envelopeChain {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} (tapes : List (Fin (n + 2)))
    {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    Structured.Internal.Basic.EnvelopeChain (registerLimit n bound)
      (wordBound tm bound) (tapes.flatMap (loadTapeOps n bound)) store := by
  induction tapes generalizing store with
  | nil => exact henvelope
  | cons tape rest ih =>
      have hfirst := loadTapeOps_envelopeChain hrepresents tape (hheads tape) henvelope
      have hfirstEnvelope := hfirst.final
      have hfirstRepresents := loadTapeOps_represents_internal hrepresents tape
      have hrest := ih hfirstRepresents hfirstEnvelope
      simpa [List.flatMap_cons] using hfirst.append hrest

theorem loadOps_measured_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store) :
    let final := Structured.Basic.execList (loadOps n bound) store
    Structured.Internal.MeasuredRuns (.basics (loadOps n bound)) store final
      (loadOps n bound).length
      (4 * (loadOps n bound).length * wordWidth tm bound)
      (spaceBound tm bound) ∧
    Structured.Internal.StoreEnvelope (registerLimit n bound)
      (wordBound tm bound) final := by
  have hsetup := setupOps_envelopeChain hrepresents henvelope
  have hsetupRepresents := (setup_loadedPrefix hrepresents).represents
  have htapes := loadTapes_envelopeChain (List.finRange (n + 2))
    hsetupRepresents hheads hsetup.final
  have hchain : Structured.Internal.Basic.EnvelopeChain (registerLimit n bound)
      (wordBound tm bound) (loadOps n bound) store := by
    simpa [loadOps] using hsetup.append htapes
  have hmeasured := Structured.Internal.MeasuredRuns.basicsEnvelopeChain
    (loadOps n bound) store hchain
  simpa [wordWidth, spaceBound, Structured.Internal.valueWidth,
    Structured.Internal.envelopeSpace] using hmeasured

end Step

end TMConfig

end RAM

end Complexity
