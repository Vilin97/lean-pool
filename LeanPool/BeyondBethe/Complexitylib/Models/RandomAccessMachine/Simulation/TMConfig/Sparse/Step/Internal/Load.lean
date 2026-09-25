/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal.Layout

/-!
# Loading sparse TM states and head symbols -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


private theorem execList_append (first second : List Structured.Basic)
    (store : Structured.Store) :
    Structured.Basic.execList (first ++ second) store =
      Structured.Basic.execList second (Structured.Basic.execList first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons op rest ih => simp [Structured.Basic.execList, ih]

private theorem loadTapeOps_apply_of_ne (n : ℕ) (tape : Fin (n + 2))
    (store : Structured.Store) (reg : ℕ)
    (hvalue : reg ≠ valueReg n) (haddress : reg ≠ addressReg n)
    (hsymbol : reg ≠ symbolReg n tape) :
    Structured.Basic.execList (loadTapeOps n tape) store reg = store reg := by
  simp [loadTapeOps, addressOps, Structured.Basic.execList,
    Structured.Basic.exec, Function.update_of_ne hvalue,
    Function.update_of_ne haddress, Function.update_of_ne hsymbol]

private theorem symbolReg_injective (n : ℕ) :
    Function.Injective (symbolReg n) := by
  intro first second heq
  apply Fin.ext
  simp [symbolReg] at heq
  omega

private structure LoadedPrefix (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (processed : List (Fin (n + 2))) (store : Structured.Store) : Prop where
  represents : Represents tm cfg store
  zero : store (zeroReg n) = 0
  one : store (oneReg n) = 1
  tapeCount : store (tapeCountReg n) = n + 2
  state : store (stateScratchReg n) = stateCode tm cfg.state
  symbols : ∀ tape, tape ∈ processed →
    store (symbolReg n tape) = symbolCode (readSymbols cfg tape)

private theorem setup_loadedPrefix {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    {store : Structured.Store} (hrepresents : Represents tm cfg store) :
    LoadedPrefix tm cfg []
      (Structured.Basic.execList (setupOps n) store) := by
  let first := (Structured.Basic.imm (zeroReg n) 0).exec store
  let second := (Structured.Basic.imm (oneReg n) 1).exec first
  let third := (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec second
  let final := (Structured.Basic.add (stateScratchReg n) stateReg
    (zeroReg n)).exec third
  have hrange := scratch_range_internal n
  have hfirstRep : Represents tm cfg first := by
    exact hrepresents.update_control_internal hrange.1.1 hrange.1.2
  have hsecondRep : Represents tm cfg second := by
    exact hfirstRep.update_control_internal hrange.2.1.1 hrange.2.1.2
  have hthirdRep : Represents tm cfg third := by
    exact hsecondRep.update_control_internal hrange.2.2.1.1 hrange.2.2.1.2
  have hfinalRep : Represents tm cfg final := by
    exact hthirdRep.update_control_internal
      hrange.2.2.2.1.1 hrange.2.2.2.1.2
  have hzero : final (zeroReg n) = 0 := by
    simp [final, third, second, first, Structured.Basic.exec, zeroReg, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hone : final (oneReg n) = 1 := by
    simp [final, third, second, first, Structured.Basic.exec, zeroReg, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hcount : final (tapeCountReg n) = n + 2 := by
    simp [final, third, second, first, Structured.Basic.exec, zeroReg, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hstateStore : store stateReg = stateCode tm cfg.state := by
    have hstate := hrepresents (Sum.inl ⟨0, by omega⟩)
    change store stateReg = stateCode tm cfg.state at hstate
    exact hstate
  have hstate : final (stateScratchReg n) = stateCode tm cfg.state := by
    simp only [final, Structured.Basic.exec, Function.update_self]
    have hthirdState : third stateReg = store stateReg := by
      simp [third, second, first, Structured.Basic.exec, stateReg, zeroReg,
        oneReg, tapeCountReg, Function.update_of_ne]
    have hthirdZero : third (zeroReg n) = 0 := by
      simp [third, second, first, Structured.Basic.exec, zeroReg, oneReg,
        tapeCountReg, Function.update_of_ne]
    rw [hthirdState, hthirdZero, hstateStore, Nat.add_zero]
  simpa [setupOps, first, second, third, final] using!
    LoadedPrefix.mk hfinalRep hzero hone hcount hstate (by simp)

private theorem loadTape_loadedPrefix {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {processed : List (Fin (n + 2))}
    {store : Structured.Store} (hloaded : LoadedPrefix tm cfg processed store)
    (tape : Fin (n + 2)) :
    LoadedPrefix tm cfg (tape :: processed)
      (Structured.Basic.execList (loadTapeOps n tape) store) := by
  have hzeroValue : zeroReg n ≠ valueReg n := by simp [zeroReg, valueReg]
  have hzeroAddress : zeroReg n ≠ addressReg n := by simp [zeroReg, addressReg]
  have hzeroSymbol : zeroReg n ≠ symbolReg n tape := by
    simp [zeroReg, symbolReg]
    omega
  have honeValue : oneReg n ≠ valueReg n := by simp [oneReg, valueReg]
  have honeAddress : oneReg n ≠ addressReg n := by simp [oneReg, addressReg]
  have honeSymbol : oneReg n ≠ symbolReg n tape := by
    simp [oneReg, symbolReg]
    omega
  have hcountValue : tapeCountReg n ≠ valueReg n := by simp [tapeCountReg, valueReg]
  have hcountAddress : tapeCountReg n ≠ addressReg n := by
    simp [tapeCountReg, addressReg]
  have hcountSymbol : tapeCountReg n ≠ symbolReg n tape := by
    simp [tapeCountReg, symbolReg]
    omega
  have hstateValue : stateScratchReg n ≠ valueReg n := by
    simp [stateScratchReg, valueReg]
  have hstateAddress : stateScratchReg n ≠ addressReg n := by
    simp [stateScratchReg, addressReg]
  have hstateSymbol : stateScratchReg n ≠ symbolReg n tape := by
    simp [stateScratchReg, symbolReg]
    omega
  refine ⟨loadTapeOps_represents_internal hloaded.represents tape,
    loadTapeOps_apply_of_ne n tape store (zeroReg n) hzeroValue hzeroAddress
      hzeroSymbol ▸ hloaded.zero,
    loadTapeOps_apply_of_ne n tape store (oneReg n) honeValue honeAddress
      honeSymbol ▸ hloaded.one,
    loadTapeOps_apply_of_ne n tape store (tapeCountReg n) hcountValue
      hcountAddress hcountSymbol ▸ hloaded.tapeCount,
    loadTapeOps_apply_of_ne n tape store (stateScratchReg n) hstateValue
      hstateAddress hstateSymbol ▸ hloaded.state, ?_⟩
  intro candidate hmem
  rcases List.mem_cons.mp hmem with heq | hprocessed
  · subst candidate
    exact loadTapeOps_symbol_internal hloaded.represents tape hloaded.tapeCount
  · by_cases heq : candidate = tape
    · subst candidate
      exact loadTapeOps_symbol_internal hloaded.represents tape hloaded.tapeCount
    · rw [loadTapeOps_apply_of_ne n tape store (symbolReg n candidate)]
      · exact hloaded.symbols candidate hprocessed
      · simp [symbolReg, valueReg]
        omega
      · simp [symbolReg, addressReg]
        omega
      · exact fun hregs => heq (symbolReg_injective n hregs)

private theorem loadTapes_loadedPrefix {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} (tapes processed : List (Fin (n + 2)))
    {store : Structured.Store} (hloaded : LoadedPrefix tm cfg processed store) :
    LoadedPrefix tm cfg (tapes.reverse ++ processed)
      (Structured.Basic.execList (tapes.flatMap (loadTapeOps n)) store) := by
  induction tapes generalizing processed store with
  | nil => simpa using! hloaded
  | cons tape rest ih =>
      have hnext := loadTape_loadedPrefix hloaded tape
      have hfinal := ih (processed := tape :: processed) hnext
      simpa [List.flatMap_cons, Structured.Basic.execList, execList_append,
        List.reverse_cons, List.append_assoc] using hfinal

theorem loadOps_loaded_internal {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    {store : Structured.Store} (hrepresents : Represents tm cfg store) :
    let final := Structured.Basic.execList (loadOps n) store
    Represents tm cfg final ∧
      final (zeroReg n) = 0 ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 ∧
      final (stateScratchReg n) = stateCode tm cfg.state ∧
      ∀ tape, final (symbolReg n tape) = symbolCode (readSymbols cfg tape) := by
  let setup := Structured.Basic.execList (setupOps n) store
  have hsetup := setup_loadedPrefix hrepresents
  have hloaded := loadTapes_loadedPrefix (List.finRange (n + 2)) [] hsetup
  rw [loadOps, execList_append]
  exact ⟨hloaded.represents, hloaded.zero, hloaded.one, hloaded.tapeCount,
    hloaded.state, fun tape => hloaded.symbols tape (by simp)⟩

end Sparse

end TMConfig

end RAM

end Complexity
