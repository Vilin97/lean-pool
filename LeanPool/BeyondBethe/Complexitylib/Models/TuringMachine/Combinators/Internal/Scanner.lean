/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Correctness of the generic finite-state scanner

Proofs that `TM.scannerTM` correctly implements a left-to-right fold with
`|x| + 2`-step running time.

## Main results

- `TM.scannerTM_reachesIn` — the scanner halts in `|x| + 2` steps on every
  input `x`, writing `finalOutput (x.foldl scanStep s₀)` to output cell 1.
- `TM.scannerTM_decidesInTime` — bridge to `DecidesInTime` for any language
  characterized by `x ∈ L ↔ finalOutput (x.foldl scanStep s₀) = Γw.one`.
-/


public section

namespace Complexity

namespace TM

variable {S : Type} [DecidableEq S] [Fintype S]

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: from `.start` with both input and output heads at cell 0 on `▷`,
    the machine enters `.scan s₀` with both heads advanced to cell 1.
    Tape cell contents are preserved (writes at cell 0 are no-ops). -/
private theorem scannerTM_step_start
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw)
    (c : Cfg 0 (scannerTM s₀ scanStep finalOutput).Q)
    (hst : c.state = ScannerPhase.start)
    (hih : c.input.head = 0) (hoh : c.output.head = 0) :
    ∃ c', (scannerTM s₀ scanStep finalOutput).step c = some c' ∧
      c'.state = ScannerPhase.scan s₀ ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, scannerTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hih]
  · rfl
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]

/-- Scan step: from `.scan s` reading a non-blank input symbol, advance
    input one cell, transition scan state via `scanStep s (decide iHead = Γ.one)`.
    Output and work tapes are preserved. -/
private theorem scannerTM_step_scan
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw)
    (c : Cfg 0 (scannerTM s₀ scanStep finalOutput).Q) (s : S)
    (hst : c.state = ScannerPhase.scan s)
    (hi_nb : c.input.read ≠ Γ.blank)
    (ho_head : c.output.head = 1)
    (ho_cell1_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (scannerTM s₀ scanStep finalOutput).step c = some c' ∧
      c'.state = ScannerPhase.scan (scanStep s (decide (c.input.read = Γ.one))) ∧
      c'.input.head = c.input.head + 1 ∧ c'.input.cells = c.input.cells ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, scannerTM, reduceCtorEq, ↓reduceIte, if_neg hi_nb]
  have hne : c.output.read ≠ Γ.start := by
    simp only [Tape.read, ho_head]; exact ho_cell1_nb
  have ho_move : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, hne]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp [Tape.move]
  · simp [Tape.writeAndMove, ho_move, Tape.move, Tape.write_head, ho_head]
  · exact tape_readBackWrite_preserves c.output _ (Or.inr hne)

/-- Halt step: from `.scan s` reading blank (end of input), emit
    `finalOutput s` at output cell 1 and enter `.done`. -/
private theorem scannerTM_step_halt
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw)
    (c : Cfg 0 (scannerTM s₀ scanStep finalOutput).Q) (s : S)
    (hst : c.state = ScannerPhase.scan s)
    (hi_blank : c.input.read = Γ.blank)
    (ho_head : c.output.head = 1)
    (ho_cell1_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (scannerTM s₀ scanStep finalOutput).step c = some c' ∧
      (scannerTM s₀ scanStep finalOutput).halted c' ∧
      c'.output.cells 1 = (finalOutput s).toΓ := by
  simp only [TM.step, hst, scannerTM, reduceCtorEq, ↓reduceIte, if_pos hi_blank]
  refine ⟨_, rfl, rfl, ?_⟩
  have hne : c.output.read ≠ Γ.start := by
    simp only [Tape.read, ho_head]; exact ho_cell1_nb
  have ho_move : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, hne]
  have h1 : (1 : ℕ) ≠ 0 := by omega
  simp [Tape.writeAndMove, ho_move, Tape.move, Tape.write, ho_head, h1]

-- ════════════════════════════════════════════════════════════════════════
-- Scan loop
-- ════════════════════════════════════════════════════════════════════════

/-- **Scan invariant**: from a scan-state configuration `.scan s` with
    input head at cell `k + 1` and `m` input bits remaining (`|x| = k + m`),
    the scanner halts in `m + 1` steps with output cell 1 set to the fold
    of `scanStep` over the remaining bits `x.drop k`, starting from `s`. -/
private theorem scannerTM_scan
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw)
    (x : List Bool) (m k : ℕ) (hlen : x.length = k + m) (s : S)
    (c : Cfg 0 (scannerTM s₀ scanStep finalOutput).Q)
    (hst : c.state = ScannerPhase.scan s)
    (hic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hih : c.input.head = k + 1)
    (hoh : c.output.head = 1)
    (hoc : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (scannerTM s₀ scanStep finalOutput).reachesIn (m + 1) c c' ∧
      (scannerTM s₀ scanStep finalOutput).halted c' ∧
      c'.output.cells 1 = (finalOutput ((x.drop k).foldl scanStep s)).toΓ := by
  induction m generalizing k s c with
  | zero =>
    -- k = x.length: reading blank, apply halt step.
    have hk : k = x.length := by omega
    have hi_blank : c.input.read = Γ.blank := by
      simp only [Tape.read, hih, hic]
      show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = Γ.blank
      simp [Tape.init, hk]
    obtain ⟨c', hstep, hhalt, hout⟩ :=
      scannerTM_step_halt s₀ scanStep finalOutput c s hst hi_blank hoh hoc
    refine ⟨c', .step hstep .zero, hhalt, ?_⟩
    have : x.drop k = [] := by simp [hk]
    rw [hout, this, List.foldl_nil]
  | succ m ih =>
    -- k < x.length: read bit, scan step, IH.
    have hk_lt : k < x.length := by omega
    have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
    have hkmap : k < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hk_lt
    -- The symbol under the input head is `Γ.ofBool x[k]`.
    have hi_read : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
      simp only [Tape.read, hih, hic]
      show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = _
      simp only [Tape.init, show k + 1 ≠ 0 from by omega, ↓reduceIte,
        Nat.add_sub_cancel, List.getElem?_eq_getElem hkmap, Option.getD_some,
        List.getElem_map]
    have hi_nb : c.input.read ≠ Γ.blank := by
      rw [hi_read]; cases x[k]'hk_lt <;> simp [Γ.ofBool]
    -- Apply scan step.
    obtain ⟨c₁, hstep, hst₁, hih₁, hic₁, hoh₁, hoc₁⟩ :=
      scannerTM_step_scan s₀ scanStep finalOutput c s hst hi_nb hoh hoc
    -- Bit decoding: `decide (Γ.ofBool b = Γ.one) = b`.
    have hbit : decide (c.input.read = Γ.one) = x[k]'hk_lt := by
      rw [hi_read]; cases x[k]'hk_lt <;> simp [Γ.ofBool]
    rw [hbit] at hst₁
    -- Apply IH at k + 1 with state `scanStep s x[k]`.
    have hlen' : x.length = (k + 1) + m := by omega
    have hic₁' : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
      rw [hic₁]; exact hic
    have hih₁' : c₁.input.head = (k + 1) + 1 := by
      rw [hih₁, hih]
    have hoc₁' : c₁.output.cells 1 ≠ Γ.start := by
      rw [hoc₁]; exact hoc
    obtain ⟨c', hreach, hhalt, hout⟩ :=
      ih (k + 1) hlen' (scanStep s (x[k]'hk_lt)) c₁ hst₁ hic₁' hih₁' hoh₁ hoc₁'
    refine ⟨c', .step hstep hreach, hhalt, ?_⟩
    -- `(x.drop k).foldl scanStep s = (x.drop (k+1)).foldl scanStep (scanStep s x[k])`.
    have hdrop : x.drop k = (x[k]'hk_lt) :: x.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hout, hdrop, List.foldl_cons]

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **`scannerTM` halts in `|x| + 2` steps and emits the fold result.**

    Output cell 1 is set to `finalOutput (x.foldl scanStep s₀)`, and the
    machine reaches a halted configuration in exactly `|x| + 2` steps on
    every input. -/
theorem scannerTM_reachesIn
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw) (x : List Bool) :
    ∃ c', (scannerTM s₀ scanStep finalOutput).reachesIn (x.length + 2)
            ((scannerTM s₀ scanStep finalOutput).initCfg x) c' ∧
      (scannerTM s₀ scanStep finalOutput).halted c' ∧
      c'.output.cells 1 = (finalOutput (x.foldl scanStep s₀)).toΓ := by
  -- Step 1: start → scan s₀.
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hoh1, hoc1⟩ :=
    scannerTM_step_start s₀ scanStep finalOutput
      ((scannerTM s₀ scanStep finalOutput).initCfg x) rfl rfl rfl
  -- Apply scan lemma from k = 0 with m = |x|.
  have hic1' : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells := hic1
  have hih1' : c₁.input.head = 0 + 1 := by simpa using hih1
  have hoc1' : c₁.output.cells 1 ≠ Γ.start := by
    rw [hoc1]; simp [Tape.init]
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    scannerTM_scan s₀ scanStep finalOutput x x.length 0 (by omega) s₀ c₁
      hst1 hic1' hih1' hoh1 hoc1'
  refine ⟨c', ?_, hhalt, ?_⟩
  · exact .step hstep1 hreach
  · simpa using hout

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- **Bridge to `DecidesInTime`**. Whenever a language `L` is characterized
    by a decision predicate `accept : S → Bool` applied to the fold, the
    scanner with finalOutput `fun s => if accept s then .one else .zero`
    decides `L` in time `n + 2`. -/
theorem scannerTM_decidesInTime
    (s₀ : S) (scanStep : S → Bool → S) (accept : S → Bool)
    {L : Language}
    (hL : ∀ x, x ∈ L ↔ accept (x.foldl scanStep s₀) = true) :
    TM.DecidesInTime
      (scannerTM s₀ scanStep (fun s => if accept s then .one else .zero))
      L (fun n => n + 2) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    scannerTM_reachesIn s₀ scanStep (fun s => if accept s then .one else .zero) x
  refine ⟨c', x.length + 2, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout, if_pos ((hL x).mp hxL)]; rfl
  · intro hxnL
    rw [hout]
    have hacc : accept (x.foldl scanStep s₀) = false := by
      rcases h : accept (x.foldl scanStep s₀) with _ | _
      · rfl
      · exact absurd ((hL x).mpr h) hxnL
    rw [if_neg (by simp [hacc])]; rfl

end TM

end Complexity
