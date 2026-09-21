/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch

/-!
# One bounded sparse-entry scan iteration — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem readableEntryMatch_to_hit
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork iterationWork matchedWork : Fin n → Tape)
    (hready : EntryScanReady tapes (Entry.encode entry ++ rest) queryBits
      initialWork iterationWork)
    (hmatch : ReadableEntryMatch tapes entry rest queryBits iterationWork matchedWork)
    (heq : entry.1.bits = queryBits) :
    EntryScanHit tapes entry rest queryBits initialWork matchedWork := by
  refine ⟨heq, hmatch.source, hmatch.value, hmatch.valueStart,
    hmatch.query, hmatch.queryStart, ?_, hmatch.resultStart,
    hmatch.parked, ?_, ⟨iterationWork, hmatch⟩⟩
  · simpa [heq] using hmatch.result
  · intro i hsource haddress hvalue haddressCounter haddressWidth
      hvalueCounter hvalueWidth hquery hresult
    exact (hmatch.frame i hsource haddress hvalue haddressCounter
      haddressWidth hvalueCounter hvalueWidth hquery hresult).trans
      (hready.frame i hsource haddress hvalue haddressCounter
        haddressWidth hvalueCounter hvalueWidth hquery hresult)

private theorem entryScanReady_reframe
    (tapes : EntryMatchTapes n) (consumed rest queryBits : List Bool)
    (initialWork iterationWork finalWork : Fin n → Tape)
    (hready : EntryScanReady tapes consumed queryBits initialWork iterationWork)
    (hfinal : EntryScanReady tapes rest queryBits iterationWork finalWork) :
    EntryScanReady tapes rest queryBits initialWork finalWork := by
  refine ⟨hfinal.source, hfinal.address, hfinal.addressStart,
    hfinal.value, hfinal.valueStart, hfinal.addressCounter,
    hfinal.addressWidth, hfinal.valueCounter, hfinal.valueWidth,
    hfinal.query, hfinal.queryStart, hfinal.result, hfinal.resultStart,
    hfinal.parked, ?_⟩
  intro i hsource haddress hvalue haddressCounter haddressWidth
    hvalueCounter hvalueWidth hquery hresult
  exact (hfinal.frame i hsource haddress hvalue haddressCounter
    haddressWidth hvalueCounter hvalueWidth hquery hresult).trans
    (hready.frame i hsource haddress hvalue haddressCounter
      haddressWidth hvalueCounter hvalueWidth hquery hresult)

theorem entryScanStepTM_hoareTime_frame_internal
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork iterationWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes (Entry.encode entry ++ rest) queryBits
      initialWork iterationWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryScanStepTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterationWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ((entry.1.bits = queryBits ∧
            EntryScanHit tapes entry rest queryBits initialWork work) ∨
          (entry.1.bits ≠ queryBits ∧
            EntryScanReady tapes rest queryBits initialWork work)) ∧
        out = out₀)
      (entryScanStepTime tapes entry queryBits iterationWork) := by
  have hmatchRun : (entryMatchReadTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterationWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ReadableEntryMatch tapes entry rest queryBits iterationWork work ∧
        out = out₀)
      (entryMatchReadTime entry queryBits) := by
    intro inp work out hpre
    rcases hpre with ⟨hinpEq, hworkEq, houtEq⟩
    subst inp
    subst work
    subst out
    obtain ⟨c', t, ht, hreach, hhalt, hinp, hmatch, hout⟩ :=
      entryMatchReadTM_reachesIn_frame tapes entry rest queryBits inp₀
        iterationWork out₀ hready.source hready.address hready.value
        hready.addressStart hready.valueStart hready.addressCounter
        hready.addressWidth hready.valueCounter hready.valueWidth hready.query
        hready.queryStart hready.result hready.resultStart hinput hready.parked
        houtput
    exact ⟨c', t, ht, hreach, hhalt, hinp, hmatch, hout⟩
  have hbranch : (entryScanBranchTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        ReadableEntryMatch tapes entry rest queryBits iterationWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ((entry.1.bits = queryBits ∧
            EntryScanHit tapes entry rest queryBits initialWork work) ∨
          (entry.1.bits ≠ queryBits ∧
            EntryScanReady tapes rest queryBits initialWork work)) ∧
        out = out₀)
      (entryScanBranchTime tapes entry queryBits iterationWork) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hmatch, hout⟩
    subst inp
    subst out
    by_cases heq : entry.1.bits = queryBits
    · have hread : (work tapes.result).read = Γ.one :=
        hmatch.result_read_eq_one_iff.mpr heq
      have hskip := TM.skipTM_hoareTime_frame inp₀ work out₀ hinput
        hmatch.parked houtput
      obtain ⟨c', t, ht, hreach, hhalt, hinp', hwork', hout'⟩ :=
        hskip inp₀ work out₀ ⟨rfl, rfl, rfl⟩
      obtain ⟨C, hbranchReach, hbranchHalt, hCinput, hCwork, hCoutput⟩ :=
        TM.branchWorkSymbolTM_reachesIn_equal_frame tapes.result Γ.one
          TM.skipTM (entryMissCleanupTM tapes) inp₀ work out₀ hread
          hinput.read_ne_start (fun i => (hmatch.parked i).read_ne_start)
          houtput.read_ne_start hreach hhalt
      have hhit := readableEntryMatch_to_hit tapes entry rest queryBits
        initialWork iterationWork work hready hmatch heq
      refine ⟨C, t + 1, ?_, hbranchReach, hbranchHalt, ?_⟩
      · unfold entryScanBranchTime TM.branchWorkSymbolTime
        omega
      · refine ⟨hCinput.trans hinp', Or.inl ⟨heq, ?_⟩,
          hCoutput.trans hout'⟩
        rw [hCwork, hwork']
        exact hhit
    · have hread : (work tapes.result).read ≠ Γ.one := by
        exact fun h => heq (hmatch.result_read_eq_one_iff.mp h)
      have hcleanup := entryMissCleanupTM_hoareTime_frame tapes entry rest
        queryBits iterationWork work inp₀ out₀ hmatch hinput houtput
      obtain ⟨c', t, ht, hreach, hhalt, hinp', hready', hout'⟩ :=
        hcleanup inp₀ work out₀ ⟨rfl, rfl, rfl⟩
      obtain ⟨C, hbranchReach, hbranchHalt, hCinput, hCwork, hCoutput⟩ :=
        TM.branchWorkSymbolTM_reachesIn_different_frame tapes.result Γ.one
          TM.skipTM (entryMissCleanupTM tapes) inp₀ work out₀ hread
          hinput.read_ne_start (fun i => (hmatch.parked i).read_ne_start)
          houtput.read_ne_start hreach hhalt
      have hreadyGlobal := entryScanReady_reframe tapes
        (Entry.encode entry ++ rest) rest queryBits initialWork iterationWork
        c'.work hready hready'
      refine ⟨C, t + 1, ?_, hbranchReach, hbranchHalt, ?_⟩
      · unfold entryScanBranchTime TM.branchWorkSymbolTime
        omega
      · refine ⟨hCinput.trans hinp', Or.inr ⟨heq, ?_⟩,
          hCoutput.trans hout'⟩
        rw [hCwork]
        exact hreadyGlobal
  have hseq := TM.seqTM_hoareTime (entryMatchReadTM tapes)
    (entryScanBranchTM tapes) hmatchRun
    (by
      intro inp work out hmid
      rcases hmid with ⟨hinp, hmatch, hout⟩
      obtain ⟨hinpTransition, hworkTransition, houtTransition⟩ :=
        TM.phaseTransition_eq_self_of_reads_ne_start
          (hinp ▸ hinput.read_ne_start)
          (fun i => (hmatch.parked i).read_ne_start)
          (hout ▸ houtput.read_ne_start)
      rw [hinpTransition, hworkTransition, houtTransition]
      exact ⟨hinp, hmatch, hout⟩)
    hbranch
  simpa [entryScanStepTM, entryScanStepTime] using hseq

end Machine

end RegisterStore

end RAM

end Complexity
