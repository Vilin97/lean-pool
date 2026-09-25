/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Internal.Ctrl
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Internal.Inv
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep

/-!
# Bounded sparse-entry scan — semantic internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

theorem entryScanTM_hoareTime_frame_internal
    (tapes : EntryScanTapes n) (store : Store) (queryBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      queryBits initialWork initialWork)
    (hcount : (initialWork tapes.count).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryScanTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanOutcome tapes store queryBits initialWork work ∧
        out = out₀)
      (entryScanTime tapes queryBits store) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  induction store generalizing initialWork with
  | nil =>
      have hblank : (initialWork tapes.count).read = Γ.blank :=
        hcount.read_eq_blank_iff.mpr rfl
      have hstep := entryScanTM_step_test_zero_internal tapes inp₀ initialWork
        out₀ hblank hinput hready.parked houtput
      refine ⟨entryScanDoneCfg tapes inp₀ initialWork out₀, 1, ?_,
        .step hstep .zero, ?_, rfl, ?_, rfl⟩
      · simp [entryScanTime]
      · rfl
      · exact Or.inr ⟨initialWork, ⟨by simp, hready, hcount, by
          intro i _ _ _ _ _ _ _ _ _ _
          simp [entryScanDoneCfg]⟩⟩
  | cons entry rest ih =>
      have hreadyStep :
          EntryScanReady tapes.entry
            (Entry.encode entry ++ rest.flatMap Entry.encode) queryBits
            initialWork initialWork := by
        simpa using hready
      have hcountPositive :
          (initialWork tapes.count).HasBinaryNat (rest.length + 1) := by
        simpa using hcount
      have hnonblank : (initialWork tapes.count).read ≠ Γ.blank := by
        intro hblank
        have hzero := hcountPositive.read_eq_blank_iff.mp hblank
        omega
      have htest := entryScanTM_step_test_positive_internal tapes inp₀
        initialWork out₀ hnonblank hinput hready.parked houtput
      have hstepContract := entryScanStepTM_hoareTime_frame tapes.entry entry
        (rest.flatMap Entry.encode) queryBits initialWork initialWork inp₀ out₀
        hreadyStep hinput houtput
      obtain ⟨bodyDone, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
          hbodyInput, hstepOutcome, hbodyOutput⟩ :=
        hstepContract inp₀ initialWork out₀ ⟨rfl, rfl, rfl⟩
      have hbodyTime' :
          bodyTime ≤ entryScanOneTime tapes entry queryBits := by
        simpa [hreadyStep.stepTime_eq_oneTime_internal] using hbodyTime
      have hbodyReach' :=
        entryScanTM_body_reachesIn_internal tapes hbodyReach
      rcases hstepOutcome with hhitTagged | hmissTagged
      · rcases hhitTagged with ⟨_, hhit⟩
        have hfinish := entryScanTM_step_body_hit_internal tapes bodyDone
          hbodyHalt hhit.result_read_one_internal
          (hbodyInput ▸ hinput) hhit.parked (hbodyOutput ▸ houtput)
        have hprefix : (entryScanTM tapes).reachesIn (bodyTime + 1)
            (entryScanTestCfg tapes inp₀ initialWork out₀)
            (entryScanBodyWrap tapes bodyDone) :=
          .step htest hbodyReach'
        have hreach : (entryScanTM tapes).reachesIn
            (bodyTime + 1 + 1)
            (entryScanTestCfg tapes inp₀ initialWork out₀)
            (entryScanDoneCfg tapes bodyDone.input bodyDone.work
              bodyDone.output) :=
          TM.reachesIn_trans _ hprefix (.step hfinish .zero)
        refine ⟨entryScanDoneCfg tapes bodyDone.input bodyDone.work
          bodyDone.output, bodyTime + 1 + 1, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · simp only [entryScanTime]
          omega
        · simpa [entryScanTestCfg, entryScanTM] using hreach
        · simpa [entryScanDoneCfg] using hbodyInput
        · exact Or.inl ⟨[], entry, rest, initialWork, ⟨by simp, by simp,
            hhit, by
              simpa [entryScanDoneCfg, hhit.count_eq_internal] using
                hcountPositive,
            hhit.scanFrame_internal⟩⟩
        · simpa [entryScanDoneCfg] using hbodyOutput
      · rcases hmissTagged with ⟨hneq, hmiss⟩
        have hdispatch := entryScanTM_step_body_miss_internal tapes bodyDone
          hbodyHalt (by
            rw [hmiss.result_read_blank_internal]
            decide)
          (hbodyInput ▸ hinput) hmiss.parked (hbodyOutput ▸ houtput)
        have hcountBody :
            (bodyDone.work tapes.count).HasBinaryNat (rest.length + 1) := by
          rw [hmiss.count_eq_internal]
          exact hcountPositive
        obtain ⟨predDone, hpredReach, hpredHalt, hpredInput,
            hpredOther, hpredCount, hpredOutput⟩ :=
          TM.binaryPredTM_reachesIn_frame tapes.count rest.length
            bodyDone.input bodyDone.work bodyDone.output hcountBody
            (hbodyInput ▸ hinput.read_ne_start)
            (fun i _ => (hmiss.parked i).read_ne_start)
            (hbodyOutput ▸ houtput.read_ne_start)
        have hpredReach' :=
          entryScanTM_pred_reachesIn_internal tapes hpredReach
        have hreadyPred := hmiss.change_count_internal hpredOther hpredCount
        have hloop := entryScanTM_step_pred_halt_internal tapes predDone
          hpredHalt (by
            rw [hpredInput, hbodyInput]
            exact hinput)
          hreadyPred.parked (by
            rw [hpredOutput, hbodyOutput]
            exact houtput)
        have hpredInput0 : predDone.input = inp₀ :=
          hpredInput.trans hbodyInput
        have hpredOutput0 : predDone.output = out₀ :=
          hpredOutput.trans hbodyOutput
        have hloop' : (entryScanTM tapes).step
            (entryScanPredWrap tapes predDone) =
            some (entryScanTestCfg tapes inp₀ predDone.work out₀) := by
          simpa [hpredInput0, hpredOutput0] using hloop
        obtain ⟨final, recTime, hrecTime, hrecReach, hrecHalt,
            hrecInput, hrecOutcome, hrecOutput⟩ :=
          ih predDone.work hreadyPred hpredCount
        have hentryFrame :
            EntryScanFrame tapes initialWork bodyDone.work :=
          hmiss.scanFrame_internal
        have hpredFrame :
            EntryScanFrame tapes bodyDone.work predDone.work := by
          intro i hcountIdx _ _ _ _ _ _ _ _ _
          exact hpredOther i hcountIdx
        have hphaseFrame :
            EntryScanFrame tapes initialWork predDone.work :=
          hentryFrame.trans_internal hpredFrame
        have hprefix : (entryScanTM tapes).reachesIn
            (bodyTime + 1 + 1 + TM.binaryPredTime rest.length + 1)
            (entryScanTestCfg tapes inp₀ initialWork out₀)
            (entryScanTestCfg tapes inp₀ predDone.work out₀) := by
          have htestBody : (entryScanTM tapes).reachesIn (bodyTime + 1)
              (entryScanTestCfg tapes inp₀ initialWork out₀)
              (entryScanBodyWrap tapes bodyDone) :=
            .step htest hbodyReach'
          have htoPred : (entryScanTM tapes).reachesIn
              (bodyTime + 1 + 1)
              (entryScanTestCfg tapes inp₀ initialWork out₀)
              (entryScanPredWrap tapes
                { state := (TM.binaryPredTM tapes.count).qstart
                  input := bodyDone.input
                  work := bodyDone.work
                  output := bodyDone.output }) :=
            TM.reachesIn_trans _ htestBody (.step hdispatch .zero)
          have hthroughPred :=
            TM.reachesIn_trans (entryScanTM tapes) htoPred hpredReach'
          have hthroughLoop := TM.reachesIn_trans (entryScanTM tapes)
            hthroughPred (.step hloop' .zero)
          simpa [Nat.add_assoc] using hthroughLoop
        have hreach :=
          TM.reachesIn_trans (entryScanTM tapes) hprefix hrecReach
        refine ⟨final,
          bodyTime + 1 + 1 + TM.binaryPredTime rest.length + 1 + recTime,
          ?_, ?_, hrecHalt, hrecInput, ?_, hrecOutput⟩
        · simp only [entryScanTime]
          omega
        · simpa [entryScanTestCfg, entryScanTM, Nat.add_assoc] using hreach
        · rcases hrecOutcome with hfound | hnone
          · rcases hfound with ⟨scanned, matched, suffix, hitBase, hfound⟩
            exact Or.inl ⟨entry :: scanned, matched, suffix, hitBase,
              ⟨by simp [hfound.store_eq], by
                  intro prior hprior
                  simp only [List.mem_cons] at hprior
                  rcases hprior with rfl | hprior
                  · exact hneq
                  · exact hfound.prefixMiss prior hprior,
                hfound.hit, hfound.count,
                hphaseFrame.trans_internal hfound.frame⟩⟩
          · rcases hnone with ⟨readyBase, hnone⟩
            exact Or.inr ⟨readyBase,
              ⟨by
                  intro candidate hcand
                  simp only [List.mem_cons] at hcand
                  rcases hcand with rfl | hcand
                  · exact hneq
                  · exact hnone.notFound candidate hcand,
                hnone.ready, hnone.count,
                hphaseFrame.trans_internal hnone.frame⟩⟩

end Machine

end RegisterStore

end RAM

end Complexity
