/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Binary work-tape loop combinator -- proof internals

This module proves exact body embedding, bit/blank scanner transitions, the
advancing loopback seam, certified finite iteration, and transducer closure.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a body configuration in the body phase of `forBinaryWorkTM`. -/
def forBinaryWorkBodyWrap (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n body.Q) : Cfg n (forBinaryWorkTM driverIdx body).Q :=
  { state := .inr cfg.state
    input := cfg.input
    work := cfg.work
    output := cfg.output }

/-- Every nonhalting body step is simulated exactly. -/
theorem forBinaryWorkTM_body_step_internal (driverIdx : Fin n) (body : TM n)
    {cfg next : Cfg n body.Q} (hstep : body.step cfg = some next) :
    (forBinaryWorkTM driverIdx body).step
      (forBinaryWorkBodyWrap driverIdx body cfg) =
        some (forBinaryWorkBodyWrap driverIdx body next) := by
  have hne : cfg.state ≠ body.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [forBinaryWorkBodyWrap, forBinaryWorkTM])]
  simp only [forBinaryWorkBodyWrap, forBinaryWorkTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize body.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
    cfg.output.read = action
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ :=
    action
  intro hstep
  cases Option.some.inj hstep
  rfl

/-- Exact body runs lift through the combined machine's body phase. -/
theorem forBinaryWorkTM_body_reachesIn_internal
    (driverIdx : Fin n) (body : TM n)
    {time : ℕ} {cfg next : Cfg n body.Q}
    (hreach : body.reachesIn time cfg next) :
    (forBinaryWorkTM driverIdx body).reachesIn time
      (forBinaryWorkBodyWrap driverIdx body cfg)
      (forBinaryWorkBodyWrap driverIdx body next) :=
  reachesIn_map (forBinaryWorkBodyWrap driverIdx body)
    (fun _ _ => forBinaryWorkTM_body_step_internal driverIdx body) hreach

/-- On either Boolean symbol, the scanner enters the body without moving or
changing any tape. -/
theorem forBinaryWorkTM_step_scan_bit_internal
    (driverIdx : Fin n) (body : TM n) (bit : Bool)
    (cfg : Cfg n (forBinaryWorkTM driverIdx body).Q)
    (hstate : cfg.state = .inl .scan)
    (hbit : (cfg.work driverIdx).read = Γ.ofBool bit)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forBinaryWorkTM driverIdx body).step cfg = some
      { state := .inr body.qstart
        input := cfg.input
        work := cfg.work
        output := cfg.output } := by
  have hstart : (cfg.work driverIdx).read ≠ Γ.start := by
    rw [hbit]
    exact Γ.ofBool_ne_start bit
  have hblank : (cfg.work driverIdx).read ≠ Γ.blank := by
    rw [hbit]
    cases bit <;> decide
  rw [TM.step, if_neg (by rw [hstate]; simp [forBinaryWorkTM])]
  simp only [forBinaryWorkTM, hstate, hstart, hblank, allReadBack,
    ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

/-- On the first blank, the scanner halts without consuming it. -/
theorem forBinaryWorkTM_step_scan_blank_internal
    (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n (forBinaryWorkTM driverIdx body).Q)
    (hstate : cfg.state = .inl .scan)
    (hblank : (cfg.work driverIdx).read = Γ.blank)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forBinaryWorkTM driverIdx body).step cfg = some
      { state := .inl .done
        input := cfg.input
        work := cfg.work
        output := cfg.output } := by
  rw [TM.step, if_neg (by rw [hstate]; simp [forBinaryWorkTM])]
  simp only [forBinaryWorkTM, hstate, hblank, allReadBack,
    ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

/-- A halted body takes one preserving seam step that advances only the
selected driver head. -/
theorem forBinaryWorkTM_step_body_halt_internal
    (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n body.Q) (hhalt : body.halted cfg)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forBinaryWorkTM driverIdx body).step
      (forBinaryWorkBodyWrap driverIdx body cfg) = some
        { state := .inl .scan
          input := cfg.input
          work := fun i =>
            if i = driverIdx then (cfg.work i).move Dir3.right
            else cfg.work i
          output := cfg.output } := by
  rw [TM.step, if_neg (by simp [forBinaryWorkBodyWrap, forBinaryWorkTM])]
  simp only [forBinaryWorkBodyWrap, forBinaryWorkTM, hhalt, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    rw [writeAndMove_readBack _ (hwork i)]
    split
    · rfl
    · rw [idleDir, if_neg (hwork i)]
      rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, if_neg houtput]
    rfl

/-- A certified bit-driven loop has its advertised exact remaining run. -/
theorem ForBinaryWorkLoopSpec.reachesIn_internal
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ} {total : ℕ}
    (spec : ForBinaryWorkLoopSpec driverIdx body bodyTime total) :
    ∀ count value, value + count = total →
      (forBinaryWorkTM driverIdx body).reachesIn
        (forBinaryWorkLoopTime bodyTime value count)
        (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value htotal
      have hvalue : value = total := by omega
      subst value
      exact .step spec.stopStep .zero
  | succ count ih =>
      intro value htotal
      have hvalue : value < total := by omega
      have hscan : (forBinaryWorkTM driverIdx body).reachesIn 1
          (spec.scanCfg value) (spec.bodyStartCfg value) :=
        .step (spec.scanStep value hvalue) .zero
      have hbody := spec.bodyRun value hvalue
      have hloopback : (forBinaryWorkTM driverIdx body).reachesIn 1
          (spec.bodyDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hvalue) .zero
      have htail := ih (value + 1) (by omega)
      have hreach := reachesIn_trans (forBinaryWorkTM driverIdx body) hscan
        (reachesIn_trans (forBinaryWorkTM driverIdx body) hbody
          (reachesIn_trans (forBinaryWorkTM driverIdx body) hloopback htail))
      convert hreach using 1
      simp only [forBinaryWorkLoopTime]
      omega

/-- Every prefix no longer than a certified loop's exact remaining runtime
respects its auxiliary-space budget. -/
theorem ForBinaryWorkLoopSpaceSpec.prefix_withinAuxSpace_internal
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ}
    {total inputLength spaceBound : ℕ}
    {spec : ForBinaryWorkLoopSpec driverIdx body bodyTime total}
    (spaceSpec :
      ForBinaryWorkLoopSpaceSpec spec inputLength spaceBound) :
    ∀ count value t (c : Cfg n (forBinaryWorkTM driverIdx body).Q),
      value + count = total →
      (forBinaryWorkTM driverIdx body).reachesIn t
        (spec.scanCfg value) c →
      t ≤ forBinaryWorkLoopTime bodyTime value count →
      c.WithinAuxSpace inputLength spaceBound := by
  intro count
  induction count with
  | zero =>
      intro value t c htotal hreach ht
      have hvalue : value = total := by omega
      subst value
      simp only [forBinaryWorkLoopTime] at ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases hreach
        exact spaceSpec.scanWithin total le_rfl
      · have hdone : (forBinaryWorkTM driverIdx body).reachesIn 1
            (spec.scanCfg total) spec.doneCfg :=
          .step spec.stopStep .zero
        have hc :=
          (forBinaryWorkTM driverIdx body).reachesIn_right_unique hreach hdone
        rw [hc]
        exact spaceSpec.doneWithin
  | succ count ih =>
      intro value t c htotal hreach ht
      have hvalue : value < total := by omega
      by_cases htzero : t = 0
      · subst t
        cases hreach
        exact spaceSpec.scanWithin value (Nat.le_of_lt hvalue)
      · let u := t - 1
        have htu : 1 + u = t := by
          dsimp only [u]
          omega
        by_cases hubody : u ≤ bodyTime value
        · obtain ⟨d, hprefix, _hsuffix⟩ := reachesIn_prefix_internal
            (spec.bodyRun value hvalue) hubody
          have hcanonical : (forBinaryWorkTM driverIdx body).reachesIn t
              (spec.scanCfg value) d := by
            have hscan : (forBinaryWorkTM driverIdx body).reachesIn 1
                (spec.scanCfg value) (spec.bodyStartCfg value) :=
              .step (spec.scanStep value hvalue) .zero
            have htotalRun :=
              reachesIn_trans (forBinaryWorkTM driverIdx body) hscan hprefix
            simpa [htu] using htotalRun
          have hc :=
            (forBinaryWorkTM driverIdx body).reachesIn_right_unique
              hreach hcanonical
          rw [hc]
          exact spaceSpec.bodyPrefixWithin value u d hvalue hubody hprefix
        · let prefixTime := 1 + bodyTime value + 1
          have hprefixTime : prefixTime ≤ t := by
            dsimp only [prefixTime, u] at ⊢ hubody
            omega
          let tailTime := t - prefixTime
          have htailEq : prefixTime + tailTime = t := by
            dsimp only [tailTime]
            exact Nat.add_sub_of_le hprefixTime
          have htailBound :
              tailTime ≤
                forBinaryWorkLoopTime bodyTime (value + 1) count := by
            rw [forBinaryWorkLoopTime] at ht
            dsimp only [prefixTime, tailTime] at ⊢
            omega
          have htailFull :=
            spec.reachesIn_internal count (value + 1) (by omega)
          obtain ⟨d, htail, _hsuffix⟩ := reachesIn_prefix_internal
            htailFull htailBound
          have hscan : (forBinaryWorkTM driverIdx body).reachesIn 1
              (spec.scanCfg value) (spec.bodyStartCfg value) :=
            .step (spec.scanStep value hvalue) .zero
          have hloopback : (forBinaryWorkTM driverIdx body).reachesIn 1
              (spec.bodyDoneCfg value) (spec.scanCfg (value + 1)) :=
            .step (spec.loopbackStep value hvalue) .zero
          have hcanonical :=
            reachesIn_trans (forBinaryWorkTM driverIdx body) hscan
              (reachesIn_trans (forBinaryWorkTM driverIdx body)
                (spec.bodyRun value hvalue)
                (reachesIn_trans (forBinaryWorkTM driverIdx body)
                  hloopback htail))
          have hcanonical' : (forBinaryWorkTM driverIdx body).reachesIn t
              (spec.scanCfg value) d := by
            convert hcanonical using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hc :=
            (forBinaryWorkTM driverIdx body).reachesIn_right_unique
              hreach hcanonical'
          rw [hc]
          exact ih (value + 1) tailTime d (by omega) htail htailBound

/-- Bit-driven work iteration preserves one-way output when the body does. -/
theorem IsTransducer.forBinaryWorkTM_internal
    {driverIdx : Fin n} {body : TM n} (hbody : body.IsTransducer) :
    (forBinaryWorkTM driverIdx body).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase with
      | scan =>
          by_cases hstart : wHeads driverIdx = Γ.start
          · cases iHead <;> cases oHead <;>
              simp [forBinaryWorkTM, hstart, allReadBack, idleDir]
          · by_cases hblank : wHeads driverIdx = Γ.blank
            · cases iHead <;> cases oHead <;>
                simp [forBinaryWorkTM, hblank, allReadBack, idleDir]
            · cases iHead <;> cases oHead <;>
                simp [forBinaryWorkTM, hstart, hblank, allReadBack, idleDir]
      | done =>
          cases iHead <;> cases oHead <;>
            simp [forBinaryWorkTM, allIdle, idleDir]
  | inr state =>
      by_cases hstate : state = body.qhalt
      · cases iHead <;> cases oHead <;>
          simp [forBinaryWorkTM, hstate, allReadBack, idleDir]
      · simpa [forBinaryWorkTM, hstate] using hbody state iHead wHeads oHead

end TM

end Complexity
