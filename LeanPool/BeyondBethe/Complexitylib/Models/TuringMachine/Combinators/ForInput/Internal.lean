/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Read-only-input loop combinator — proof internals

This module supplies the exact body-simulation embedding and the structural
one-way-output proof for `TM.forInputTM`.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a body configuration into the body phase of `forInputTM`. -/
def forInputBodyWrap (body : TM n) (c : Cfg n body.Q) :
    Cfg n (forInputTM body).Q :=
  { state := .inr c.state
    input := c.input
    work := c.work
    output := c.output }

/-- Every nonhalting body step is simulated exactly by one `forInputTM` step. -/
theorem forInputTM_body_step_internal (body : TM n)
    {c c' : Cfg n body.Q} (hstep : body.step c = some c') :
    (forInputTM body).step (forInputBodyWrap body c) =
      some (forInputBodyWrap body c') := by
  have hne : c.state ≠ body.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by simp [forInputBodyWrap, forInputTM])]
  simp only [forInputBodyWrap, forInputTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize body.δ c.state c.input.read (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  intro hstep
  cases Option.some.inj hstep
  rfl

/-- Exact body runs lift through the body phase of `forInputTM`. -/
theorem forInputTM_body_reachesIn_internal (body : TM n)
    {t : ℕ} {c c' : Cfg n body.Q} (hreach : body.reachesIn t c c') :
    (forInputTM body).reachesIn t
      (forInputBodyWrap body c) (forInputBodyWrap body c') :=
  reachesIn_map (forInputBodyWrap body)
    (fun _ _ => forInputTM_body_step_internal body) hreach

/-- On a Boolean input symbol, the driver advances the read-only input and
enters the body while preserving every off-start work and output tape. -/
theorem forInputTM_step_scan_bit_internal (body : TM n)
    (c : Cfg n (forInputTM body).Q)
    (hstate : c.state = .inl .scan)
    (hstart : c.input.read ≠ Γ.start) (hblank : c.input.read ≠ Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step c = some
      { state := .inr body.qstart
        input := c.input.move Dir3.right
        work := c.work
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [forInputTM])]
  simp only [forInputTM, hstate, hstart, hblank, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, ite_eq_right (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- At the first input blank, the driver halts while preserving all off-start
tapes exactly. -/
theorem forInputTM_step_scan_blank_internal (body : TM n)
    (c : Cfg n (forInputTM body).Q)
    (hstate : c.state = .inl .scan) (hblank : c.input.read = Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step c = some
      { state := .inl .done
        input := c.input
        work := c.work
        output := c.output } := by
  have hstart : c.input.read ≠ Γ.start := by rw [hblank]; decide
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [forInputTM])]
  simp only [forInputTM, hstate, hblank, allReadBack, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · simp [idleDir, Tape.move]
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, ite_eq_right (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- A halted body takes one preserving seam step back to the input scanner. -/
theorem forInputTM_step_body_halt_internal (body : TM n)
    (c : Cfg n body.Q) (hhalt : body.halted c)
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step (forInputBodyWrap body c) = some
      { state := .inl .scan
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step, ite_eq_right (by simp [forInputBodyWrap, forInputTM])]
  simp only [forInputBodyWrap, forInputTM, hhalt, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, ite_eq_right (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- A certified input-driven loop has the advertised exact remaining run. -/
theorem ForInputLoopSpec.reachesIn_internal {body : TM n}
    {bodyTime : ℕ → ℕ} {total : ℕ}
    (spec : ForInputLoopSpec body bodyTime total) :
    ∀ count value, value + count = total →
      (forInputTM body).reachesIn (forInputLoopTime bodyTime value count)
        (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value htotal
      have hvalue : value = total := by omega
      subst value
      exact .step spec.blankStep .zero
  | succ count ih =>
      intro value htotal
      have hvalue : value < total := by omega
      have hscan : (forInputTM body).reachesIn 1
          (spec.scanCfg value) (spec.bodyStartCfg value) :=
        .step (spec.scanStep value hvalue) .zero
      have hbody := spec.bodyRun value hvalue
      have hloopback : (forInputTM body).reachesIn 1
          (spec.bodyDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hvalue) .zero
      have htail := ih (value + 1) (by omega)
      have hreach := reachesIn_trans (forInputTM body) hscan
        (reachesIn_trans (forInputTM body) hbody
          (reachesIn_trans (forInputTM body) hloopback htail))
      convert hreach using 1
      simp only [forInputLoopTime]
      omega

/-- Every configuration reached no later than a certified loop's exact
remaining runtime satisfies its auxiliary-space budget. -/
theorem ForInputLoopSpaceSpec.prefix_withinAuxSpace_internal
    {body : TM n} {bodyTime : ℕ → ℕ} {total inputLength spaceBound : ℕ}
    {spec : ForInputLoopSpec body bodyTime total}
    (spaceSpec : ForInputLoopSpaceSpec spec inputLength spaceBound) :
    ∀ count value t (c : Cfg n (forInputTM body).Q),
      value + count = total →
      (forInputTM body).reachesIn t (spec.scanCfg value) c →
      t ≤ forInputLoopTime bodyTime value count →
      c.WithinAuxSpace inputLength spaceBound := by
  intro count
  induction count with
  | zero =>
      intro value t c htotal hreach ht
      have hvalue : value = total := by omega
      subst value
      simp only [forInputLoopTime] at ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases hreach
        exact spaceSpec.scanWithin total le_rfl
      · have hdone : (forInputTM body).reachesIn 1
            (spec.scanCfg total) spec.doneCfg :=
          .step spec.blankStep .zero
        have hc := (forInputTM body).reachesIn_right_unique hreach hdone
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
          have hcanonical : (forInputTM body).reachesIn t
              (spec.scanCfg value) d := by
            have hscan : (forInputTM body).reachesIn 1
                (spec.scanCfg value) (spec.bodyStartCfg value) :=
              .step (spec.scanStep value hvalue) .zero
            have htotalRun := reachesIn_trans (forInputTM body) hscan hprefix
            simpa [htu] using htotalRun
          have hc := (forInputTM body).reachesIn_right_unique hreach hcanonical
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
              tailTime ≤ forInputLoopTime bodyTime (value + 1) count := by
            rw [forInputLoopTime] at ht
            dsimp only [prefixTime, tailTime] at ⊢
            omega
          have htailFull := spec.reachesIn_internal count (value + 1) (by omega)
          obtain ⟨d, htail, _hsuffix⟩ := reachesIn_prefix_internal
            htailFull htailBound
          have hscan : (forInputTM body).reachesIn 1
              (spec.scanCfg value) (spec.bodyStartCfg value) :=
            .step (spec.scanStep value hvalue) .zero
          have hloopback : (forInputTM body).reachesIn 1
              (spec.bodyDoneCfg value) (spec.scanCfg (value + 1)) :=
            .step (spec.loopbackStep value hvalue) .zero
          have hcanonical := reachesIn_trans (forInputTM body) hscan
            (reachesIn_trans (forInputTM body) (spec.bodyRun value hvalue)
              (reachesIn_trans (forInputTM body) hloopback htail))
          have hcanonical' : (forInputTM body).reachesIn t
              (spec.scanCfg value) d := by
            convert hcanonical using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hc := (forInputTM body).reachesIn_right_unique hreach hcanonical'
          rw [hc]
          exact ih (value + 1) tailTime d (by omega) htail htailBound

/-- A read-only-input loop preserves the body's one-way-output discipline. -/
theorem IsTransducer.forInputTM_internal {body : TM n}
    (hbody : body.IsTransducer) : (forInputTM body).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase <;> cases iHead <;> cases oHead <;>
        simp [forInputTM, allIdle, allReadBack, idleDir]
  | inr q =>
      by_cases hq : q = body.qhalt
      · cases oHead <;> simp [forInputTM, hq, allReadBack, idleDir]
      · simpa [forInputTM, hq] using hbody q iHead wHeads oHead

end TM

end Complexity
