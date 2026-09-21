/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Internal

/-!
# Canonical binary count-up loops — proof internals

This module turns the wrapper-free loop certificates from `BinaryFor.Defs`
into exact executions and all-prefix auxiliary-space bounds. It also proves
that the binary loop driver preserves the one-way-output discipline of its
body.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A certified canonical binary count-up loop has its advertised exact
remaining run. -/
theorem BinaryForLoopSpec.reachesIn_internal {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ} {limitValue : ℕ}
    (spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue) :
    ∀ count value, value + count = limitValue →
      (binaryForTM body counterIdx limitIdx).reachesIn
        (binaryForLoopTime bodyTime limitValue value count)
        (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value hlimit
      have hvalue : value = limitValue := by omega
      subst value
      exact spec.doneRun
  | succ count ih =>
      intro value hlimit
      have hvalue : value < limitValue := by omega
      have htest := spec.testRun value hvalue
      have hiteration := spec.iterationRun value hvalue
      have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
          (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hvalue) .zero
      have htail := ih (value + 1) (by omega)
      have hreach := reachesIn_trans (binaryForTM body counterIdx limitIdx) htest
        (reachesIn_trans (binaryForTM body counterIdx limitIdx) hiteration
          (reachesIn_trans (binaryForTM body counterIdx limitIdx) hloopback htail))
      convert hreach using 1
      simp only [binaryForLoopTime]
      omega

/-- Scanner bounds are the reflexive prefixes of the comparison obligation. -/
theorem BinaryForLoopSpaceSpec.scanWithin_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound value : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound)
    (hvalue : value ≤ limitValue) :
    (spec.scanCfg value).WithinAuxSpace inputLength spaceBound :=
  spaceSpec.testPrefixWithin value 0 (spec.scanCfg value) hvalue
    (Nat.zero_le _) .zero

/-- The final-state bound is the complete final comparison prefix. -/
theorem BinaryForLoopSpaceSpec.doneWithin_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound) :
    spec.doneCfg.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.testPrefixWithin limitValue (binaryForCompareTime limitValue)
    spec.doneCfg le_rfl le_rfl spec.doneRun

/-- Every configuration reached no later than a certified binary loop's exact
remaining runtime satisfies its auxiliary-space budget. -/
theorem BinaryForLoopSpaceSpec.prefix_withinAuxSpace_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound) :
    ∀ count value t (c : Cfg n (binaryForTM body counterIdx limitIdx).Q),
      value + count = limitValue →
      (binaryForTM body counterIdx limitIdx).reachesIn t (spec.scanCfg value) c →
      t ≤ binaryForLoopTime bodyTime limitValue value count →
      c.WithinAuxSpace inputLength spaceBound := by
  intro count
  induction count with
  | zero =>
      intro value t c hlimit hreach htime
      have hvalue : value = limitValue := by omega
      subst value
      simp only [binaryForLoopTime] at htime
      exact spaceSpec.testPrefixWithin limitValue t c le_rfl htime hreach
  | succ count ih =>
      intro value t c hlimit hreach htime
      have hvalue : value < limitValue := by omega
      by_cases htest : t ≤ binaryForCompareTime limitValue
      · exact spaceSpec.testPrefixWithin value t c (Nat.le_of_lt hvalue)
          htest hreach
      · let iterationTime := t - binaryForCompareTime limitValue
        have htimeEq : binaryForCompareTime limitValue + iterationTime = t := by
          dsimp only [iterationTime]
          exact Nat.add_sub_of_le (by omega)
        by_cases hiteration :
            iterationTime ≤ binaryForIterationTime bodyTime value
        · obtain ⟨d, hprefix, _hsuffix⟩ := reachesIn_prefix_internal
            (spec.iterationRun value hvalue) hiteration
          have hcanonical : (binaryForTM body counterIdx limitIdx).reachesIn t
              (spec.scanCfg value) d := by
            have htotalRun := reachesIn_trans
              (binaryForTM body counterIdx limitIdx)
              (spec.testRun value hvalue) hprefix
            simpa [htimeEq] using htotalRun
          have hc := (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
            hreach hcanonical
          rw [hc]
          exact spaceSpec.iterationPrefixWithin value iterationTime d hvalue
            hiteration hprefix
        · let prefixTime := binaryForCompareTime limitValue +
              binaryForIterationTime bodyTime value + 1
          have hprefixTime : prefixTime ≤ t := by
            dsimp only [prefixTime, iterationTime] at ⊢ hiteration
            omega
          let tailTime := t - prefixTime
          have htailEq : prefixTime + tailTime = t := by
            dsimp only [tailTime]
            exact Nat.add_sub_of_le hprefixTime
          have htailBound :
              tailTime ≤
                binaryForLoopTime bodyTime limitValue (value + 1) count := by
            rw [binaryForLoopTime] at htime
            dsimp only [prefixTime, tailTime] at ⊢
            omega
          have htailFull := spec.reachesIn_internal count (value + 1) (by omega)
          obtain ⟨d, htail, _hsuffix⟩ := reachesIn_prefix_internal
            htailFull htailBound
          have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
              (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
            .step (spec.loopbackStep value hvalue) .zero
          have hcanonical := reachesIn_trans
            (binaryForTM body counterIdx limitIdx) (spec.testRun value hvalue)
            (reachesIn_trans (binaryForTM body counterIdx limitIdx)
              (spec.iterationRun value hvalue)
              (reachesIn_trans (binaryForTM body counterIdx limitIdx)
                hloopback htail))
          have hcanonical' : (binaryForTM body counterIdx limitIdx).reachesIn t
              (spec.scanCfg value) d := by
            convert hcanonical using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hc := (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
            hreach hcanonical'
          rw [hc]
          exact ih (value + 1) tailTime d (by omega) htail htailBound

/-- A canonical binary count-up loop preserves the body's one-way-output
discipline. -/
theorem IsTransducer.binaryForTM_internal {body : TM n}
    (hbody : body.IsTransducer) (counterIdx limitIdx : Fin n) :
    (binaryForTM body counterIdx limitIdx).IsTransducer := by
  have hiteration : (binaryForIterationTM body counterIdx).IsTransducer := by
    exact hbody.seqTM_internal (binarySuccTM_isTransducer_internal counterIdx)
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase with
      | scan equalSoFar =>
          simp only [binaryForTM]
          split <;> simp [idleDir] <;> split <;> decide
      | rewind equalSoFar =>
          simp only [binaryForTM]
          split <;> simp [idleDir] <;> split <;> decide
      | done =>
          simp [binaryForTM, allIdle, idleDir]
          split <;> decide
  | inr q =>
      by_cases hq : q = (binaryForIterationTM body counterIdx).qhalt
      · simp [binaryForTM, hq, allReadBack, idleDir]
        split <;> decide
      · simpa [binaryForTM, hq] using hiteration q iHead wHeads oHead

end TM

end Complexity
