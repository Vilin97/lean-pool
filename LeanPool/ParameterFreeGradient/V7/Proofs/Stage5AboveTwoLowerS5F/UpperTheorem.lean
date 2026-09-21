/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.UpperTrial

namespace V7.Stage5AboveTwoLowerS5F

open V7.Stage4AboveTwoFinalTrial

private theorem singleton_charged_run (algorithm : DeterministicExactPairAlgorithm d)
    (x0 : Point d) (oracle : PairOracle d) :
    ChargedKnownParameterRun algorithm x0 oracle [oracle.observe x0] := by
  refine ⟨?_, ?_, by simp, by simp [O3.PairOracle.observe]⟩
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simp [O3.PairOracle.observe]
  · intro obs hobs
    simp only [List.mem_singleton] at hobs
    subst obs
    rfl

private theorem output_guarantee (trial : LocalTrial d) (p M D eps : ℝ)
    (x0 : Point d) (oracle : PairOracle d) (trace : List (Observation d))
    (hexact : TraceExact oracle trace)
    (hsmall : ∃ obs ∈ trace,
      lpNorm (conjugateExponent p) obs.gradient ≤ eps) :
    let algorithm := chargedTrialAlgorithm p trial M D eps
    let xhat := algorithm.output x0 trace
    WasQueried trace xhat ∧
      lpNorm (conjugateExponent p) (oracle.gradient xhat) ≤ eps := by
  dsimp only
  obtain ⟨obs, hmem, hout, hgrad⟩ :=
    chargedTrial_output_spec trial M D x0 trace hsmall
  refine ⟨⟨obs, hmem, hout.symm⟩, ?_⟩
  have hobs := hexact obs hmem
  have hgradient : oracle.gradient obs.point = obs.gradient := by
    simpa [O3.PairOracle.observe] using
      (congrArg O3.Observation.gradient hobs).symm
  rw [hout]
  simpa [hgradient] using hgrad

theorem knownParameterAboveTwoUpper : KnownParameterAboveTwoUpperStatement := by
  intro p hp
  refine ⟨trialConstant p + 1, by
    have := trialConstant_pos p hp
    linarith, ?_⟩
  intro d eps L R heps hL hR x0
  let nf := nF p eps L R
  let nd := nD p eps L R
  let trial := aboveLocalTrial p eps x0 nf nd
  let algorithm := chargedTrialAlgorithm p trial L R eps
  refine ⟨algorithm, ?_⟩
  intro inst hinstL hinstR
  let cached : CachedPair d := ⟨inst.oracle.observe x0⟩
  let G := lpNorm (conjugateExponent p) (inst.oracle.gradient x0)
  have hGLR : G ≤ L * R := by
    exact initial_gradient_le_LR inst hp hL hinstL hinstR
  by_cases hsmall0 : G ≤ eps
  · let trace := [inst.oracle.observe x0]
    refine ⟨trace, ?_⟩
    dsimp only
    have hrun : ChargedKnownParameterRun algorithm x0 inst.oracle trace :=
      singleton_charged_run algorithm x0 inst.oracle
    have hsmall : ∃ obs ∈ trace,
        lpNorm (conjugateExponent p) obs.gradient ≤ eps := by
      refine ⟨inst.oracle.observe x0, by simp [trace], ?_⟩
      simpa [G, O3.PairOracle.observe] using hsmall0
    have hout := output_guarantee trial p L R eps x0 inst.oracle trace
      hrun.2.1 hsmall
    refine ⟨hrun, hout.1, hout.2, ?_⟩
    have hpow : 0 ≤ (L * R / eps) ^ (p / (p + 2)) :=
      Real.rpow_nonneg (by positivity) _
    have hC := trialConstant_pos p hp
    simp only [trace, List.length_cons, List.length_nil]
    nlinarith
  · have hG : eps < G := lt_of_not_ge hsmall0
    have hDG : R ≥ G / L := by
      apply (div_le_iff₀ hL).2
      simpa [mul_comm] using hGLR
    obtain ⟨report, w, hexec, hcert, hop, hcalls⟩ :=
      explicit_aboveLocalTrial p hp eps L R heps hL hR x0 cached inst
        (by rfl) hG hDG
    obtain ⟨fuel, hfuel⟩ := hexec
    obtain ⟨suffix, htrace, hgenerated, hexactSuffix⟩ :=
      runFuel_suffix trial inst.oracle hfuel
    simp only [List.nil_append] at htrace
    subst suffix
    rcases hcert with
      ⟨hexactReport, hguardExact, hexhaustive, hsuccess, hscale, hradius⟩
    have hsuccessOutcome : ∃ obs,
        report.outcome = .success obs := by
      rcases hexhaustive with hsucc | hscaleOrRadius
      · exact hsucc
      · rcases hscaleOrRadius with ⟨failed, hfailed⟩ | ⟨terminal, hterminal⟩
        · obtain ⟨_, _, _, _, hlt⟩ := hscale failed hfailed
          rw [hinstL] at hlt
          linarith
        · obtain ⟨_, _, _, _, hlt⟩ := hradius terminal hterminal
          linarith
    obtain ⟨terminal, hterminal⟩ := hsuccessOutcome
    have hterminalData := hsuccess terminal hterminal
    let trace := cached.observation :: report.trace
    have hcharged : ChargedKnownParameterRun algorithm x0 inst.oracle trace := by
      refine ⟨?_, ?_, by simp [trace], by simp [trace, cached, O3.PairOracle.observe]⟩
      · exact chargedTrace_generated trial L R eps x0 cached.observation report.trace
          (by simp [cached, O3.PairOracle.observe]) hgenerated
      · intro obs hmem
        rcases List.mem_cons.mp hmem with hfirst | hrest
        · subst obs
          rfl
        · exact hexactReport obs hrest
    have hsmall : ∃ obs ∈ trace,
        lpNorm (conjugateExponent p) obs.gradient ≤ eps := by
      exact ⟨terminal, by simp [trace, hterminalData.1], hterminalData.2.2.2⟩
    have hout := output_guarantee trial p L R eps x0 inst.oracle trace
      hcharged.2.1 hsmall
    refine ⟨trace, ?_⟩
    dsimp only
    refine ⟨hcharged, hout.1, hout.2, ?_⟩
    have hpow : 0 ≤ (L * R / eps) ^ (p / (p + 2)) :=
      Real.rpow_nonneg (by positivity) _
    have hC := trialConstant_pos p hp
    have hlength : (trace.length : ℝ) = (report.calls : ℝ) + 1 := by
      simp [trace, TrialReport.calls]
    rw [hlength]
    nlinarith

end V7.Stage5AboveTwoLowerS5F

namespace V7

theorem knownParameterAboveTwoUpper : KnownParameterAboveTwoUpperStatement :=
  Stage5AboveTwoLowerS5F.knownParameterAboveTwoUpper

end V7
