/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.GuardAdapters
import LeanPool.ParameterFreeGradient.O3.Stage3Anchor

/-!
The anchor-search theorem transported to the current positive secant interface.
-/

namespace V7

private noncomputable def toAdmissibleInstance (p : ℝ) (hp : 1 < p)
    (input : MethodInput d) (inst : PositiveInstance p d input.x0)
    (hip : input.p = p) (heps : 0 < input.eps)
    (hsec : SecantInitialization input inst.oracle) :
    O3.AdmissibleInstance d p where
  f := inst.oracle.value
  grad := inst.oracle.gradient
  L := inst.L
  eps := input.eps
  x0 := input.x0
  z0 := input.z0
  M0 := input.M0
  p_gt_one := hp
  L_pos := inst.L_pos
  eps_pos := heps
  gradient_spec := inst.coordinateGradient
  convex := inst.convex
  minimizer_nonempty := inst.minimizerNonempty
  smooth := inst.smooth
  secant := by
    rcases hsec with ⟨hx, hg, hM, hMpos⟩
    refine ⟨hx, hg, ?_, hMpos⟩
    simpa [hip] using hM

private theorem mapped_anchor_trace_head (oracle : PairOracle d)
    (y : ℕ → Point d) {k accepted : ℕ} (hk : k < accepted + 1) :
    ((((List.range (accepted + 1)).map fun i => oracle.observe (y i)).drop k).head?) =
      some (oracle.observe (y k)) := by
  rw [List.head?_drop]
  simp [hk]

private theorem mapped_anchor_trace_exact (oracle : PairOracle d)
    (y : ℕ → Point d) (accepted : ℕ) :
    TraceExact oracle ((List.range (accepted + 1)).map fun i => oracle.observe (y i)) := by
  intro obs hobs
  simp only [List.mem_map, List.mem_range] at hobs
  rcases hobs with ⟨k, _, rfl⟩
  rfl

theorem anchor : AnchorStatement := by
  intro p hp d input inst hip heps hsec hM0L cached hcached hG
  let P := toAdmissibleInstance p hp input inst hip heps hsec
  let cfg := P.anchorConfig
  let N := Nat.ceil (Real.logb 2 (P.L / P.M0))
  have hlarge : P.eps < cfg.G := by
    simpa [P, cfg, toAdmissibleInstance, O3.AdmissibleInstance.anchorConfig]
      using hG
  have hOld := O3.anchor p d P hlarge
  obtain ⟨oldResult, hrun, hscaleEq, hradiusEq, hpointEq, haccept,
      hscaleLt, hradiusLe, hcount, htrace⟩ := hOld
  let accepted := oldResult.epoch
  let G := lpNorm (conjugateExponent p) (inst.oracle.gradient input.x0)
  let Mfun : ℕ → ℝ := fun k => (2 : ℝ) ^ k * input.M0
  let Dfun : ℕ → ℝ := fun k => G / Mfun k
  let yfun : ℕ → Point d := fun k =>
    input.x0 - Dfun k • normingDirection (conjugateExponent p)
      cached.observation.gradient
  let trace : List (Observation d) :=
    (List.range (accepted + 1)).map fun k => inst.oracle.observe (yfun k)
  let run : AnchorRunData d :=
    { acceptedIndex := accepted, M := Mfun, D := Dfun, y := yfun, trace := trace }
  have hcfg : cfg = P.anchorConfig := rfl
  have hcacheGrad : cached.observation.gradient = inst.oracle.gradient input.x0 := by
    rw [hcached]
    rfl
  have hnorming : ∀ k, yfun k =
      O3.anchorProbePoint (conjugateExponent p) input.x0
        (inst.oracle.gradient input.x0) G input.M0 k := by
    intro k
    simp only [yfun, O3.anchorProbePoint, O3.anchorRadius, O3.anchorScale,
      Dfun, Mfun, hcacheGrad, G, normingDirection_eq_anchorNormingVector]
  have hrunFacts :
      (∀ k < accepted,
        ¬ AnchorTest inst.oracle input.x0 G (Dfun k) (yfun k)) ∧
      AnchorTest inst.oracle input.x0 G (Dfun accepted) (yfun accepted) := by
    have hsemantic : ∀ {fuel start : ℕ} {history : List (Observation d)}
        {result : O3.AnchorResult d},
        O3.runAnchor P.oracle cfg fuel start history = some result →
        (∀ k, start ≤ k → k < result.epoch →
          ¬ O3.AnchorTest P.f P.x0 cfg.G
            (O3.anchorRadius cfg.G cfg.M₀ k)
            (O3.anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ k)) ∧
        O3.AnchorTest P.f P.x0 cfg.G result.acceptedRadius result.acceptedPoint := by
      intro fuel
      induction fuel with
      | zero =>
          intro start history result hs
          simp [O3.runAnchor] at hs
      | succ fuel ih =>
          intro start history result hs
          rw [O3.runAnchor] at hs
          by_cases hpass :
              P.oracle.value (O3.anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start) ≤
                cfg.f₀ - cfg.G * O3.anchorRadius cfg.G cfg.M₀ start / 2
          · simp only [hpass, ↓reduceIte] at hs
            injection hs with hrs
            subst result
            constructor
            · intro k hsk hk
              change k < start at hk
              omega
            · exact hpass
          · simp only [hpass, ↓reduceIte] at hs
            obtain ⟨hreject, hacc⟩ := ih hs
            constructor
            · intro k hsk hk
              by_cases hks : k = start
              · subst k
                exact hpass
              · exact hreject k (by omega) hk
            · exact hacc
    have hs := hsemantic hrun
    constructor
    · intro k hk
      have hkold := hs.1 k (by omega) (by simpa [accepted] using hk)
      simpa [P, cfg, toAdmissibleInstance, O3.AdmissibleInstance.anchorConfig,
        O3.AdmissibleInstance.oracle, G, Dfun, Mfun, hnorming k,
        O3.anchorRadius, O3.anchorScale, AnchorTest, O3.AnchorTest] using hkold
    · have ha := hs.2
      rw [hradiusEq, hpointEq] at ha
      simpa [P, cfg, toAdmissibleInstance, O3.AdmissibleInstance.anchorConfig,
        O3.AdmissibleInstance.oracle, accepted, G, Dfun, Mfun,
        hnorming accepted, hscaleEq, O3.anchorRadius, O3.anchorScale,
        AnchorTest, O3.AnchorTest] using ha
  refine ⟨run, ?_, ?_⟩
  · dsimp only [AnchorExecution]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; rfl
    · intro k
      simp [run, Dfun, Mfun, G, hcacheGrad]
    · intro k; rfl
    · simp [run, trace]
    · intro k hk
      refine ⟨inst.oracle.observe (yfun k), ?_, rfl⟩
      apply mapped_anchor_trace_head inst.oracle yfun
      simpa [run, trace] using hk
    · simpa [run, G, hcacheGrad] using hrunFacts.1
    · simpa [run, G, hcacheGrad] using hrunFacts.2
  · dsimp only
    have hM0 : 0 < input.M0 := hsec.2.2.2
    have hMaPos : 0 < Mfun accepted := mul_pos (pow_pos (by norm_num) _) hM0
    have hMaEq : Mfun accepted = oldResult.acceptedScale := by
      rw [hscaleEq]
      rfl
    have hDaEq : Dfun accepted = oldResult.acceptedRadius := by
      rw [hradiusEq]
      simp [P, toAdmissibleInstance, O3.AdmissibleInstance.anchorConfig,
        Dfun, G, hMaEq]
    refine ⟨hMaPos, by simp [run, Dfun, Mfun, G], ?_, ?_,
      mapped_anchor_trace_exact inst.oracle yfun accepted, ?_⟩
    · simpa [run, accepted, hMaEq, P, toAdmissibleInstance] using hscaleLt
    · simpa [run, accepted, hDaEq, P, toAdmissibleInstance,
        O3.AdmissibleInstance.radius, PositiveInstance.R, minimizerDistance]
        using hradiusLe
    · have hcountNat : accepted + 1 ≤ 1 + N := by
        have hepoch := O3.runAnchor_epoch_lt P.oracle cfg hrun
        simpa [accepted, N] using hepoch
      have harg0 : 0 ≤ Real.log (inst.L / input.M0) / Real.log 2 := by
        have hratio : 1 ≤ inst.L / input.M0 := (le_div_iff₀ hM0).2 (by simpa using hM0L)
        exact div_nonneg (Real.log_nonneg hratio) (Real.log_nonneg (by norm_num))
      have hceil :
          ((Nat.ceil (Real.log (inst.L / input.M0) / Real.log 2) : ℕ) : ℝ) =
            (⌈Real.log (inst.L / input.M0) / Real.log 2⌉ : ℤ) := by
        exact_mod_cast Int.natCast_ceil_eq_ceil harg0
      have hN : N = Nat.ceil (Real.log (inst.L / input.M0) / Real.log 2) := by
        rfl
      rw [show run.trace.length = accepted + 1 by simp [run, trace]]
      rw [hN] at hcountNat
      exact_mod_cast (show (accepted : ℝ) + 1 ≤
        1 + (⌈Real.log (inst.L / input.M0) / Real.log 2⌉ : ℤ) by
          rw [← hceil]
          exact_mod_cast hcountNat)

end V7
