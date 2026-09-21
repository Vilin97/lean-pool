/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.Refinement
import LeanPool.ParameterFreeGradient.V7.Proofs.Anchor

namespace V7.Stage8Main

def runtimeDataFromAnchor (input : MethodInput d) (hp : 1 < input.p)
    (heps : 0 < input.eps) (hM0 : 0 < input.M0) (cached : CachedPair d)
    (G : ℝ) (hGdef : G = lpNorm (conjugateExponent input.p)
      cached.observation.gradient) (hG : 0 < G)
    (anchorResult : O3.AnchorResult d) : RuntimeData d :=
  { input := input
    hp := hp
    heps := heps
    hM0 := hM0
    cached := cached
    G := G
    G_eq := hGdef
    hG := hG
    anchorEpoch := anchorResult.epoch
    anchorTrace := anchorResult.observations }

theorem currentMethod_early_run (oracle : PairOracle d) (input : MethodInput d)
    (hp : 1 < input.p) (heps : 0 < input.eps) (hM0 : 0 < input.M0)
    (hsmall : lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0) ≤ input.eps) :
    (currentMethod d).run oracle input.toO3 2 =
      some { returned := input.x0, queries := [oracle.observe input.x0] } := by
  simp [O3.FirstOrderMethod.run, O3.FirstOrderMethod.runFuel, currentMethod,
    currentMethodAction, MethodInput.toO3, O3.PairOracle.observe, hp, heps, hM0,
    hsmall]

theorem currentMethod_anchor_splice (oracle : PairOracle d)
    (input : MethodInput d) (hp : 1 < input.p) (heps : 0 < input.eps)
    (hM0 : 0 < input.M0) (cached : CachedPair d)
    (hcached : cached.observation = oracle.observe input.x0)
    (G : ℝ) (hGdef : G = lpNorm (conjugateExponent input.p)
      cached.observation.gradient) (hG : 0 < G) :
    ∀ {anchorFuel epoch : ℕ} {anchorHistory : List (Observation d)}
      {anchorResult : O3.AnchorResult d} {publicPrefix : List (Observation d)}
      {tailFuel : ℕ} {result : O3.RunResult d},
      O3.runAnchor oracle
          (O3.anchorPrefixConfig input.toO3 cached.observation.value
            cached.observation.gradient G)
          anchorFuel epoch anchorHistory = some anchorResult →
      (currentMethod d).runFuel oracle tailFuel
          (.controllerReady
            (runtimeDataFromAnchor input hp heps hM0 cached G hGdef hG anchorResult)
            initialRuntimeControllerState)
          (publicPrefix ++ anchorResult.observations) = some result →
      ∃ methodFuel,
        (currentMethod d).runFuel oracle methodFuel
            (.anchoring input hp heps hM0 cached G hGdef hG epoch anchorHistory)
            (publicPrefix ++ anchorHistory) = some result := by
  intro anchorFuel
  induction anchorFuel with
  | zero =>
      intro epoch anchorHistory anchorResult publicPrefix tailFuel result hrun
      simp [O3.runAnchor] at hrun
  | succ anchorFuel ih =>
      intro epoch anchorHistory anchorResult publicPrefix tailFuel result hrun htail
      let cfg := O3.anchorPrefixConfig input.toO3 cached.observation.value
        cached.observation.gradient G
      let D := O3.anchorRadius cfg.G cfg.M₀ epoch
      let y := O3.anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      rw [O3.runAnchor] at hrun
      by_cases hpass : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [cfg, D, y] at hpass
        simp only [hpass, ↓reduceIte] at hrun
        injection hrun with hresult
        subst anchorResult
        refine ⟨tailFuel + 1, ?_⟩
        dsimp only [currentMethod]
        rw [O3.FirstOrderMethod.runFuel]
        simp only [currentMethodAction]
        simp only [O3.PairOracle.observe, hpass, ↓reduceIte]
        simpa [currentMethod, O3.PairOracle.observe, runtimeDataFromAnchor,
          O3.anchorPrefixConfig, List.append_assoc] using htail
      · dsimp only [cfg, D, y] at hpass
        simp only [hpass, ↓reduceIte] at hrun
        obtain ⟨methodFuel, hmethod⟩ := ih
          (publicPrefix := publicPrefix) hrun htail
        refine ⟨methodFuel + 1, ?_⟩
        dsimp only [currentMethod]
        rw [O3.FirstOrderMethod.runFuel]
        simp only [currentMethodAction]
        simp only [O3.PairOracle.observe, hpass, ↓reduceIte]
        simpa [currentMethod, O3.PairOracle.observe, cfg, y,
          O3.anchorPrefixConfig, List.append_assoc] using hmethod

theorem currentMethod_full_splice (oracle : PairOracle d)
    (input : MethodInput d) (hp : 1 < input.p) (heps : 0 < input.eps)
    (hM0 : 0 < input.M0)
    (hlarge : input.eps < lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0))
    {anchorFuel : ℕ} {anchorResult : O3.AnchorResult d}
    {tailFuel : ℕ} {result : O3.RunResult d}
    (hrun : O3.runAnchor oracle
      (O3.anchorPrefixConfig input.toO3 (oracle.value input.x0)
        (oracle.gradient input.x0)
        (lpNorm (conjugateExponent input.p) (oracle.gradient input.x0)))
      anchorFuel 0 [] = some anchorResult)
    (htail : (currentMethod d).runFuel oracle tailFuel
      (.controllerReady
        (runtimeDataFromAnchor input hp heps hM0
          ⟨oracle.observe input.x0⟩
          (lpNorm (conjugateExponent input.p) (oracle.gradient input.x0))
          (by simp [O3.PairOracle.observe])
          (heps.trans hlarge) anchorResult)
        initialRuntimeControllerState)
      ([oracle.observe input.x0] ++ anchorResult.observations) = some result) :
    ∃ methodFuel,
      (currentMethod d).run oracle input.toO3 methodFuel = some result := by
  let cached : CachedPair d := ⟨oracle.observe input.x0⟩
  have hcached : cached.observation = oracle.observe input.x0 := rfl
  obtain ⟨methodFuel, hmethod⟩ := currentMethod_anchor_splice oracle input
    hp heps hM0 cached hcached
    (lpNorm (conjugateExponent input.p) (oracle.gradient input.x0))
    (by simp [cached, O3.PairOracle.observe]) (heps.trans hlarge)
    (publicPrefix := [oracle.observe input.x0]) hrun htail
  have hnot : ¬lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0) ≤ input.eps := not_le.mpr hlarge
  have hvalid : 1 < input.p ∧ 0 < input.eps ∧ 0 < input.M0 :=
    ⟨hp, heps, hM0⟩
  refine ⟨methodFuel + 1, ?_⟩
  unfold O3.FirstOrderMethod.run
  dsimp only [currentMethod]
  rw [O3.FirstOrderMethod.runFuel]
  simp only [currentMethodAction, MethodInput.toO3, O3.PairOracle.observe]
  simp [hvalid, hnot]
  simpa [currentMethod, O3.PairOracle.observe, cached] using hmethod

end V7.Stage8Main
