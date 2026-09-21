/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.RateAlgebra

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLowerS5A2Envelope

theorem physical_query_gradient {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d)
    (x0 : Point d) {L R rT : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hrT : 0 < rT) (hrTupper : rT < 4) {t : ℕ} (ht : t < T) :
    let normAlg := normalizedAdversaryAlgorithm x0 L R rT algorithm
    let data := unitObjectiveData p d T normAlg hT hTd
    lpNorm (conjugateExponent p)
        ((physicalOracle x0 L R rT data.completedOracle).gradient
          (physicalForward x0 R rT (data.queries t))) ≥
      L * R / (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
  dsimp only
  let normAlg := normalizedAdversaryAlgorithm x0 L R rT algorithm
  let data := unitObjectiveData p d T normAlg hT hTd
  have hassum := unitObjectiveData_assumptions normAlg hp hd hT hTd
  have hbar := V7.aboveLowerBaseGradient p hp d T data hassum t ht
  change lpNorm (conjugateExponent p)
      (data.completedOracle.gradient (data.queries t)) ≥
    1 / (128 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) at hbar
  let B := L * R / rT
  have hB : 0 < B := by dsimp [B]; positivity
  have hq := O3.one_lt_conjugateExponent (by linarith : 1 < p)
  change lpNorm (conjugateExponent p)
      (B • data.completedOracle.gradient
        (physicalBackward x0 R rT (physicalForward x0 R rT (data.queries t)))) ≥ _
  rw [physicalBackward_forward x0 hR hrT]
  change O3.lpNorm (conjugateExponent p)
      (B • data.completedOracle.gradient (data.queries t)) ≥ _
  rw [O3.Stage2RouteC.lpNorm_smul hq.le, abs_of_pos hB]
  have hden : 0 < repairMpd p d * (T : ℝ) ^ (1 + 2 / p) :=
    mul_pos (repairMpd_pos hp hd) (Real.rpow_pos_of_pos (by positivity) _)
  have hLR : 0 < L * R := mul_pos hL hR
  have hBquarter : L * R / 4 < B := by
    dsimp [B]
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hrT]
    nlinarith
  have hbarPos : 0 < lpNorm (conjugateExponent p)
      (data.completedOracle.gradient (data.queries t)) := by
    have htarget : 0 < 1 / (128 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
      apply one_div_pos.mpr
      exact mul_pos (mul_pos (by norm_num) (repairMpd_pos hp hd))
        (Real.rpow_pos_of_pos (by positivity) _)
    linarith
  apply le_of_lt
  calc
    B * lpNorm (conjugateExponent p)
        (data.completedOracle.gradient (data.queries t)) >
      (L * R / 4) * lpNorm (conjugateExponent p)
        (data.completedOracle.gradient (data.queries t)) :=
      mul_lt_mul_of_pos_right hBquarter hbarPos
    _ ≥ (L * R / 4) *
        (1 / (128 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p))) :=
      mul_le_mul_of_nonneg_left hbar (by positivity)
    _ = L * R / (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
      field_simp [hden.ne']
      ring

theorem physical_charged_run {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d)
    (x0 : Point d) {L R rT : ℝ} (hR : 0 < R) (hrT : 0 < rT) :
    let normAlg := normalizedAdversaryAlgorithm x0 L R rT algorithm
    let data := unitObjectiveData p d T normAlg hT hTd
    let trace := physicalTrace x0 L R rT (unitTrace p d T normAlg hT hTd)
    ChargedKnownParameterRun algorithm x0
      (physicalOracle x0 L R rT data.completedOracle) trace := by
  dsimp only
  let normAlg := normalizedAdversaryAlgorithm x0 L R rT algorithm
  let barTrace := unitTrace p d T normAlg hT hTd
  let data := unitObjectiveData p d T normAlg hT hTd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact physicalTrace_generated x0 hR hrT algorithm barTrace
      (unitTrace_generated normAlg hp hd hT hTd)
  · exact physicalTrace_exact x0 hR hrT data.completedOracle barTrace
      (unitTrace_exact normAlg hT hTd)
  · intro hnil
    have hlen := congrArg List.length hnil
    simp [physicalTrace, barTrace, unitTrace] at hlen
    omega
  · exact physicalTrace_head_point x0 barTrace
      (unitTrace_head_point normAlg hT hTd)

theorem _root_.V7.knownParameterAboveTwoLower :
    KnownParameterAboveTwoLowerStatement := by
  let C : ℝ := 15 * Real.exp (2 / 3)
  refine ⟨C, by positivity, ?_⟩
  intro p hp d T hd hT hTd L R hL hR x0 algorithm
  let kernel := repairKernel p d
  have hkernel := repairKernel_assumptions hp hd
  obtain ⟨rT, hrTlower, hrTupper, hradiusAll⟩ :=
    V7.aboveLowerOptimizerRadius p hp d T hd hT hTd kernel hkernel
  have hrT : 0 < rT := by linarith
  let normAlg := normalizedAdversaryAlgorithm x0 L R rT algorithm
  let data := unitObjectiveData p d T normAlg hT hTd
  have hassum : LowerObjectiveAssumptions data :=
    unitObjectiveData_assumptions normAlg hp hd hT hTd
  have hradius : minimizerDistance p data.completedOracle 0 = rT := by
    symm
    exact hradiusAll data rfl hassum
  let barInst := unitPositiveInstance normAlg hp hd hT hTd
  have hbarOracle : barInst.oracle = data.completedOracle := rfl
  let inst : PositiveInstance p d x0 :=
    { oracle := physicalOracle x0 L R rT data.completedOracle
      L := L
      L_pos := hL
      coordinateGradient := physicalOracle_coordinateGradient (p := p) x0 hL hR hrT
        data.completedOracle hassum.2.2
      convex := physicalOracle_convex x0 hL hR hrT data.completedOracle hassum.2.1
      minimizerNonempty := physical_minimizerNonempty x0 hL hR hrT
        data.completedOracle barInst.minimizerNonempty
      smooth := physicalOracle_smooth hp x0 hL hR hrT data.completedOracle
        (unitCompleted_smooth normAlg hp hd hT hTd) }
  let trace := physicalTrace x0 L R rT (unitTrace p d T normAlg hT hTd)
  have hquery : ∀ t < T, ∃ obs : Observation d,
      (trace.drop t).head? = some obs ∧
      lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≥
        L * R / (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
    intro t ht
    let barObs := data.completedOracle.observe (data.queries t)
    let obs := physicalObservation x0 L R rT barObs
    refine ⟨obs, ?_, ?_⟩
    · rw [List.head?_drop]
      simp [trace, physicalTrace, unitTrace, obs, barObs, ht,
        data, unitObjectiveData]
    · have hpoint : obs.point = physicalForward x0 R rT (data.queries t) := by
        rfl
      rw [hpoint]
      exact physical_query_gradient algorithm hp hd hT hTd x0 hL hR hrT hrTupper ht
  have hnoSmall : ∀ eps : ℝ,
      eps < L * R / (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) →
      ¬ ∃ t < T, ∃ obs : Observation d,
        (trace.drop t).head? = some obs ∧
        lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≤ eps := by
    intro eps hepsSmall hsuccess
    rcases hsuccess with ⟨t, ht, obs, hhead, hsmall⟩
    obtain ⟨obs', hhead', hlower⟩ := hquery t ht
    have hobs : obs = obs' := Option.some.inj (hhead.symm.trans hhead')
    subst obs'
    linarith
  refine ⟨inst, trace, repairMpd p d, rfl, ?_, ?_, ?_,
    repairMpd_pos hp hd, ?_, repairMpd_universal_bound hp hd, ?_⟩
  · change minimizerDistance p (physicalOracle x0 L R rT data.completedOracle) x0 = R
    exact physical_minimizerDistance hp x0 hL hR hrT data.completedOracle hradius
  · exact physical_charged_run algorithm hp hd hT hTd x0 hR hrT
  · simp [trace, physicalTrace, unitTrace]
  · rfl
  · intro t ht
    obtain ⟨obs, hhead, hlower⟩ := hquery t ht
    refine ⟨obs, hhead, hlower, ?_, ?_, ?_⟩
    · intro eps heps hepsSmall hsuccess
      exact hnoSmall eps hepsSmall hsuccess
    · intro eps heps hpower hsuccess
      have hminPos : 0 < min p (Real.log d) := by
        have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast
          (lt_of_lt_of_le (by decide : 1 < 2) hd))
        exact lt_min_iff.mpr ⟨by linarith, hlog⟩
      have hK : 0 < 512 * C * min p (Real.log d) := by positivity
      have hpower' : (T : ℝ) <
          (L * R / ((512 * C * min p (Real.log d)) * eps)) ^ (p / (p + 2)) := by
        convert hpower using 1 <;> ring
      have hepsSmall := rate_power_implication hp (by positivity : (0 : ℝ) < T)
        (mul_pos hL hR) hK heps hpower'
      have hMbound : repairMpd p d ≤ C * min p (Real.log d) :=
        repairMpd_universal_bound hp hd
      have hdenT : 0 < (T : ℝ) ^ (1 + 2 / p) := by positivity
      have hthreshold : L * R /
          (512 * C * min p (Real.log d) * (T : ℝ) ^ (1 + 2 / p)) ≤
        L * R /
          (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
        have hm := mul_le_mul_of_nonneg_left hMbound (by norm_num : (0 : ℝ) ≤ 512)
        have hdenLe := mul_le_mul_of_nonneg_right hm hdenT.le
        have hdenLe' : 512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p) ≤
            512 * C * min p (Real.log d) * (T : ℝ) ^ (1 + 2 / p) := by
          calc
            _ ≤ 512 * (C * min p (Real.log d)) *
                (T : ℝ) ^ (1 + 2 / p) := hdenLe
            _ = _ := by ring
        exact div_le_div_of_nonneg_left (mul_nonneg hL.le hR.le)
          (mul_pos (mul_pos (by norm_num) (repairMpd_pos hp hd)) hdenT) hdenLe'
      exact hnoSmall eps (lt_of_lt_of_le hepsSmall hthreshold) hsuccess
    · intro hpLog eps heps hpower hsuccess
      have hK : 0 < 2560 * p := by positivity
      have hepsSmall := rate_power_implication hp (by positivity : (0 : ℝ) < T)
        (mul_pos hL hR) hK heps hpower
      have hMbound : repairMpd p d ≤ 5 * p := by
        unfold repairMpd
        rw [if_pos hpLog]
      have hdenT : 0 < (T : ℝ) ^ (1 + 2 / p) := by positivity
      have hthreshold : L * R / (2560 * p * (T : ℝ) ^ (1 + 2 / p)) ≤
        L * R / (512 * repairMpd p d * (T : ℝ) ^ (1 + 2 / p)) := by
        have hm := mul_le_mul_of_nonneg_left hMbound (by norm_num : (0 : ℝ) ≤ 512)
        have hm' : 512 * repairMpd p d ≤ 2560 * p := by
          calc
            _ ≤ 512 * (5 * p) := hm
            _ = 2560 * p := by ring
        have hdenLe := mul_le_mul_of_nonneg_right hm' hdenT.le
        exact div_le_div_of_nonneg_left (mul_nonneg hL.le hR.le)
          (mul_pos (mul_pos (by norm_num) (repairMpd_pos hp hd)) hdenT) hdenLe
      exact hnoSmall eps (lt_of_lt_of_le hepsSmall hthreshold) hsuccess

end V7.Stage5AboveTwoLowerS5F
