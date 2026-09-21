/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.ObjectiveData

/-!
The completed normalized resisting trace is exact, causal, and charges its initial query.
-/

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLowerS5A2Envelope

/-- The finite exact trace of the normalized completed resisting oracle. -/
noncomputable def unitTrace (p : ℝ) (d T : ℕ)
    (algorithm : DeterministicExactPairAlgorithm d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    List (Observation d) :=
  let data := unitCompletionData p d T algorithm hT hTd
  (List.range T).map fun s => data.completedOracle.observe (data.queries s)

lemma completed_partial_map_eq {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d)
    {t : ℕ} (ht : t ≤ T) :
    (List.range t).map (fun s =>
      (unitCompletionData p d T algorithm hT hTd).completedOracle.observe
        ((unitCompletionData p d T algorithm hT hTd).queries s)) =
    (List.range t).map (fun s =>
      ((unitCompletionData p d T algorithm hT hTd).partialOracle s).observe
        ((unitCompletionData p d T algorithm hT hTd).queries s)) := by
  let data := unitCompletionData p d T algorithm hT hTd
  have hassum := unitCompletionData_assumptions algorithm hp hd hT hTd
  have hexact := V7.aboveLowerExactPairCompletion p hp d T data hassum
  apply List.map_congr_left
  intro s hs
  apply hexact s
  exact lt_of_lt_of_le (List.mem_range.mp hs) ht

lemma unitTrace_take {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hT : 1 ≤ T) (hTd : T ≤ d) {t : ℕ} (ht : t ≤ T) :
    (unitTrace p d T algorithm hT hTd).take t =
      (List.range t).map (fun s =>
        (unitCompletionData p d T algorithm hT hTd).completedOracle.observe
          ((unitCompletionData p d T algorithm hT hTd).queries s)) := by
  unfold unitTrace
  ext n
  by_cases hn : n < t
  · have hnT : n < T := lt_of_lt_of_le hn ht
    simp [hn, hnT]
  · simp [hn]

lemma unitTrace_generated {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    GeneratedBy algorithm 0 (unitTrace p d T algorithm hT hTd) := by
  intro t ht
  have htT : t < T := by
    simpa [unitTrace] using ht
  let P := unitParameters p d T algorithm hT hTd
  let data := unitCompletionData p d T algorithm hT hTd
  have hget : ((unitTrace p d T algorithm hT hTd).get ⟨t, ht⟩).point =
      data.queries t := by
    simp [unitTrace, data, O3.PairOracle.observe]
  rw [hget]
  change query P t = if t = 0 then 0 else
    algorithm.nextQuery 0 ((unitTrace p d T algorithm hT hTd).take t)
  rw [query_chronology]
  congr 2
  rw [unitTrace_take algorithm hT hTd (Nat.le_of_lt htT)]
  simpa [P, data, unitCompletionData, completionData] using
    (completed_partial_map_eq algorithm hp hd hT hTd (Nat.le_of_lt htT)).symm

lemma unitTrace_exact {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hT : 1 ≤ T) (hTd : T ≤ d) :
    TraceExact (unitCompletionData p d T algorithm hT hTd).completedOracle
      (unitTrace p d T algorithm hT hTd) := by
  intro obs hobs
  simp only [unitTrace, List.mem_map, List.mem_range] at hobs
  rcases hobs with ⟨s, -, rfl⟩
  rfl

lemma unitTrace_head_point {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hT : 1 ≤ T) (hTd : T ≤ d) :
    ((unitTrace p d T algorithm hT hTd).head?.map O3.Observation.point) =
      some (0 : Point d) := by
  have hTpos : 0 < T := hT
  have hhead : (List.range T).head? = some 0 := by
    rw [List.head?_eq_getElem?]
    simp [hTpos]
  unfold unitTrace
  rw [List.head?_map, hhead]
  simp [unitCompletionData, completionData, query, stepQuery,
    unitParameters, O3.PairOracle.observe]

theorem unitChargedRun {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    ChargedKnownParameterRun algorithm 0
      (unitCompletionData p d T algorithm hT hTd).completedOracle
      (unitTrace p d T algorithm hT hTd) := by
  refine ⟨unitTrace_generated algorithm hp hd hT hTd,
    unitTrace_exact algorithm hT hTd, ?_, unitTrace_head_point algorithm hT hTd⟩
  intro hnil
  have hlen := congrArg List.length hnil
  simp [unitTrace] at hlen
  omega

end V7.Stage5AboveTwoLowerS5F
