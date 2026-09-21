/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.PrefixState

namespace V7.Stage5AboveTwoLowerS5F

lemma obsPrefix_succ (P : PrefixParameters p d T) (t : ℕ) :
    (prefixState P (t + 1)).obsPrefix =
      (prefixState P t).obsPrefix ++
        [(partialOracle P t).observe (query P t)] := by
  rfl

/-- The load-bearing causal invariant: the stored prefix is exactly the list
of chronological partial-oracle observations appearing in the frozen carrier. -/
theorem obsPrefix_eq_map_range (P : PrefixParameters p d T) (t : ℕ) :
    (prefixState P t).obsPrefix =
      (List.range t).map (fun s => (partialOracle P s).observe (query P s)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [obsPrefix_succ, ih, List.range_succ, List.map_append]
      rfl

lemma query_chronology (P : PrefixParameters p d T) (t : ℕ) :
    query P t = if t = 0 then 0 else
      P.algorithm.nextQuery 0
        ((List.range t).map
          (fun s => (partialOracle P s).observe (query P s))) := by
  rw [query, stepQuery, obsPrefix_eq_map_range]

lemma obsPrefix_take {P : PrefixParameters p d T} {t u : ℕ} (htu : t ≤ u) :
    (prefixState P u).obsPrefix.take t = (prefixState P t).obsPrefix := by
  rw [obsPrefix_eq_map_range, obsPrefix_eq_map_range]
  ext n
  by_cases hn : n < t
  · have hnu : n < u := lt_of_lt_of_le hn htu
    simp [hn, hnu]
  · simp [hn]

lemma obsPrefix_getElemOption {P : PrefixParameters p d T} {s t : ℕ} (hst : s < t) :
    (prefixState P t).obsPrefix[s]? =
      some ((partialOracle P s).observe (query P s)) := by
  rw [obsPrefix_eq_map_range]
  simp [hst]

lemma obsPrefix_ne_nil {P : PrefixParameters p d T} {t : ℕ} (ht : 0 < t) :
    (prefixState P t).obsPrefix ≠ [] := by
  exact List.ne_nil_of_length_pos (by simpa [(prefix_lengths P t).2.2])

end V7.Stage5AboveTwoLowerS5F
