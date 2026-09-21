/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Semantics

/-!
Consecutive below-two guard checks match the cached observation and the two phase traces.
-/

namespace V7.Stage3BelowTwoS3F

/-- The cocoercivity checks between consecutive observations, starting from a cached observation. -/
noncomputable def chainChecks (first : Observation d) : List (Observation d) →
    List (ObservableGuardCheck d)
  | [] => []
  | obs :: rest => cocoCheck first obs :: chainChecks obs rest

@[simp] theorem chainChecks_length (first : Observation d) (trace) :
    (chainChecks first trace).length = trace.length := by
  induction trace generalizing first with
  | nil => rfl
  | cons obs rest ih => simp [chainChecks, ih]

theorem chainChecks_append (first : Observation d) (xs ys : List (Observation d)) :
    chainChecks first (xs ++ ys) = chainChecks first xs ++
      chainChecks (xs.getLastD first) ys := by
  induction xs generalizing first with
  | nil => simp [chainChecks]
  | cons x xs ih =>
      cases xs with
      | nil => simp [chainChecks]
      | cons y rest =>
          change cocoCheck first x :: chainChecks x ((y :: rest) ++ ys) =
            cocoCheck first x ::
              (chainChecks x (y :: rest) ++
                chainChecks ((x :: y :: rest).getLastD first) ys)
          rw [ih x]
          rfl

theorem chainChecks_kinds (first : Observation d) (trace) :
    ∀ check ∈ chainChecks first trace, check.kind = .cocoercivity := by
  induction trace generalizing first with
  | nil => simp [chainChecks]
  | cons obs rest ih =>
      intro check hcheck
      simp only [chainChecks, List.mem_cons] at hcheck
      rcases hcheck with rfl | hcheck
      · rfl
      · exact ih obs check hcheck

theorem chainChecks_ledger (cached : CachedPair d) (trace : List (Observation d)) :
    ConsecutiveGuardLedger cached ⟨trace, chainChecks cached.observation trace,
      .radius cached.observation⟩ := by
  intro i hi
  induction trace generalizing cached i with
  | nil => simp [chainChecks] at hi
  | cons obs rest ih =>
      cases i with
      | zero =>
          refine ⟨cocoCheck cached.observation obs, by simp [chainChecks],
            by simp [cocoCheck], by simp [cocoCheck]⟩
      | succ i =>
          have hi' : i < (chainChecks obs rest).length := by
            simpa [chainChecks] using hi
          obtain ⟨check, hc, hx, hy⟩ := ih ⟨obs⟩ i hi'
          refine ⟨check, ?_, ?_, ?_⟩
          · simpa [chainChecks] using hc
          · simpa using hx
          · simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hy

theorem chainChecks_ledger_prefix (cached : CachedPair d)
    (pre suf : List (Observation d)) :
    ConsecutiveGuardLedger cached
      ⟨pre ++ suf, chainChecks cached.observation pre,
        .radius cached.observation⟩ := by
  intro i hi
  have hiPre : i < pre.length := by
    simpa [chainChecks_length] using hi
  obtain ⟨check, hc, hx, hy⟩ := chainChecks_ledger cached pre i hi
  refine ⟨check, hc, ?_, ?_⟩
  · have hne : (cached.observation :: pre).drop i ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    rw [show cached.observation :: (pre ++ suf) =
      (cached.observation :: pre) ++ suf by simp,
      List.drop_append_of_le_length (show i ≤
        (cached.observation :: pre).length by simp; omega),
      List.head?_append_of_ne_nil _ hne]
    exact hx
  · have hne : (cached.observation :: pre).drop (i + 1) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    rw [show cached.observation :: (pre ++ suf) =
      (cached.observation :: pre) ++ suf by simp,
      List.drop_append_of_le_length (show i + 1 ≤
        (cached.observation :: pre).length by simp; omega),
      List.head?_append_of_ne_nil _ hne]
    simpa using hy

theorem chainChecks_data_exact (cached : CachedPair d) (oracle : PairOracle d)
    (trace : List (Observation d))
    (hcached : cached.observation = oracle.observe cached.observation.point)
    (htrace : TraceExact oracle trace) :
    GuardDataExact cached oracle
      ⟨trace, chainChecks cached.observation trace, .radius cached.observation⟩ := by
  refine ⟨hcached, ?_⟩
  induction trace generalizing cached with
  | nil => simp [chainChecks]
  | cons obs rest ih =>
      intro check hcheck
      simp only [chainChecks, List.mem_cons] at hcheck
      have hobs : obs = oracle.observe obs.point := htrace obs (by simp)
      rcases hcheck with rfl | hrest
      · refine ⟨Or.inl (by simp [cocoCheck]), Or.inr (by simp [cocoCheck]),
          by simpa [cocoCheck] using hcached, by simpa [cocoCheck] using hobs⟩
      · have htail : TraceExact oracle rest := by
          intro o ho
          exact htrace o (by simp [ho])
        have hr := ih ⟨obs⟩ hobs htail check hrest
        rcases hr with ⟨hx, hy, hex, hey⟩
        refine ⟨?_, ?_, hex, hey⟩
        · rcases hx with hx | hx
          · exact Or.inr (by simp [hx])
          · exact Or.inr (by simp [hx])
        · rcases hy with hy | hy
          · exact Or.inr (by simp [hy])
          · exact Or.inr (by simp [hy])

theorem chainChecks_data_exact_prefix (cached : CachedPair d)
    (oracle : PairOracle d) (pre suf : List (Observation d))
    (hcached : cached.observation = oracle.observe cached.observation.point)
    (hpre : TraceExact oracle pre) :
    GuardDataExact cached oracle
      ⟨pre ++ suf, chainChecks cached.observation pre,
        .radius cached.observation⟩ := by
  have h := chainChecks_data_exact cached oracle pre hcached hpre
  refine ⟨h.1, ?_⟩
  intro check hcheck
  obtain ⟨hx, hy, hex, hey⟩ := h.2 check hcheck
  refine ⟨?_, ?_, hex, hey⟩
  · rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_append_left _ hx)
  · rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (List.mem_append_left _ hy)

theorem cocoPairHolds_iff_not_fails (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) :
    cocoPairHolds p M (oracle.observe x) (oracle.observe y) ↔
      ¬ GuardFails p M oracle (cocoCheck (oracle.observe x) (oracle.observe y)).failure := by
  simp [cocoPairHolds, cocoCheck, ObservableGuardCheck.failure, GuardFails,
    CocoercivityGuard, BregmanRemainder, O3.PairOracle.observe]

theorem phaseOneTrace_lastD (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    (phaseOneNewTrace p eps M D x0 oracle m).getLastD
      (phaseOneObs p eps M D x0 oracle 0) =
        phaseOneObs p eps M D x0 oracle m := by
  cases m with
  | zero => simp [phaseOneNewTrace]
  | succ m => rw [phaseOneTrace_succ]; simp

theorem phaseTwoTrace_lastD (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    (phaseTwoNewTrace p eps M D x0 oracle m).getLastD
      (phaseTwoObs p eps M D x0 oracle 0) =
        phaseTwoObs p eps M D x0 oracle m := by
  cases m with
  | zero => simp [phaseTwoNewTrace]
  | succ m => rw [phaseTwoTrace_succ]; simp

theorem phaseOne_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    chainChecks (phaseOneObs p eps M D x0 oracle 0)
      (phaseOneNewTrace p eps M D x0 oracle m) =
        phaseOneChecks p eps M D x0 oracle m := by
  induction m with
  | zero => simp [phaseOneNewTrace, phaseOneChecks, chainChecks]
  | succ m ih =>
      rw [phaseOneTrace_succ, chainChecks_append, phaseOneTrace_lastD,
        ih, phaseOneChecks_succ]
      rfl

theorem phaseTwo_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    chainChecks (phaseTwoObs p eps M D x0 oracle 0)
      (phaseTwoNewTrace p eps M D x0 oracle m) =
        phaseTwoChecks p eps M D x0 oracle m := by
  induction m with
  | zero => simp [phaseTwoNewTrace, phaseTwoChecks, chainChecks]
  | succ m ih =>
      rw [phaseTwoTrace_succ, chainChecks_append, phaseTwoTrace_lastD,
        ih, phaseTwoChecks_succ]
      rfl

theorem total_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₁ m₂ : ℕ) (hm₁ : m₁ = horizon p eps M D) :
    chainChecks (phaseOneObs p eps M D x0 oracle 0)
      (phaseOneNewTrace p eps M D x0 oracle m₁ ++
        phaseTwoNewTrace p eps M D x0 oracle m₂) =
      allChecks p eps M D x0 oracle m₁ m₂ := by
  rw [chainChecks_append, phaseOneTrace_lastD, phaseOne_chain]
  subst m₁
  rw [← phaseTwoObs_zero, phaseTwo_chain]
  rfl

end V7.Stage3BelowTwoS3F
