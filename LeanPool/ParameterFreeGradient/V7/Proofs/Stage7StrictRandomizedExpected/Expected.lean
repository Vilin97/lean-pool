/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage7StrictRandomizedExpected.Randomized

open MeasureTheory

namespace V7.Stage7StrictRandomizedExpected

open Stage6StrictDeterministic

attribute [local instance] Classical.propDecidable

/-- One finite random bound controlling every affine query through `N` and
every horizon-indexed output from zero through `N`. -/
noncomputable def allHorizonDisplacementBound
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint) (eps : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => max 0
      ((method ω).output 0 (causalTrace method x0 (strictAffineOracle eps x0) 0 ω) 0 - x0 0)
  | n + 1 => fun ω => max (allHorizonDisplacementBound method x0 eps n ω)
      (max
        (causalQuery method x0 ω n
          (causalTrace method x0 (strictAffineOracle eps x0) n ω) 0 - x0 0)
        ((method ω).output (n + 1)
          (causalTrace method x0 (strictAffineOracle eps x0) (n + 1) ω) 0 - x0 0))

theorem allHorizonDisplacementBound_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint) (eps : ℝ) :
    ∀ N, Measurable (allHorizonDisplacementBound method x0 eps N) := by
  intro N
  induction N with
  | zero =>
      have htrace := causalTrace_measurable method x0 (strictAffineOracle eps x0)
        (strictAffineObserve_measurable eps x0) 0
      have hout := causalOutput_measurable method 0 htrace
      exact measurable_const.max ((measurable_pi_apply 0 |>.comp hout).sub measurable_const)
  | succ n ih =>
      have htraceN := causalTrace_measurable method x0 (strictAffineOracle eps x0)
        (strictAffineObserve_measurable eps x0) n
      have hquery := causalQuery_measurable method x0 n htraceN
      have htraceSucc := causalTrace_measurable method x0 (strictAffineOracle eps x0)
        (strictAffineObserve_measurable eps x0) (n + 1)
      have hout := causalOutput_measurable method (n + 1) htraceSucc
      exact ih.max (((measurable_pi_apply 0 |>.comp hquery).sub measurable_const).max
        ((measurable_pi_apply 0 |>.comp hout).sub measurable_const))

theorem allHorizonDisplacementBound_lt_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint) (eps : ℝ)
    (N : ℕ) (ω : Ω) {H : ℝ} (hH : 0 < H) :
    allHorizonDisplacementBound method x0 eps N ω < H ↔
      (∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
        obs.point 0 - x0 0 < H) ∧
      ∀ m ≤ N,
        (method ω).output m
          (causalTrace method x0 (strictAffineOracle eps x0) m ω) 0 - x0 0 < H := by
  induction N with
  | zero =>
      simp [allHorizonDisplacementBound, hH]
  | succ n ih =>
      constructor
      · intro hb
        rw [allHorizonDisplacementBound, max_lt_iff, max_lt_iff] at hb
        rcases hb with ⟨hprev, hquery, hout⟩
        have hprev' := (ih).mp hprev
        constructor
        · intro obs hobs
          rw [causalTrace_succ] at hobs
          simp only [List.mem_append, List.mem_singleton] at hobs
          rcases hobs with hobs | rfl
          · exact hprev'.1 obs hobs
          · simpa [O3.PairOracle.observe] using hquery
        · intro m hm
          by_cases hmn : m ≤ n
          · exact hprev'.2 m hmn
          · have hmEq : m = n + 1 := by omega
            subst m
            exact hout
      · rintro ⟨htrace, houtput⟩
        rw [allHorizonDisplacementBound, max_lt_iff, max_lt_iff]
        refine ⟨(ih).mpr ⟨?_, fun m hm => houtput m (hm.trans (Nat.le_succ n))⟩, ?_,
          houtput (n + 1) le_rfl⟩
        · intro obs hobs
          exact htrace obs (by simp [causalTrace_succ, hobs])
        · have hlast := htrace
            ((strictAffineOracle eps x0).observe
              (causalQuery method x0 ω n
                (causalTrace method x0 (strictAffineOracle eps x0) n ω)))
            (by simp [causalTrace_succ])
          simpa [O3.PairOracle.observe] using hlast

theorem allHorizonBoundedEvent_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint) (eps : ℝ)
    (N : ℕ) {H : ℝ} (hH : 0 < H) :
    MeasurableSet {ω |
      (∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
        obs.point 0 - x0 0 < H) ∧
      ∀ m ≤ N,
        (method ω).output m
          (causalTrace method x0 (strictAffineOracle eps x0) m ω) 0 - x0 0 < H} := by
  have hm := allHorizonDisplacementBound_measurable method x0 eps N
  have hs : MeasurableSet {ω | allHorizonDisplacementBound method x0 eps N ω < H} :=
    hm measurableSet_Iio
  convert hs using 1
  ext ω
  exact (allHorizonDisplacementBound_lt_iff method x0 eps N ω hH).symm

theorem no_success_before_of_allHorizonBound
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (eps H : ℝ) (heps0 : 0 < eps)
    (heps : ∀ ω, (method ω).eps = eps)
    (hx0 : ∀ ω, (method ω).x0 = x0) (N : ℕ) (ω : Ω)
    (hgood :
      (∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
        obs.point 0 - x0 0 < H) ∧
      ∀ m ≤ N,
        (method ω).output m
          (causalTrace method x0 (strictAffineOracle eps x0) m ω) 0 - x0 0 < H) :
    ∀ m ≤ N, ¬ StrictSuccessThrough (method ω) (hardOracle eps x0 H)
      (causalTrace method x0 (hardOracle eps x0 H) m ω) m := by
  intro m hm
  apply success_impossible_on_bounded_affine_event method x0 eps H heps0 heps hx0 m ω
  constructor
  · intro obs hobs
    apply hgood.1 obs
    have ht := causalTrace_take method x0 (strictAffineOracle eps x0) hm ω
    apply List.mem_of_mem_take
    rw [ht]
    exact hobs
  · exact hgood.2 m hm

/-- The frozen `sInf` hitting time is the countable infimum of measurable
horizon values (finite at successful horizons, top otherwise). -/
theorem strictHittingTime_eq_iInf (method : StrictLocalMethod)
    (oracle : PairOracle 1) (traces : ℕ → StrictTranscript) :
    strictHittingTime method oracle traces =
      ⨅ N : ℕ, if StrictSuccessThrough method oracle (traces N) N
        then (N : ENNReal) else ⊤ := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro N
    by_cases hN : StrictSuccessThrough method oracle (traces N) N
    · rw [if_pos hN]
      exact sInf_le ⟨N, rfl, hN⟩
    · simp [hN]
  · apply le_sInf
    intro t ht
    rcases ht with ⟨N, rfl, hN⟩
    exact iInf_le_of_le N (by simp [hN])

theorem strictHittingTime_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (eps H : ℝ) (heps : ∀ ω, (method ω).eps = eps) :
    Measurable (fun ω => strictHittingTime (method ω) (hardOracle eps x0 H)
      (fun N => causalTrace method x0 (hardOracle eps x0 H) N ω)) := by
  classical
  let success : ℕ → Set Ω := fun N => {ω |
    StrictSuccessThrough (method ω) (hardOracle eps x0 H)
      (causalTrace method x0 (hardOracle eps x0 H) N ω) N}
  have hsuccess : ∀ N, MeasurableSet (success N) :=
    fun N => hardSuccessEvent_measurable method x0 eps H heps N
  have hvalue : ∀ N, Measurable (fun ω =>
      if ω ∈ success N then (N : ENNReal) else ⊤) := fun N =>
    measurable_const.ite (hsuccess N) measurable_const
  have hinf : Measurable (fun ω => ⨅ N : ℕ,
      if ω ∈ success N then (N : ENNReal) else ⊤) :=
    Measurable.iInf hvalue
  convert hinf using 1
  funext ω
  rw [strictHittingTime_eq_iInf]
  rfl

theorem hittingTime_gt_of_no_success_before
    (method : StrictLocalMethod) (oracle : PairOracle 1)
    (traces : ℕ → StrictTranscript) (N : ℕ)
    (hfail : ∀ m ≤ N, ¬ StrictSuccessThrough method oracle (traces m) m) :
    (N : ENNReal) < strictHittingTime method oracle traces := by
  unfold strictHittingTime
  rw [lt_sInf_iff]
  refine ⟨((N + 1 : ℕ) : ENNReal), ?_, ?_⟩
  · exact_mod_cast Nat.lt_succ_self N
  intro t ht
  rcases ht with ⟨m, rfl, hsuccess⟩
  have hNm : N < m := by
    by_contra hnot
    exact hfail m (Nat.le_of_not_gt hnot) hsuccess
  have hsucc : N + 1 ≤ m := by omega
  exact_mod_cast hsucc

theorem strictHardInstance_normalized {eps H : ℝ} {x0 : StrictPoint}
    (heps : 0 < eps) (hH : 0 < H) :
    StrictNormalizedInstance eps x0 ((2 * eps) / H) (2 * H)
      (hardOracle eps x0 H) (hardMinimizer x0 H) := by
  rcases strictHardInstance eps x0 H heps hH with
    ⟨_, _, _, hconv, hcoercive, hgradient, hmin, hLip, hL, hR, hnorm⟩
  exact ⟨hconv, hcoercive, hgradient, hmin, hLip, hL, hR, hnorm⟩

theorem lintegral_lower_bound_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ENNReal) {N : ℕ} {tail : Set Ω}
    (htail : MeasurableSet tail) (hpoint : ∀ ω ∈ tail, (N : ENNReal) ≤ T ω) :
    (N : ENNReal) * μ tail ≤ ∫⁻ ω, T ω ∂μ := by
  rw [← lintegral_indicator_const htail]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ tail
  · simpa [Set.indicator_of_mem hω] using hpoint ω hω
  · simp [hω]

end V7.Stage7StrictRandomizedExpected

namespace V7

open Stage6StrictDeterministic Stage7StrictRandomizedExpected

theorem infiniteWorstCaseExpectedHittingTime :
    InfiniteWorstCaseExpectedHittingTimeStatement := by
  intro p eps hp heps Ω _ μ _ method x0 hmethod
  have heqeps : ∀ ω, (method ω).eps = eps := fun ω => (hmethod ω).1
  have hx0 : ∀ ω, (method ω).x0 = x0 := fun ω => (hmethod ω).2
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨k, hbk⟩ := ENNReal.exists_nat_gt (ne_of_lt hb)
  let N : ℕ := 2 * k
  let B : Ω → ℝ := allHorizonDisplacementBound method x0 eps N
  have hB : Measurable B := allHorizonDisplacementBound_measurable method x0 eps N
  obtain ⟨H, hH, hmass⟩ := exists_deterministic_threshold μ B hB
    (delta := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  let oracle := hardOracle eps x0 H
  let traces : Ω → ℕ → StrictTranscript := fun ω n => causalTrace method x0 oracle n ω
  let T : Ω → ENNReal := fun ω => strictHittingTime (method ω) oracle (traces ω)
  let good : Set Ω := {ω |
    (∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
      obs.point 0 - x0 0 < H) ∧
    ∀ m ≤ N,
      (method ω).output m
        (causalTrace method x0 (strictAffineOracle eps x0) m ω) 0 - x0 0 < H}
  have hgood : MeasurableSet good :=
    allHorizonBoundedEvent_measurable method x0 eps N hH
  have hmassGood : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ good := by
    have hset : {ω | B ω < H} = good := by
      ext ω
      exact allHorizonDisplacementBound_lt_iff method x0 eps N ω hH
    have hm := hmass
    rw [hset] at hm
    norm_num at hm ⊢
    exact hm
  have hT : Measurable T := by
    dsimp [T, oracle, traces]
    exact strictHittingTime_measurable method x0 eps H heqeps
  let tail : Set Ω := {ω | (N : ENNReal) < T ω}
  have htail : MeasurableSet tail := hT measurableSet_Ioi
  have hgood_tail : good ⊆ tail := by
    intro ω hω
    have hfail := no_success_before_of_allHorizonBound method x0 eps H heps heqeps hx0 N ω hω
    exact hittingTime_gt_of_no_success_before (method ω) oracle (traces ω) N
      (by simpa [oracle, traces] using hfail)
  have htailmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ tail :=
    hmassGood.trans (measure_mono hgood_tail)
  let E : ENNReal := ∫⁻ ω, T ω ∂μ
  have hEtail : (N : ENNReal) * μ tail ≤ E := by
    apply lintegral_lower_bound_of_tail μ T htail
    intro ω hω
    exact (le_of_lt hω)
  have hkE : (k : ENNReal) ≤ E := by
    calc
      (k : ENNReal) = (N : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) := by
        have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num
        rw [hhalf]
        norm_num [N, mul_assoc, mul_comm, mul_left_comm]
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        simp
      _ ≤ (N : ENNReal) * μ tail := mul_le_mul' le_rfl htailmass
      _ ≤ E := hEtail
  refine ⟨E, ?_, hbk.trans_le hkE⟩
  refine ⟨(2 * eps) / H, 2 * H, oracle, hardMinimizer x0 H, traces,
    strictHardInstance_normalized heps hH, ?_, ?_, hT, rfl⟩
  · intro ω n
    exact ⟨causalTrace_length method x0 oracle n ω,
      causalTrace_runConsistent method x0 oracle hx0 n ω⟩
  · intro ω n
    exact (causalTrace_take method x0 oracle (Nat.le_succ n) ω).symm

end V7
