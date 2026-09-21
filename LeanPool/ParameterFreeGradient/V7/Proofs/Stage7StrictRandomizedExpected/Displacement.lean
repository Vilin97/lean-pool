/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage7StrictRandomizedExpected.MeasurableTrace

open MeasureTheory Filter

namespace V7.Stage7StrictRandomizedExpected

open Stage6StrictDeterministic

theorem traceDisplacementBound_append_singleton (x0 : StrictPoint)
    (trace : StrictTranscript) (obs : StrictObservation) :
    traceDisplacementBound x0 (trace ++ [obs]) =
      max (traceDisplacementBound x0 trace) (obs.point 0 - x0 0) := by
  induction trace with
  | nil => simp [max_comm]
  | cons head tail ih =>
      simp only [List.cons_append, traceDisplacementBound_cons, ih]
      ac_rfl

theorem traceDisplacementBound_lt_iff (x0 : StrictPoint)
    (trace : StrictTranscript) {H : ℝ} (hH : 0 < H) :
    traceDisplacementBound x0 trace < H ↔
      ∀ obs ∈ trace, obs.point 0 - x0 0 < H := by
  induction trace with
  | nil => simp [hH]
  | cons head tail ih =>
      simp only [traceDisplacementBound_cons, max_lt_iff, ih, List.mem_cons]
      constructor
      · rintro ⟨hhead, htail⟩ obs (rfl | hobs)
        · exact hhead
        · exact htail obs hobs
      · intro h
        exact ⟨h head (by simp), fun obs hobs => h obs (by simp [hobs])⟩

theorem causalTraceDisplacementBound_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe) :
    ∀ n : ℕ, Measurable (fun ω =>
      traceDisplacementBound x0 (causalTrace method x0 oracle n ω)) := by
  intro n
  induction n with
  | zero => simpa [causalTrace_zero] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  | succ n ih =>
      have htrace := causalTrace_measurable method x0 oracle hobserve n
      have hquery := causalQuery_measurable method x0 n htrace
      have hdisp : Measurable (fun ω =>
          causalQuery method x0 ω n (causalTrace method x0 oracle n ω) 0 - x0 0) :=
        (measurable_pi_apply 0 |>.comp hquery).sub measurable_const
      convert ih.max hdisp using 1
      funext ω
      rw [causalTrace_succ, traceDisplacementBound_append_singleton]
      rfl

/-- Maximum of zero, all affine-query displacements, and the horizon output. -/
noncomputable def finiteDisplacementBound
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (N : ℕ) (ω : Ω) : ℝ :=
  max (traceDisplacementBound x0 (causalTrace method x0 oracle N ω))
    ((method ω).output N (causalTrace method x0 oracle N ω) 0 - x0 0)

theorem finiteDisplacementBound_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe) (N : ℕ) :
    Measurable (finiteDisplacementBound method x0 oracle N) := by
  have htrace := causalTrace_measurable method x0 oracle hobserve N
  have hbound := causalTraceDisplacementBound_measurable method x0 oracle hobserve N
  have hout := causalOutput_measurable method N htrace
  exact hbound.max ((measurable_pi_apply 0 |>.comp hout).sub measurable_const)

theorem finiteDisplacementBound_lt_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (N : ℕ) (ω : Ω) {H : ℝ} (hH : 0 < H) :
    finiteDisplacementBound method x0 oracle N ω < H ↔
      (∀ obs ∈ causalTrace method x0 oracle N ω,
        obs.point 0 - x0 0 < H) ∧
      (method ω).output N (causalTrace method x0 oracle N ω) 0 - x0 0 < H := by
  rw [finiteDisplacementBound, max_lt_iff,
    traceDisplacementBound_lt_iff x0 _ hH]

theorem boundedDisplacementEvent_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe)
    (N : ℕ) {H : ℝ} (hH : 0 < H) :
    MeasurableSet {ω |
      (∀ obs ∈ causalTrace method x0 oracle N ω,
        obs.point 0 - x0 0 < H) ∧
      (method ω).output N (causalTrace method x0 oracle N ω) 0 - x0 0 < H} := by
  have hm := finiteDisplacementBound_measurable method x0 oracle hobserve N
  have hs : MeasurableSet {ω | finiteDisplacementBound method x0 oracle N ω < H} :=
    hm measurableSet_Iio
  convert hs using 1
  ext ω
  exact (finiteDisplacementBound_lt_iff method x0 oracle N ω hH).symm

/-- A finite measurable real random variable admits one deterministic positive
threshold carrying any prescribed probability strictly below one. -/
theorem exists_deterministic_threshold
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Ω → ℝ) (hM : Measurable M) {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ H : ℝ, 0 < H ∧
      ENNReal.ofReal (1 - delta) ≤ μ {ω | M ω < H} := by
  let S : ℕ → Set Ω := fun n => {ω | M ω < ((n + 1 : ℕ) : ℝ)}
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => hM measurableSet_Iio
  have hSmono : Monotone S := by
    intro m n hmn ω hω
    change M ω < ((m + 1 : ℕ) : ℝ) at hω
    change M ω < ((n + 1 : ℕ) : ℝ)
    exact lt_of_lt_of_le hω (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hUnion : (⋃ n, S n) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (M ω)
    exact ⟨n, hn.trans_le (by exact_mod_cast Nat.le_add_right n 1)⟩
  have hlim : Tendsto (fun n => μ (S n)) atTop (nhds 1) := by
    convert tendsto_measure_iUnion_atTop (μ := μ) hSmono using 1 <;>
      simp [Function.comp_def, hUnion]
  have htarget : ENNReal.ofReal (1 - delta) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 _ htarget).exists
  refine ⟨((n + 1 : ℕ) : ℝ), ?_, ?_⟩
  · exact_mod_cast Nat.succ_pos n
  · simpa [S] using hn.le

end V7.Stage7StrictRandomizedExpected
