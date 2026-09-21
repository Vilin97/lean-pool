/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.Closure

open MeasureTheory

namespace V7.Stage7StrictRandomizedExpected

/-- A fixed-length transcript is measurable for the frozen cylinder sigma
algebra once each of its finitely many coordinates is measurable. -/
theorem measurable_strictTranscript_of_fixedLength
    {Ω : Type*} [MeasurableSpace Ω] {trace : Ω → StrictTranscript} {n : ℕ}
    (hlen : ∀ ω, (trace ω).length = n)
    (hcoord : ∀ (k : ℕ) (hk : k < n),
      Measurable (fun ω => (trace ω)[k]'(by simpa [hlen ω] using hk))) :
    Measurable trace := by
  change @Measurable Ω StrictTranscript _
    (MeasurableSpace.generateFrom {s : Set StrictTranscript |
      (∃ m : ℕ, s = {tr | tr.length = m}) ∨
      ∃ (k : ℕ) (B : Set StrictObservation), MeasurableSet B ∧
        s = {tr | ∃ obs ∈ B, (tr.drop k).head? = some obs}}) trace
  apply measurable_generateFrom
  intro s hs
  rcases hs with ⟨m, rfl⟩ | ⟨k, B, hB, rfl⟩
  · by_cases hnm : n = m
    · simpa [Set.preimage_setOf_eq, hlen, hnm] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    · simpa [Set.preimage_setOf_eq, hlen, hnm] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  · by_cases hk : k < n
    · have hm := (hcoord k hk) hB
      convert hm using 1
      ext ω
      rw [Set.mem_preimage, Set.mem_setOf_eq, List.head?_drop,
        List.getElem?_eq_getElem (by simpa [hlen ω] using hk)]
      simp
    · have hnone : ∀ ω, (trace ω)[k]? = none := by
        intro ω
        rw [List.getElem?_eq_none]
        simpa [hlen ω] using hk
      have hempty : trace ⁻¹' {tr | ∃ obs ∈ B, (tr.drop k).head? = some obs} = ∅ := by
        ext ω
        rw [Set.mem_preimage, Set.mem_setOf_eq, List.head?_drop, hnone ω]
        simp
      rw [hempty]
      exact MeasurableSet.empty

/-- The query selected by a seed-indexed method after a chronological prefix. -/
def causalQuery {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (ω : Ω) (t : ℕ) (trace : StrictTranscript) : StrictPoint :=
  if t = 0 then x0 else (method ω).nextQuery trace

/-- Exact chronological transcript against one fixed oracle, simultaneously
defined for every seed and every finite horizon. -/
noncomputable def causalTrace {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) : ℕ → Ω → StrictTranscript
  | 0 => fun _ => []
  | n + 1 => fun ω =>
      let trace := causalTrace method x0 oracle n ω
      trace ++ [oracle.observe (causalQuery method x0 ω n trace)]

@[simp] theorem causalTrace_zero {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (ω : Ω) :
    causalTrace method x0 oracle 0 ω = [] := rfl

theorem causalTrace_succ {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (n : ℕ) (ω : Ω) :
    causalTrace method x0 oracle (n + 1) ω =
      causalTrace method x0 oracle n ω ++
        [oracle.observe (causalQuery method x0 ω n
          (causalTrace method x0 oracle n ω))] := rfl

@[simp] theorem causalTrace_length {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (n : ℕ) (ω : Ω) :
    (causalTrace method x0 oracle n ω).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [causalTrace_succ, ih]

theorem causalTrace_take {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    (causalTrace method x0 oracle n ω).take m =
      causalTrace method x0 oracle m ω := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [causalTrace_succ, List.take_append_of_le_length]
        · exact ih hmn'
        · simpa using hmn'
      · have hm : m = n + 1 := by omega
        subst m
        simp [causalTrace_succ]

theorem causalTrace_get {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (n t : ℕ) (ht : t < n) (ω : Ω) :
    (causalTrace method x0 oracle n ω).get
        ⟨t, by simpa using ht⟩ =
      oracle.observe (causalQuery method x0 ω t
        (causalTrace method x0 oracle t ω)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [causalTrace_succ]
      by_cases htn : t < n
      · change (causalTrace method x0 oracle n ω ++
            [oracle.observe (causalQuery method x0 ω n
              (causalTrace method x0 oracle n ω))])[t]'
                (by simp [causalTrace_length]; omega)
            = oracle.observe (causalQuery method x0 ω t
              (causalTrace method x0 oracle t ω))
        rw [List.getElem_append_left]
        exact ih htn
      · have hteq : t = n := by omega
        subst t
        change (causalTrace method x0 oracle n ω ++
            [oracle.observe (causalQuery method x0 ω n
              (causalTrace method x0 oracle n ω))])[n]'
                (by simp [causalTrace_length])
            = oracle.observe (causalQuery method x0 ω n
              (causalTrace method x0 oracle n ω))
        rw [List.getElem_append_right (by simp [causalTrace_length])]
        simp [causalTrace_length]

/-- Exactness of the generated transcript against its fixed oracle. -/
theorem causalTrace_exact {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (n : ℕ) (ω : Ω) :
    StrictTranscriptExact oracle (causalTrace method x0 oracle n ω) := by
  intro obs hobs
  induction n with
  | zero => simp at hobs
  | succ n ih =>
      rw [causalTrace_succ] at hobs
      simp only [List.mem_append, List.mem_singleton] at hobs
      rcases hobs with hobs | rfl
      · exact ih hobs
      · rfl

theorem strictAffineObserve_measurable (eps : ℝ) (x0 : StrictPoint) :
    Measurable (strictAffineOracle eps x0).observe := by
  apply measurable_comap_iff.mpr
  exact measurable_id.prodMk
    (((measurable_pi_apply 0).sub measurable_const).const_mul _ |>.prodMk
      (measurable_pi_lambda _ fun _ => measurable_const))

theorem hardObserve_measurable (eps : ℝ) (x0 : StrictPoint) (H : ℝ) :
    Measurable (Stage6StrictDeterministic.hardOracle eps x0 H).observe := by
  have hz : Measurable (fun x : StrictPoint => x 0 - x0 0) :=
    (measurable_pi_apply 0).sub measurable_const
  have hH : MeasurableSet {x : StrictPoint | x 0 - x0 0 ≤ H} :=
    hz measurableSet_Iic
  have h3H : MeasurableSet {x : StrictPoint | x 0 - x0 0 ≤ 3 * H} :=
    hz measurableSet_Iic
  have hvalue : Measurable (strictHardFamily eps x0 H) := by
    unfold strictHardFamily
    exact (measurable_const.mul hz).ite hH
      (((measurable_const.mul hz).add
        (measurable_const.mul ((hz.sub measurable_const).pow_const 2))).ite h3H
        ((measurable_const.mul hz).sub measurable_const))
  have hslope : Measurable (fun x : StrictPoint =>
      Stage6StrictDeterministic.hardSlope eps H (x 0 - x0 0)) := by
    unfold Stage6StrictDeterministic.hardSlope
    exact measurable_const.ite hH
      ((measurable_const.mul ((hz.div_const H).sub measurable_const)).ite h3H
        measurable_const)
  apply measurable_comap_iff.mpr
  exact measurable_id.prodMk
    (hvalue.prodMk (measurable_pi_lambda _ fun _ => hslope))

theorem causalQuery_measurable {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint) (n : ℕ)
    {trace : Ω → StrictTranscript} (htrace : Measurable trace) :
    Measurable (fun ω => causalQuery method x0 ω n (trace ω)) := by
  by_cases hn : n = 0
  · simp [causalQuery, hn]
  · simp only [causalQuery, hn, if_false]
    convert method.joint_nextQuery_measurable.comp (measurable_id.prodMk htrace) using 1
    funext ω
    rfl

/-- Measurability of the complete finite causal recursion, proved directly
from the frozen cylinder generators and the joint method fields. -/
theorem causalTrace_measurable {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe) :
    ∀ n : ℕ, Measurable (causalTrace method x0 oracle n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply measurable_strictTranscript_of_fixedLength (n := n)
      · intro k hk
        have hquery : Measurable (fun ω => causalQuery method x0 ω k
            (causalTrace method x0 oracle k ω)) :=
          causalQuery_measurable method x0 k (ih k hk)
        have hobs := hobserve.comp hquery
        convert hobs using 1
        funext ω
        exact causalTrace_get method x0 oracle n k hk ω
      · exact fun seed => causalTrace_length method x0 oracle n seed

theorem causalOutput_measurable {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (N : ℕ)
    {trace : Ω → StrictTranscript} (htrace : Measurable trace) :
    Measurable (fun ω => (method ω).output N (trace ω)) := by
  change Measurable ((fun z : Ω × StrictTranscript =>
    (method z.1).output N z.2) ∘ fun ω => (ω, trace ω))
  exact method.joint_output_measurable N |>.comp (measurable_id.prodMk htrace)

theorem causalTrace_runConsistent {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1)
    (hx0 : ∀ ω, (method ω).x0 = x0) (n : ℕ) (ω : Ω) :
    StrictRunConsistent (method ω) oracle (causalTrace method x0 oracle n ω) := by
  refine ⟨causalTrace_exact method x0 oracle n ω, ?_⟩
  intro t ht
  rw [causalTrace_get method x0 oracle n t (by simpa using ht) ω]
  simp only [O3.PairOracle.observe]
  rw [causalTrace_take method x0 oracle (Nat.le_of_lt (by simpa using ht)) ω]
  by_cases ht0 : t = 0
  · simp [causalQuery, ht0, hx0 ω]
  · simp [causalQuery, ht0]

end V7.Stage7StrictRandomizedExpected
