/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage7StrictRandomizedExpected.Displacement

/-!
A single normalized hard instance makes finite-horizon randomized success arbitrarily
unlikely.
-/

open MeasureTheory

namespace V7.Stage7StrictRandomizedExpected

open Stage6StrictDeterministic

theorem hard_causalTrace_eq_affine_of_left
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (eps H : ℝ)
    (x0 : StrictPoint) (ω : Ω) (N : ℕ)
    (hleft : ∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
      obs.point 0 - x0 0 < H) :
    causalTrace method x0 (hardOracle eps x0 H) N ω =
      causalTrace method x0 (strictAffineOracle eps x0) N ω := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hleftN : ∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
          obs.point 0 - x0 0 < H := by
        intro obs hobs
        exact hleft obs (by simp [causalTrace_succ, hobs])
      rw [causalTrace_succ, causalTrace_succ, ih hleftN]
      congr 1
      congr 1
      apply hard_affine_observation_eq
      have hq := hleft
        ((strictAffineOracle eps x0).observe
          (causalQuery method x0 ω N
            (causalTrace method x0 (strictAffineOracle eps x0) N ω)))
        (by simp [causalTrace_succ])
      simpa [O3.PairOracle.observe] using hq

theorem hardGradientMagnitude_measurable (eps : ℝ) (x0 : StrictPoint) (H : ℝ) :
    Measurable (fun x : StrictPoint =>
      |(hardOracle eps x0 H).gradient x 0|) := by
  have hz : Measurable (fun x : StrictPoint => x 0 - x0 0) :=
    (measurable_pi_apply 0).sub measurable_const
  have hH : MeasurableSet {x : StrictPoint | x 0 - x0 0 ≤ H} :=
    hz measurableSet_Iic
  have h3H : MeasurableSet {x : StrictPoint | x 0 - x0 0 ≤ 3 * H} :=
    hz measurableSet_Iic
  have hslope : Measurable (fun x : StrictPoint => hardSlope eps H (x 0 - x0 0)) := by
    unfold hardSlope
    exact measurable_const.ite hH
      ((measurable_const.mul ((hz.div_const H).sub measurable_const)).ite h3H
        measurable_const)
  simpa only [hardOracle, strictHardDerivative_apply, Real.norm_eq_abs] using hslope.norm

theorem causalTrace_coordinate_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe)
    (n k : ℕ) (hk : k < n) :
    Measurable (fun ω => (causalTrace method x0 oracle n ω)[k]'
      (by simpa using hk)) := by
  have hquery : Measurable (fun ω => causalQuery method x0 ω k
      (causalTrace method x0 oracle k ω)) :=
    causalQuery_measurable method x0 k
      (causalTrace_measurable method x0 oracle hobserve k)
  have hobs := hobserve.comp hquery
  convert hobs using 1
  funext ω
  exact causalTrace_get method x0 oracle n k hk ω

theorem querySuccessEvent_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (oracle : PairOracle 1) (hobserve : Measurable oracle.observe)
    (hgrad : Measurable (fun x : StrictPoint => |oracle.gradient x 0|))
    (eps : ℝ) (heps : ∀ ω, (method ω).eps = eps) :
    ∀ n : ℕ, MeasurableSet {ω |
      ∃ obs ∈ causalTrace method x0 oracle n ω,
        |oracle.gradient obs.point 0| ≤ (method ω).eps} := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have htrace := causalTrace_measurable method x0 oracle hobserve n
      have hquery := causalQuery_measurable method x0 n htrace
      have hlast : MeasurableSet {ω |
          |oracle.gradient
            (causalQuery method x0 ω n (causalTrace method x0 oracle n ω)) 0| ≤
              (method ω).eps} := by
        have hm := hgrad.comp hquery
        have hs : MeasurableSet {ω |
            |oracle.gradient
              (causalQuery method x0 ω n (causalTrace method x0 oracle n ω)) 0| ≤ eps} :=
          hm measurableSet_Iic
        convert hs using 1
        ext ω
        simp [heps ω]
      have hu := ih.union hlast
      convert hu using 1
      ext ω
      simp [causalTrace_succ, O3.PairOracle.observe]

theorem hardSuccessEvent_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (eps H : ℝ) (heps : ∀ ω, (method ω).eps = eps) (N : ℕ) :
    MeasurableSet {ω | StrictSuccessThrough (method ω) (hardOracle eps x0 H)
      (causalTrace method x0 (hardOracle eps x0 H) N ω) N} := by
  let oracle := hardOracle eps x0 H
  have hobserve : Measurable oracle.observe := hardObserve_measurable eps x0 H
  have hgrad : Measurable (fun x : StrictPoint => |oracle.gradient x 0|) :=
    hardGradientMagnitude_measurable eps x0 H
  have hquery := querySuccessEvent_measurable method x0 oracle hobserve hgrad eps heps N
  have htrace := causalTrace_measurable method x0 oracle hobserve N
  have hout := causalOutput_measurable method N htrace
  have houtput : MeasurableSet {ω |
      |oracle.gradient ((method ω).output N (causalTrace method x0 oracle N ω)) 0| ≤
        (method ω).eps} := by
    have hm := hgrad.comp hout
    have hs : MeasurableSet {ω |
        |oracle.gradient ((method ω).output N (causalTrace method x0 oracle N ω)) 0| ≤ eps} :=
      hm measurableSet_Iic
    convert hs using 1
    ext ω
    simp [heps ω]
  have hu := hquery.union houtput
  convert hu using 1
  ext ω
  simp only [StrictSuccessThrough, Set.mem_ofPred_eq, Set.mem_union]
  rw [show (causalTrace method x0 oracle N ω).take N =
      causalTrace method x0 oracle N ω by
        rw [List.take_eq_self_iff]
        simp]

theorem success_impossible_on_bounded_affine_event
    {Ω : Type*} [MeasurableSpace Ω]
    (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint)
    (eps H : ℝ) (heps0 : 0 < eps)
    (heps : ∀ ω, (method ω).eps = eps)
    (hx0 : ∀ ω, (method ω).x0 = x0) (N : ℕ) (ω : Ω)
    (hgood :
      (∀ obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω,
        obs.point 0 - x0 0 < H) ∧
      (method ω).output N
        (causalTrace method x0 (strictAffineOracle eps x0) N ω) 0 - x0 0 < H) :
    ¬ StrictSuccessThrough (method ω) (hardOracle eps x0 H)
      (causalTrace method x0 (hardOracle eps x0 H) N ω) N := by
  have hcouple := hard_causalTrace_eq_affine_of_left method eps H x0 ω N hgood.1
  rw [hcouple]
  intro hsuccess
  rcases hsuccess with hquery | houtput
  · obtain ⟨obs, hobs, hsmall⟩ := hquery
    have hmem : obs ∈ causalTrace method x0 (strictAffineOracle eps x0) N ω :=
      List.mem_of_mem_take hobs
    have hfail := all_queries_fail_of_left heps0 x0
      (causalTrace_length method x0 (strictAffineOracle eps x0) N ω) hgood.1
    rw [heps ω] at hsmall
    exact (not_lt_of_ge hsmall) (hfail.2 obs hmem)
  · have hgood' :
        (method ω).output N (causalTrace method x0 (strictAffineOracle eps x0) N ω) 0 -
            (method ω).x0 0 < H := by
      simpa [hx0 ω] using hgood.2
    have hfail := finite_output_fails_of_left heps0 (heps ω)
      (causalTrace method x0 (strictAffineOracle eps x0) N ω) N hgood'
    change (method ω).eps <
      |(hardOracle eps (method ω).x0 H).gradient
        ((method ω).output N
          (causalTrace method x0 (strictAffineOracle eps x0) N ω)) 0| at hfail
    rw [hx0 ω] at hfail
    exact (not_lt_of_ge houtput) hfail

theorem probability_success_le_delta
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {good success : Set Ω} (hgood : MeasurableSet good)
    (hsubset : success ⊆ goodᶜ) {delta : ℝ}
     (hdelta1 : delta < 1)
    (hmass : ENNReal.ofReal (1 - delta) ≤ μ good) :
    μ success ≤ ENNReal.ofReal delta := by
  calc
    μ success ≤ μ goodᶜ := measure_mono hsubset
    _ = 1 - μ good := by
      rw [measure_compl hgood (measure_ne_top μ good), measure_univ]
    _ ≤ 1 - ENNReal.ofReal (1 - delta) := tsub_le_tsub_left hmass 1
    _ = ENNReal.ofReal delta := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - delta)]
      congr 1
      ring

end V7.Stage7StrictRandomizedExpected

namespace V7

open Stage6StrictDeterministic Stage7StrictRandomizedExpected

theorem randomizedFiniteHorizonImpossibility :
    RandomizedFiniteHorizonImpossibilityStatement := by
  intro p eps hp heps Ω _ μ _ method x0 hmethod N delta hN hdelta0 hdelta1
  let affineTraces : Ω → StrictTranscript :=
    causalTrace method x0 (strictAffineOracle eps x0) N
  have hx0 : ∀ ω, (method ω).x0 = x0 := fun ω => (hmethod ω).2
  have heqeps : ∀ ω, (method ω).eps = eps := fun ω => (hmethod ω).1
  have haffine_meas : Measurable affineTraces :=
    causalTrace_measurable method x0 (strictAffineOracle eps x0)
      (strictAffineObserve_measurable eps x0) N
  refine ⟨affineTraces, ?_, ?_⟩
  · intro ω
    exact ⟨causalTrace_length method x0 (strictAffineOracle eps x0) N ω,
      causalTrace_runConsistent method x0 (strictAffineOracle eps x0) hx0 N ω⟩
  · let M : Ω → ℝ := finiteDisplacementBound method x0
      (strictAffineOracle eps x0) N
    have hM : Measurable M := finiteDisplacementBound_measurable method x0
      (strictAffineOracle eps x0) (strictAffineObserve_measurable eps x0) N
    obtain ⟨H, hH, hmass⟩ :=
      exists_deterministic_threshold μ M hM hdelta0
    have hmassGood : ENNReal.ofReal (1 - delta) ≤ μ {ω |
        (∀ obs ∈ affineTraces ω, obs.point 0 - x0 0 < H) ∧
        (method ω).output N (affineTraces ω) 0 - x0 0 < H} := by
      have hset : {ω | M ω < H} = {ω |
          (∀ obs ∈ affineTraces ω, obs.point 0 - x0 0 < H) ∧
          (method ω).output N (affineTraces ω) 0 - x0 0 < H} := by
        ext ω
        change finiteDisplacementBound method x0 (strictAffineOracle eps x0) N ω < H ↔ _
        exact finiteDisplacementBound_lt_iff method x0
          (strictAffineOracle eps x0) N ω hH
      rwa [hset] at hmass
    let oracle := hardOracle eps x0 H
    let hardTraces : Ω → StrictTranscript := causalTrace method x0 oracle N
    refine ⟨H, (2 * eps) / H, 2 * H, oracle, hardMinimizer x0 H,
      strictHardInstance eps x0 H heps hH, hardTraces, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ω
      exact ⟨causalTrace_length method x0 oracle N ω,
        causalTrace_runConsistent method x0 oracle hx0 N ω⟩
    · exact boundedDisplacementEvent_measurable method x0
        (strictAffineOracle eps x0) (strictAffineObserve_measurable eps x0) N hH
    · exact hardSuccessEvent_measurable method x0 eps H heqeps N
    · exact hmassGood
    · intro ω hgood
      exact hard_causalTrace_eq_affine_of_left method eps H x0 ω N hgood.1
    · refine probability_success_le_delta μ
        (boundedDisplacementEvent_measurable method x0
          (strictAffineOracle eps x0) (strictAffineObserve_measurable eps x0) N hH)
        ?_ hdelta1 hmassGood
      intro ω hsuccess
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      intro hgood
      exact success_impossible_on_bounded_affine_event method x0 eps H heps heqeps hx0 N ω
        hgood (by simpa [oracle, hardTraces] using hsuccess)

end V7
