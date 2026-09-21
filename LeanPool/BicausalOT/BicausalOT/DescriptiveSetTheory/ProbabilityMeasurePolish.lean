/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  The space of probability measures on a Polish space is Polish

  Blueprint: BLUEPRINT.md §3W (wall W1). Mathlib (2025) provides the
  Lévy-Prokhorov metric, its identification with the topology of weak
  convergence on separable spaces, and Prokhorov's theorem
  (`isCompact_closure_of_isTightMeasureSet`); what is missing — and
  supplied here — is completeness (Node A + C1) of the Lévy-Prokhorov
  metric. Separability (Node B) and the `PolishSpace` assembly follow.
-/
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! ## Node A: Lévy-Prokhorov Cauchy sequences are uniformly tight -/

open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal

noncomputable section

variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]



omit [SeparableSpace Ω] [CompleteSpace Ω] in
/-- A1, heads: any single probability measure puts mass `≥ 1 - ε` on a
    finite union of `η`-balls centered in a countable dense sequence. -/
theorem exists_range_measure_ball_compl_lt
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D : ℕ → Ω} (hD : DenseRange D)
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℕ, μ ((⋃ j ∈ Finset.range M, ball (D j) η)ᶜ) < ε := by
  have hcover : (⋃ j, ball (D j) η) = univ := by
    refine eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hD x η hη
    exact mem_iUnion.mpr ⟨j, by simpa [Metric.mem_ball, dist_comm] using hj⟩
  have hanti : Antitone fun M => (⋃ j ∈ Finset.range M, ball (D j) η)ᶜ := by
    intro M M' hMM'
    apply compl_subset_compl.mpr
    refine biUnion_subset_biUnion_left ?_
    intro j hj
    simp only [Finset.coe_range, mem_Iio] at hj ⊢
    omega
  have hinter : (⋂ M, (⋃ j ∈ Finset.range M, ball (D j) η)ᶜ) = ∅ := by
    rw [← compl_iUnion,
      show (⋃ M, ⋃ j ∈ Finset.range M, ball (D j) η) = ⋃ j, ball (D j) η by
        ext x
        simp only [mem_iUnion, Finset.mem_range]
        exact ⟨fun ⟨_, j, _, hx⟩ => ⟨j, hx⟩, fun ⟨j, hx⟩ => ⟨j + 1, j, by omega, hx⟩⟩,
      hcover, compl_univ]
  have htendsto : Tendsto (fun M => μ ((⋃ j ∈ Finset.range M, ball (D j) η)ᶜ))
      atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (s := fun M => (⋃ j ∈ Finset.range M, ball (D j) η)ᶜ)
      (fun M => ((isOpen_biUnion fun j _ =>
        isOpen_ball).isClosed_compl.measurableSet).nullMeasurableSet)
      hanti ⟨0, measure_ne_top μ _⟩
    rwa [hinter, measure_empty] at h
  exact (htendsto.eventually_lt_const hε).exists

omit [CompleteSpace Ω] in
open scoped Classical in
/-- A1: for a Lévy-Prokhorov Cauchy sequence of probability measures on a
    Polish space, all measures simultaneously put mass `≥ 1 - δ` on one
    common finite union of `η`-balls. Heads are covered by density and
    continuity from below; tails are transferred from `u N` along the
    Lévy-Prokhorov inequality. -/
theorem cauchySeq_exists_finset_measure_ball_compl_le
    (u : ℕ → LevyProkhorov (ProbabilityMeasure Ω)) (hu : CauchySeq u)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ F : Finset Ω, ∀ n,
      ((u n).toMeasure : Measure Ω) ((⋃ x ∈ F, ball x η)ᶜ)
        ≤ ENNReal.ofReal δ := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exfalso
    have h1 : ((u 0).toMeasure : Measure Ω) univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hΩ, measure_empty] at h1
    exact zero_ne_one h1
  set c : ℝ := min (δ / 2) (η / 2) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu c hcpos
  obtain ⟨D, hD⟩ := exists_dense_seq Ω
  have hhead : ∀ i : ℕ, ∃ M : ℕ,
      ((u i).toMeasure : Measure Ω)
        ((⋃ j ∈ Finset.range M, ball (D j) (η / 2))ᶜ)
        < ENNReal.ofReal (δ / 2) := by
    intro i
    refine exists_range_measure_ball_compl_lt _ hD (by linarith) ?_
    rw [ENNReal.ofReal_pos]
    linarith
  choose M hM using hhead
  set Mstar : ℕ := (Finset.range (N + 1)).sup M with hMstar
  refine ⟨(Finset.range Mstar).image D, fun n => ?_⟩
  set B : Set Ω := ⋃ x ∈ (Finset.range Mstar).image D, ball x (η / 2) with hB
  have hhead_le : ∀ i ≤ N,
      ((u i).toMeasure : Measure Ω) (Bᶜ) ≤ ENNReal.ofReal (δ / 2) := by
    intro i hi
    refine le_trans (measure_mono (compl_subset_compl.mpr ?_)) (hM i).le
    intro y hy
    simp only [mem_iUnion, Finset.mem_range, exists_prop] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    have hjM : j < Mstar :=
      lt_of_lt_of_le hj (Finset.le_sup (Finset.mem_range.mpr (by omega)))
    simp only [hB, mem_iUnion, exists_prop]
    exact ⟨D j, Finset.mem_image_of_mem D (Finset.mem_range.mpr hjM), hyj⟩
  set A : Set Ω := (⋃ x ∈ (Finset.range Mstar).image D, ball x η)ᶜ with hA
  have hAmble : MeasurableSet A :=
    (isOpen_biUnion fun x _ => isOpen_ball).isClosed_compl.measurableSet
  have hAB : A ⊆ Bᶜ := by
    apply compl_subset_compl.mpr
    exact iUnion₂_mono fun x _ => ball_subset_ball (by linarith)
  rcases le_or_gt n N with hn | hn
  · calc ((u n).toMeasure : Measure Ω) A
        ≤ ((u n).toMeasure : Measure Ω) (Bᶜ) := measure_mono hAB
      _ ≤ ENNReal.ofReal (δ / 2) := hhead_le n hn
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
  · have hdist : dist (u n) (u N) < c := hN n hn.le
    have hedist : levyProkhorovEDist
        ((u N).toMeasure : Measure Ω) ((u n).toMeasure : Measure Ω)
        < ENNReal.ofReal c := by
      rw [levyProkhorovEDist_comm]
      exact (ENNReal.lt_ofReal_iff_toReal_lt
        (levyProkhorovEDist_ne_top _ _)).mpr hdist
    have key := right_measure_le_of_levyProkhorovEDist_lt hedist hAmble
    have hthick : thickening (ENNReal.ofReal c).toReal A ⊆ Bᶜ := by
      rw [ENNReal.toReal_ofReal hcpos.le]
      intro y hy
      obtain ⟨z, hzA, hyz⟩ := Metric.mem_thickening_iff.mp hy
      intro hyB
      simp only [hB, mem_iUnion, exists_prop] at hyB
      obtain ⟨x, hxF, hyx⟩ := hyB
      apply hzA
      simp only [mem_iUnion, exists_prop]
      refine ⟨x, hxF, ?_⟩
      have h1 : dist z x ≤ dist z y + dist y x := dist_triangle z y x
      have h2 : dist z y < c := by rwa [dist_comm] at hyz
      have h3 : dist y x < η / 2 := hyx
      have h4 : c ≤ η / 2 := min_le_right _ _
      exact Metric.mem_ball.mpr (by linarith)
    calc ((u n).toMeasure : Measure Ω) A
        ≤ ((u N).toMeasure : Measure Ω)
            (thickening (ENNReal.ofReal c).toReal A) + ENNReal.ofReal c := key
      _ ≤ ((u N).toMeasure : Measure Ω) (Bᶜ) + ENNReal.ofReal c :=
          add_le_add
            (measure_mono (μ := ((u N).toMeasure : Measure Ω)) hthick) le_rfl
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (hhead_le N le_rfl)
            (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num

/-- A2 (**Node A**): a Lévy-Prokhorov Cauchy sequence of probability
    measures on a Polish space is uniformly tight: the compact set is an
    intersection of finite unions of closed balls at scales `2⁻ʲ`. -/
theorem isTightMeasureSet_of_cauchySeq
    (u : ℕ → LevyProkhorov (ProbabilityMeasure Ω)) (hu : CauchySeq u) :
    IsTightMeasureSet {((u n).toMeasure : Measure Ω) | n : ℕ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_or_ne ε ∞ with rfl | hεtop
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεtop,
        (ENNReal.ofReal_toReal hεtop).le⟩
  have hlayer : ∀ j : ℕ, ∃ F : Finset Ω, ∀ n,
      ((u n).toMeasure : Measure Ω)
        ((⋃ x ∈ F, ball x ((1 / 2 : ℝ) ^ j))ᶜ)
        ≤ ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1)) := by
    intro j
    refine cauchySeq_exists_finset_measure_ball_compl_le u hu ?_ ?_
    · positivity
    · positivity
  choose F hF using hlayer
  set K : Set Ω := ⋂ j, ⋃ x ∈ F j, closedBall x ((1 / 2 : ℝ) ^ j) with hK
  have hKclosed : IsClosed K := by
    refine isClosed_iInter fun j => ?_
    exact (F j).finite_toSet.isClosed_biUnion fun x _ => isClosed_closedBall
  have hKtb : TotallyBounded K := by
    rw [Metric.totallyBounded_iff]
    intro ρ hρ
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨F j, (F j).finite_toSet, ?_⟩
    intro y hy
    have hyj := mem_iInter.mp hy j
    simp only [mem_iUnion, exists_prop] at hyj ⊢
    obtain ⟨x, hxF, hyx⟩ := hyj
    exact ⟨x, hxF, Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hyx) hj)⟩
  have hKcompact : IsCompact K := hKtb.isCompact_of_isClosed hKclosed
  refine ⟨K, hKcompact, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hlayer_le : ∀ j : ℕ,
      ((u n).toMeasure : Measure Ω)
        ((⋃ x ∈ F j, closedBall x ((1 / 2 : ℝ) ^ j))ᶜ)
        ≤ ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1)) := by
    intro j
    refine le_trans (measure_mono (compl_subset_compl.mpr ?_)) (hF j n)
    exact iUnion₂_mono fun x _ => ball_subset_closedBall
  have hgeom : (∑' j : ℕ, ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1)))
      = ENNReal.ofReal e := by
    have hterm : ∀ j : ℕ, ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1))
        = ENNReal.ofReal e * (2 : ℝ≥0∞)⁻¹ ^ (j + 1) := by
      intro j
      rw [ENNReal.ofReal_mul he.le, ENNReal.ofReal_pow (by norm_num)]
      congr 2
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    calc (∑' j : ℕ, ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1)))
        = ∑' j : ℕ, ENNReal.ofReal e * (2 : ℝ≥0∞)⁻¹ ^ (j + 1) := by
          exact tsum_congr hterm
      _ = ENNReal.ofReal e * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal e * ((2 : ℝ≥0∞)⁻¹ * (1 - 2⁻¹)⁻¹) := by
          congr 1
          rw [show (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1))
              = ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ j by
            exact tsum_congr fun j => by rw [pow_succ, mul_comm]]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = ENNReal.ofReal e := by
          rw [ENNReal.one_sub_inv_two, inv_inv,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  calc ((u n).toMeasure : Measure Ω) (Kᶜ)
      = ((u n).toMeasure : Measure Ω)
          (⋃ j, (⋃ x ∈ F j, closedBall x ((1 / 2 : ℝ) ^ j))ᶜ) := by
        rw [hK, compl_iInter]
    _ ≤ ∑' j : ℕ, ((u n).toMeasure : Measure Ω)
          ((⋃ x ∈ F j, closedBall x ((1 / 2 : ℝ) ^ j))ᶜ) :=
        measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (e * (1 / 2 : ℝ) ^ (j + 1)) :=
        ENNReal.tsum_le_tsum hlayer_le
    _ = ENNReal.ofReal e := hgeom
    _ ≤ ε := heε

/-! ## Node C1: completeness of the Lévy-Prokhorov metric -/

/-- **Completeness of the Lévy-Prokhorov metric** on probability measures
    over a Polish space: Cauchy sequences are uniformly tight (Node A),
    Prokhorov's theorem gives a weakly convergent subsequence, and the
    Lévy-Prokhorov topology agrees with the weak topology. -/
instance : CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω)) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have htight := isTightMeasureSet_of_cauchySeq u hu
  have hS : IsTightMeasureSet
      {((μ : ProbabilityMeasure Ω) : Measure Ω) |
        μ ∈ Set.range fun n => (u n).toMeasure} := by
    have hset : {((μ : ProbabilityMeasure Ω) : Measure Ω) |
        μ ∈ Set.range fun n => (u n).toMeasure}
        = {((u n).toMeasure : Measure Ω) | n : ℕ} := by
      ext m
      constructor
      · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨(u n).toMeasure, ⟨n, rfl⟩, rfl⟩
    rw [hset]
    exact htight
  have hcpt : IsCompact (closure (Set.range fun n => (u n).toMeasure)) :=
    isCompact_closure_of_isTightMeasureSet hS
  have hmem : ∀ n, (u n).toMeasure
      ∈ closure (Set.range fun n => (u n).toMeasure) :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨p, -, φ, hφmono, hφtendsto⟩ := hcpt.tendsto_subseq hmem
  refine ⟨LevyProkhorov.ofMeasure p, ?_⟩
  have hcont : Continuous (LevyProkhorov.ofMeasure :
      ProbabilityMeasure Ω → LevyProkhorov (ProbabilityMeasure Ω)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  have hsub : Tendsto (fun j => u (φ j)) atTop
      (𝓝 (LevyProkhorov.ofMeasure p)) := by
    have h := (hcont.tendsto p).comp hφtendsto
    exact h
  exact tendsto_nhds_of_cauchySeq_of_subseq hu hφmono.tendsto_atTop hsub

/-! ## Node B: separability of the Lévy-Prokhorov metric

The countable dense family consists of normalized mixtures of Dirac
measures with natural-number weights, at points of a countable dense
sequence. -/

/-- A normalized finite mixture of Dirac measures with natural weights;
    falls back to `dirac x₀` when all weights vanish. -/
def diracMix (x₀ : Ω) {N : ℕ} (x : Fin N → Ω) (a : Fin N → ℕ) : Measure Ω :=
  if (∑ i, a i) = 0 then Measure.dirac x₀
  else (∑ i, (a i : ℝ≥0∞))⁻¹ • ∑ i, (a i : ℝ≥0∞) • Measure.dirac (x i)

omit [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω] [BorelSpace Ω] in
theorem diracMix_sum_ne_zero (x₀ : Ω) {N : ℕ} (x : Fin N → Ω) (a : Fin N → ℕ)
    (h : (∑ i, a i) ≠ 0) :
    diracMix x₀ x a
      = (∑ i, (a i : ℝ≥0∞))⁻¹ • ∑ i, (a i : ℝ≥0∞) • Measure.dirac (x i) := by
  rw [diracMix, ite_eq_right h]

instance diracMix_isProbabilityMeasure (x₀ : Ω) {N : ℕ}
    (x : Fin N → Ω) (a : Fin N → ℕ) :
    IsProbabilityMeasure (diracMix x₀ x a) := by
  rw [diracMix]
  split
  · infer_instance
  · rename_i h
    constructor
    have hsum : (∑ i, (a i : ℝ≥0∞)) ≠ 0 := by
      rw [← Nat.cast_sum]
      exact_mod_cast h
    have htop : (∑ i, (a i : ℝ≥0∞)) ≠ ∞ := by
      rw [← Nat.cast_sum]
      exact ENNReal.natCast_ne_top _
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [show (∑ i, (a i : ℝ≥0∞) * Measure.dirac (x i) univ)
        = ∑ i, (a i : ℝ≥0∞) by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [measure_univ, mul_one]]
    exact ENNReal.inv_mul_cancel hsum htop

omit [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω] [BorelSpace Ω] in
open scoped Classical in
/-- Lower bound for a Dirac mixture on a measurable set: the normalized
    weight of the atoms lying in the set, with any upper bound `m` on the
    total weight. -/
theorem le_diracMix_apply (x₀ : Ω) {N : ℕ} (x : Fin N → Ω) (a : Fin N → ℕ)
    {m : ℕ} (hm : (∑ i, a i) ≤ m) (E : Set Ω) :
    (m : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => x i ∈ E), (a i : ℝ≥0∞)
      ≤ diracMix x₀ x a E := by
  rcases eq_or_ne (∑ i, a i) 0 with hzero | hne
  · have hall : ∀ i ∈ Finset.univ.filter (fun i => x i ∈ E), (a i : ℝ≥0∞) = 0 := by
      intro i _
      have := Finset.sum_eq_zero_iff.mp hzero i (Finset.mem_univ i)
      exact_mod_cast this
    rw [Finset.sum_eq_zero hall, mul_zero]
    exact zero_le
  · rw [diracMix_sum_ne_zero x₀ x a hne]
    have hstep : ∑ i ∈ Finset.univ.filter (fun i => x i ∈ E), (a i : ℝ≥0∞)
        ≤ ∑ i, (a i : ℝ≥0∞) * Measure.dirac (x i) E := by
      calc ∑ i ∈ Finset.univ.filter (fun i => x i ∈ E), (a i : ℝ≥0∞)
          = ∑ i ∈ Finset.univ.filter (fun i => x i ∈ E),
              (a i : ℝ≥0∞) * Measure.dirac (x i) E := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Measure.dirac_apply_of_mem (Finset.mem_filter.mp hi).2, mul_one]
        _ ≤ ∑ i, (a i : ℝ≥0∞) * Measure.dirac (x i) E :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
    have hinv : (m : ℝ≥0∞)⁻¹ ≤ (∑ i, (a i : ℝ≥0∞))⁻¹ := by
      refine ENNReal.inv_le_inv.mpr ?_
      rw [← Nat.cast_sum]
      exact_mod_cast hm
    calc (m : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => x i ∈ E), (a i : ℝ≥0∞)
        ≤ (∑ i, (a i : ℝ≥0∞))⁻¹ * ∑ i, (a i : ℝ≥0∞) * Measure.dirac (x i) E :=
          mul_le_mul' hinv hstep
      _ = ((∑ i, (a i : ℝ≥0∞))⁻¹ • ∑ i, (a i : ℝ≥0∞) • Measure.dirac (x i)) E := by
          rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
          simp only [Measure.smul_apply, smul_eq_mul]

omit [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω] [BorelSpace Ω] in
/-- A probability measure exhausts any countable measurable cover:
    some finite subfamily captures all but `ε` of the mass. -/
theorem exists_measure_compl_partial_iUnion_lt
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : (⋃ n, s n) = univ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, μ ((⋃ j ∈ Finset.range N, s j)ᶜ) < ε := by
  have hanti : Antitone fun M => (⋃ j ∈ Finset.range M, s j)ᶜ := by
    intro M M' hMM'
    apply compl_subset_compl.mpr
    refine biUnion_subset_biUnion_left ?_
    intro j hj
    simp only [Finset.coe_range, mem_Iio] at hj ⊢
    omega
  have hinter : (⋂ M, (⋃ j ∈ Finset.range M, s j)ᶜ) = ∅ := by
    rw [← compl_iUnion,
      show (⋃ M, ⋃ j ∈ Finset.range M, s j) = ⋃ j, s j by
        ext x
        simp only [mem_iUnion, Finset.mem_range]
        exact ⟨fun ⟨_, j, _, hx⟩ => ⟨j, hx⟩, fun ⟨j, hx⟩ => ⟨j + 1, j, by omega, hx⟩⟩,
      hcover, compl_univ]
  have htendsto : Tendsto (fun M => μ ((⋃ j ∈ Finset.range M, s j)ᶜ))
      atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (s := fun M => (⋃ j ∈ Finset.range M, s j)ᶜ)
      (fun M => ((MeasurableSet.biUnion (Finset.range M).countable_toSet
        fun j _ => hs j).compl).nullMeasurableSet)
      hanti ⟨0, measure_ne_top μ _⟩
    rwa [hinter, measure_empty] at h
  exact (htendsto.eventually_lt_const hε).exists

omit [CompleteSpace Ω] in
omit [MetricSpace Ω] [SeparableSpace Ω] [BorelSpace Ω] [CompleteSpace Ω] in
open scoped Classical in
private theorem sum_floor_partition_mass_le (μ : ProbabilityMeasure Ω)
    {A : ℕ → Set Ω} (hAmble : ∀ n, MeasurableSet (A n))
    (hAdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (N m : ℕ) :
    (∑ i : Fin N, ⌊((μ : Measure Ω) (A i)).toReal * m⌋₊) ≤ m := by
  have hpart : (∑ n ∈ Finset.range N, (μ : Measure Ω) (A n)) ≤ 1 := by
    rw [← measure_biUnion_finset
      (fun i _ k _ hik => hAdisj hik) (fun n _ => hAmble n)]
    exact prob_le_one
  have hreal : (∑ n ∈ Finset.range N, ((μ : Measure Ω) (A n)).toReal) ≤ 1 := by
    rw [← ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)]
    calc (∑ n ∈ Finset.range N, (μ : Measure Ω) (A n)).toReal
        ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hpart
      _ = 1 := ENNReal.toReal_one
  have hcast : ((∑ i : Fin N, ⌊((μ : Measure Ω) (A i)).toReal * m⌋₊ : ℕ) : ℝ) ≤ m := by
    push_cast
    calc (∑ i : Fin N, (⌊((μ : Measure Ω) (A i)).toReal * m⌋₊ : ℝ))
        ≤ ∑ i : Fin N, ((μ : Measure Ω) (A i)).toReal * m :=
          Finset.sum_le_sum fun i _ => Nat.floor_le (by positivity)
      _ = (∑ i : Fin N, ((μ : Measure Ω) (A i)).toReal) * m := by
          rw [← Finset.sum_mul]
      _ ≤ 1 * m := by
          have hsum_range :
              (∑ i : Fin N, ((μ : Measure Ω) (A i)).toReal)
                = ∑ n ∈ Finset.range N, ((μ : Measure Ω) (A n)).toReal :=
            Fin.sum_univ_eq_sum_range
              (fun n => ((μ : Measure Ω) (A n)).toReal) N
          rw [hsum_range]
          nlinarith [hreal]
      _ = m := one_mul _
  exact_mod_cast hcast

omit [CompleteSpace Ω] in
open scoped Classical in
/-- B1+B2: every probability measure on a Polish space is within `3ε` in
    Lévy-Prokhorov distance of a normalized natural-weight Dirac mixture
    at points of any dense sequence. -/
theorem exists_diracMix_levyProkhorovDist_le
    (μ : ProbabilityMeasure Ω) {D : ℕ → Ω} (hD : DenseRange D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (a : Fin N → ℕ) (j : Fin N → ℕ),
      levyProkhorovDist (μ : Measure Ω)
        (diracMix (D 0) (fun i => D (j i)) a) ≤ 3 * ε := by
  -- measurable partition with small diameters
  obtain ⟨A, hAmble, hAbdd, hAdiam, hAcover, hAdisj⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le (Ω := Ω) hε
  -- finite head capturing all but ε of the mass
  obtain ⟨N, hN⟩ := exists_measure_compl_partial_iUnion_lt
    (μ : Measure Ω) hAmble hAcover (ε := ENNReal.ofReal ε)
    (by rw [ENNReal.ofReal_pos]; exact hε)
  -- atoms: dense points near each nonempty cell
  have hsel : ∀ n : ℕ, ∃ k : ℕ,
      (A n).Nonempty → ∃ p ∈ A n, dist (D k) p < ε := by
    intro n
    by_cases h : (A n).Nonempty
    · obtain ⟨p, hp⟩ := h
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hD p ε hε
      exact ⟨k, fun _ => ⟨p, hp, by rwa [dist_comm] at hk⟩⟩
    · exact ⟨0, fun hne => absurd hne h⟩
  choose j hj using hsel
  -- weights: floors of the rescaled masses, common denominator m
  set m : ℕ := ⌈(N : ℝ) / ε⌉₊ + 1 with hm
  have hmpos : 0 < m := Nat.succ_pos _
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  set a : Fin N → ℕ :=
    fun i => ⌊((μ : Measure Ω) (A i)).toReal * m⌋₊ with ha
  refine ⟨N, a, fun i => j i, ?_⟩
  set ν : Measure Ω := diracMix (D 0) (fun i : Fin N => D (j i)) a with hν
  -- total weight is at most m
  have hsum_le : (∑ i, a i) ≤ m :=
    sum_floor_partition_mass_le μ hAmble hAdisj N m
  -- per-cell mass bound by weights
  have hterm : ∀ i : Fin N, (μ : Measure Ω) (A i)
      ≤ ((a i : ℝ≥0∞) + 1) * (m : ℝ≥0∞)⁻¹ := by
    intro i
    have h1 : ((μ : Measure Ω) (A i)).toReal < ((a i : ℝ) + 1) / m := by
      rw [lt_div_iff₀ hmposR]
      exact_mod_cast Nat.lt_floor_add_one (((μ : Measure Ω) (A i)).toReal * m)
    calc (μ : Measure Ω) (A i)
        = ENNReal.ofReal (((μ : Measure Ω) (A i)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (((a i : ℝ) + 1) / m) :=
          ENNReal.ofReal_le_ofReal h1.le
      _ = ((a i : ℝ≥0∞) + 1) * (m : ℝ≥0∞)⁻¹ := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_inv_of_pos hmposR]
          congr 1
          · rw [show ((a i : ℝ) + 1) = (((a i + 1 : ℕ)) : ℝ) by push_cast; ring,
              ENNReal.ofReal_natCast]
            push_cast
            ring
          · rw [ENNReal.ofReal_natCast]
  -- floors budget: N/m ≤ ε
  have hNm : (N : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal ε := by
    have hreal : (N : ℝ) / m ≤ ε := by
      rw [div_le_iff₀ hmposR]
      have hceil : (N : ℝ) / ε ≤ (⌈(N : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
      have hmge : ((⌈(N : ℝ) / ε⌉₊ : ℝ)) + 1 ≤ m := by
        rw [hm]; push_cast; linarith
      have hNe : ((N : ℝ) / ε) * ε = N := div_mul_cancel₀ _ hε.ne'
      nlinarith
    calc (N : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹
        = ENNReal.ofReal ((N : ℝ) / m) := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_inv_of_pos hmposR, ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
  -- the one-sided Lévy-Prokhorov estimate
  refine levyProkhorovDist_le_of_forall_le (μ : Measure Ω) ν
    (by positivity) (fun ε' B hε' hB => ?_)
  have hεε' : 2 * ε < ε' := by linarith
  set S : Finset (Fin N) :=
    Finset.univ.filter (fun i => (A (i : ℕ) ∩ B).Nonempty) with hS
  -- atoms of cells meeting B land in the thickening
  have hatoms : ∀ i ∈ S, D (j (i : ℕ)) ∈ thickening ε' B := by
    intro i hiS
    obtain ⟨b, hbA, hbB⟩ := (Finset.mem_filter.mp hiS).2
    obtain ⟨p, hpA, hpd⟩ := hj (i : ℕ) ⟨b, hbA⟩
    refine Metric.mem_thickening_iff.mpr ⟨b, hbB, ?_⟩
    have hdiam : dist p b ≤ ε :=
      le_trans (Metric.dist_le_diam_of_mem (hAbdd _) hpA hbA) (hAdiam _)
    calc dist (D (j (i : ℕ))) b ≤ dist (D (j (i : ℕ))) p + dist p b :=
          dist_triangle _ _ _
      _ < ε + ε := by linarith
      _ < ε' := by linarith
  -- decompose μ B along the partition head
  have hsplit : (μ : Measure Ω) B
      ≤ (∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ))) + ENNReal.ofReal ε := by
    have hsubset : B ⊆ (⋃ i : Fin N, (A (i : ℕ) ∩ B))
        ∪ (⋃ n ∈ Finset.range N, A n)ᶜ := by
      intro pt hpt
      by_cases hin : pt ∈ ⋃ n ∈ Finset.range N, A n
      · left
        simp only [mem_iUnion, Finset.mem_range, exists_prop] at hin
        obtain ⟨n, hnN, hptn⟩ := hin
        exact mem_iUnion.mpr ⟨⟨n, hnN⟩, hptn, hpt⟩
      · right
        exact hin
    calc (μ : Measure Ω) B
        ≤ (μ : Measure Ω) ((⋃ i : Fin N, (A (i : ℕ) ∩ B))
            ∪ (⋃ n ∈ Finset.range N, A n)ᶜ) := measure_mono hsubset
      _ ≤ (μ : Measure Ω) (⋃ i : Fin N, (A (i : ℕ) ∩ B))
            + (μ : Measure Ω) ((⋃ n ∈ Finset.range N, A n)ᶜ) :=
          measure_union_le _ _
      _ ≤ (∑ i : Fin N, (μ : Measure Ω) (A (i : ℕ) ∩ B)) + ENNReal.ofReal ε :=
          add_le_add (measure_iUnion_fintype_le _ _) hN.le
      _ ≤ (∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ))) + ENNReal.ofReal ε := by
          refine add_le_add ?_ le_rfl
          rw [show (∑ i : Fin N, (μ : Measure Ω) (A (i : ℕ) ∩ B))
              = ∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ) ∩ B) from
            (Finset.sum_subset (Finset.filter_subset _ _) fun i _ hiS => by
              rw [Finset.mem_filter, not_and] at hiS
              rw [Set.not_nonempty_iff_eq_empty.mp
                (hiS (Finset.mem_univ i)), measure_empty]).symm]
          exact Finset.sum_le_sum fun i _ =>
            measure_mono inter_subset_left
  -- cell masses against the mixture on the thickening
  have hmass : (∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ)))
      ≤ ν (thickening ε' B) + ENNReal.ofReal ε := by
    calc (∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ)))
        ≤ ∑ i ∈ S, ((a i : ℝ≥0∞) + 1) * (m : ℝ≥0∞)⁻¹ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i ∈ S, (a i : ℝ≥0∞)) * (m : ℝ≥0∞)⁻¹
            + (S.card : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
          rw [← Finset.sum_mul, ← add_mul]
          congr 1
          rw [Finset.sum_add_distrib]
          simp
      _ ≤ (m : ℝ≥0∞)⁻¹ * (∑ i ∈ Finset.univ.filter
            (fun i : Fin N => D (j (i : ℕ)) ∈ thickening ε' B), (a i : ℝ≥0∞))
            + (N : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
          refine add_le_add ?_ ?_
          · rw [mul_comm]
            refine mul_le_mul' le_rfl ?_
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun _ _ _ => zero_le)
            intro i hiS
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ i, hatoms i hiS⟩
          · refine mul_le_mul' ?_ le_rfl
            have hcard : S.card ≤ N := by
              calc S.card ≤ (Finset.univ : Finset (Fin N)).card :=
                    Finset.card_le_card (Finset.subset_univ S)
                _ = N := by simp
            exact_mod_cast hcard
      _ ≤ ν (thickening ε' B) + ENNReal.ofReal ε := by
          refine add_le_add ?_ hNm
          exact le_diracMix_apply (D 0) _ a hsum_le _
  -- assemble
  calc (μ : Measure Ω) B
      ≤ (∑ i ∈ S, (μ : Measure Ω) (A (i : ℕ))) + ENNReal.ofReal ε := hsplit
    _ ≤ (ν (thickening ε' B) + ENNReal.ofReal ε) + ENNReal.ofReal ε :=
        add_le_add hmass le_rfl
    _ = ν (thickening ε' B) + ENNReal.ofReal (ε + ε) := by
        rw [add_assoc, ENNReal.ofReal_add hε.le hε.le]
    _ ≤ ν (thickening ε' B) + ENNReal.ofReal ε' :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (by linarith))

/-! ## Node B → C2: separability and the Polish instance for the LP space -/

instance : SeparableSpace (LevyProkhorov (ProbabilityMeasure Ω)) := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have : IsEmpty (ProbabilityMeasure Ω) := by
      constructor
      intro μ
      have h1 : (μ : Measure Ω) univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.mpr hΩ, measure_empty] at h1
      exact zero_ne_one h1
    have : IsEmpty (LevyProkhorov (ProbabilityMeasure Ω)) :=
      ⟨fun x => IsEmpty.elim ‹_› x.toMeasure⟩
    exact ⟨⟨∅, countable_empty, by
      rw [dense_iff_closure_eq, closure_empty]
      exact (Set.univ_eq_empty_iff.mpr ‹_›).symm⟩⟩
  · obtain ⟨D, hD⟩ := exists_dense_seq Ω
    set Φ : (Σ N : ℕ, (Fin N → ℕ) × (Fin N → ℕ))
        → LevyProkhorov (ProbabilityMeasure Ω) :=
      fun p => LevyProkhorov.ofMeasure
        (⟨diracMix (D 0) (fun i => D (p.2.2 i)) p.2.1, inferInstance⟩ :
          ProbabilityMeasure Ω) with hΦ
    refine ⟨⟨Set.range Φ, countable_range Φ, ?_⟩⟩
    have hdr : DenseRange Φ := by
      rw [Metric.denseRange_iff]
      intro x r hr
      obtain ⟨N, a, j, hle⟩ := exists_diracMix_levyProkhorovDist_le
        (x.toMeasure) hD (ε := r / 4) (by linarith)
      refine ⟨⟨N, a, j⟩, ?_⟩
      have hdist_eq : dist (Φ ⟨N, a, j⟩) x
          = levyProkhorovDist
            (diracMix (D 0) (fun i => D (j i)) a)
            ((x.toMeasure : ProbabilityMeasure Ω) : Measure Ω) := rfl
      rw [dist_comm, hdist_eq, levyProkhorovDist_comm]
      calc levyProkhorovDist
            ((x.toMeasure : ProbabilityMeasure Ω) : Measure Ω)
            (diracMix (D 0) (fun i => D (j i)) a) ≤ 3 * (r / 4) := hle
        _ < r := by linarith
    exact hdr

instance : SecondCountableTopology (LevyProkhorov (ProbabilityMeasure Ω)) :=
  UniformSpace.secondCountable_of_separable _

/-- C2: the Lévy-Prokhorov space of probability measures over a Polish
    space is Polish (complete + separable metric). -/
instance : PolishSpace (LevyProkhorov (ProbabilityMeasure Ω)) := by
  infer_instance

/-! ## C3: transfer along the homeomorphism -/

/-- **W1, final form**: the space of probability measures on a Polish
    space, with the topology of weak convergence, is Polish. -/
instance ProbabilityMeasure.instPolishSpace
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    PolishSpace (ProbabilityMeasure X) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact (LevyProkhorov.probabilityMeasureHomeomorph
    (Ω := X)).isClosedEmbedding.polishSpace

/-! ## W2: the Giry σ-algebra is contained in the Borel σ-algebra of the
    weak topology

The evaluation maps `γ ↦ γ s` are Borel on `ProbabilityMeasure Ω`:
continuous test integrals give closed sets (outer approximation), and a
π-λ induction extends to all Borel sets. Consequently the coercion to
`Measure Ω` (with its Giry σ-algebra) is Borel-measurable — this is what
lets `ProbabilityMeasure Ω` act as a parameter space for kernels. -/

omit [SeparableSpace Ω] [CompleteSpace Ω] in
/-- Integration of a bounded continuous test function is continuous in the
    measure, for the topology of weak convergence. -/
theorem probabilityMeasure_continuous_lintegral (f : BoundedContinuousFunction Ω ℝ≥0) :
    Continuous fun γ : ProbabilityMeasure Ω =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂(γ : Measure Ω) := by
  have heq : (fun γ : ProbabilityMeasure Ω =>
        ∫⁻ x, (f x : ℝ≥0∞) ∂(γ : Measure Ω))
      = fun γ => ((γ.toFiniteMeasure.testAgainstNN f : ℝ≥0) : ℝ≥0∞) := by
    funext γ
    rw [FiniteMeasure.testAgainstNN_coe_eq]
    rfl
  rw [heq]
  exact ENNReal.continuous_coe.comp
    ((FiniteMeasure.continuous_testAgainstNN_eval f).comp
      (ProbabilityMeasure.toFiniteMeasure_isEmbedding Ω).continuous)

omit [SeparableSpace Ω] [CompleteSpace Ω] in
/-- The measure of a closed set is a Borel function of the measure. -/
theorem probabilityMeasure_borel_measurable_apply_isClosed
    {F : Set Ω} (hF : IsClosed F) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) F) := by
  let : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  have : BorelSpace (ProbabilityMeasure Ω) := ⟨rfl⟩
  have hlim : Tendsto
      (fun n => fun γ : ProbabilityMeasure Ω =>
        ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂(γ : Measure Ω))
      atTop (𝓝 fun γ => (γ : Measure Ω) F) := by
    rw [tendsto_pi_nhds]
    intro γ
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (γ : Measure Ω)
  exact measurable_of_tendsto_metrizable
    (fun n => (probabilityMeasure_continuous_lintegral (hF.apprSeq n)).measurable)
    hlim

omit [SeparableSpace Ω] [CompleteSpace Ω] in
/-- The measure of any Borel set is a Borel function of the measure
    (π-λ induction from the closed sets). -/
theorem probabilityMeasure_borel_measurable_apply
    {s : Set Ω} (hs : MeasurableSet s) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) s) := by
  let : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  have : BorelSpace (ProbabilityMeasure Ω) := ⟨rfl⟩
  induction s, hs using MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace Ω))
    (s := {t : Set Ω | IsClosed t})
    ((BorelSpace.measurable_eq (α := Ω)).trans borel_eq_generateFrom_isClosed)
    isPiSystem_isClosed with
  | empty =>
    simp only [measure_empty]
    exact measurable_const
  | basic t ht =>
    exact probabilityMeasure_borel_measurable_apply_isClosed ht
  | compl t htm iht =>
    have heq : (fun γ : ProbabilityMeasure Ω => (γ : Measure Ω) tᶜ)
        = fun γ : ProbabilityMeasure Ω => 1 - (γ : Measure Ω) t := by
      funext γ
      rw [prob_compl_eq_one_sub htm]
    rw [heq]
    exact measurable_const.sub iht
  | iUnion f hdisj hfm ihf =>
    have heq : (fun γ : ProbabilityMeasure Ω => (γ : Measure Ω) (⋃ n, f n))
        = fun γ : ProbabilityMeasure Ω => ∑' n, (γ : Measure Ω) (f n) := by
      funext γ
      exact measure_iUnion hdisj hfm
    rw [heq]
    exact Measurable.tsum ihf

omit [SeparableSpace Ω] [CompleteSpace Ω] in
/-- **W2**: the coercion from probability measures (Borel σ-algebra of the
    weak topology) to measures (Giry σ-algebra) is measurable. -/
theorem probabilityMeasure_borel_measurable_toMeasure :
    @Measurable (ProbabilityMeasure Ω) (Measure Ω)
      (borel (ProbabilityMeasure Ω)) inferInstance
      ((↑) : ProbabilityMeasure Ω → Measure Ω) := by
  let : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  exact Measure.measurable_measure.mpr
    fun s hs => probabilityMeasure_borel_measurable_apply hs

end

/-! ## The Giry-valued equalizer

Companion to W2: for measurable families of probability measures, the set
where two families agree is measurable. This is what makes the feasibility
correspondences of the Bellman recursion Borel. -/

noncomputable section

/-- The π-system generated by a countable collection of sets is countable:
    every element of `generatePiSystem S` is the intersection `⋂₀ T` of a
    finite subcollection `T ⊆ S`. -/
theorem countable_generatePiSystem {α : Type*} {S : Set (Set α)}
    (hS : S.Countable) : (generatePiSystem S).Countable := by
  refine ((countable_ofPred_finite_subset hS).image fun T => ⋂₀ T).mono
    fun t ht => ?_
  induction ht with
  | base h_s =>
    exact ⟨{_}, ⟨finite_singleton _, singleton_subset_iff.mpr h_s⟩,
      sInter_singleton _⟩
  | inter _ _ _ ih_s ih_u =>
    obtain ⟨T₁, ⟨hT₁fin, hT₁sub⟩, rfl⟩ := ih_s
    obtain ⟨T₂, ⟨hT₂fin, hT₂sub⟩, rfl⟩ := ih_u
    exact ⟨T₁ ∪ T₂, ⟨hT₁fin.union hT₂fin, union_subset hT₁sub hT₂sub⟩,
      sInter_union T₁ T₂⟩

/-- **Giry-valued equalizer.** If `F G : α → Measure W` are measurable
    families of probability measures on a Polish space `W`, then
    `{a | F a = G a}` is measurable: two probability measures coincide as
    soon as they agree on the countable π-system generated by a countable
    topological basis (`ext_of_generate_finite`), so the equalizer is a
    countable intersection of measurable `ℝ≥0∞`-equalizers. -/
theorem measurableSet_eq_measure {α : Type*} [MeasurableSpace α] {W : Type*}
    [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]
    {F G : α → Measure W} (hF : Measurable F) (hG : Measurable G)
    (hFfin : ∀ a, IsProbabilityMeasure (F a))
    (hGfin : ∀ a, IsProbabilityMeasure (G a)) :
    MeasurableSet {a | F a = G a} := by
  have hCcnt : (generatePiSystem (countableBasis W)).Countable :=
    countable_generatePiSystem (countable_countableBasis W)
  have hCpi : IsPiSystem (generatePiSystem (countableBasis W)) :=
    isPiSystem_generatePiSystem _
  have hCgen : ‹MeasurableSpace W› =
      MeasurableSpace.generateFrom (generatePiSystem (countableBasis W)) := by
    rw [generateFrom_generatePiSystem_eq,
      ← (isBasis_countableBasis W).borel_eq_generateFrom]
    exact ‹BorelSpace W›.measurable_eq
  have hCmeas : ∀ s ∈ generatePiSystem (countableBasis W), MeasurableSet s :=
    fun s hs => generatePiSystem_measurableSet
      (fun _ hu => (isOpen_of_mem_countableBasis hu).measurableSet) s hs
  have hset : {a | F a = G a} =
      ⋂ s ∈ generatePiSystem (countableBasis W), {a | F a s = G a s} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    refine ⟨fun h s _ => by rw [h], fun h => ?_⟩
    have := hFfin a
    exact ext_of_generate_finite _ hCgen hCpi h
      (by rw [(hFfin a).measure_univ, (hGfin a).measure_univ])
  rw [hset]
  exact MeasurableSet.biInter hCcnt fun s hs =>
    measurableSet_eq_fun ((Measure.measurable_coe (hCmeas s hs)).comp hF)
      ((Measure.measurable_coe (hCmeas s hs)).comp hG)

end
