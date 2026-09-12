/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Defs
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Probability.CDF
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Straight pieces of finite Hausdorff sets

This file proves the positive-piece form of Delaware's straight-set theorem for Hausdorff
one-measure in the Euclidean plane.  It also records the elementary restriction API used later.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal MeasureTheory NNReal Topology

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Straightness passes to a smaller measure. -/
theorem IsStraightMeasure.mono {μ ν : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : IsStraightMeasure μ)
    (hν : ν ≤ μ) : IsStraightMeasure ν := by
  intro s hs
  exact (hν s).trans (hμ s hs)

/-- Every restriction of a straight measure is straight. -/
theorem IsStraightMeasure.restrict {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : IsStraightMeasure μ)
    (s : Set (EuclideanSpace ℝ (Fin 2))) : IsStraightMeasure (μ.restrict s) :=
  hμ.mono Measure.restrict_le_self

/-- Straightness of a Hausdorff restriction passes to measurable subsets. -/
theorem isStraightMeasure_restrict_mono {s t : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : IsStraightMeasure (μH[1].restrict s)) (ht : t ⊆ s) :
    IsStraightMeasure (μH[1].restrict t) :=
  hs.mono (Measure.restrict_mono ht le_rfl)

/-- Hausdorff content with diameter cutoff `r`, before passage to infinitesimal scales. -/
private def hausdorffPre (r : ℝ≥0∞) : OuterMeasure X :=
  OuterMeasure.mkMetric'.pre (fun s : Set X ↦ Metric.ediam s) r

private theorem hausdorffPre_le {r : ℝ≥0∞} (hr : 0 < r) :
    hausdorffPre (X := X) r ≤ (μH[1] : Measure X).toOuterMeasure := by
  change hausdorffPre (X := X) r ≤
    (Measure.mkMetric (fun d ↦ d ^ (1 : ℝ)) : Measure X).toOuterMeasure
  rw [Measure.mkMetric_toOuterMeasure]
  change OuterMeasure.mkMetric'.pre (fun s : Set X ↦ Metric.ediam s) r ≤
    OuterMeasure.mkMetric (fun d ↦ d ^ (1 : ℝ))
  simpa only [OuterMeasure.mkMetric, OuterMeasure.mkMetric', ENNReal.rpow_one] using
    (le_iSup₂ (f := fun q (_ : 0 < q) ↦
      OuterMeasure.mkMetric'.pre (fun s : Set X ↦ Metric.ediam s) q) r hr)

private theorem tendsto_hausdorffPre (s : Set X) :
    Tendsto (fun r ↦ hausdorffPre (X := X) r s) (𝓝[>] 0) (𝓝 (μH[1] s)) := by
  convert OuterMeasure.mkMetric'.tendsto_pre (fun t : Set X ↦ Metric.ediam t) s using 1
  · rfl
  · congr 1
    change μH[1] s = OuterMeasure.mkMetric (fun d ↦ d) s
    rw [OuterMeasure.coe_mkMetric]
    simp only [Measure.hausdorffMeasure, ENNReal.rpow_one]

/-- An atomless finite measure on the plane has measurable subsets of every prescribed fraction. -/
private theorem exists_subset_measure_eq_mul
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    [NullSingletonClass μ] {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : MeasurableSet s) {q : ℝ}
    (hq_zero : 0 ≤ q) (hq_one : q ≤ 1) :
    ∃ t : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet t ∧ t ⊆ s ∧ μ t = ENNReal.ofReal q * μ s := by
  rcases eq_or_lt_of_le hq_zero with rfl | hq_pos
  · exact ⟨∅, MeasurableSet.empty, empty_subset s, by simp⟩
  rcases hq_one.eq_or_lt with rfl | hq_lt
  · exact ⟨s, hs, Subset.rfl, by simp⟩
  by_cases hμs : μ s = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset s, by simp [hμs]⟩
  have hμs_pos : 0 < μ s := pos_iff_ne_zero.mpr hμs
  let f : (EuclideanSpace ℝ (Fin 2)) → ℝ := embeddingReal (EuclideanSpace ℝ (Fin 2))
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal (EuclideanSpace ℝ (Fin 2))
  let ν : Measure ℝ := (μ.restrict s).map f
  have hν_univ : ν univ = μ s := by
    simp only [ν, Measure.map_apply hf.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  haveI : NullSingletonClass ν := by
    refine ⟨fun x ↦ ?_⟩
    change ((μ.restrict s).map f) {x} = 0
    rw [Measure.map_apply hf.measurable (MeasurableSet.singleton x)]
    have hsub : (f ⁻¹' {x}).Subsingleton := by
      intro y hy z hz
      apply hf.injective
      simpa only [mem_preimage, mem_singleton_iff] using hy.trans hz.symm
    exact hsub.measure_zero (μ.restrict s)
  let νf : FiniteMeasure ℝ := ⟨ν, inferInstance⟩
  have hν_pos : 0 < ν univ := by simpa only [hν_univ] using hμs_pos
  have hν_ne : νf ≠ 0 := by
    intro hzero
    have hzero' : ν = 0 := congrArg (fun m : FiniteMeasure ℝ ↦ (m : Measure ℝ)) hzero
    have : ν univ = 0 := by rw [hzero']; rfl
    exact hν_pos.ne' this
  let P : ProbabilityMeasure ℝ := νf.normalize
  letI : IsProbabilityMeasure (P : Measure ℝ) := P.property
  haveI : NullSingletonClass (P : Measure ℝ) := by
    refine ⟨fun x ↦ ?_⟩
    have hνf_single : νf {x} = 0 := by
      apply ENNReal.coe_injective
      rw [νf.ennreal_coeFn_eq_coeFn_toMeasure]
      change ν {x} = 0
      exact measure_singleton x
    rw [← νf.normalize.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [νf.normalize_eq_of_nonzero hν_ne]
    simp only [hνf_single, mul_zero, ENNReal.coe_zero]
  let F : ℝ → ℝ := ProbabilityTheory.cdf (P : Measure ℝ)
  have hF_mono : Monotone F := ProbabilityTheory.monotone_cdf _
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [hF_mono.continuousAt_iff_leftLim_eq_rightLim]
    change leftLim (ProbabilityTheory.cdf (P : Measure ℝ)) x =
      rightLim (ProbabilityTheory.cdf (P : Measure ℝ)) x
    rw [(ProbabilityTheory.cdf (P : Measure ℝ)).rightLim_eq]
    apply le_antisymm (hF_mono.leftLim_le le_rfl)
    have hz : ENNReal.ofReal
        (ProbabilityTheory.cdf (P : Measure ℝ) x -
          leftLim (ProbabilityTheory.cdf (P : Measure ℝ)) x) = 0 := by
      rw [← StieltjesFunction.measure_singleton, ProbabilityTheory.measure_cdf]
      exact measure_singleton x
    exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz)
  have hF_bot : Tendsto F atBot (𝓝 0) := ProbabilityTheory.tendsto_cdf_atBot _
  have hF_top : Tendsto F atTop (𝓝 1) := ProbabilityTheory.tendsto_cdf_atTop _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, F x₀ < q :=
    (hF_bot.eventually (eventually_lt_nhds hq_pos)).exists
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, q < F x₁ :=
    (hF_top.eventually (eventually_gt_nhds hq_lt)).exists
  have hx_le : x₀ ≤ x₁ := by
    by_contra hnot
    exact (not_le_of_gt (hx₀.trans hx₁)) (hF_mono (not_le.mp hnot).le)
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hx_le hF_cont.continuousOn
    ⟨hx₀.le, hx₁.le⟩
  let t : Set (EuclideanSpace ℝ (Fin 2)) := s ∩ f ⁻¹' Iic x
  refine ⟨t, hs.inter (measurableSet_Iic.preimage hf.measurable), inter_subset_left, ?_⟩
  have hmap : ν (Iic x) = μ t := by
    change ((μ.restrict s).map f) (Iic x) = μ t
    rw [Measure.map_apply hf.measurable measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage hf.measurable)]
    exact congrArg μ (inter_comm _ _)
  rw [← hmap]
  change (νf : Measure ℝ) (Iic x) = ENNReal.ofReal q * μ s
  rw [← νf.ennreal_coeFn_eq_coeFn_toMeasure]
  have hnorm := congrArg (fun z : ℝ≥0 ↦ (z : ℝ≥0∞))
    (νf.self_eq_mass_mul_normalize (Iic x))
  rw [hnorm]
  rw [ENNReal.coe_mul, νf.normalize.ennreal_coeFn_eq_coeFn_toMeasure]
  change (νf.mass : ℝ≥0∞) * (P : Measure ℝ) (Iic x) = ENNReal.ofReal q * μ s
  rw [← ProbabilityTheory.ofReal_cdf (P : Measure ℝ), ← hx]
  rw [mul_comm]
  congr 1
  rw [FiniteMeasure.ennreal_mass]
  change ν univ = μ s
  exact hν_univ

private def lossWeight (n : ℕ) : ℝ≥0∞ :=
  (8 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ n

private theorem lossWeight_pos (n : ℕ) : 0 < lossWeight n := by
  rw [lossWeight, ENNReal.mul_pos_iff]
  exact ⟨by norm_num, ENNReal.pow_pos (by norm_num) n⟩

private theorem lossWeight_lt_one (n : ℕ) : lossWeight n < 1 := by
  calc
    lossWeight n ≤ (8 : ℝ≥0∞)⁻¹ * 1 := by
      rw [lossWeight]
      gcongr
      exact pow_le_one₀ (by positivity) (by norm_num)
    _ < 1 := by norm_num

private theorem lossWeight_le_eighth (n : ℕ) :
    lossWeight n ≤ (8 : ℝ≥0∞)⁻¹ := by
  calc
    lossWeight n ≤ (8 : ℝ≥0∞)⁻¹ * 1 := by
      rw [lossWeight]
      gcongr
      exact pow_le_one₀ (by positivity) (by norm_num)
    _ = (8 : ℝ≥0∞)⁻¹ := mul_one _

private def thinningFraction (n : ℕ) : ℝ≥0 :=
  1 - 2 * (lossWeight n).toNNReal

private theorem two_lossWeight_toNNReal_lt_one (n : ℕ) :
    2 * (lossWeight n).toNNReal < 1 := by
  apply ENNReal.coe_lt_coe.mp
  rw [ENNReal.coe_mul, ENNReal.coe_two,
    ENNReal.coe_toNNReal (lossWeight_lt_one n).ne_top, ENNReal.coe_one]
  calc
    2 * lossWeight n ≤ 2 * (8 : ℝ≥0∞)⁻¹ := by gcongr; exact lossWeight_le_eighth n
    _ < 2 * (2 : ℝ≥0∞)⁻¹ := by
      apply ENNReal.mul_lt_mul_right (by norm_num) (by norm_num)
      exact ENNReal.inv_lt_inv.mpr (by norm_num)
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private theorem thinningFraction_pos (n : ℕ) : 0 < thinningFraction n := by
  rw [thinningFraction, tsub_pos_iff_lt]
  exact two_lossWeight_toNNReal_lt_one n

private theorem thinningFraction_le_one (n : ℕ) : thinningFraction n ≤ 1 :=
  tsub_le_self

private theorem thinningFraction_compensates (n : ℕ) :
    (thinningFraction n : ℝ≥0∞) * (1 + lossWeight n) ^ 2 ≤ 1 := by
  let q : ℝ≥0 := (lossWeight n).toNNReal
  have hq : (q : ℝ≥0∞) = lossWeight n :=
    ENNReal.coe_toNNReal (lossWeight_lt_one n).ne_top
  have htwo : 2 * q ≤ 1 := (two_lossWeight_toNNReal_lt_one n).le
  have hcomp : thinningFraction n * (1 + q) ^ 2 ≤ (1 : ℝ≥0) := by
    change (1 - 2 * q) * (1 + q) ^ 2 ≤ 1
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_mul, NNReal.coe_sub htwo, NNReal.coe_one, NNReal.coe_add,
      NNReal.coe_pow]
    have hq_nonneg : 0 ≤ (q : ℝ) := q.2
    rw [show (1 - ((2 : ℝ≥0) : ℝ) * (q : ℝ)) * (1 + q) ^ 2 =
      1 - q ^ 2 * (3 + 2 * q) by norm_num; ring]
    exact sub_le_self 1 (mul_nonneg (sq_nonneg (q : ℝ)) (by positivity))
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_add, ENNReal.coe_one, hq] using
    ENNReal.coe_le_coe.mpr hcomp

private theorem one_sub_thinningFraction (n : ℕ) :
    (1 : ℝ≥0) - thinningFraction n = 2 * (lossWeight n).toNNReal := by
  rw [thinningFraction, tsub_tsub_cancel_of_le (two_lossWeight_toNNReal_lt_one n).le]

private theorem one_sub_thinningFraction_ennreal (n : ℕ) :
    (1 : ℝ≥0∞) - thinningFraction n = 2 * lossWeight n := by
  rw [← ENNReal.coe_one, ← ENNReal.coe_sub, one_sub_thinningFraction,
    ENNReal.coe_mul, ENNReal.coe_two,
    ENNReal.coe_toNNReal (lossWeight_lt_one n).ne_top]

private theorem tsum_lossWeight : ∑' n : ℕ, lossWeight n = (4 : ℝ≥0∞)⁻¹ := by
  simp_rw [lossWeight]
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_geometric]
  rw [ENNReal.one_sub_inv_two, inv_inv]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [mul_assoc, show (2 : ℝ≥0∞) * 4 = 8 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The first ball in a dense enumeration that reaches a point. -/
private def metricCell (r : ℝ≥0) (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ball (denseSeq (EuclideanSpace ℝ (Fin 2)) n) r \
    ⋃ k : Fin n, ball (denseSeq (EuclideanSpace ℝ (Fin 2)) k) r

private theorem measurableSet_metricCell (r : ℝ≥0) (n : ℕ) :
    MeasurableSet (metricCell r n) :=
  Metric.isOpen_ball.measurableSet.diff <| MeasurableSet.iUnion fun _ ↦
    Metric.isOpen_ball.measurableSet

private theorem pairwiseDisjoint_metricCell (r : ℝ≥0) :
    Pairwise (Disjoint on metricCell r) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · apply Set.disjoint_left.2
    intro x hxm hxn
    exact hxn.2 (mem_iUnion.2 ⟨⟨m, hmn⟩, hxm.1⟩)
  · apply Set.disjoint_left.2
    intro x hxm hxn
    exact hxm.2 (mem_iUnion.2 ⟨⟨n, hnm⟩, hxn.1⟩)

private theorem iUnion_metricCell (r : ℝ≥0) (hr : 0 < r) :
    ⋃ n : ℕ, metricCell r n = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  have hex : ∃ n : ℕ, x ∈ ball (denseSeq (EuclideanSpace ℝ (Fin 2)) n) r := by
    obtain ⟨n, hn⟩ :
        ∃ n : ℕ, dist x (denseSeq (EuclideanSpace ℝ (Fin 2)) n) < (r : ℝ) :=
      (denseRange_denseSeq (EuclideanSpace ℝ (Fin 2))).exists_dist_lt x hr
    exact ⟨n, Metric.mem_ball.mpr hn⟩
  let n := Nat.find hex
  apply mem_iUnion.2
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro hx
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hk)) k.isLt

private theorem cells_meeting_subset_thickening
    (r : ℝ≥0) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    (⋃ k : {n // (metricCell r n ∩ s).Nonempty}, metricCell r k) ⊆
      thickening (2 * r) s := by
  intro x hx
  obtain ⟨k, hxk⟩ := mem_iUnion.1 hx
  obtain ⟨z, hzk, hzs⟩ := k.property
  rw [Metric.mem_thickening_iff]
  refine ⟨z, hzs, ?_⟩
  calc
    dist x z ≤
        dist x (denseSeq (EuclideanSpace ℝ (Fin 2)) k) +
          dist z (denseSeq (EuclideanSpace ℝ (Fin 2)) k) :=
      dist_triangle_right _ _ _
    _ < r + r := add_lt_add hxk.1 hzk.1
    _ = 2 * r := (two_mul (r : ℝ)).symm

private def descendingRadius (R : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => min 1 (R 0)
  | n + 1 => min (descendingRadius R n / 2) (R (n + 1))

private theorem descendingRadius_pos {R : ℕ → ℝ≥0} (hR : ∀ n, 0 < R n) :
    ∀ n, 0 < descendingRadius R n := by
  intro n
  induction n with
  | zero => simpa only [descendingRadius, lt_min_iff, zero_lt_one, true_and] using hR 0
  | succ n ih =>
      rw [descendingRadius, lt_min_iff]
      exact ⟨div_pos ih (by norm_num), hR (n + 1)⟩

private theorem descendingRadius_le (R : ℕ → ℝ≥0) (n : ℕ) :
    descendingRadius R n ≤ R n := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n => exact min_le_right _ _

private theorem descendingRadius_succ_lt {R : ℕ → ℝ≥0} (hR : ∀ n, 0 < R n)
    (n : ℕ) : descendingRadius R (n + 1) < descendingRadius R n := by
  calc
    descendingRadius R (n + 1) ≤ descendingRadius R n / 2 := min_le_left _ _
    _ < descendingRadius R n := NNReal.half_lt_self (descendingRadius_pos hR n).ne'

private theorem descendingRadius_le_invPow (R : ℕ → ℝ≥0) (n : ℕ) :
    (descendingRadius R n : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  induction n with
  | zero => simpa only [descendingRadius, pow_zero, ENNReal.coe_one] using
      ENNReal.coe_le_coe.mpr (min_le_left 1 (R 0))
  | succ n ih =>
      calc
        (descendingRadius R (n + 1) : ℝ≥0∞) ≤
            (descendingRadius R n / 2 : ℝ≥0) := by
          exact_mod_cast min_le_left (descendingRadius R n / 2) (R (n + 1))
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * 2⁻¹ := by
          rw [ENNReal.coe_div (by norm_num), ENNReal.coe_two, div_eq_mul_inv]
          gcongr
        _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := (pow_succ _ _).symm

private theorem exists_descendingRadius_interval {R : ℕ → ℝ≥0} {d : ℝ≥0∞}
    (hd : 0 < d) (hdR : d < descendingRadius R 0) :
    ∃ n : ℕ, (descendingRadius R (n + 1) : ℝ≥0∞) ≤ d ∧
      d < descendingRadius R n := by
  classical
  have hex : ∃ n : ℕ, (descendingRadius R n : ℝ≥0∞) ≤ d := by
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hd.ne'
    exact ⟨n, (descendingRadius_le_invPow R n).trans hn.le⟩
  have hfind_ne : Nat.find hex ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hdR) (by simpa only [hzero] using Nat.find_spec hex)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
  refine ⟨n, by simpa only [hn] using Nat.find_spec hex, ?_⟩
  exact lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))

/-- A finite Hausdorff set has an arbitrarily large subset that is straight up to any prescribed
factor larger than one, uniformly below some scale. -/
private theorem exists_large_almostStraightSubset
    {e : Set (EuclideanSpace ℝ (Fin 2))} (he : MeasurableSet e)
    (he_fin : μH[1] e < ∞) {c d : ℝ≥0∞} (hd : d < μH[1] e)
    (hc_pos : 0 < c) (hc_one : c < 1) :
    ∃ a : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet a ∧ a ⊆ e ∧ d < μH[1] a ∧
      ∃ r : ℝ≥0∞, 0 < r ∧ ∀ s : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet s → Metric.ediam s ≤ r →
        μH[1] (a ∩ s) ≤ c⁻¹ * Metric.ediam s := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := μH[1].restrict e
  have hμe : μ e = μH[1] e := Measure.restrict_apply_self μH[1] e
  have hc_ne_top : c ≠ ∞ := hc_one.ne_top
  have hweight_pos : 0 < 1 - c := tsub_pos_iff_lt.mpr hc_one
  have hweight_ne_top : 1 - c ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
  have hmul : c * μH[1] e + (1 - c) * d < μH[1] e := by
    calc
      c * μH[1] e + (1 - c) * d <
          c * μH[1] e + (1 - c) * μH[1] e := by
        apply ENNReal.add_lt_add_left (ENNReal.mul_ne_top hc_ne_top he_fin.ne)
        exact ENNReal.mul_lt_mul_right hweight_pos.ne' hweight_ne_top hd
      _ = (c + (1 - c)) * μH[1] e := (add_mul _ _ _).symm
      _ = μH[1] e := by rw [add_tsub_cancel_of_le hc_one.le, one_mul]
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ≥0∞),
      c * μH[1] e + (1 - c) * d < hausdorffPre (X := (EuclideanSpace ℝ (Fin 2))) r e :=
    (tendsto_hausdorffPre e).eventually (eventually_gt_nhds hmul)
  obtain ⟨r, hr_pos, hr_large⟩ :
      ∃ r : ℝ≥0∞, 0 < r ∧
        c * μH[1] e + (1 - c) * d < hausdorffPre (X := (EuclideanSpace ℝ (Fin 2))) r e := by
    simpa only [mem_Ioi, and_comm] using (hevent.and self_mem_nhdsWithin).exists
  let p : OuterMeasure (EuclideanSpace ℝ (Fin 2)) := hausdorffPre r
  let Good : Set (Set (Set (EuclideanSpace ℝ (Fin 2)))) :=
    {C | (∀ b ∈ C, MeasurableSet b ∧ b ⊆ e ∧ p b < c * μ b) ∧
      C.PairwiseDisjoint id}
  obtain ⟨C, hC⟩ : ∃ C, Maximal (fun D ↦ D ∈ Good) C := by
    refine zorn_subset Good fun U hU hchain ↦ ?_
    refine ⟨⋃₀ U, ?_, fun D hD ↦ subset_sUnion_of_mem hD⟩
    refine ⟨?_, (pairwiseDisjoint_sUnion hchain.directedOn).2 fun D hD ↦ (hU hD).2⟩
    intro b hb
    obtain ⟨D, hDU, hbD⟩ := hb
    exact (hU hDU).1 b hbD
  have hC_mem : C ∈ Good := hC.prop
  have hC_pos (b : C) : 0 < μ b := by
    have : 0 < c * μ b := (bot_le : 0 ≤ p b).trans_lt (hC_mem.1 b b.2).2.2
    exact (ENNReal.mul_pos_iff.mp this).2
  letI : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using he_fin⟩
  haveI : Countable C := by
    apply Set.countable_univ_iff.mp
    have hcount := Measure.countable_meas_pos_of_disjoint_iUnion
      (μ := μ) (As := fun b : C ↦ (b : Set (EuclideanSpace ℝ (Fin 2))))
      (fun b ↦ (hC_mem.1 b b.2).1)
      (hC_mem.2.subtype _ _)
    simpa only [hC_pos, setOf_true] using hcount
  have C_count : C.Countable := Set.countable_coe_iff.mp inferInstance
  have hUnion_meas : MeasurableSet (⋃₀ C) :=
    MeasurableSet.sUnion C_count fun b hb ↦ (hC_mem.1 b hb).1
  have hUnion_sub : ⋃₀ C ⊆ e :=
    sUnion_subset fun b hb ↦ (hC_mem.1 b hb).2.1
  let a : Set (EuclideanSpace ℝ (Fin 2)) := e \ ⋃₀ C
  have ha_meas : MeasurableSet a := he.diff hUnion_meas
  have ha_sub : a ⊆ e := sdiff_subset
  have no_bad {t : Set (EuclideanSpace ℝ (Fin 2))} (ht : MeasurableSet t) (hta : t ⊆ a) :
      c * μ t ≤ p t := by
    by_contra hnot
    have ht_bad : p t < c * μ t := lt_of_not_ge hnot
    have ht_pos : 0 < μ t := by
      have : 0 < c * μ t := (bot_le : 0 ≤ p t).trans_lt ht_bad
      exact (ENNReal.mul_pos_iff.mp this).2
    have ht_not_mem : t ∉ C := by
      intro htC
      have ht_empty : t = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hxt
        have hxa := hta hxt
        exact hxa.2 (subset_sUnion_of_mem htC hxt)
      rw [ht_empty, measure_empty] at ht_pos
      exact (lt_irrefl 0 ht_pos)
    apply ht_not_mem
    apply hC.mem_of_prop_insert
    refine ⟨?_, hC_mem.2.insert fun b hb hbt ↦ ?_⟩
    · intro b hb
      rcases hb with rfl | hb
      · exact ⟨ht, hta.trans ha_sub, ht_bad⟩
      · exact hC_mem.1 b hb
    · exact Disjoint.mono hta (subset_sUnion_of_mem hb) disjoint_sdiff_left
  have ha_large : d < μH[1] a := by
    have hμa : μ a = μH[1] a := by
      change (μH[1].restrict e) a = μH[1] a
      rw [Measure.restrict_apply ha_meas, inter_eq_left.mpr ha_sub]
    by_contra hnot
    have hμa_le : μ a ≤ d := by simpa only [hμa] using not_lt.mp hnot
    have hpa : p a ≤ μ a := by
      calc
        p a ≤ μH[1] a := hausdorffPre_le hr_pos a
        _ = μ a := hμa.symm
    have hE_union : e = ⋃₀ C ∪ a := by
      change e = ⋃₀ C ∪ (e \ ⋃₀ C)
      rw [union_sdiff_cancel hUnion_sub]
    have hp_union : p (⋃₀ C) ≤ ∑' b : C, p b := by
      rw [sUnion_eq_biUnion]
      exact measure_biUnion_le p C_count id
    have hμ_union : μ (⋃₀ C) = ∑' b : C, μ b :=
      measure_sUnion C_count hC_mem.2 fun b hb ↦ (hC_mem.1 b hb).1
    have hpμ : ∑' b : C, p b ≤ c * ∑' b : C, μ b := by
      calc
        (∑' b : C, p b) ≤ ∑' b : C, c * μ b :=
          ENNReal.tsum_le_tsum fun b ↦ (hC_mem.1 b b.2).2.2.le
        _ = c * ∑' b : C, μ b := ENNReal.tsum_mul_left
    have hμ_parts : μ e = μ (⋃₀ C) + μ a := by
      rw [hE_union, MeasureTheory.measure_union disjoint_sdiff_right ha_meas]
    have hp_total : p e ≤ c * μ (⋃₀ C) + μ a := by
      calc
        p e = p (⋃₀ C ∪ a) := congrArg p hE_union
        p (⋃₀ C ∪ a) ≤ p (⋃₀ C) + p a := measure_union_le _ _
        _ ≤ (∑' b : C, p b) + μ a := add_le_add hp_union hpa
        _ ≤ c * ∑' b : C, μ b + μ a := add_le_add hpμ le_rfl
        _ = c * μ (⋃₀ C) + μ a := by rw [hμ_union]
    have hbound : c * μ (⋃₀ C) + μ a ≤
        c * μ e + (1 - c) * d := by
      calc
        c * μ (⋃₀ C) + μ a =
            c * (μ (⋃₀ C) + μ a) + (1 - c) * μ a := by
          rw [mul_add, add_assoc, ← add_mul, add_tsub_cancel_of_le hc_one.le, one_mul]
        _ = c * μ e + (1 - c) * μ a := by rw [← hμ_parts]
        _ ≤ c * μ e + (1 - c) * d := by gcongr
    exact (not_lt_of_ge (by simpa only [p, hμe] using hp_total.trans hbound)) hr_large
  refine ⟨a, ha_meas, ha_sub, ha_large, r, hr_pos, ?_⟩
  intro s hs hsr
  have hca : c * μ (a ∩ s) ≤ p (a ∩ s) :=
    no_bad (ha_meas.inter hs) inter_subset_left
  have hpre : p (a ∩ s) ≤ Metric.ediam (a ∩ s) :=
    OuterMeasure.mkMetric'.pre_le ((Metric.ediam_mono inter_subset_right).trans hsr)
  have hmass : μH[1] (a ∩ s) = μ (a ∩ s) := by
    change μH[1] (a ∩ s) = (μH[1].restrict e) (a ∩ s)
    rw [Measure.restrict_apply (ha_meas.inter hs)]
    rw [inter_eq_left.mpr (inter_subset_left.trans ha_sub)]
  rw [hmass]
  calc
    μ (a ∩ s) = c⁻¹ * (c * μ (a ∩ s)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc_pos.ne' hc_one.ne_top, one_mul]
    _ ≤ c⁻¹ * p (a ∩ s) := by gcongr
    _ ≤ c⁻¹ * Metric.ediam (a ∩ s) := by gcongr
    _ ≤ c⁻¹ * Metric.ediam s := by
      gcongr
      exact inter_subset_right

/-- A positive finite Hausdorff set has a positive subset with asymptotically sharp bounds at a
sequence of scales. -/
private theorem exists_multiscaleAlmostStraightSubset
    {e : Set (EuclideanSpace ℝ (Fin 2))} (he : MeasurableSet e)
    (he_pos : 0 < μH[1] e) (he_fin : μH[1] e < ∞) :
    ∃ a : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet a ∧ a ⊆ e ∧ 0 < μH[1] a ∧
      ∀ n : ℕ, ∃ r : ℝ≥0∞, 0 < r ∧ ∀ s : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet s → Metric.ediam s ≤ r →
          μH[1] (a ∩ s) ≤ (1 + lossWeight n) * Metric.ediam s := by
  have hexists (n : ℕ) :
      ∃ a : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet a ∧ a ⊆ e ∧
        μH[1] e - lossWeight n * μH[1] e < μH[1] a ∧
        ∃ r : ℝ≥0∞, 0 < r ∧ ∀ s : Set (EuclideanSpace ℝ (Fin 2)),
          MeasurableSet s → Metric.ediam s ≤ r →
            μH[1] (a ∩ s) ≤ (1 + lossWeight n) * Metric.ediam s := by
    have hd : μH[1] e - lossWeight n * μH[1] e < μH[1] e :=
      ENNReal.sub_lt_self he_fin.ne he_pos.ne'
        (ENNReal.mul_pos_iff.mpr ⟨lossWeight_pos n, he_pos⟩).ne'
    have hc_pos : 0 < (1 + lossWeight n)⁻¹ := by
      rw [ENNReal.inv_pos]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (lossWeight_lt_one n).ne_top⟩
    have hc_one : (1 + lossWeight n)⁻¹ < 1 := by
      rw [ENNReal.inv_lt_one]
      exact ENNReal.lt_add_right ENNReal.one_ne_top (lossWeight_pos n).ne'
    simpa only [inv_inv] using exists_large_almostStraightSubset he he_fin hd hc_pos hc_one
  choose A hA_meas hA_sub hA_large r hr_pos hlocal using hexists
  have hcomplement (n : ℕ) :
      μH[1] (e \ A n) < lossWeight n * μH[1] e := by
    have hA_fin : μH[1] (A n) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono (hA_sub n)) he_fin).ne
    rw [measure_sdiff (hA_sub n) (hA_meas n).nullMeasurableSet hA_fin]
    apply (ENNReal.sub_lt_iff_lt_left hA_fin (measure_mono (hA_sub n))).2
    have hweight_le : lossWeight n * μH[1] e ≤ μH[1] e := by
      calc
        lossWeight n * μH[1] e ≤ 1 * μH[1] e := by gcongr; exact (lossWeight_lt_one n).le
        _ = μH[1] e := one_mul _
    have hweight_ne_top : lossWeight n * μH[1] e ≠ ∞ :=
      ENNReal.mul_ne_top (lossWeight_lt_one n).ne_top he_fin.ne
    simpa only [add_comm] using
      (ENNReal.sub_lt_iff_lt_left hweight_ne_top hweight_le).1 (hA_large n)
  let u : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ n : ℕ, e \ A n
  have hu_meas : MeasurableSet u := MeasurableSet.iUnion fun n ↦ he.diff (hA_meas n)
  have hu_sub : u ⊆ e := iUnion_subset fun _ ↦ sdiff_subset
  have hu_lt : μH[1] u < μH[1] e := by
    calc
      μH[1] u ≤ ∑' n : ℕ, μH[1] (e \ A n) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, lossWeight n * μH[1] e :=
        ENNReal.tsum_le_tsum fun n ↦ (hcomplement n).le
      _ = (∑' n : ℕ, lossWeight n) * μH[1] e := ENNReal.tsum_mul_right
      _ = (4 : ℝ≥0∞)⁻¹ * μH[1] e := by rw [tsum_lossWeight]
      _ < μH[1] e := by
        calc
          (4 : ℝ≥0∞)⁻¹ * μH[1] e < 1 * μH[1] e :=
            ENNReal.mul_lt_mul_left he_pos.ne' he_fin.ne
              (ENNReal.inv_lt_one.mpr (by norm_num))
          _ = μH[1] e := one_mul _
  let a : Set (EuclideanSpace ℝ (Fin 2)) := e \ u
  have ha_meas : MeasurableSet a := he.diff hu_meas
  have ha_sub : a ⊆ e := sdiff_subset
  have ha_A (n : ℕ) : a ⊆ A n := by
    intro x hx
    by_contra hxA
    exact hx.2 (mem_iUnion.2 ⟨n, hx.1, hxA⟩)
  have ha_pos : 0 < μH[1] a := by
    by_contra hnot
    have ha_zero : μH[1] a = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have he_union : e = u ∪ a := by
      change e = u ∪ (e \ u)
      rw [union_sdiff_cancel hu_sub]
    have hparts : μH[1] e = μH[1] u + μH[1] a := by
      rw [he_union, MeasureTheory.measure_union disjoint_sdiff_right ha_meas]
    rw [ha_zero, add_zero] at hparts
    exact hu_lt.ne hparts.symm
  refine ⟨a, ha_meas, ha_sub, ha_pos, fun n ↦ ⟨r n, hr_pos n, ?_⟩⟩
  intro s hs hsr
  exact (measure_mono (inter_subset_inter_left s (ha_A n))).trans
    (hlocal n s hs hsr)

/-- Every measurable set of positive finite Hausdorff one-measure has a positive straight piece. -/
theorem exists_straight_measure_restrict_subset
    {e : Set (EuclideanSpace ℝ (Fin 2))} (he : MeasurableSet e)
    (he_pos : 0 < μH[1] e) (he_fin : μH[1] e < ∞) :
    ∃ a : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet a ∧ a ⊆ e ∧ 0 < μH[1] a ∧
      IsStraightMeasure (μH[1].restrict a) := by
  classical
  letI : NullSingletonClass (μH[1] : Measure (EuclideanSpace ℝ (Fin 2))) :=
    Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num)
  obtain ⟨A, hA_meas, hA_sub, hA_pos, hscale⟩ :=
    exists_multiscaleAlmostStraightSubset he he_pos he_fin
  choose r hr_pos hlocal using hscale
  have hA_fin : μH[1] A < ∞ := (measure_mono hA_sub).trans_lt he_fin
  have hR_exists (n : ℕ) :
      ∃ R : ℝ≥0, 0 < R ∧ (R : ℝ≥0∞) * 2 < r n :=
    ENNReal.exists_nnreal_pos_mul_lt (by norm_num) (hr_pos n).ne'
  choose R hR_pos hR_scale using hR_exists
  let ρ : ℕ → ℝ≥0 := descendingRadius R
  have hρ_pos (n : ℕ) : 0 < ρ n := descendingRadius_pos hR_pos n
  have hρ_R (n : ℕ) : ρ n ≤ R n := descendingRadius_le R n
  obtain ⟨c, hc_pos, hc_small⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt hA_fin.ne (ENNReal.coe_pos.mpr (hρ_pos 0)).ne'
  let c' : ℝ≥0 := min c 1
  have hc'_pos : 0 < c' := lt_min hc_pos zero_lt_one
  have hc'_one : c' ≤ 1 := min_le_right _ _
  let μA : Measure (EuclideanSpace ℝ (Fin 2)) := μH[1].restrict A
  letI : IsFiniteMeasure μA :=
    ⟨by simpa only [μA, Measure.restrict_apply_univ] using hA_fin⟩
  obtain ⟨E, hE_meas, hE_sub, hE_mass⟩ := exists_subset_measure_eq_mul
    (μ := μA) hA_meas (q := (c' : ℝ)) c'.2 (by exact_mod_cast hc'_one)
  have hμA_A : μA A = μH[1] A := Measure.restrict_apply_self μH[1] A
  have hμA_E : μA E = μH[1] E := by
    change (μH[1].restrict A) E = μH[1] E
    rw [Measure.restrict_apply hE_meas, inter_eq_left.mpr hE_sub]
  have hE_mass' : μH[1] E = (c' : ℝ≥0∞) * μH[1] A := by
    simpa only [hμA_E, hμA_A, ENNReal.ofReal_coe_nnreal] using hE_mass
  have hE_pos : 0 < μH[1] E := by
    rw [hE_mass', ENNReal.mul_pos_iff]
    exact ⟨ENNReal.coe_pos.mpr hc'_pos, hA_pos⟩
  have hE_small : μH[1] E < ρ 0 := by
    rw [hE_mass']
    apply lt_of_le_of_lt _ hc_small
    gcongr
    exact min_le_left c 1
  have hE_sub_e : E ⊆ e := hE_sub.trans hA_sub
  have hE_fin : μH[1] E < ∞ := (measure_mono hE_sub_e).trans_lt he_fin
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := μH[1].restrict E
  letI : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using hE_fin⟩
  let mesh (n : ℕ) : ℝ≥0 :=
    (lossWeight n).toNNReal * ρ (n + 1) / 4
  have hmesh_pos (n : ℕ) : 0 < mesh n := by
    dsimp only [mesh]
    exact div_pos (mul_pos (ENNReal.toNNReal_pos (lossWeight_pos n).ne'
      (lossWeight_lt_one n).ne_top) (hρ_pos (n + 1))) (by norm_num)
  have hselect (n k : ℕ) :
      ∃ t : Set (EuclideanSpace ℝ (Fin 2)),
        MeasurableSet t ∧ t ⊆ E ∩ metricCell (mesh n) k ∧
        μ t = (thinningFraction n : ℝ≥0∞) *
          μ (E ∩ metricCell (mesh n) k) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using exists_subset_measure_eq_mul
      (μ := μ) (hE_meas.inter (measurableSet_metricCell _ _))
      (q := (thinningFraction n : ℝ)) (thinningFraction n).2
      (by exact_mod_cast thinningFraction_le_one n)
  choose S hS_meas hS_sub hS_mass using hselect
  have hmeasure_selected (n : ℕ) (K : Set ℕ) :
      μ (⋃ k : K, S n k) = (thinningFraction n : ℝ≥0∞) *
        μ (⋃ k : K, E ∩ metricCell (mesh n) k) := by
    have hS_disj : Pairwise (Disjoint on fun k : K ↦ S n k) := by
      intro i j hij
      exact Disjoint.mono (hS_sub n i) (hS_sub n j) <|
        Disjoint.mono inter_subset_right inter_subset_right <|
          pairwiseDisjoint_metricCell (mesh n) (Subtype.coe_ne_coe.mpr hij)
    have hcell_disj : Pairwise
        (Disjoint on fun k : K ↦ E ∩ metricCell (mesh n) k) := by
      intro i j hij
      exact Disjoint.mono inter_subset_right inter_subset_right <|
        pairwiseDisjoint_metricCell (mesh n) (Subtype.coe_ne_coe.mpr hij)
    calc
      μ (⋃ k : K, S n k) = ∑' k : K, μ (S n k) :=
        measure_iUnion hS_disj fun k ↦ hS_meas n k
      _ = ∑' k : K, (thinningFraction n : ℝ≥0∞) *
          μ (E ∩ metricCell (mesh n) k) := by
        congr 1
        funext k
        exact hS_mass n k
      _ = (thinningFraction n : ℝ≥0∞) *
          ∑' k : K, μ (E ∩ metricCell (mesh n) k) := ENNReal.tsum_mul_left
      _ = (thinningFraction n : ℝ≥0∞) *
          μ (⋃ k : K, E ∩ metricCell (mesh n) k) := by
        rw [measure_iUnion hcell_disj fun k ↦
          hE_meas.inter (measurableSet_metricCell _ _)]
  let T (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ k : (univ : Set ℕ), S n k
  have hT_meas (n : ℕ) : MeasurableSet (T n) :=
    MeasurableSet.iUnion fun k ↦ hS_meas n k
  have hT_sub (n : ℕ) : T n ⊆ E :=
    iUnion_subset fun k ↦ (hS_sub n k).trans inter_subset_left
  have hcells_univ (n : ℕ) :
      (⋃ k : (univ : Set ℕ), E ∩ metricCell (mesh n) k) = E := by
    apply Subset.antisymm
    · exact iUnion_subset fun _ ↦ inter_subset_left
    · intro x hxE
      have hxcell : x ∈ ⋃ k : ℕ, metricCell (mesh n) k := by
        rw [iUnion_metricCell (mesh n) (hmesh_pos n)]
        exact mem_univ x
      obtain ⟨k, hxk⟩ := mem_iUnion.1 hxcell
      exact mem_iUnion.2 ⟨⟨k, mem_univ k⟩, hxE, hxk⟩
  have hT_mass (n : ℕ) :
      μ (T n) = (thinningFraction n : ℝ≥0∞) * μ E := by
    change μ (⋃ k : (univ : Set ℕ), S n k) =
      (thinningFraction n : ℝ≥0∞) * μ E
    rw [hmeasure_selected n univ, hcells_univ]
  have hμ_E : μ E = μH[1] E := Measure.restrict_apply_self μH[1] E
  have hT_loss (n : ℕ) :
      μ (E \ T n) = 2 * lossWeight n * μ E := by
    have hT_fin : μ (T n) ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono (hT_sub n)) (by simpa only [hμ_E] using hE_fin)).ne
    rw [measure_sdiff (hT_sub n) (hT_meas n).nullMeasurableSet hT_fin, hT_mass]
    calc
      μ E - (thinningFraction n : ℝ≥0∞) * μ E =
          (1 - thinningFraction n) * μ E := by
        rw [ENNReal.sub_mul (fun _ _ ↦ (by simpa only [hμ_E] using hE_fin.ne)), one_mul]
      _ = 2 * lossWeight n * μ E := by rw [one_sub_thinningFraction_ennreal]
  let bad : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ n : ℕ, E \ T n
  have hbad_meas : MeasurableSet bad :=
    MeasurableSet.iUnion fun n ↦ hE_meas.diff (hT_meas n)
  have hbad_sub : bad ⊆ E := iUnion_subset fun _ ↦ sdiff_subset
  have hbad_lt : μ bad < μ E := by
    calc
      μ bad ≤ ∑' n : ℕ, μ (E \ T n) := measure_iUnion_le _
      _ = ∑' n : ℕ, (2 * lossWeight n) * μ E := by
        congr 1
        funext n
        exact hT_loss n
      _ = (∑' n : ℕ, 2 * lossWeight n) * μ E := ENNReal.tsum_mul_right
      _ = (2 * ∑' n : ℕ, lossWeight n) * μ E := by rw [ENNReal.tsum_mul_left]
      _ = (2 * (4 : ℝ≥0∞)⁻¹) * μ E := by rw [tsum_lossWeight]
      _ < μ E := by
        calc
          (2 * (4 : ℝ≥0∞)⁻¹) * μ E < 1 * μ E :=
            ENNReal.mul_lt_mul_left (by simpa only [hμ_E] using hE_pos.ne')
              (by simpa only [hμ_E] using hE_fin.ne) (by
                calc
                  2 * (4 : ℝ≥0∞)⁻¹ < 2 * (2 : ℝ≥0∞)⁻¹ := by
                    apply ENNReal.mul_lt_mul_right (by norm_num) (by norm_num)
                    exact ENNReal.inv_lt_inv.mpr (by norm_num)
                  _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
          _ = μ E := one_mul _
  let a : Set (EuclideanSpace ℝ (Fin 2)) := E \ bad
  have ha_meas : MeasurableSet a := hE_meas.diff hbad_meas
  have ha_sub_E : a ⊆ E := sdiff_subset
  have ha_sub_e : a ⊆ e := ha_sub_E.trans hE_sub_e
  have ha_T (n : ℕ) : a ⊆ T n := by
    intro x hx
    by_contra hxT
    exact hx.2 (mem_iUnion.2 ⟨n, hx.1, hxT⟩)
  have hμ_a : μ a = μH[1] a := by
    change (μH[1].restrict E) a = μH[1] a
    rw [Measure.restrict_apply ha_meas, inter_eq_left.mpr ha_sub_E]
  have ha_pos : 0 < μH[1] a := by
    rw [← hμ_a]
    by_contra hnot
    have ha_zero : μ a = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have he_union : E = bad ∪ a := by
      change E = bad ∪ (E \ bad)
      rw [union_sdiff_cancel hbad_sub]
    have hparts : μ E = μ bad + μ a := by
      rw [he_union, MeasureTheory.measure_union disjoint_sdiff_right ha_meas]
    rw [ha_zero, add_zero] at hparts
    exact hbad_lt.ne hparts.symm
  refine ⟨a, ha_meas, ha_sub_e, ha_pos, ?_⟩
  intro s hs
  rw [Measure.restrict_apply hs]
  have has_sub_E : s ∩ a ⊆ E := inter_subset_right.trans ha_sub_E
  rcases eq_or_lt_of_le (bot_le : 0 ≤ Metric.ediam s) with hdiam | hdiam
  · have hs_zero : μH[1] s = 0 :=
      (Metric.ediam_eq_zero_iff.mp hdiam.symm).measure_zero μH[1]
    calc
      μH[1] (s ∩ a) ≤ μH[1] s := measure_mono inter_subset_left
      _ = 0 := hs_zero
      _ = Metric.ediam s := hdiam
  by_cases hlarge : (ρ 0 : ℝ≥0∞) ≤ Metric.ediam s
  · calc
      μH[1] (s ∩ a) ≤ μH[1] E := measure_mono has_sub_E
      _ ≤ (ρ 0 : ℝ≥0∞) := hE_small.le
      _ ≤ Metric.ediam s := hlarge
  obtain ⟨n, hn_lower, hn_upper⟩ :=
    exists_descendingRadius_interval hdiam (lt_of_not_ge hlarge)
  let K : Set ℕ := {k | (metricCell (mesh n) k ∩ s).Nonempty}
  let V : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ k : K, S n k
  let W : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ k : K, E ∩ metricCell (mesh n) k
  have has_V : s ∩ a ⊆ V := by
    intro x hx
    have hxT := ha_T n hx.2
    change x ∈ ⋃ k : (univ : Set ℕ), S n k at hxT
    obtain ⟨k, hxS⟩ := mem_iUnion.1 hxT
    have hxcell : x ∈ metricCell (mesh n) k := (hS_sub n k hxS).2
    exact mem_iUnion.2 ⟨⟨k, ⟨x, hxcell, hx.1⟩⟩, hxS⟩
  have hW_sub : W ⊆ E ∩ thickening (2 * mesh n) s := by
    intro x hx
    obtain ⟨k, hxk⟩ := mem_iUnion.1 hx
    refine ⟨hxk.1, cells_meeting_subset_thickening (mesh n) s ?_⟩
    exact mem_iUnion.2 ⟨k, hxk.2⟩
  have hmesh_eq : (4 : ℝ≥0∞) * mesh n =
      lossWeight n * (ρ (n + 1) : ℝ≥0∞) := by
    have hNN : (4 : ℝ≥0) * mesh n =
        (lossWeight n).toNNReal * ρ (n + 1) := by
      dsimp only [mesh]
      rw [mul_comm, div_mul_cancel₀ _ (by norm_num)]
    rw [← ENNReal.coe_toNNReal (lossWeight_lt_one n).ne_top]
    exact_mod_cast hNN
  have hmesh_bound : (4 : ℝ≥0∞) * mesh n ≤
      lossWeight n * Metric.ediam s := by
    rw [hmesh_eq]
    gcongr
  have hed_thick : Metric.ediam (thickening (2 * mesh n) s) ≤
      (1 + lossWeight n) * Metric.ediam s := by
    calc
      Metric.ediam (thickening (2 * mesh n) s) ≤
          Metric.ediam s + 2 * (2 * mesh n : ℝ≥0) :=
        Metric.ediam_thickening_le (s := s) (2 * mesh n)
      _ = Metric.ediam s + (4 : ℝ≥0∞) * mesh n := by norm_num; ring
      _ ≤ Metric.ediam s + lossWeight n * Metric.ediam s := add_le_add le_rfl hmesh_bound
      _ = (1 + lossWeight n) * Metric.ediam s := by rw [add_mul, one_mul]
  have hed_scale : Metric.ediam (thickening (2 * mesh n) s) ≤ r n := by
    exact hed_thick.trans <| le_of_lt <| by
      calc
        (1 + lossWeight n) * Metric.ediam s ≤ 2 * Metric.ediam s := by
          gcongr
          calc
            1 + lossWeight n ≤ 1 + 1 := by gcongr; exact (lossWeight_lt_one n).le
            _ = 2 := one_add_one_eq_two
        _ < 2 * (ρ n : ℝ≥0∞) :=
          ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hn_upper
        _ ≤ 2 * (R n : ℝ≥0∞) := by gcongr; exact hρ_R n
        _ < r n := by simpa only [mul_comm] using hR_scale n
  have hμ_W : μ W ≤ μH[1] (E ∩ thickening (2 * mesh n) s) := by
    calc
      μ W ≤ μ (E ∩ thickening (2 * mesh n) s) := measure_mono hW_sub
      _ = μH[1] (E ∩ thickening (2 * mesh n) s) := by
        change (μH[1].restrict E) (E ∩ thickening (2 * mesh n) s) = _
        rw [Measure.restrict_apply
          (hE_meas.inter Metric.isOpen_thickening.measurableSet)]
        congr 1
        exact inter_eq_left.mpr inter_subset_left
  have hlocal_thick : μH[1] (E ∩ thickening (2 * mesh n) s) ≤
      (1 + lossWeight n) * Metric.ediam (thickening (2 * mesh n) s) :=
    (measure_mono (inter_subset_inter_left _ hE_sub)).trans <|
      hlocal n _ Metric.isOpen_thickening.measurableSet hed_scale
  have hμ_sa : μH[1] (s ∩ a) = μ (s ∩ a) := by
    change μH[1] (s ∩ a) = (μH[1].restrict E) (s ∩ a)
    rw [Measure.restrict_apply (hs.inter ha_meas), inter_eq_left.mpr has_sub_E]
  rw [hμ_sa]
  calc
    μ (s ∩ a) ≤ μ V := measure_mono has_V
    _ = (thinningFraction n : ℝ≥0∞) * μ W := hmeasure_selected n K
    _ ≤ (thinningFraction n : ℝ≥0∞) *
        μH[1] (E ∩ thickening (2 * mesh n) s) := by gcongr
    _ ≤ (thinningFraction n : ℝ≥0∞) *
        ((1 + lossWeight n) * Metric.ediam (thickening (2 * mesh n) s)) := by gcongr
    _ ≤ (thinningFraction n : ℝ≥0∞) *
        ((1 + lossWeight n) * ((1 + lossWeight n) * Metric.ediam s)) := by gcongr
    _ = ((thinningFraction n : ℝ≥0∞) * (1 + lossWeight n) ^ 2) *
        Metric.ediam s := by ring
    _ ≤ 1 * Metric.ediam s := by gcongr; exact thinningFraction_compensates n
    _ = Metric.ediam s := one_mul _

end LeanPool.Besicovitch
