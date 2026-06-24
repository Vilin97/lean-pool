/-
Copyright (c) 2026 seb488, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: seb488, Aristotle
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
/-!
# Uniqueness of the Herglotz–Riesz measure

## Main Results

Theorem `HerglotzRiesz_representation_uniqueness`:

If for two probability measures `μ₁` and `μ₂` on the unit circle
the two functions ∫ x, (x + z) / (x - z) ∂μ₁ and ∫ x, (x + z) / (x - z) ∂μ₂ are
identical on the unit disc, then `μ₁` = `μ₂`.
-/

namespace LeanPool.LeanComplexAnalysis

open MeasureTheory Metric Complex Topology

/-- Equal moments with natural exponents imply equal moments with integer exponents. -/
lemma moments_eq_integers (μ₁ μ₂ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (h : ∀ n : ℕ, ∫ x : sphere (0 : ℂ) 1, x.val ^ n ∂μ₁ = ∫ x : sphere (0 : ℂ) 1, x.val ^ n ∂μ₂) :
    ∀ n : ℤ, ∫ x : sphere (0 : ℂ) 1, x.val ^ n ∂μ₁ = ∫ x : sphere (0 : ℂ) 1, x.val ^ n ∂μ₂ := by
  intro n
  by_cases h_neg : n < 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -m := by
      exact ⟨Int.toNat (-n), by rw [Int.toNat_of_nonneg (neg_nonneg.mpr h_neg.le)]; ring⟩
    have h_inv : ∀ x : sphere (0 : ℂ) 1, x ^ (-m : ℤ) = starRingEnd ℂ (x ^ m) := by
      simp only [mem_sphere_zero_iff_norm, Subtype.forall]
      intro x hx
      rw [zpow_neg]
      rw [inv_eq_of_mul_eq_one_right]
      simp [← mul_pow, mul_conj, normSq_eq_norm_sq, hx]
    have aux : ∀ ν : ProbabilityMeasure (sphere (0 : ℂ) 1),
        ∫ x : sphere (0 : ℂ) 1, (x : ℂ) ^ (-m : ℤ) ∂ν =
        starRingEnd ℂ (∫ x : sphere (0 : ℂ) 1, (x : ℂ) ^ m ∂ν) := by
      intro ν
      rw [show (starRingEnd ℂ) (∫ (x : sphere (0 : ℂ) 1), (x : ℂ) ^ m ∂↑ν) =
            ∫ (x : sphere (0 : ℂ) 1), (starRingEnd ℂ) ((x : ℂ) ^ m) ∂↑ν from integral_conj.symm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact h_inv x
    have h_inv_integral : ∫ x : sphere (0 : ℂ) 1, (x : ℂ) ^ (-m : ℤ) ∂μ₁ =
      starRingEnd ℂ (∫ x : sphere (0 : ℂ) 1, (x : ℂ) ^ m ∂μ₁) ∧ ∫ x : sphere (0 : ℂ) 1,
        (x : ℂ) ^ (-m : ℤ) ∂μ₂ = starRingEnd ℂ (∫ x : sphere (0 : ℂ) 1, (x : ℂ) ^ m ∂μ₂) :=
      ⟨aux μ₁, aux μ₂⟩
    rw [h_inv_integral.1, h_inv_integral.2, h]
  · have hn : 0 ≤ n := by omega
    lift n to ℕ using hn
    simp only [zpow_natCast]
    exact h n

lemma continuous_zpow_on_unit_circle (n : ℤ) :
    Continuous (fun x : sphere (0 : ℂ) 1 => x.val ^ n) := by
  cases n with
  | ofNat m =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact continuous_subtype_val.pow m
  | negSucc m =>
       simp only [zpow_negSucc]
       apply Continuous.inv₀
       · exact continuous_subtype_val.pow (m + 1)
       · intro x
         apply pow_ne_zero _
         have : ‖(x : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
         rw [← norm_ne_zero_iff, this]
         exact one_ne_zero

/-- The span of moments is dense in the space of continuous functions on the unit circle. -/
lemma span_moments_dense : (Submodule.span ℂ (Set.range (fun n : ℤ => ContinuousMap.mk (
    fun x : sphere (0 : ℂ) 1 => x.val ^ n)
      (continuous_zpow_on_unit_circle n)))).topologicalClosure = ⊤ := by
  set A : StarSubalgebra ℂ (ContinuousMap (sphere (0 : ℂ) 1) ℂ) := StarAlgebra.adjoin ℂ
    {ContinuousMap.mk fun x : sphere (0 : ℂ) 1 => x.val}
  rw [eq_top_iff]
  have h_dense : Dense (A : Set (ContinuousMap (sphere (0 : ℂ) 1) ℂ)) := by
    have h_stone_weierstrass : ∀ (A : StarSubalgebra ℂ (ContinuousMap (sphere (0 : ℂ) 1) ℂ)),
      (∀ x y : sphere (0 : ℂ) 1, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
        (∀ c : ℂ, ContinuousMap.const (sphere (0 : ℂ) 1) c ∈ A) →
          Dense (A : Set (ContinuousMap (sphere (0 : ℂ) 1) ℂ)) := by
      intro A hA hA'
      have h_sep : A.SeparatesPoints := by
        intro x y hxy
        obtain ⟨f, hf_mem, hf_ne⟩ := hA x y hxy
        exact ⟨f, ⟨f, hf_mem, rfl⟩, hf_ne⟩
      have h_top := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
        A h_sep
      have h_closure : closure (A : Set C(↑(sphere (0 : ℂ) 1), ℂ)) = Set.univ := by
        rw [← StarSubalgebra.topologicalClosure_coe, h_top]
        simp
      rw [dense_iff_closure_eq, h_closure]
    apply h_stone_weierstrass A
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      refine ⟨⟨fun x => x.val, continuous_subtype_val⟩, ?_, ?_⟩
      · apply StarAlgebra.subset_adjoin
        simp only [Set.mem_singleton_iff]
      · simp only [ContinuousMap.coe_mk, ne_eq]
        intro h
        exact hab (Subtype.ext h)
    · intro c
      have h_eq : ContinuousMap.const (↑(sphere (0 : ℂ) 1)) c
          = algebraMap ℂ C(↑(sphere (0 : ℂ) 1), ℂ) c := by
        ext x
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h_eq]
      exact StarSubalgebra.algebraMap_mem _ c
  intro x hx
  refine closure_mono ?_ (h_dense x)
  intro f hf
  induction hf using StarAlgebra.adjoin_induction with
  | mem x hx =>
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      apply Submodule.subset_span
      use (1 : ℤ)
      ext
      simp only [zpow_one]
  | algebraMap r =>
    refine Submodule.mem_span.mpr ?_
    intro p hp
    have h1 : (1 : C((sphere (0 : ℂ) 1), ℂ)) ∈ p := hp ⟨0, by ext x; simp⟩
    have hsmul : r • (1 : C((sphere (0 : ℂ) 1), ℂ)) ∈ p := p.smul_mem r h1
    convert hsmul using 1
    simp [Algebra.smul_def]
  | add => exact AddMemClass.add_mem ‹_› ‹_›
  | mul =>
    rename_i hx hy
    simp only [SetLike.mem_coe] at hx hy ⊢
    rw [Submodule.mem_toAddSubmonoid] at hx hy ⊢
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx hy
    obtain ⟨c₁, hc₁⟩ := hx; obtain ⟨c₂, hc₂⟩ := hy; rw [← hc₁, ← hc₂]
    simp only [Finsupp.sum, Finset.sum_mul _ _ _, Algebra.smul_mul_assoc]
    simp only [Finset.mul_sum _ _ _]
    refine Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
    rw [mul_smul_comm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + j, ?_⟩)
    ext x
    simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply]
    rw [zpow_add₀]
    unfold sphere at x
    obtain ⟨x, hx⟩ := x
    dsimp at hx
    convert (zero_lt_one (α := ℝ)).trans_eq hx.symm using 1
    constructor
    · intro _; rw [hx]; exact zero_lt_one
    · intro _; rw [← dist_pos, hx]; exact zero_lt_one
  | star =>
    rename_i h₁ h₂ h₃
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h₃
    · simp only [Set.mem_range, ContinuousMap.ext_iff, ContinuousMap.coe_mk, Subtype.forall,
      mem_sphere_iff_norm, sub_zero, Submodule.coe_toAddSubmonoid, SetLike.mem_coe,
      forall_exists_index]
      intro f n hn
      refine Submodule.subset_span ⟨-n, ?_⟩
      ext ⟨y, hy⟩
      have hy' : ‖y‖ = 1 := by exact mem_sphere_zero_iff_norm.mp hy
      simp only [zpow_neg, ContinuousMap.coe_mk, hn y hy', ContinuousMap.star_apply,
        RCLike.star_def]
      rw [← hn y hy', inv_def]
      simp [normSq_eq_norm_sq, hy']
    · simp [star_zero]
    · simp only [star_add, SetLike.mem_coe]
      exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy'
    · intro a x hx hsx
      rw [star_smul]
      exact Submodule.smul_mem _ _ hsx

/-- If two finite measures agree on a dense subspace of continuous functions,
then they agree on all continuous functions. -/
lemma integral_eq_on_dense_set {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Submodule ℂ C(X, ℂ)) (hS : S.topologicalClosure = ⊤)
    (h : ∀ f ∈ S, ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    ∀ f : C(X, ℂ), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  have h_cont : Continuous (fun f : C(X, ℂ) => ∫ x, f x ∂μ) ∧
    Continuous (fun f : C(X, ℂ) => ∫ x, f x ∂ν) := by
    constructor <;> refine continuous_iff_continuousAt.2 fun f => ?_ <;>
    · refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun g => g.continuous.aestronglyMeasurable
      · refine ⟨‖f‖ + 1, ?_⟩
        rw [Metric.eventually_nhds_iff]
        refine ⟨1, zero_lt_one, fun g hg => Filter.Eventually.of_forall fun x => ?_⟩
        have := ContinuousMap.norm_coe_le_norm g x
        refine le_trans this ?_
        calc  ‖g‖ = ‖f + (g - f)‖ := by simp
          _ ≤ ‖f‖ + ‖g - f‖ := norm_add_le _ _
          _ ≤ ‖f‖ + 1 :=  by rw [<- dist_eq_norm]; linarith
      · exact Filter.Eventually.of_forall fun x => Continuous.tendsto (by continuity) _
  intro f
  obtain ⟨f_n, hf_n⟩ : ∃ f_n : ℕ → C(X, ℂ), (∀ n, f_n n ∈ S) ∧
    Filter.Tendsto f_n Filter.atTop (𝓝 f) := by
    have h_dense : f ∈ S.topologicalClosure := by rw [hS]; exact Submodule.mem_top
    exact mem_closure_iff_seq_limit.mp h_dense
  exact tendsto_nhds_unique (h_cont.1.continuousAt.tendsto.comp hf_n.2)
    (h_cont.2.continuousAt.tendsto.comp hf_n.2 |> Filter.Tendsto.congr (by
      intro x
      have hx : f_n x ∈ S := hf_n.1 x
      dsimp [(· ∘ ·)]
      symm
      exact h (f_n x) hx))

/-- If two probability measures on the unit circle have the same moments, then they are equal. -/
lemma measure_eq_of_moments (μ₁ μ₂ : Measure (sphere (0 : ℂ) 1))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ n : ℕ, ∫ x, x.val ^ n ∂μ₁ = ∫ x, x.val ^ n ∂μ₂) : μ₁ = μ₂ := by
  have h_integrals : ∀ f : C((sphere (0 : ℂ) 1), ℂ), ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
    apply_rules [integral_eq_on_dense_set]
    · exact span_moments_dense
    · intro f hf
      have h_integrals : ∀ n : ℤ, ∫ x, x.val ^ n ∂μ₁ = ∫ x, x.val ^ n ∂μ₂ :=
         fun n ↦ moments_eq_integers ⟨μ₁, inferInstance⟩ ⟨μ₂, inferInstance⟩ h n
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hf
      obtain ⟨c, rfl⟩ := hf
      simp_rw [Finsupp.sum, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
        ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum, integral_finsetSum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show (∫ (a : ↑(sphere 0 1)), c i * (↑a : ℂ) ^ i ∂μ₁) =
              c i * ∫ (a : ↑(sphere 0 1)), (↑a : ℂ) ^ i ∂μ₁ from
            MeasureTheory.integral_const_mul _ _,
            show (∫ (a : ↑(sphere 0 1)), c i * (↑a : ℂ) ^ i ∂μ₂) =
              c i * ∫ (a : ↑(sphere 0 1)), (↑a : ℂ) ^ i ∂μ₂ from
            MeasureTheory.integral_const_mul _ _,
            h_integrals]
      · intro n hn; apply_rules [Integrable.const_mul, integrable_const]
        refine Integrable.mono' (g := fun _ => 1) ?_ ?_ ?_
        · norm_num
        · exact Continuous.aestronglyMeasurable (continuous_zpow_on_unit_circle n)
        · filter_upwards with x
          have hx : ‖(x : ℂ)‖ = 1 := by exact mem_sphere_zero_iff_norm.mp x.2
          simp [hx]
      · intro n hn; apply_rules [Integrable.const_mul, integrable_const]
        refine Integrable.mono' (g := fun _ => 1) ?_ ?_ ?_
        · norm_num
        · exact Continuous.aestronglyMeasurable (continuous_zpow_on_unit_circle n)
        · filter_upwards with x
          have hx : ‖(x : ℂ)‖ = 1 := by exact mem_sphere_zero_iff_norm.mp x.2
          simp [hx]
  have h_eq : ∀ f : C((sphere (0 : ℂ) 1), ℝ), ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
    intro f
    convert congr_arg re (h_integrals (ContinuousMap.mk (fun x =>
      f x : sphere (0 : ℂ) 1 → ℂ)
      (by continuity))) using 1 <;> norm_num [Complex.ext_iff, integral_sub, integral_const_mul]
    · exact Eq.symm (by erw [integral_ofReal]; norm_cast)
    · exact Eq.symm (by erw [integral_ofReal]; norm_cast)
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ h_eq f.toContinuousMap

/-- A power series `∑ z^(k+1) * c k` with bounded coefficients is summable for `‖z‖ < 1`. -/
private lemma summable_zpow_mul {z : ℂ} (hz : ‖z‖ < 1) {c : ℕ → ℂ} {M : ℝ}
    (hc : ∀ n, ‖c n‖ ≤ M) : Summable (fun k => z ^ (k + 1) * c k) := by
  have h_summable : Summable (fun k => ‖z‖ ^ (k + 1) * ‖c k‖) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hc n) (pow_nonneg (norm_nonneg _) _))
      (Summable.mul_right _ <| summable_geometric_of_lt_one (norm_nonneg _) hz
        |> Summable.comp_injective <| Nat.succ_injective)
  exact Summable.of_norm <| by simpa using h_summable

/-- If two power series are equal on the unit disc, then their coefficients are equal. -/
lemma coeffs_eq_of_series_eq (c1 c2 : ℕ → ℂ)
    (hc1 : ∃ M, ∀ n, ‖c1 n‖ ≤ M) (hc2 : ∃ M, ∀ n, ‖c2 n‖ ≤ M)
    (h : ∀ z : ℂ, ‖z‖ < 1 → ∑' n, z ^ (n + 1) * c1 n = ∑' n, z ^ (n + 1) * c2 n) : c1 = c2 := by
  ext n
  have h_eq : ∀ z : ℂ, ‖z‖ < 1 → ∑' k, z ^ (k + 1) * (c1 k - c2 k) = 0 := by
    intro z hz
    convert sub_eq_zero.mpr (h z hz) using 1
    rw [← Summable.tsum_sub]
    · congr
      ext n
      ring
    · exact summable_zpow_mul hz hc1.choose_spec
    · exact summable_zpow_mul hz hc2.choose_spec
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have h_limit : Filter.Tendsto (fun z : ℂ => (∑' k, z ^ (k + 1) * (c1 k - c2 k)) / z ^ (n + 1))
    (nhdsWithin 0 {0}ᶜ) (𝓝 ((c1 n - c2 n))) := by
    have h_series : ∀ z : ℂ, ‖z‖ < 1 → (∑' k, z ^ (k + 1) * (c1 k - c2 k)) =
      z^(n + 1) * (c1 n - c2 n) + ∑' k, z^(k + n + 2) * (c1 (k + n + 1) - c2 (k + n + 1)) := by
      intro z hz
      rw [← Summable.sum_add_tsum_nat_add]
      rotate_left
      · use n + 1
      · simpa only [mul_sub] using
          (summable_zpow_mul hz hc1.choose_spec).sub (summable_zpow_mul hz hc2.choose_spec)
      · simp only [Finset.sum_range_succ, add_assoc, Nat.reduceAdd, add_eq_right]
        exact Finset.sum_eq_zero fun i hi => by simp [ih i (Finset.mem_range.mp hi)]
    have h_factor : Filter.Tendsto
                      (fun z : ℂ =>
                           (c1 n - c2 n) + ∑' k, z ^ (k + 1) * (c1 (k + n + 1) - c2 (k + n + 1)))
                      (nhdsWithin 0 {0}ᶜ) (𝓝 ((c1 n - c2 n))) := by
      have h_factor : ContinuousOn
                        (fun z : ℂ =>
                            ∑' k, z ^ (k + 1) * (c1 (k + n + 1) - c2 (k + n + 1)))
                        (closedBall 0 (1 / 2)) := by
        refine continuousOn_tsum
                  (u := fun k => (1 / 2) ^ (k + 1) * (hc1.choose + hc2.choose)) ?_ ?_ ?_
        · exact fun i => Continuous.continuousOn (by continuity)
        · exact Summable.mul_right _ (summable_geometric_two.mul_right _)
        · norm_num
          exact fun k z hz => mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
            (le_trans (norm_sub_le _ _) (add_le_add (hc1.choose_spec _) (hc2.choose_spec _)))
              (by positivity) (by positivity)
      exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using Filter.Tendsto.add
                          tendsto_const_nhds
                          (h_factor.continuousAt
                              (Metric.closedBall_mem_nhds _ <| by norm_num) |> fun h => h.tendsto))
    refine Filter.Tendsto.congr' ?_ h_factor
    filter_upwards [self_mem_nhdsWithin,
                    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)] with z hz hz'
    rw [h_series z <| by simpa using hz']
    rw [eq_div_iff <| pow_ne_zero _ hz]
    ring_nf
    rw [← tsum_mul_left]
    congr
    ext k
    ring_nf
  have h_zero_limit : Filter.Tendsto (fun z : ℂ =>
                                          (∑' k, z ^ (k + 1) * (c1 k - c2 k)) / z ^ (n + 1))
                                     (nhdsWithin 0 {0}ᶜ) (𝓝 0) :=
    tendsto_const_nhds.congr'
      (by filter_upwards [self_mem_nhdsWithin,
                          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)]
                          with z hz hz'; simp_all only [Set.mem_compl_iff, Set.mem_singleton_iff,
                            mem_ball, dist_zero_right, zero_div])
  exact eq_of_sub_eq_zero (tendsto_nhds_unique h_limit h_zero_limit)

/-- We expand the Herglotz–Riesz kernel into a power series at 0 by using that
 1/(1 - z/w) = Σ_{n=0}^∞ (z/w)^n. -/
lemma kernel_expansion (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ) (hw : ‖w‖ = 1) :
    (w + z) / (w - z) = 1 + 2 * ∑' n : ℕ, z ^ (n + 1) * star (w ^ (n + 1)) := by
  have h_expand : (1 : ℂ) + 2 * z / (w - z) = 1 + 2 * ∑' n : ℕ, (z / w) ^ (n + 1) := by
    have h_expand : ∑' n : ℕ, (z / w) ^ (n + 1) = z / w / (1 - z / w) := by
      have h_geo_series : (∑' n : ℕ, (z / w) ^ (n + 1)) =
        (z / w) * (∑' n : ℕ, (z / w) ^ n) := by
        rw [← tsum_mul_left]; exact tsum_congr fun _ => by ring
      rw [h_geo_series, tsum_geometric_of_norm_lt_one]
      · rfl
      · rw [norm_div, hw, div_one]
        exact hz
    rw [h_expand]
    have w_ne : w ≠ 0 := by
      intro hw0
      rw [hw0, norm_zero] at hw
      simp at hw
    field_simp [w_ne]
  convert h_expand using 1
  · rw [one_add_div]
    · ring
    · exact sub_ne_zero_of_ne <| by rintro rfl; rw [hw] at hz ; exact (not_lt_of_ge (le_refl 1) hz)
  · simp only [star_pow, RCLike.star_def, div_pow, add_right_inj, mul_eq_mul_left_iff,
    OfNat.ofNat_ne_zero, or_false]
    congr! 2
    rw [div_eq_mul_inv, inv_def]
    simp [normSq_eq_norm_sq,hw]

/-- The kernel_expansion is used to rewrite the integral. -/
lemma integral_kernel_expansion
    (μ : ProbabilityMeasure (sphere (0 : ℂ) 1)) (z : ℂ) (hz : ‖z‖ < 1) :
    ∫ x : sphere (0 : ℂ) 1, (x + z) / (x - z) ∂μ = 1 + 2 * ∑' n : ℕ,
      z ^ (n + 1) * ∫ x : sphere (0 : ℂ) 1, star (x.val ^ (n + 1)) ∂μ := by
  have h_integral : ∫ x : sphere (0 : ℂ) 1, (x + z) / (x - z) ∂μ =
     ∫ x : sphere (0 : ℂ) 1, (1 + 2 * ∑' n : ℕ, z ^ (n + 1) * star ((x : ℂ) ^ (n + 1))) ∂μ := by
    apply integral_congr_ae (by filter_upwards with x; apply kernel_expansion z hz; simp)
  have h_integrable_tsum :
      Integrable (fun x : sphere (0 : ℂ) 1 => ∑' n : ℕ, z ^ (n + 1) * star ((x : ℂ) ^ (n + 1))) μ :=
    by
      refine Integrable.mono' (g := fun x => ∑' n : ℕ, ‖z‖ ^ (n + 1) *
        ‖starRingEnd ℂ (x : ℂ)‖ ^ (n + 1)) ?_ ?_ ?_
      · norm_num
      · refine Continuous.aestronglyMeasurable ?_
        refine continuous_tsum (u := fun n => ‖z‖ ^ (n + 1)) ?_ ?_ ?_
        · fun_prop (disch := norm_num)
        · exact Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg _) hz)
            (Nat.succ_injective)
        · norm_num
      · refine Filter.Eventually.of_forall fun x => ?_
        refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
        · simpa using summable_nat_add_iff 1 |>.2 <|
             summable_geometric_of_lt_one (norm_nonneg _) hz
        · refine le_of_eq ?_
          congr 1
          ext i
          simp [norm_pow]
  rw [h_integral, integral_add (integrable_const 1)
        ((MeasureTheory.Integrable.const_mul h_integrable_tsum (2 : ℂ)))]
  rw [show ∫ a : sphere (0 : ℂ) 1, (2 : ℂ) *
        (∑' (n : ℕ), z ^ (n + 1) * star ((a : ℂ) ^ (n + 1))) ∂μ =
      (2 : ℂ) * ∫ a : sphere (0 : ℂ) 1,
        (∑' (n : ℕ), z ^ (n + 1) * star ((a : ℂ) ^ (n + 1))) ∂μ from
      MeasureTheory.integral_const_mul _ _]
  simp only [integral_const, MeasureTheory.probReal_univ, one_smul]
  congr 1
  rw [integral_tsum]
  · congr 1
    apply tsum_congr
    intro i
    exact MeasureTheory.integral_const_mul (z ^ (i + 1))
      (fun a : sphere (0 : ℂ) 1 => star ((a : ℂ) ^ (i + 1)))
  · fun_prop (disch := norm_num)
  · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
      (g := fun n => ENNReal.ofReal (‖z‖ ^ (n + 1))) fun n => ?_) ?_)
    · refine le_trans (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (‖z‖ ^ (n + 1))) ?_) ?_
      · simp only [enorm, nnnorm_mul, nnnorm_pow, ENNReal.coe_mul,
        ENNReal.coe_pow, norm_nonneg, ENNReal.ofReal_pow, ofReal_norm]
        filter_upwards with a
        simp [show ‖(a : ℂ)‖₊ = 1 from by ext; simp]
      · norm_num
    · rw [← ENNReal.ofReal_tsum_of_nonneg] <;> norm_num
      exact Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg _) hz)
        (Nat.succ_injective)

/-- If two probability measures on the unit circle yield the same Herglotz–Riesz functions,
then they are equal. -/
theorem HerglotzRiesz_representation_uniqueness
    (μ₁ μ₂ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (h : ∀ z ∈ ball (0 : ℂ) 1, ∫ x : sphere (0 : ℂ) 1, (x + z) / (x - z) ∂μ₁ =
      ∫ x : sphere (0 : ℂ) 1, (x + z) / (x - z) ∂μ₂) :
    μ₁ = μ₂ := by
  have h_coeffs : ∀ k : ℕ,
        ∫ x : sphere (0 : ℂ) 1, star (x.val ^ (k + 1)) ∂μ₁ =
        ∫ x : sphere (0 : ℂ) 1, star (x.val ^ (k + 1)) ∂μ₂ := by
    have h_integral_expansion : ∀ z : ℂ, ‖z‖ < 1 →
      (∑' n : ℕ, z ^ (n + 1) * ∫ x : sphere (0 : ℂ) 1, star (x.val ^ (n + 1)) ∂μ₁) =
      (∑' n : ℕ, z ^ (n + 1) * ∫ x : sphere (0 : ℂ) 1, star (x.val ^ (n + 1)) ∂μ₂) := by
      intro z hz
      have h_integral_expansion1 : (∫ x : sphere (0 : ℂ) 1, ((x.val + z) / (x.val - z)) ∂μ₁) =
        1 + 2 * (∑' n : ℕ, z ^ (n + 1) * ∫ x : sphere (0 : ℂ) 1,
          star (x.val ^ (n + 1)) ∂μ₁) := integral_kernel_expansion μ₁ z hz
      have h_integral_expansion2 : (∫ x : sphere (0 : ℂ) 1, ((x.val + z) / (x.val - z)) ∂μ₂) =
        1 + 2 * (∑' n : ℕ, z ^ (n + 1) * ∫ x : sphere (0 : ℂ) 1,
          star (x.val ^ (n + 1)) ∂μ₂) := integral_kernel_expansion μ₂ z hz
      have hz' : z ∈ ball 0 1 := by
        rw [Metric.mem_ball, dist_eq]
        simp [hz]
      linear_combination h z hz' / 2 - h_integral_expansion1 / 2 + h_integral_expansion2 / 2
    have h_bounds : ∀ n : ℕ, ‖∫ x : sphere (0 : ℂ) 1, star (x.val ^ (n + 1)) ∂μ₁‖ ≤ 1 ∧
                             ‖∫ x : sphere (0 : ℂ) 1, star (x.val ^ (n + 1)) ∂μ₂‖ ≤ 1 := by
      intro n
      refine ⟨?_, ?_⟩ <;> refine le_trans (norm_integral_le_integral_norm _) ?_
      all_goals simp
    apply_rules [coeffs_eq_of_series_eq]
    · exact ⟨1, fun n => h_bounds n |>.1⟩
    · exact ⟨1, fun n => h_bounds n |>.2⟩
  have h : μ₁.toMeasure = μ₂.toMeasure := by
    apply_rules [measure_eq_of_moments]
    ext (_ | k) <;> simp only [star_pow, RCLike.star_def, pow_zero, integral_const, probReal_univ,
      one_smul] at h_coeffs ⊢
    convert congr_arg Star.star (h_coeffs k) using 1
    · rw [Complex.star_def]
      rw [show (starRingEnd ℂ) (∫ (x : sphere (0 : ℂ) 1),
              (starRingEnd ℂ) (x : ℂ) ^ (k + 1) ∂↑μ₁) =
            ∫ (x : sphere (0 : ℂ) 1), (starRingEnd ℂ) ((starRingEnd ℂ) (x : ℂ) ^ (k + 1)) ∂↑μ₁
          from integral_conj.symm]
      simp
    · rw [Complex.star_def]
      rw [show (starRingEnd ℂ) (∫ (x : sphere (0 : ℂ) 1),
              (starRingEnd ℂ) (x : ℂ) ^ (k + 1) ∂↑μ₂) =
            ∫ (x : sphere (0 : ℂ) 1), (starRingEnd ℂ) ((starRingEnd ℂ) (x : ℂ) ^ (k + 1)) ∂↑μ₂
          from integral_conj.symm]
      simp
  exact Subtype.ext h

end LeanPool.LeanComplexAnalysis
