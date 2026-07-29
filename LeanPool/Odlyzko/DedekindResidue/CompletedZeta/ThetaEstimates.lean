/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.ClassTheta

/-!
# Decay estimates for the Hecke theta  (SP1-AGE-4, brick 4a)

The analytic inputs feeding the `WeakFEPair` construction of `Λ_K`:

* `exists_pos_norm_le_of_discrete` — a discrete lattice has a positive shortest-vector
  bound;
* `summable_real_weightedGaussian` — pointwise summability of the real weighted Gaussian
  over a lattice (weights bounded below);
* `tsum_ite_gaussian_tail` — the zero-removed Gaussian lattice sum decays like
  `exp(-π(a-a₀)δ²)`;
* `heckeTheta_eq_one_add` — splitting `Θ_I(c) = 1 + Θ*_I(c)` at the zero lattice point;
* `abs_fullLog_le` / `le_heckeWeights_of_bounded` — uniform weight lower bound
  `c(t,u)_w ≥ m·t^{1/n}` over any coordinate-bounded set of the log-torus;
* `exists_heckeTheta_dev_bound` — the packaged estimate: uniformly over the unit box and
  `t ≥ 1`, `0 ≤ Θ_I(c(t,u)) − 1 ≤ C·exp(−c'·t^{1/n})`.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped nonZeroDivisors Real

variable {ι : Type*} [Fintype ι]


/-- Every discrete additive subgroup of a normed space has a positive shortest-vector
bound: nonzero elements have norm at least `δ` for some `δ > 0`. -/
theorem exists_pos_norm_le_of_discrete (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : L, v ≠ 0 → δ ≤ ‖(v : EuclideanSpace ℝ ι)‖ := by
  have hopen : IsOpen ({0} : Set L) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 rfl
  refine ⟨ε, hε, fun v hv => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : v ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_eq_of_lt rfl hlt
  exact hv (hball hmem)

open scoped Classical in
/-- Summability of the real weighted Gaussian over a lattice, for weights bounded below by
a positive constant (restriction of the `ThetaLattice` machinery to the point `0`). -/
theorem summable_real_weightedGaussian (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {c : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hca : ∀ i, a ≤ c i) :
    Summable fun v : L =>
      Real.exp (-π * ∑ i, c i * ((v : EuclideanSpace ℝ ι) i) ^ 2) := by
  have h := summable_norm_restrict_weightedGaussianCM L ha hca
    ⟨{0}, isCompact_singleton⟩
  refine h.of_nonneg_of_le (fun v => (Real.exp_pos _).le) (fun v => ?_)
  have heval : Real.exp (-π * ∑ i, c i * ((v : EuclideanSpace ℝ ι) i) ^ 2)
      = ‖(((weightedGaussianCM c).comp
          (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
            ({0} : Set (EuclideanSpace ℝ ι)))
          (⟨0, rfl⟩ : ({0} : Set (EuclideanSpace ℝ ι)))‖ := by
    rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
    show _ = ‖weightedGaussianCM c (0 + (v : EuclideanSpace ℝ ι))‖
    rw [zero_add, norm_weightedGaussianCM_apply]
  rw [heval]
  exact ContinuousMap.norm_coe_le_norm _ _

open scoped Classical in
/-- The zero-removed weighted Gaussian lattice sum decays like `exp(-π(a-a₀)δ²)` for
weights `≥ a`: pull the shortest-vector Gaussian factor out of every term. -/
theorem tsum_ite_gaussian_tail (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {a a₀ δ : ℝ} (ha₀ : 0 < a₀) (haa : a₀ ≤ a)
    (hδ : 0 < δ) (hδL : ∀ v : L, v ≠ 0 → δ ≤ ‖(v : EuclideanSpace ℝ ι)‖)
    {c : ι → ℝ} (hca : ∀ i, a ≤ c i) :
    (∑' v : L, if v = 0 then 0
        else Real.exp (-π * ∑ i, c i * ((v : EuclideanSpace ℝ ι) i) ^ 2))
      ≤ Real.exp (-π * (a - a₀) * δ ^ 2)
        * ∑' v : L, Real.exp (-π * ∑ i, a₀ * ((v : EuclideanSpace ℝ ι) i) ^ 2) := by
  have hsum₀ : Summable fun v : L =>
      Real.exp (-π * ∑ i, a₀ * ((v : EuclideanSpace ℝ ι) i) ^ 2) :=
    summable_real_weightedGaussian L ha₀ (fun i => le_refl a₀)
  rw [← smul_eq_mul, ← tsum_const_smul'' (Real.exp (-π * (a - a₀) * δ ^ 2))]
  refine Summable.tsum_le_tsum (fun v => ?_) ?_ (hsum₀.const_smul _)
  · by_cases hv : v = 0
    · rw [if_pos hv]
      have : (0:ℝ) < Real.exp (-π * (a - a₀) * δ ^ 2)
          * Real.exp (-π * ∑ i, a₀ * ((v : EuclideanSpace ℝ ι) i) ^ 2) := by
        positivity
      exact le_of_lt (by simpa [smul_eq_mul] using this)
    · rw [if_neg hv, smul_eq_mul, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hnorm : δ ^ 2 ≤ ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2 := by
        have h1 : δ ^ 2 ≤ ‖(v : EuclideanSpace ℝ ι)‖ ^ 2 :=
          pow_le_pow_left₀ hδ.le (hδL v hv) 2
        rwa [norm_sq_eq_sum] at h1
      have hsplit : ∀ i : ι, c i * ((v : EuclideanSpace ℝ ι) i) ^ 2
          ≥ (a - a₀) * ((v : EuclideanSpace ℝ ι) i) ^ 2
            + a₀ * ((v : EuclideanSpace ℝ ι) i) ^ 2 := by
        intro i
        have := hca i
        nlinarith [sq_nonneg ((v : EuclideanSpace ℝ ι) i)]
      have hsum_ge : ∑ i, c i * ((v : EuclideanSpace ℝ ι) i) ^ 2
          ≥ (a - a₀) * ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2
            + ∑ i, a₀ * ((v : EuclideanSpace ℝ ι) i) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun i _ => hsplit i)
      have hδterm : -π * (a - a₀) * δ ^ 2
          ≥ -π * ((a - a₀) * ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2)
            + π * ((a - a₀) * ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2)
              - π * ((a - a₀) * ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2) := by
        have hmul : (a - a₀) * δ ^ 2 ≤ (a - a₀) * ∑ i, ((v : EuclideanSpace ℝ ι) i) ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm (by linarith)
        nlinarith [Real.pi_pos]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr haa),
        Real.pi_pos.le]
  · refine (summable_real_weightedGaussian L (lt_of_lt_of_le ha₀ haa) hca).of_nonneg_of_le
      (fun v => ?_) (fun v => ?_)
    · split_ifs
      · exact le_refl 0
      · exact (Real.exp_pos _).le
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_refl _

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- Splitting the Hecke theta at the zero lattice point: `Θ_I(c) = 1 + Θ*_I(c)`. -/
theorem heckeTheta_eq_one_add (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : InfinitePlace K → ℝ} {a : ℝ} (ha : 0 < a) (hca : ∀ w, a ≤ c w) :
    heckeTheta K I c
      = 1 + ∑' v : idealZLattice K I, (if v = 0 then 0
          else Real.exp (-π * ∑ i : index K,
            placeWeights K c i * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
  have hplaceW : ∀ i, a ≤ placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hca _
  have hsum := summable_real_weightedGaussian (idealZLattice K I) ha hplaceW
  rw [heckeTheta, hsum.tsum_eq_add_tsum_ite 0]
  congr 1
  have hzero : ((0 : idealZLattice K I) : EuclideanSpace ℝ (index K)) = 0 := rfl
  rw [hzero]
  simp

open scoped Classical in
/-- Uniform box bound for `fullLog`: on any coordinate-bounded set of `logSpace`,
`|fullLog u w| ≤ card·R`. -/
theorem abs_fullLog_le {u : logSpace K} {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ i, |u i| ≤ R) (w : InfinitePlace K) :
    |fullLog K u w| ≤ (Fintype.card (InfinitePlace K)) * R := by
  have hcard1 : (1 : ℝ) ≤ (Fintype.card (InfinitePlace K) : ℝ) := by
    have := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace K))
    exact_mod_cast this
  rw [fullLog]
  split_ifs with h
  · calc |-∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'|
        = |∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'| := abs_neg _
      _ ≤ ∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, |u w'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, R :=
          Finset.sum_le_sum (fun i _ => hu i)
      _ = (Fintype.card {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}) * R := by
          rw [Finset.sum_const, nsmul_eq_mul, Fintype.card]
      _ ≤ (Fintype.card (InfinitePlace K)) * R := by
          refine mul_le_mul_of_nonneg_right ?_ hR
          exact_mod_cast Fintype.card_subtype_le _
  · calc |u ⟨w, h⟩| ≤ R := hu _
      _ = 1 * R := (one_mul R).symm
      _ ≤ (Fintype.card (InfinitePlace K)) * R := mul_le_mul_of_nonneg_right hcard1 hR

open scoped Classical in
/-- **Uniform lower bound for the Hecke weights over any bounded set** of the log-torus:
`c(t,u)_w ≥ m·t^{1/n}` with `m > 0` depending only on the bound. -/
theorem le_heckeWeights_of_bounded {R : ℝ} (hR : 0 ≤ R) {u : logSpace K}
    (hu : ∀ i, |u i| ≤ R) {t : ℝ} (ht : 0 ≤ t) (w : InfinitePlace K) :
    Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R))
        * t ^ ((1 : ℝ) / (Module.finrank ℚ K))
      ≤ heckeWeights K t u w := by
  rw [heckeWeights, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht _)
  rw [Real.exp_le_exp]
  have habs := abs_fullLog_le K hR hu w
  have hmult1 : (1 : ℝ) ≤ (mult w : ℝ) := by
    have := mult_pos (w := w)
    exact_mod_cast this
  have hbound : |2 * fullLog K u w / mult w| ≤ 2 * (Fintype.card (InfinitePlace K)) * R := by
    rw [abs_div, abs_mul]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2, abs_of_pos (lt_of_lt_of_le one_pos hmult1)]
    rw [div_le_iff₀ (lt_of_lt_of_le one_pos hmult1)]
    calc 2 * |fullLog K u w| ≤ 2 * ((Fintype.card (InfinitePlace K)) * R) := by linarith
      _ = 2 * (Fintype.card (InfinitePlace K)) * R * 1 := by ring
      _ ≤ 2 * (Fintype.card (InfinitePlace K)) * R * (mult w : ℝ) := by
          refine mul_le_mul_of_nonneg_left hmult1 ?_
          positivity
  linarith [neg_abs_le (2 * fullLog K u w / mult w), hbound]

open scoped Classical in
/-- **Exponential deviation bound for the Hecke theta over the unit box**: uniformly in
`u` in the fundamental box and `t ≥ 1`,
`0 ≤ Θ_I(c(t,u)) − 1 ≤ C·exp(−c'·t^{1/n})`. -/
theorem exists_heckeTheta_dev_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ {t : ℝ}, 1 ≤ t → ∀ u ∈ ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
        0 ≤ heckeTheta K I (heckeWeights K t u) - 1
          ∧ heckeTheta K I (heckeWeights K t u) - 1
              ≤ C * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
    (ZSpan.fundamentalDomain_isBounded
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ))
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hcoord : ∀ u ∈ ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      ∀ i, |u i| ≤ R := by
    intro u hu i
    have h1 : ‖u‖ ≤ R₀ := by
      have := hR₀ hu
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc |u i| = ‖u i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u‖ := norm_le_pi_norm u i
      _ ≤ R₀ := h1
      _ ≤ R := le_max_left _ _
  set m : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hmdef
  have hm : 0 < m := Real.exp_pos _
  obtain ⟨δ, hδ, hδL⟩ := exists_pos_norm_le_of_discrete (idealZLattice K I)
  set Θ₀ : ℝ := ∑' v : idealZLattice K I,
    Real.exp (-π * ∑ i : index K, m * ((v : EuclideanSpace ℝ (index K)) i) ^ 2) with hΘ₀def
  have hΘ₀sum : Summable fun v : idealZLattice K I =>
      Real.exp (-π * ∑ i : index K, m * ((v : EuclideanSpace ℝ (index K)) i) ^ 2) :=
    summable_real_weightedGaussian _ hm (fun i => le_refl m)
  have hΘ₀pos : 0 < Θ₀ := by
    have h0 : Real.exp (-π * ∑ i : index K,
        m * (((0 : idealZLattice K I) : EuclideanSpace ℝ (index K)) i) ^ 2) ≤ Θ₀ :=
      hΘ₀sum.le_tsum 0 (fun v _ => (Real.exp_pos _).le)
    exact lt_of_lt_of_le (Real.exp_pos _) h0
  refine ⟨Real.exp (π * m * δ ^ 2) * Θ₀, π * m * δ ^ 2,
    by positivity, by positivity, fun {t} ht u hu => ?_⟩
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
  have htpow : (1:ℝ) ≤ t ^ ((1 : ℝ) / (Module.finrank ℚ K)) := by
    refine Real.one_le_rpow ht ?_
    have := finrank_pos_real K
    positivity
  have hca : ∀ w, m * t ^ ((1 : ℝ) / (Module.finrank ℚ K)) ≤ heckeWeights K t u w :=
    fun w => le_heckeWeights_of_bounded K hR (hcoord u hu) ht0.le w
  have ha : (0:ℝ) < m * t ^ ((1 : ℝ) / (Module.finrank ℚ K)) := by positivity
  rw [heckeTheta_eq_one_add K I ha hca, add_sub_cancel_left]
  constructor
  · refine tsum_nonneg (fun v => ?_)
    split_ifs
    · exact le_refl 0
    · exact (Real.exp_pos _).le
  · have hplace : ∀ i : index K, m * t ^ ((1 : ℝ) / (Module.finrank ℚ K))
        ≤ placeWeights K (heckeWeights K t u) i := by
      rintro (w | ⟨w, j⟩) <;> exact hca _
    have htail := tsum_ite_gaussian_tail (idealZLattice K I) hm
      (le_mul_of_one_le_right hm.le htpow) hδ hδL hplace
    refine le_trans htail (le_of_eq ?_)
    rw [← hΘ₀def]
    have hexp : Real.exp (-π * (m * t ^ ((1 : ℝ) / (Module.finrank ℚ K)) - m) * δ ^ 2)
        = Real.exp (π * m * δ ^ 2)
          * Real.exp (-(π * m * δ ^ 2) * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring

/-- Monotone comparison for weighted Gaussian terms. -/
theorem exp_weighted_le_exp_iso {c : ι → ℝ} {a : ℝ} (hca : ∀ i, a ≤ c i)
    (x : EuclideanSpace ℝ ι) :
    Real.exp (-π * ∑ i, c i * (x i) ^ 2) ≤ Real.exp (-π * ∑ i, a * (x i) ^ 2) := by
  refine Real.exp_le_exp.mpr ?_
  have h : ∑ i, a * (x i) ^ 2 ≤ ∑ i, c i * (x i) ^ 2 :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hca i) (sq_nonneg _))
  nlinarith [Real.pi_pos]

open scoped Classical in
/-- **Joint continuity of the Hecke theta** in the ray parameter and the log-torus
variable, at every positive `t`. -/
theorem continuousAt_heckeTheta_heckeWeights (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × logSpace K =>
      heckeTheta K I (heckeWeights K q.1 q.2)) p := by
  set a : ℝ := p.1 / 2 with ha_def
  have ha : 0 < a := by positivity
  set R : ℝ := ‖p.2‖ + 1 with hR_def
  have hR : 0 ≤ R := by positivity
  set m : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hm_def
  have hm : 0 < m := Real.exp_pos _
  set a' : ℝ := m * a ^ ((1 : ℝ) / (Module.finrank ℚ K)) with ha'_def
  have ha' : 0 < a' := by
    have : (0:ℝ) < a ^ ((1 : ℝ) / (Module.finrank ℚ K)) := Real.rpow_pos_of_pos ha _
    positivity
  have hsub : ∀ q : ℝ × logSpace K, q ∈ Set.Ioi a ×ˢ Metric.ball (0 : logSpace K) R →
      ∀ i, a' ≤ placeWeights K (heckeWeights K q.1 q.2) i := by
    rintro q ⟨hq1, hq2⟩ i
    have hcoord : ∀ j, |q.2 j| ≤ R := by
      intro j
      calc |q.2 j| = ‖q.2 j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖q.2‖ := norm_le_pi_norm q.2 j
        _ ≤ R := by
            have := Metric.mem_ball.mp hq2
            rw [dist_zero_right] at this
            exact this.le
    have hq1' : (0:ℝ) < q.1 := lt_trans ha hq1
    have hbase := le_heckeWeights_of_bounded K hR hcoord hq1'.le
    have hple : ∀ w : InfinitePlace K, a' ≤ heckeWeights K q.1 q.2 w := by
      intro w
      refine le_trans ?_ (hbase w)
      rw [ha'_def, hm_def]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Real.rpow_le_rpow ha.le (Set.mem_Ioi.mp hq1).le (by positivity)
    rcases i with (w | ⟨w, j⟩) <;> exact hple _
  refine ContinuousOn.continuousAt (s := Set.Ioi a ×ˢ Metric.ball (0 : logSpace K) R) ?_ ?_
  · show ContinuousOn (fun q : ℝ × logSpace K => ∑' v : idealZLattice K I,
      Real.exp (-π * ∑ i : index K, placeWeights K (heckeWeights K q.1 q.2) i
        * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) _
    refine continuousOn_tsum (u := fun v : idealZLattice K I =>
      Real.exp (-π * ∑ i : index K, a' * ((v : EuclideanSpace ℝ (index K)) i) ^ 2))
      (fun v => ?_) (summable_real_weightedGaussian _ ha' (fun i => le_refl _))
      (fun v q hq => ?_)
    · -- each term continuous on the set
      refine ContinuousOn.rexp ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine continuousOn_finsetSum _ (fun i _ => ContinuousOn.mul ?_ continuousOn_const)
      -- placeWeights (heckeWeights q.1 q.2) i continuous in q on the set
      have hw : ∀ w : InfinitePlace K, ContinuousOn
          (fun q : ℝ × logSpace K => heckeWeights K q.1 q.2 w)
          (Set.Ioi a ×ˢ Metric.ball (0 : logSpace K) R) := by
        intro w
        show ContinuousOn (fun q : ℝ × logSpace K =>
          q.1 ^ ((1 : ℝ) / (Module.finrank ℚ K))
            * Real.exp (2 * fullLog K q.2 w / mult w)) _
        refine ContinuousOn.mul ?_ ?_
        · refine ContinuousOn.rpow_const (continuous_fst.continuousOn) ?_
          rintro q ⟨hq1, -⟩
          exact Or.inl (ne_of_gt (lt_trans ha hq1))
        · refine Continuous.continuousOn ?_
          refine Real.continuous_exp.comp ?_
          refine Continuous.div_const ?_ _
          refine Continuous.mul continuous_const ?_
          -- fullLog continuous in u; compose with snd
          have hfl : Continuous (fun u : logSpace K => fullLog K u w) := by
            rw [show (fun u : logSpace K => fullLog K u w)
              = fun u : logSpace K => if h : w = (w₀ : InfinitePlace K) then
                  -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'
                else u ⟨w, h⟩ from rfl]
            split_ifs with h
            · exact (continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)).neg
            · exact continuous_apply _
          exact hfl.comp continuous_snd
      rcases i with (w | ⟨w, j⟩) <;>
        · show ContinuousOn (fun q : ℝ × logSpace K => heckeWeights K q.1 q.2 _) _
          exact hw _
    · -- the uniform bound on the set
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_weighted_le_exp_iso (hsub q hq) (v : EuclideanSpace ℝ (index K))
  · refine IsOpen.mem_nhds (IsOpen.prod isOpen_Ioi Metric.isOpen_ball) ?_
    refine ⟨?_, ?_⟩
    · show a < p.1
      rw [ha_def]
      linarith
    · show p.2 ∈ Metric.ball (0 : logSpace K) R
      rw [Metric.mem_ball, dist_zero_right, hR_def]
      linarith

open scoped Classical in
/-- Isotropic comparison for the full theta: weights bounded below give a theta bounded by
the isotropic lattice Gaussian. -/
theorem heckeTheta_le_iso (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : InfinitePlace K → ℝ}
    {a : ℝ} (ha : 0 < a) (hca : ∀ w, a ≤ c w) :
    heckeTheta K I c ≤ ∑' v : idealZLattice K I,
      Real.exp (-π * ∑ i : index K, a * ((v : EuclideanSpace ℝ (index K)) i) ^ 2) := by
  have hplaceW : ∀ i, a ≤ placeWeights K c i := by
    rintro (w | ⟨w, j⟩) <;> exact hca _
  rw [heckeTheta]
  refine Summable.tsum_le_tsum (fun v => exp_weighted_le_exp_iso hplaceW _)
    (summable_real_weightedGaussian _ ha hplaceW)
    (summable_real_weightedGaussian _ ha (fun i => le_refl a))

open scoped Classical in
/-- The fundamental box of the unit lattice has coordinate-bounded elements. -/
theorem exists_box_coord_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u ∈ ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      ∀ i, |u i| ≤ R := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
    (ZSpan.fundamentalDomain_isBounded
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ))
  refine ⟨max R₀ 0, le_max_right _ _, fun u hu i => ?_⟩
  have h1 : ‖u‖ ≤ R₀ := by
    have := hR₀ hu
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  calc |u i| = ‖u i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖u‖ := norm_le_pi_norm u i
    _ ≤ R₀ := h1
    _ ≤ max R₀ 0 := le_max_left _ _

open scoped Classical in
/-- **Continuity of the unit-averaged theta** on the positive ray. -/
theorem continuousOn_heckeG (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (heckeG K I) (Set.Ioi (0 : ℝ)) := by
  intro t₀ ht₀
  refine ContinuousAt.continuousWithinAt ?_
  have ht₀' : (0:ℝ) < t₀ := ht₀
  obtain ⟨R, hR, hbox⟩ := exists_box_coord_bound K
  set m : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hm_def
  have hm : 0 < m := Real.exp_pos _
  set a' : ℝ := m * (t₀ / 2) ^ ((1 : ℝ) / (Module.finrank ℚ K)) with ha'_def
  have ha' : 0 < a' := by
    have : (0:ℝ) < (t₀ / 2) ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hG : heckeG K I = fun t => (torsionOrder K : ℝ)⁻¹ *
      ∫ u in ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
        heckeTheta K I (heckeWeights K t u) := by
    funext t
    rw [heckeG]
  rw [hG]
  refine ContinuousAt.mul continuousAt_const ?_
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ =>
    ∑' v : idealZLattice K I,
      Real.exp (-π * ∑ i : index K, a' * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) ?_ ?_ ?_ ?_
  · -- a.e.-strong measurability near t₀
    refine Filter.eventually_of_mem (Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)) ?_
    intro t ht
    have hcont : Continuous (fun u : logSpace K => heckeTheta K I (heckeWeights K t u)) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hj := continuousAt_heckeTheta_heckeWeights K I
        (p := ((t : ℝ), u)) (lt_trans (by positivity) ht)
      have hin : ContinuousAt (fun u' : logSpace K => ((t : ℝ), u')) u :=
        (continuous_const.prodMk continuous_id).continuousAt
      have hcompeq : (fun u' : logSpace K => heckeTheta K I (heckeWeights K t u'))
          = (fun q : ℝ × logSpace K => heckeTheta K I (heckeWeights K q.1 q.2))
            ∘ (fun u' : logSpace K => ((t : ℝ), u')) := rfl
      rw [hcompeq]
      exact ContinuousAt.comp (x := u) hj hin
    exact hcont.aestronglyMeasurable
  · -- uniform bound near t₀
    refine Filter.eventually_of_mem (Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)) ?_
    intro t ht
    refine (MeasureTheory.ae_restrict_iff' (ZSpan.fundamentalDomain_measurableSet _)).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hca : ∀ w, a' ≤ heckeWeights K t u w := by
      intro w
      refine le_trans ?_ (le_heckeWeights_of_bounded K hR (hbox u hu)
        (le_of_lt (lt_trans (by positivity) ht)) w)
      rw [ha'_def, hm_def]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Real.rpow_le_rpow (by positivity) (le_of_lt ht) (by positivity)
    rw [Real.norm_eq_abs, abs_of_pos]
    · exact heckeTheta_le_iso K I ha' hca
    · -- theta positive: at least the zero term
      have hsplit := heckeTheta_eq_one_add K I ha' hca
      have htail : 0 ≤ ∑' v : idealZLattice K I, (if v = 0 then 0
          else Real.exp (-π * ∑ i : index K,
            placeWeights K (heckeWeights K t u) i
              * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
        refine tsum_nonneg (fun v => ?_)
        split_ifs
        · exact le_refl 0
        · exact (Real.exp_pos _).le
      rw [hsplit]
      linarith
  · -- the bound is integrable on the (finite-measure) box
    exact MeasureTheory.integrableOn_const
      (ne_top_of_lt (ZSpan.fundamentalDomain_isBounded _).measure_lt_top)
  · -- a.e. continuity in t at t₀
    refine Filter.Eventually.of_forall (fun u => ?_)
    have hj := continuousAt_heckeTheta_heckeWeights K I (p := ((t₀ : ℝ), u)) ht₀'
    have hin : ContinuousAt (fun t : ℝ => ((t : ℝ), u)) t₀ :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hcompeq : (fun x : ℝ => heckeTheta K I (heckeWeights K x u))
        = (fun q : ℝ × logSpace K => heckeTheta K I (heckeWeights K q.1 q.2))
          ∘ (fun t : ℝ => ((t : ℝ), u)) := rfl
    rw [hcompeq]
    exact ContinuousAt.comp (x := t₀) hj hin

open scoped Classical in
/-- The volume of the unit fundamental box — the constant term of the theta integral. -/
noncomputable def unitBoxVol : ℝ :=
  (volume (ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ))).toReal

open scoped Classical in
theorem unitBoxVol_pos : 0 < unitBoxVol K := by
  rw [unitBoxVol]
  exact ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero _)
    (ne_top_of_lt (ZSpan.fundamentalDomain_isBounded _).measure_lt_top)

open scoped Classical in
/-- **Exponential approach of `g_I` to its constant term**: for `t ≥ 1`,
`|g_I(t) − w⁻¹·vol| ≤ C·exp(−c'·t^{1/n})`. -/
theorem exists_heckeG_dev_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∀ {t : ℝ}, 1 ≤ t →
      |heckeG K I t - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K|
        ≤ C * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  obtain ⟨Cθ, c', hCθ, hc', hdev⟩ := exists_heckeTheta_dev_bound K I
  have hw : (0:ℝ) < (torsionOrder K : ℝ)⁻¹ := by
    have h1 : 0 < torsionOrder K := torsionOrder_pos K
    have : (0:ℝ) < (torsionOrder K : ℝ) := by exact_mod_cast h1
    positivity
  refine ⟨(torsionOrder K : ℝ)⁻¹ * unitBoxVol K * Cθ, c',
    by have := unitBoxVol_pos K; positivity, hc', fun {t} ht => ?_⟩
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
  set B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) with hBdef
  have hBmeas : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  -- integrability of Θ on the box
  have hcontu : Continuous (fun u : logSpace K => heckeTheta K I (heckeWeights K t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hj := continuousAt_heckeTheta_heckeWeights K I (p := ((t : ℝ), u)) ht0
    have hin : ContinuousAt (fun u' : logSpace K => ((t : ℝ), u')) u :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hcompeq : (fun u' : logSpace K => heckeTheta K I (heckeWeights K t u'))
        = (fun q : ℝ × logSpace K => heckeTheta K I (heckeWeights K q.1 q.2))
          ∘ (fun u' : logSpace K => ((t : ℝ), u')) := rfl
    rw [hcompeq]
    exact ContinuousAt.comp (x := u) hj hin
  have hint : IntegrableOn (fun u : logSpace K =>
      heckeTheta K I (heckeWeights K t u)) B := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (ne_top_of_lt hBfin)
        (C := 1 + Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K)))))
      hcontu.aestronglyMeasurable.restrict ?_
    refine (MeasureTheory.ae_restrict_iff' hBmeas).mpr (Filter.Eventually.of_forall
      (fun u hu => ?_))
    obtain ⟨h0, hle⟩ := hdev ht u hu
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  -- split off the constant
  have hsplit : ∫ u in B, heckeTheta K I (heckeWeights K t u)
      = unitBoxVol K + ∫ u in B, (heckeTheta K I (heckeWeights K t u) - 1) := by
    rw [MeasureTheory.integral_sub hint (MeasureTheory.integrableOn_const
      (ne_top_of_lt hBfin))]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    have hvol : volume.real B = unitBoxVol K := by
      rw [unitBoxVol, hBdef]
      rfl
    rw [hvol]
    ring
  have hGdev : heckeG K I t - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K
      = (torsionOrder K : ℝ)⁻¹
        * ∫ u in B, (heckeTheta K I (heckeWeights K t u) - 1) := by
    rw [heckeG, ← hBdef, hsplit]
    ring
  rw [hGdev, abs_mul, abs_of_pos hw]
  have hbound : |∫ u in B, (heckeTheta K I (heckeWeights K t u) - 1)|
      ≤ Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) * (volume B).toReal := by
    rw [← Real.norm_eq_abs]
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hBfin (fun u hu => ?_)
    obtain ⟨h0, hle⟩ := hdev ht u hu
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hle
  calc (torsionOrder K : ℝ)⁻¹ * |∫ u in B, (heckeTheta K I (heckeWeights K t u) - 1)|
      ≤ (torsionOrder K : ℝ)⁻¹
        * (Cθ * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K)))
            * (volume B).toReal) := by
        exact mul_le_mul_of_nonneg_left hbound hw.le
    _ = (torsionOrder K : ℝ)⁻¹ * unitBoxVol K * Cθ
        * Real.exp (-c' * t ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
        have hvol2 : (volume B).toReal = unitBoxVol K := by
          rw [unitBoxVol, hBdef]
        rw [hvol2]
        ring

end

end DedekindResidue
