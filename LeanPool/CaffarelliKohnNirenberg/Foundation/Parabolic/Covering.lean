/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# A parabolic Vitali covering estimate

This file records the measure estimate obtained by applying the Vitali
covering theorem to the metric balls associated with the parabolic cylinders.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Explicit parabolic metric-ball family used in the covering argument. -/
abbrev coveringParabolicMetricBall (c : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c r

lemma measurableSet_parabolicCylinder (x : Vec3) (t r : ℝ) :
    MeasurableSet (parabolicCylinder x t r) := by
  rw [parabolicCylinder]
  exact (vec3Ball_measurable x r).prod measurableSet_Ioc

private lemma parabolicMetricBall_ediam_le (c : ParabolicPoint) (r : ℝ) :
    ediam (coveringParabolicMetricBall c r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le
  intro x hx y hy
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      x c < r at hx
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      y c < r at hy
  have hxy : @dist ParabolicPoint
      (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) x y ≤
      @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) x c +
        @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) c y :=
    dist_triangle x c y
  have hcy : @dist ParabolicPoint
      (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) c y < r := by
    simpa only [dist_comm] using hy
  apply le_of_lt
  calc
    @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) x y ≤
        @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) x c +
          @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) c y
            := hxy
    _ < r + r := add_lt_add hx hcy
    _ = 2 * r := by ring

private lemma tendsto_parabolicCoverRadius :
    Tendsto (fun n : ℕ => (10 : ℝ≥0∞) *
      ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.cast_add, add_comm] using
      (Filter.tendsto_atTop_add_const_left atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp hn)
  have hof : Tendsto (fun n : ℕ => ENNReal.ofReal
      (1 / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
    by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hinv
  have hpair : Tendsto (fun n : ℕ =>
      ((10 : ℝ≥0∞), ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)))) atTop
      (𝓝 ((10 : ℝ≥0∞), 0)) :=
    tendsto_const_nhds.prodMk_nhds hof
  convert ((ENNReal.tendsto_mul (by norm_num) (by norm_num)).comp hpair) using 1 <;>
    simp [Function.comp_def]

private lemma volume_vec3Ball_finite (x : Vec3) :
    volume (vec3Ball x 2) < (∞ : ℝ≥0∞) := by
  have hsub : vec3Ball x 2 ⊆ @Metric.ball Vec3 inferInstance x 2 := by
    intro y hy
    change vec3EuclideanNorm (y - x) < 2 at hy
    rw [Metric.mem_ball]
    change ‖y - x‖ < 2
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun b => ‖(y - x) b‖₊) < (2 : ℝ≥0) := by
      apply (Finset.sup_lt_iff (by norm_num)).2
      intro i hi
      have hi' : ‖(WithLp.toLp 2 (y - x)).ofLp i‖ ≤
          ‖WithLp.toLp 2 (y - x)‖ := PiLp.norm_apply_le _ i
      have hi'' : ‖y i - x i‖ ≤ vec3EuclideanNorm (y - x) := by
        rw [vec3EuclideanNorm_eq_l2]
        exact hi'
      have hreal : ‖y i - x i‖ < (2 : ℝ) := lt_of_le_of_lt hi'' hy
      exact_mod_cast hreal
    exact_mod_cast hsup
  exact (measure_mono hsub).trans_lt measure_ball_lt_top

private lemma parabolicMetricBall_subset_finiteCylinder (p : ParabolicPoint) :
    coveringParabolicMetricBall p 1 ⊆
      parabolicCylinder p.1 (p.2 + 1) 2 := by
  rcases p with ⟨x, t⟩
  rintro q hs
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      q ((x, t) : ParabolicPoint) < 1 at hs
  rw [dist_eq_parabolicDist q ((x, t) : ParabolicPoint)] at hs
  rcases q with ⟨y, s⟩
  rcases max_lt_iff.mp hs with ⟨hspace, htime⟩
  have habs : |s - t| < 1 := by
    simpa using (Real.sqrt_lt' one_pos).mp htime
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  change (y, s) ∈ parabolicCylinder x (t + 1) 2
  exact ⟨hspace.trans (by norm_num), by linarith only [hlo], le_of_lt (by
    linarith only [hhi])⟩

private lemma volume_parabolicMetricBall_finite (p : ParabolicPoint) :
    volume (coveringParabolicMetricBall p 1) < (∞ : ℝ≥0∞) := by
  have hfinite : volume (parabolicCylinder p.1 (p.2 + 1) 2) < (∞ : ℝ≥0∞) := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top (volume_vec3Ball_finite p.1) (by norm_num)
  exact (measure_mono (parabolicMetricBall_subset_finiteCylinder p)).trans_lt hfinite

instance coveringParabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  { finiteAtNhds := fun p =>
      ⟨coveringParabolicMetricBall p 1,
        @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p 1 one_pos,
        volume_parabolicMetricBall_finite p⟩ }

private lemma hausdorff_covering_diameter_integral_le_1 :
    ∀ {g : ParabolicPoint → ℝ≥0∞} {U S : Set ParabolicPoint} {ε : ℝ≥0},
      (0 : ℝ≥0) < ε →
        ∀ (radius : ℕ → (↑S : Type) → ℝ),
          (∀ (n : ℕ) (z : (↑S : Type)),
              (0 : ℝ) < radius n z ∧
                radius n z < (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ∧
                  parabolicCylinder (↑z : ParabolicPoint).1 (↑z : ParabolicPoint).2 (radius n z) ⊆
                      U ∧
                    (↑ε : ℝ≥0∞) * ENNReal.ofReal (radius n z) <
                      ∫⁻ (y : ParabolicPoint) in
                        parabolicCylinder (↑z : ParabolicPoint).1 (↑z : ParabolicPoint).2
                          (radius n z),
                        g y) →
            ∀ (center : ℕ → (↑S : Type) → ParabolicPoint),
              let ball : ℕ → (↑S : Type) → Set ParabolicPoint := fun (n : ℕ) (z : (↑S : Type)) =>
                coveringParabolicMetricBall (center n z) (radius n z);
              ∀
                (vitali :
                  ∀ (n : ℕ),
                    ∃ (u : Set (↑S : Type)),
                      u.PairwiseDisjoint (ball n) ∧
                        ∀ (a : (↑S : Type)),
                          ∃ b ∈ u,
                            (ball n a ∩ ball n b).Nonempty ∧ radius n a ≤ (2 : ℝ) * radius n b),
                let selected : ℕ → Set (↑S : Type) := fun (n : ℕ) => Classical.choose (vitali n);
                let index : ℕ → Type := fun (n : ℕ) => { z : (↑S : Type) // z ∈ selected n };
                let cylinder : (n : ℕ) → index n → Set ParabolicPoint :=
                  fun (n : ℕ) (i : index n) =>
                  parabolicCylinder (↑(↑i : (↑S : Type)) : ParabolicPoint).1
                    (↑(↑i : (↑S : Type)) : ParabolicPoint).2 (radius n (↑i : (↑S : Type)));
                let enlarged : (n : ℕ) → index n → Set ParabolicPoint :=
                  fun (n : ℕ) (i : index n) =>
                  coveringParabolicMetricBall (center n (↑i : (↑S : Type)))
                    ((5 : ℝ) * radius n (↑i : (↑S : Type)));
                (∀ (n : ℕ) (i : index n),
                    ediam (enlarged n i) ≤
                      (10 : ℝ≥0∞) * ENNReal.ofReal (radius n (↑i : (↑S : Type)))) →
                  let K : ℝ≥0∞ := (10 : ℝ≥0∞) / (↑ε : ℝ≥0∞);
                  ∀ (n : ℕ) (i : index n),
                    ediam (enlarged n i) ≤ K * ∫⁻ (y : ParabolicPoint) in cylinder n i, g y
    := by
  intro g U S ε hε radius radius_spec center ball vitali selected index cylinder enlarged
    diameter_le K n i
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  have hεtop : (ε : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hmul : (ε : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) ≤
      ∫⁻ y in cylinder n i, g y :=
    (radius_spec n i.1).2.2.2.le
  have hfactor : (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) =
      K * ((ε : ℝ≥0∞) * ENNReal.ofReal (radius n i.1)) := by
    dsimp [K]
    rw [ENNReal.div_eq_inv_mul]
    calc
      (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) =
          1 * ((10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1)) := by simp
      _ = ((ε : ℝ≥0∞)⁻¹ * (ε : ℝ≥0∞)) *
          ((10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1)) := by
        rw [ENNReal.inv_mul_cancel hε0 hεtop]
      _ = ((ε : ℝ≥0∞)⁻¹ * (10 : ℝ≥0∞)) *
          ((ε : ℝ≥0∞) * ENNReal.ofReal (radius n i.1)) := by ac_rfl
  calc
    ediam (enlarged n i) ≤ (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) :=
      diameter_le n i
    _ = K * ((ε : ℝ≥0∞) * ENNReal.ofReal (radius n i.1)) := hfactor
    _ ≤ K * (∫⁻ y in cylinder n i, g y) :=
      mul_le_mul_of_nonneg_left hmul bot_le

private lemma hausdorff_covering_hausdorff_bound_2 :
    ∀ {g : ParabolicPoint → ℝ≥0∞} {U S : Set ParabolicPoint} {ε : ℝ≥0}
      (radius : ℕ → (↑S : Type) → ℝ),
      (∀ (n : ℕ) (z : (↑S : Type)),
          (0 : ℝ) < radius n z ∧
            radius n z < (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ∧
              parabolicCylinder (↑z : ParabolicPoint).1 (↑z : ParabolicPoint).2 (radius n z) ⊆ U ∧
                (↑ε : ℝ≥0∞) * ENNReal.ofReal (radius n z) <
                  ∫⁻ (y : ParabolicPoint) in
                    parabolicCylinder (↑z : ParabolicPoint).1 (↑z : ParabolicPoint).2 (radius n z),
                    g y) →
        ∀ (center : ℕ → (↑S : Type) → ParabolicPoint),
          let ball : ℕ → (↑S : Type) → Set ParabolicPoint := fun (n : ℕ) (z : (↑S : Type)) =>
            coveringParabolicMetricBall (center n z) (radius n z);
          ∀
            (vitali :
              ∀ (n : ℕ),
                ∃ (u : Set (↑S : Type)),
                  u.PairwiseDisjoint (ball n) ∧
                    ∀ (a : (↑S : Type)),
                      ∃ b ∈ u, (ball n a ∩ ball n b).Nonempty ∧ radius n a ≤ (2 : ℝ) * radius n b),
            let selected : ℕ → Set (↑S : Type) := fun (n : ℕ) => Classical.choose (vitali n);
            let index : ℕ → Type := fun (n : ℕ) => { z : (↑S : Type) // z ∈ selected n };
            (∀ (n : ℕ), Countable (index n)) →
              let enlarged : (n : ℕ) → index n → Set ParabolicPoint := fun (n : ℕ) (i : index n) =>
                coveringParabolicMetricBall (center n (↑i : (↑S : Type)))
                  ((5 : ℝ) * radius n (↑i : (↑S : Type)));
              (∀ (n : ℕ) (i : index n),
                  ediam (enlarged n i) ≤
                    (10 : ℝ≥0∞) * ENNReal.ofReal (radius n (↑i : (↑S : Type)))) →
                ∀ (K : ℝ≥0∞),
                  (∀ (n : ℕ) (a : (↑S : Type)),
                      (↑a : ParabolicPoint) ∈ ⋃ (i : index n), enlarged n i) →
                    (∀ (n : ℕ),
                        ∑' (i : index n), ediam (enlarged n i) ^ (1 : ℝ) ≤
                          K * ∫⁻ (y : ParabolicPoint) in U, g y) →
                      (μH[(1 : ℝ)] : Set ParabolicPoint → ℝ≥0∞) S ≤
                        K * ∫⁻ (y : ParabolicPoint) in U, g y
    := by
  intro g U S ε radius radius_spec center ball vitali selected index this enlarged diameter_le K
    enlarged_contains diameter_sum_le
  have hdiam : ∀ᶠ (n : ℕ) in atTop, ∀ i : index n,
      ediam (enlarged n i) ≤ (10 : ℝ≥0∞) *
        ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [] with n i
    calc
      ediam (enlarged n i) ≤ (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) :=
        diameter_le n i
      _ ≤ (10 : ℝ≥0∞) * ENNReal.ofReal
          (1 / ((n + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
          (radius_spec n i.1).2.1.le) bot_le
  have hcover : ∀ᶠ (n : ℕ) in atTop, S ⊆ ⋃ i : index n, enlarged n i := by
    filter_upwards [] with n
    intro z hz
    exact enlarged_contains n ⟨z, hz⟩
  have hhaus := Measure.hausdorffMeasure_le_liminf_tsum (1 : ℝ) S
    (fun n : ℕ => (10 : ℝ≥0∞) *
      ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)))
    tendsto_parabolicCoverRadius (fun n i => enlarged n i) hdiam hcover
  have hliminf : liminf
      (fun n => ∑' i : index n, ediam (enlarged n i) ^ (1 : ℝ)) atTop ≤
      K * (∫⁻ y in U, g y) := by
    refine Filter.liminf_le_of_le (hf := by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (diameter_sum_le n)
  exact hhaus.trans hliminf

theorem parabolicHausdorffMeasure_one_le_integral_of_small_cylinders
    {g : ParabolicPoint → ℝ≥0∞} {U S : Set ParabolicPoint}
    (_ : Measurable g) (_ : IsOpen U) (_ : S ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε)
    (hsmall : ∀ z ∈ S, ∀ n : ℕ, ∃ r : ℝ,
      0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
        parabolicCylinder z.1 z.2 r ⊆ U ∧
          (ε : ℝ≥0∞) * ENNReal.ofReal r <
            ∫⁻ y in parabolicCylinder z.1 z.2 r, g y)
    (_ : (∫⁻ y in U, g y) < ∞) :
    parabolicHausdorffMeasure 1 S ≤
      ((10 : ℝ≥0∞) / (ε : ℝ≥0∞)) * (∫⁻ y in U, g y) := by
  let radius : ℕ → S → ℝ := fun n z =>
    Classical.choose (hsmall z z.property n)
  have radius_spec (n : ℕ) (z : S) :
      0 < radius n z ∧ radius n z < 1 / ((n + 1 : ℕ) : ℝ) ∧
        parabolicCylinder z.1.1 z.1.2 (radius n z) ⊆ U ∧
          (ε : ℝ≥0∞) * ENNReal.ofReal (radius n z) <
            ∫⁻ y in parabolicCylinder z.1.1 z.1.2 (radius n z), g y := by
    exact Classical.choose_spec (hsmall z z.property n)
  let center : ℕ → S → ParabolicPoint := fun n z =>
    (z.1.1, z.1.2 - (radius n z) ^ 2 / 2)
  let ball : ℕ → S → Set ParabolicPoint := fun n z =>
    coveringParabolicMetricBall (center n z) (radius n z)
  have ball_mem (n : ℕ) (z : S) : z.1 ∈ ball n z := by
    have hzc : z.1 ∈ parabolicCylinder z.1.1 z.1.2 (radius n z) := by
      rcases z with ⟨⟨x, t⟩, hz⟩
      change vec3EuclideanNorm (x - x) < radius n ⟨(x, t), hz⟩ ∧
        t - (radius n ⟨(x, t), hz⟩) ^ 2 < t ∧ t ≤ t
      refine ⟨?_, ?_, le_rfl⟩
      · simpa [sub_self, vec3EuclideanNorm_zero] using
          (radius_spec n ⟨(x, t), hz⟩).1
      · exact sub_lt_self _ (sq_pos_of_pos (radius_spec n ⟨(x, t), hz⟩).1)
    simpa [ball, center] using
      (parabolicCylinder_subset_metricBall (radius_spec n z).1 hzc)
  have ball_nonempty (n : ℕ) (z : S) : (ball n z).Nonempty :=
    ⟨z.1, ball_mem n z⟩
  have radius_le_one (n : ℕ) (z : S) : radius n z ≤ 1 := by
    have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hfrac : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      have hden1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa only [one_mul] using hden1
    exact ((radius_spec n z).2.1.trans_le hfrac).le
  have vitali (n : ℕ) :
      ∃ u : Set S, u.PairwiseDisjoint (ball n) ∧
        ∀ a : S, ∃ b ∈ u,
          (ball n a ∩ ball n b).Nonempty ∧ radius n a ≤ 2 * radius n b := by
    obtain ⟨u, hu, hdisj, hcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement
        (fun z : S => ball n z) Set.univ (radius n) 2 (by norm_num)
        (fun a _ => (radius_spec n a).1.le) 1
        (fun a _ => radius_le_one n a) (fun a _ => ball_nonempty n a)
    exact ⟨u, hdisj, fun a => hcover a trivial⟩
  let selected : ℕ → Set S := fun n => Classical.choose (vitali n)
  have selected_spec (n : ℕ) :
      (selected n).PairwiseDisjoint (ball n) ∧
        ∀ a : S, ∃ b ∈ selected n,
          (ball n a ∩ ball n b).Nonempty ∧ radius n a ≤ 2 * radius n b := by
    exact Classical.choose_spec (vitali n)
  let index : ℕ → Type := fun n => {z : S // z ∈ selected n}
  have : ∀ n, Countable (index n) := by
    intro n
    dsimp [index]
    refine (selected_spec n).1.countable_of_isOpen ?_ ?_
    · intro z hz
      change IsOpen (coveringParabolicMetricBall (center n z) (radius n z))
      exact Metric.isOpen_ball
    · intro z hz
      simpa [ball] using ball_nonempty n z
  let cylinder : ∀ n, index n → Set ParabolicPoint := fun n i =>
    parabolicCylinder i.1.1.1 i.1.1.2 (radius n i.1)
  let enlarged : ∀ n, index n → Set ParabolicPoint := fun n i =>
    coveringParabolicMetricBall (center n i.1) (5 * radius n i.1)
  have cylinder_measurable (n : ℕ) (i : index n) :
      MeasurableSet (cylinder n i) := by
    exact measurableSet_parabolicCylinder _ _ _
  have cylinder_subset_ball (n : ℕ) (i : index n) :
      cylinder n i ⊆ ball n i.1 := by
    simpa [cylinder, ball, center] using
      (parabolicCylinder_subset_metricBall (radius_spec n i.1).1)
  have cylinder_disjoint (n : ℕ) {i j : index n} (hij : i ≠ j) :
      Disjoint (cylinder n i) (cylinder n j) := by
    apply Set.disjoint_of_subset (cylinder_subset_ball n i) (cylinder_subset_ball n j)
    apply (selected_spec n).1 i.property j.property
    intro hij'
    apply hij
    exact Subtype.ext hij'
  have cylinder_subset_U (n : ℕ) (i : index n) :
      cylinder n i ⊆ U := by
    exact (radius_spec n i.1).2.2.1
  have sum_integral_le (n : ℕ) :
      (∑' i : index n, ∫⁻ y in cylinder n i, g y) ≤ ∫⁻ y in U, g y := by
    calc
      (∑' i : index n, ∫⁻ y in cylinder n i, g y) =
          ∫⁻ y in ⋃ i : index n, cylinder n i, g y := by
        symm
        apply lintegral_iUnion
        · exact cylinder_measurable n
        · intro i j hij
          exact cylinder_disjoint n hij
      _ ≤ ∫⁻ y in U, g y := by
        apply lintegral_mono_set
        intro y hy
        rcases mem_iUnion.mp hy with ⟨i, hi⟩
        exact cylinder_subset_U n i hi
  have diameter_le (n : ℕ) (i : index n) :
      ediam (enlarged n i) ≤ (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) := by
    calc
      ediam (enlarged n i) ≤ ENNReal.ofReal (2 * (5 * radius n i.1)) := by
        exact parabolicMetricBall_ediam_le (center n i.1) (5 * radius n i.1)
      _ = (10 : ℝ≥0∞) * ENNReal.ofReal (radius n i.1) := by
        rw [show 2 * (5 * radius n i.1) = 10 * radius n i.1 by ring]
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  let K : ℝ≥0∞ := (10 : ℝ≥0∞) / (ε : ℝ≥0∞)
  have diameter_integral_le (n : ℕ) (i : index n) := @hausdorff_covering_diameter_integral_le_1 g
    U S ε hε radius radius_spec center vitali diameter_le n i
  have enlarged_contains (n : ℕ) (a : S) :
      a.1 ∈ ⋃ i : index n, enlarged n i := by
    obtain ⟨b, hb, hab, hrad⟩ := (selected_spec n).2 a
    have hdist : @dist ParabolicPoint
        (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) (center n a)
          (center n b) < radius n a + radius n b :=
      Metric.dist_lt_add_of_nonempty_ball_inter_ball hab
    have hsum : radius n a + @dist ParabolicPoint
        (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) (center n a)
          (center n b) < 5 * radius n b := by
      calc
        radius n a + @dist ParabolicPoint
            (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace)) (center n a)
              (center n b) < radius n a + (radius n a + radius n b) :=
        add_lt_add_right hdist _
        _ ≤ 5 * radius n b := by
          linarith only [hrad, (radius_spec n b).1]
    have hsubset : ball n a ⊆ enlarged n ⟨b, hb⟩ := by
      simpa only [ball, enlarged] using
        (Metric.ball_subset_ball' (le_of_lt hsum))
    refine mem_iUnion.2 ⟨⟨b, hb⟩, ?_⟩
    apply hsubset
    exact ball_mem n a
  have diameter_sum_le (n : ℕ) :
      (∑' i : index n, ediam (enlarged n i) ^ (1 : ℝ)) ≤
        K * (∫⁻ y in U, g y) := by
    calc
      (∑' i : index n, ediam (enlarged n i) ^ (1 : ℝ)) =
          ∑' i : index n, ediam (enlarged n i) := by
        simp only [ENNReal.rpow_one]
      _ ≤ ∑' i : index n, K * (∫⁻ y in cylinder n i, g y) :=
        ENNReal.tsum_le_tsum (fun i => diameter_integral_le n i)
      _ = K * (∑' i : index n, ∫⁻ y in cylinder n i, g y) :=
        ENNReal.tsum_mul_left
      _ ≤ K * (∫⁻ y in U, g y) :=
        mul_le_mul_of_nonneg_left (sum_integral_le n) bot_le
  have hausdorff_bound := @hausdorff_covering_hausdorff_bound_2 g U S ε radius radius_spec center
    vitali (by infer_instance) diameter_le K enlarged_contains diameter_sum_le
  rw [parabolicHausdorffMeasure]
  norm_num
  simpa [K] using hausdorff_bound

/-- Volume coefficient for the parabolic covering estimates. -/
noncomputable def parabolicVolumeConstant : ℝ≥0∞ :=
  ENNReal.ofReal ((4 : ℝ) ^ 5) * volume (parabolicCylinder 0 0 1)

private lemma volume_cylinder_unit_time (x : Vec3) (t : ℝ) :
    volume (parabolicCylinder x t 1) = volume (parabolicCylinder 0 0 1) := by
  rw [volume_parabolicCylinder_zero, volume_parabolicCylinder_zero, volume_vec3Ball]

private lemma parabolicVolumeConstant_ne_zero : parabolicVolumeConstant ≠ 0 := by
  rw [parabolicVolumeConstant]
  exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
    (ne_of_gt (Integration.volume_parabolicCylinder_pos (by norm_num)))

private lemma parabolicVolumeConstant_ne_top : parabolicVolumeConstant ≠ ∞ := by
  rw [parabolicVolumeConstant]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_of_lt Integration.volume_parabolicCylinder_lt_top)

private lemma volume_singleton_parabolic (x : ParabolicPoint) :
    volume ({x} : Set ParabolicPoint) = 0 := by
  rcases x with ⟨x, t⟩
  rw [Integration.volume_parabolicPoint_eq_prod]
  change (volume.prod volume) ({(x, t)} : Set (Vec3 × ℝ)) = 0
  rw [show ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} by simp]
  rw [Measure.prod_prod]
  simp

private lemma volume_closedBall_le_parabolicVolumeConstant_mul {z : ParabolicPoint}
    {r : ℝ} (hr : 0 < r) :
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) ≤
      parabolicVolumeConstant * ENNReal.ofReal (r ^ 5) := by
  have hsubset := closedBall_subset_parabolicCylinder (x := z.1) (t := z.2) hr
  have hscale := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := z.2 + 8 * r ^ 2) (r := 1) (a := 4 * r) (by positivity)
  calc
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) ≤
        volume (parabolicCylinder z.1 (z.2 + 8 * r ^ 2) (4 * r)) :=
      measure_mono hsubset
    _ = ENNReal.ofReal ((4 * r) ^ 5) *
        volume (parabolicCylinder z.1 (z.2 + 8 * r ^ 2) 1) := by
      simpa using hscale
    _ = ENNReal.ofReal ((4 * r) ^ 5) * volume (parabolicCylinder 0 0 1) := by
      rw [volume_cylinder_unit_time]
    _ = parabolicVolumeConstant * ENNReal.ofReal (r ^ 5) := by
      rw [show (4 * r) ^ 5 = (4 : ℝ) ^ 5 * r ^ 5 by ring]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ 5)]
      simp only [parabolicVolumeConstant]
      ac_rfl

private lemma volume_le_parabolicVolumeConstant_mul_ediam (s : Set ParabolicPoint) :
    volume s ≤ parabolicVolumeConstant * ediam s ^ (5 : ℝ) := by
  by_cases hs : s.Nonempty
  · let x : ParabolicPoint := Classical.choose hs
    have hx : x ∈ s := Classical.choose_spec hs
    by_cases htop : ediam s = ∞
    · calc
        volume s ≤ ∞ := le_top
        _ = parabolicVolumeConstant * ∞ :=
          (ENNReal.mul_top parabolicVolumeConstant_ne_zero).symm
        _ = parabolicVolumeConstant * ediam s ^ (5 : ℝ) := by simp [htop]
    let R : ℝ := (ediam s).toReal
    have hR : 0 ≤ R := ENNReal.toReal_nonneg
    have hdiam : s ⊆
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace x R := by
      intro y hy
      rw [Metric.mem_closedBall]
      have hdist := Metric.edist_le_ediam_of_mem hy hx
      rw [edist_dist] at hdist
      have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).2 hdist
      simpa [R, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist y x)] using hreal
    by_cases hR0 : R = 0
    · have hs_singleton : s ⊆ ({x} : Set ParabolicPoint) := by
        intro y hy
        have hyball := hdiam hy
        rw [Metric.mem_closedBall, hR0] at hyball
        have hyx : y = x := dist_eq_zero.mp (le_antisymm hyball (dist_nonneg))
        simp [hyx]
      calc
        volume s ≤ volume ({x} : Set ParabolicPoint) := measure_mono hs_singleton
        _ = 0 := volume_singleton_parabolic x
        _ ≤ parabolicVolumeConstant * ediam s ^ (5 : ℝ) := bot_le
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      have hball := volume_closedBall_le_parabolicVolumeConstant_mul (z := x) hRpos
      calc
        volume s ≤ volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace x R) :=
          measure_mono hdiam
        _ ≤ parabolicVolumeConstant * ENNReal.ofReal (R ^ 5) := hball
        _ = parabolicVolumeConstant * ediam s ^ (5 : ℝ) := by
          rw [← ENNReal.ofReal_toReal htop]
          simp [R]
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp

theorem parabolicHausdorffMeasure_one_lt_top_imp_volume_zero {E : Set ParabolicPoint}
    (hE : parabolicHausdorffMeasure 1 E < ∞) : volume E = 0 := by
  have hE' : MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) E < ∞ := by
    simpa [parabolicHausdorffMeasure] using hE
  have hH5 : MeasureTheory.Measure.hausdorffMeasure (5 : ℝ) E = 0 := by
    rcases MeasureTheory.Measure.hausdorffMeasure_zero_or_top
        (by norm_num : (1 : ℝ) < 5) E with h | h
    · exact h
    · exact False.elim (ne_of_lt hE' h)
  let μ : Measure ParabolicPoint := parabolicVolumeConstant⁻¹ • volume
  have hμ : μ ≤ MeasureTheory.Measure.hausdorffMeasure (5 : ℝ) := by
    refine MeasureTheory.Measure.le_hausdorffMeasure 5 μ ∞ ENNReal.coe_lt_top ?_
    intro s hsdiam
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      parabolicVolumeConstant⁻¹ * volume s ≤
          parabolicVolumeConstant⁻¹ *
            (parabolicVolumeConstant * ediam s ^ (5 : ℝ)) := by
        gcongr
        exact volume_le_parabolicVolumeConstant_mul_ediam s
      _ = ediam s ^ (5 : ℝ) := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel parabolicVolumeConstant_ne_zero
            parabolicVolumeConstant_ne_top, one_mul]
  have hzero := hμ E
  rw [hH5] at hzero
  have hzero' : parabolicVolumeConstant⁻¹ * volume E = 0 := by
    simpa [μ] using hzero
  have hinv : parabolicVolumeConstant⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr parabolicVolumeConstant_ne_top
  exact (mul_eq_zero.mp hzero').resolve_left hinv

private lemma parabolicCylinder_subset_metricBall_same_center {z : ParabolicPoint}
    {r : ℝ} (hr : 0 < r) :
    parabolicCylinder z.1 z.2 r ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r := by
  intro p hp
  rcases z with ⟨x, t⟩
  rcases p with ⟨y, s⟩
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      (y, s) ((x, t) : ParabolicPoint) < r
  have hdist : @dist ParabolicPoint
      (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      (y, s) ((x, t) : ParabolicPoint) = parabolicDist (y, s) (x, t) := by
    exact dist_eq_parabolicDist (y, s) (x, t)
  rw [hdist]
  change parabolicDist (y, s) (x, t) < r at *
  change (y, s) ∈ parabolicCylinder x t r at hp
  rw [mem_parabolicCylinder] at hp
  refine max_lt hp.1 ?_
  apply (Real.sqrt_lt' hr).2
  apply (abs_lt).2
  constructor
  · linarith only [hp.2.1]
  · linarith only [hp.2.2, sq_pos_of_pos hr]

theorem parabolicHausdorffMeasure_one_eq_zero_of_small_cylinders
    {g : ParabolicPoint → ℝ≥0∞} (hg : Measurable g) {U S : Set ParabolicPoint}
    (hU : IsOpen U) (hSU : S ⊆ U) {ε : ℝ≥0} (hε : 0 < ε)
    (hsmall : ∀ z ∈ S, ∀ n : ℕ, ∃ r : ℝ,
      0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
        parabolicCylinder z.1 z.2 r ⊆ U ∧
          (ε : ℝ≥0∞) * ENNReal.ofReal r <
            ∫⁻ y in parabolicCylinder z.1 z.2 r, g y)
    (hfin : (∫⁻ y, g y) < ∞) :
    parabolicHausdorffMeasure 1 S = 0 := by
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  have hεtop : (ε : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  let K : ℝ≥0∞ := (10 : ℝ≥0∞) / (ε : ℝ≥0∞)
  have hK0 : K ≠ 0 := by
    dsimp [K]
    exact ENNReal.div_ne_zero.mpr ⟨by norm_num, hεtop⟩
  have hKtop : K < ∞ := by
    dsimp [K]
    exact ENNReal.div_lt_top (by norm_num) hε0
  have hfinU : (∫⁻ y in U, g y) < ∞ :=
    (setLIntegral_le_lintegral U g).trans_lt hfin
  have hbound := parabolicHausdorffMeasure_one_le_integral_of_small_cylinders
    hg hU hSU hε hsmall hfinU
  have hfiniteH : parabolicHausdorffMeasure 1 S < ∞ := by
    calc
      parabolicHausdorffMeasure 1 S ≤ K * (∫⁻ y in U, g y) := by
        simpa [K] using hbound
      _ < ∞ := ENNReal.mul_lt_top hKtop hfinU
  have hS : volume S = 0 :=
    parabolicHausdorffMeasure_one_lt_top_imp_volume_zero hfiniteH
  have hsmall_integral (η : ℝ≥0∞) (hη : 0 < η) (hηtop : η ≠ ∞) :
      ∃ V : Set ParabolicPoint, S ⊆ V ∧ IsOpen V ∧
        (∫⁻ y in V, g y) < η / K := by
    obtain ⟨δ, hδ, hδint⟩ :=
      exists_pos_setLIntegral_lt_of_measure_lt (μ := volume) (f := g)
        (ne_of_lt hfin) (ENNReal.div_ne_zero.mpr ⟨hη.ne', hKtop.ne⟩)
    obtain ⟨V, hSV, hVopen, hVvol⟩ :=
      Set.exists_isOpen_lt_of_lt (μ := volume) S δ (by simpa [hS] using hδ)
    exact ⟨V, hSV, hVopen, hδint V hVvol⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro η hη
    by_cases hηtop : η = ∞
    · simp [hηtop]
    obtain ⟨V, hSV, hVopen, hVint⟩ := hsmall_integral η hη hηtop
    let W : Set ParabolicPoint := V ∩ U
    have hWopen : IsOpen W := hVopen.inter hU
    have hSW : S ⊆ W := by
      intro z hz
      exact ⟨hSV hz, hSU hz⟩
    have hsmallW : ∀ z ∈ S, ∀ n : ℕ, ∃ r : ℝ,
        0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
          parabolicCylinder z.1 z.2 r ⊆ W ∧
            (ε : ℝ≥0∞) * ENNReal.ofReal r <
              ∫⁻ y in parabolicCylinder z.1 z.2 r, g y := by
      intro z hz n
      obtain ⟨ρ, hρ, hballV⟩ :=
        Metric.mem_nhds_iff.mp (hVopen.mem_nhds (hSV hz))
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ρ)
      let m : ℕ := max n N
      have hdenNnat : N ≤ m + 1 := by
        dsimp [m]
        exact Nat.le_succ_of_le (Nat.le_max_right n N)
      have hdenN : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdenNnat
      have hprodN : 1 < ρ * (N : ℝ) := by
        have h := (div_lt_iff₀ hρ).mp hN
        simpa [mul_comm] using h
      have hprod : 1 < ρ * ((m + 1 : ℕ) : ℝ) := by
        calc
          1 < ρ * (N : ℝ) := hprodN
          _ ≤ ρ * ((m + 1 : ℕ) : ℝ) := by gcongr
      have hsmallradius : 1 / ((m + 1 : ℕ) : ℝ) < ρ := by
        apply (div_lt_iff₀ (by positivity)).2
        simpa [mul_comm] using hprod
      have hdennat : n + 1 ≤ m + 1 := by
        dsimp [m]
        exact Nat.succ_le_succ (Nat.le_max_left n N)
      have hden : ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdennat
      have hfrac : 1 / ((m + 1 : ℕ) : ℝ) ≤
          1 / ((n + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (by positivity) hden
      obtain ⟨r, hr, hrm, hcylU, henergy⟩ := hsmall z hz m
      refine ⟨r, hr, hrm.trans_le hfrac, ?_, henergy⟩
      refine subset_inter ?_ hcylU
      have hrr : r < ρ := hrm.trans hsmallradius
      exact (parabolicCylinder_subset_metricBall_same_center hr).trans
        ((Metric.ball_subset_ball hrr.le).trans hballV)
    have hWint : (∫⁻ y in W, g y) < η / K := by
      change (∫⁻ y in V ∩ U, g y) < η / K
      exact (lintegral_mono_set inter_subset_left).trans_lt hVint
    have hfinW : (∫⁻ y in W, g y) < ∞ :=
      hWint.trans (ENNReal.div_lt_top hηtop hK0)
    have hboundW := parabolicHausdorffMeasure_one_le_integral_of_small_cylinders
      hg hWopen hSW hε hsmallW hfinW
    have hboundW' : parabolicHausdorffMeasure 1 S ≤
        K * (∫⁻ y in W, g y) := by
      simpa [K] using hboundW
    have hprodW : K * (∫⁻ y in W, g y) < η := by
      calc
        K * (∫⁻ y in W, g y) < K * (η / K) :=
          ENNReal.mul_lt_mul_right hK0 hKtop.ne hWint
        _ = η := ENNReal.mul_div_cancel hK0 hKtop.ne
    simpa only [zero_add] using hboundW'.trans hprodW.le
  · exact bot_le

end CKN.Foundation.Parabolic
