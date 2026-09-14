/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.DensityPoint
public import LeanPool.Besicovitch.Rectifiability.Straight
public import LeanPool.Besicovitch.Measure.DensityBasic

/-!
# Localizing lower density to a straight subset

At almost every point of a measurable subset, the complementary restriction is negligible
relative to the restricted measure.  Straightness turns this relative differentiation statement
into preservation of every strictly smaller lower-density bound.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- An eventual lower ball-mass bound gives the corresponding lower-density bound. -/
theorem le_lowerOneDensity_of_eventually_ball_measure_ge
    {s : Set (EuclideanSpace ℝ (Fin 2))} {x : (EuclideanSpace ℝ (Fin 2))}
    {beta scale : ℝ} (hbeta : 0 ≤ beta) (hscale : 0 < scale)
    (hmass : ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * beta * r) ≤ μH[1] (s ∩ Metric.ball x r)) :
    ENNReal.ofReal beta ≤ lowerOneDensity s x := by
  rw [lowerOneDensity]
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards [Ioc_mem_nhdsGT (half_pos hscale)] with r hr
  have hr_scale : r < scale := hr.2.trans_lt (half_lt_self hscale)
  have hden_pos : ENNReal.ofReal (2 * r) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos (by norm_num) hr.1)).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden_pos) (Or.inl ENNReal.ofReal_ne_top)]
  calc
    ENNReal.ofReal beta * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal (2 * beta * r) := by
      rw [← ENNReal.ofReal_mul hbeta]
      congr 1
      ring
    _ ≤ μH[1] (s ∩ Metric.ball x r) := hmass r hr.1 hr_scale

/-- A straight measurable subset inherits every strictly smaller lower-density threshold almost
everywhere from a finite measurable ambient set. -/
theorem ae_lt_lowerOneDensity_of_subset_of_straight
    {e a : Set (EuclideanSpace ℝ (Fin 2))} (ha : MeasurableSet a) (hae : a ⊆ e)
    (he_fin : μH[1] e < ∞) (ha_straight : IsStraightMeasure (μH[1].restrict a))
    {beta gamma : ℝ} (hbeta : 0 ≤ beta) (hbeta_gamma : beta < gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict a,
      ENNReal.ofReal gamma ≤ lowerOneDensity e x) :
    ∀ᵐ x ∂μH[1].restrict a,
      ENNReal.ofReal beta < lowerOneDensity a x := by
  let mu : Measure (EuclideanSpace ℝ (Fin 2)) := μH[1].restrict a
  let nu : Measure (EuclideanSpace ℝ (Fin 2)) := μH[1].restrict (e \ a)
  have hmu_fin : mu Set.univ < ∞ := by
    simpa only [mu, Measure.restrict_apply_univ] using
      (measure_mono hae).trans_lt he_fin
  have hnu_fin : nu Set.univ < ∞ := by
    simpa only [nu, Measure.restrict_apply_univ] using
      (measure_mono sdiff_subset).trans_lt he_fin
  letI : IsFiniteMeasure mu := ⟨hmu_fin⟩
  letI : IsFiniteMeasure nu := ⟨hnu_fin⟩
  have hsingular : nu ⟂ₘ mu := by
    refine Measure.MutuallySingular.mk (s := a) (t := aᶜ) ?_ ?_ (by simp)
    · simp [nu, Measure.restrict_apply ha]
    · simp [mu, Measure.restrict_apply ha.compl]
  have hderiv_zero : nu.rnDeriv mu =ᵐ[mu] 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular hsingular
      Measure.AbsolutelyContinuous.rfl
  have hratio := _root_.Besicovitch.ae_tendsto_rnDeriv nu mu
  change ∀ᵐ x ∂mu, ENNReal.ofReal beta < lowerOneDensity a x
  have hdensity_mu : ∀ᵐ x ∂mu,
      ENNReal.ofReal gamma ≤ lowerOneDensity e x := hdensity
  filter_upwards [hratio, hderiv_zero, hdensity_mu] with x hxratio hxzero hxe
  have hxratio_zero : Tendsto
      (fun r ↦ nu (Metric.closedBall x r) / mu (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
    have hxzero' : nu.rnDeriv mu x = 0 := by simpa using hxzero
    simpa only [hxzero'] using hxratio
  let theta := (beta + gamma) / 2
  let eta := (beta + theta) / 2
  let epsilon := theta - eta
  have hbeta_theta : beta < theta := by
    dsimp only [theta]
    linarith
  have htheta_gamma : theta < gamma := by
    dsimp only [theta]
    linarith
  have hbeta_eta : beta < eta := by
    dsimp only [eta]
    linarith
  have heta_theta : eta < theta := by
    dsimp only [eta]
    linarith
  have htheta_nonneg : 0 ≤ theta := hbeta.trans hbeta_theta.le
  have heta_nonneg : 0 ≤ eta := hbeta.trans hbeta_eta.le
  have hepsilon_pos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have htheta_density : ENNReal.ofReal theta < lowerOneDensity e x :=
    ((ENNReal.ofReal_lt_ofReal_iff (hbeta.trans_lt hbeta_gamma)).2 htheta_gamma).trans_le hxe
  obtain ⟨densityScale, hdensityScale, hmass_e⟩ :=
    lowerOneDensity_eventually_ball_measure_gt htheta_nonneg htheta_density
  have hratio_eventually : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      nu (Metric.closedBall x r) / mu (Metric.closedBall x r) <
        ENNReal.ofReal epsilon :=
    hxratio_zero.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon_pos))
  obtain ⟨neighborhood, hneighborhood, hratio_on⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hratio_eventually
  obtain ⟨ratioScale, hratioScale, hball_ratio⟩ :=
    Metric.mem_nhds_iff.mp hneighborhood
  have hmass_a : ∀ r : ℝ, 0 < r → r < min densityScale ratioScale →
      ENNReal.ofReal (2 * eta * r) < μH[1] (a ∩ Metric.ball x r) := by
    intro r hr hrscale
    have hr_density : r < densityScale := hrscale.trans_le (min_le_left _ _)
    have hr_ratio : r < ratioScale := hrscale.trans_le (min_le_right _ _)
    have hr_mem : r ∈ neighborhood ∩ Ioi (0 : ℝ) := by
      refine ⟨hball_ratio ?_, hr⟩
      simpa [Real.dist_eq, abs_of_pos hr] using hr_ratio
    have hratio_le : nu (Metric.closedBall x r) ≤
        ENNReal.ofReal epsilon * mu (Metric.closedBall x r) := by
      apply (ENNReal.div_le_iff_le_mul
        (Or.inr ENNReal.ofReal_ne_top)
        (Or.inr (ENNReal.ofReal_pos.2 hepsilon_pos).ne')).mp
      exact (hratio_on hr_mem).le
    have hnu_le : nu (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * epsilon * r) := by
      calc
        nu (Metric.closedBall x r) ≤
            ENNReal.ofReal epsilon * mu (Metric.closedBall x r) := hratio_le
        _ ≤ ENNReal.ofReal epsilon * ENNReal.ofReal (2 * r) := by
          gcongr
          exact ha_straight.measure_closedBall_le x r
        _ = ENNReal.ofReal (2 * epsilon * r) := by
          rw [← ENNReal.ofReal_mul hepsilon_pos.le]
          congr 1
          ring
    have he_subset : e ∩ Metric.ball x r ⊆
        (a ∩ Metric.ball x r) ∪ ((e \ a) ∩ Metric.closedBall x r) := by
      intro y hy
      by_cases hya : y ∈ a
      · exact Or.inl ⟨hya, hy.2⟩
      · exact Or.inr ⟨⟨hy.1, hya⟩, Metric.ball_subset_closedBall hy.2⟩
    have he_measure : μH[1] (e ∩ Metric.ball x r) ≤
        μH[1] (a ∩ Metric.ball x r) + nu (Metric.closedBall x r) := by
      calc
        μH[1] (e ∩ Metric.ball x r) ≤
            μH[1] ((a ∩ Metric.ball x r) ∪
              ((e \ a) ∩ Metric.closedBall x r)) := measure_mono he_subset
        _ ≤ μH[1] (a ∩ Metric.ball x r) +
            μH[1] ((e \ a) ∩ Metric.closedBall x r) := measure_union_le _ _
        _ = μH[1] (a ∩ Metric.ball x r) + nu (Metric.closedBall x r) := by
          change μH[1] (a ∩ Metric.ball x r) +
              μH[1] ((e \ a) ∩ Metric.closedBall x r) =
            μH[1] (a ∩ Metric.ball x r) +
              (μH[1].restrict (e \ a)) (Metric.closedBall x r)
          rw [Measure.restrict_apply measurableSet_closedBall]
          congr 1
          exact congrArg μH[1] (inter_comm _ _)
    by_contra hnot
    have ha_upper : μH[1] (a ∩ Metric.ball x r) ≤
        ENNReal.ofReal (2 * eta * r) := le_of_not_gt hnot
    have he_upper : μH[1] (e ∩ Metric.ball x r) ≤
        ENNReal.ofReal (2 * theta * r) := by
      calc
        μH[1] (e ∩ Metric.ball x r) ≤
            μH[1] (a ∩ Metric.ball x r) + nu (Metric.closedBall x r) := he_measure
        _ ≤ ENNReal.ofReal (2 * eta * r) + ENNReal.ofReal (2 * epsilon * r) :=
          add_le_add ha_upper hnu_le
        _ = ENNReal.ofReal (2 * theta * r) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp only [epsilon]
          ring
    exact (not_le_of_gt (hmass_e r hr hr_density)) he_upper
  have hscale : 0 < min densityScale ratioScale := lt_min hdensityScale hratioScale
  exact ((ENNReal.ofReal_lt_ofReal_iff (hbeta.trans_lt hbeta_eta)).2 hbeta_eta).trans_le
    (le_lowerOneDensity_of_eventually_ball_measure_ge heta_nonneg hscale fun r hr hrs ↦
      (hmass_a r hr hrs).le)

end LeanPool.Besicovitch
