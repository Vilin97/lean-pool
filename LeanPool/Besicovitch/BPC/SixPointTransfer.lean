/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Extraction
public import LeanPool.Besicovitch.BPC.PackingMeasure
public import LeanPool.Besicovitch.BPC.Parameters
public import LeanPool.Besicovitch.BPC.RootBalls
public import LeanPool.Besicovitch.SixPoint.FiniteProperty
public import LeanPool.Besicovitch.SixPoint.Normalization
public import LeanPool.Besicovitch.SixPoint.Realization
public import LeanPool.Besicovitch.SixPoint.Scaling

/-!
# From the six-point property to the Besicovitch pair condition

This file turns a finite two-color packing theorem into the Besicovitch pair condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LeanPool.Besicovitch

private theorem SixPointConfiguration.dist_root_le_one {configuration : SixPointConfiguration}
    {s : ℝ} (h : configuration.IsAdmissibleAt s) (color : SixPointColor)
    (label : SixPointLabel) :
    dist (configuration color .root) (configuration color label) ≤ 1 := by
  cases label
  · simp
  · exact h.child_distance color .left (by simp)
  · exact h.child_distance color .right (by simp)

private theorem SixPointConfiguration.dist_roots_le_one
    {configuration : SixPointConfiguration} {s : ℝ} (h : configuration.IsAdmissibleAt s)
    (color₁ color₂ : SixPointColor) :
    dist (configuration color₁ .root) (configuration color₂ .root) ≤ 1 := by
  cases color₁ <;> cases color₂
  · simp
  · exact h.root_distance.le
  · simpa [dist_comm] using h.root_distance.le
  · simp

private theorem SixPointConfiguration.dist_le_three
    {configuration : SixPointConfiguration} {s : ℝ} (h : configuration.IsAdmissibleAt s)
    (color₁ color₂ : SixPointColor) (label₁ label₂ : SixPointLabel) :
    dist (configuration color₁ label₁) (configuration color₂ label₂) ≤ 3 := by
  calc
    _ ≤ dist (configuration color₁ label₁) (configuration color₁ .root) +
          dist (configuration color₁ .root) (configuration color₂ .root) +
            dist (configuration color₂ .root) (configuration color₂ label₂) :=
      dist_triangle4 _ _ _ _
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · simpa [dist_comm] using
          SixPointConfiguration.dist_root_le_one h color₁ label₁
      · exact SixPointConfiguration.dist_roots_le_one h color₁ color₂
      · exact SixPointConfiguration.dist_root_le_one h color₂ label₂
    _ = 3 := by norm_num

private theorem SixPointPacking.virtualDiameter_le_five
    {configuration : SixPointConfiguration} {s : ℝ} (packing : SixPointPacking configuration)
    (h : configuration.IsAdmissibleAt s) : packing.virtualDiameter ≤ 5 := by
  unfold SixPointPacking.virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  calc
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j ≤ 3 + 1 + 1 := by
      gcongr
      · exact SixPointConfiguration.dist_le_three h i.1.1 j.1.1 i.1.2 j.1.2
      · exact (packing.radius i).property.2
      · exact (packing.radius j).property.2
    _ = 5 := by norm_num

private theorem root_leakage_real_bound {beta gamma q d length tau : ℝ} (hq : 0 < q)
    (hq_one : q < 1) (hgamma : gamma < beta) (hd : 0 < d) (hd_length : d ≤ length)
    (hlength : length < d / q) (htau_le : tau ≤ (beta - gamma) * q / 4) :
    tau * (length + 2 * d) ≤ 2 * (beta - gamma) * d := by
  have hgap : 0 < beta - gamma := sub_pos.mpr hgamma
  have hlength_pos : 0 < length := hd.trans_le hd_length
  have hq_length : q * length < d := by
    nlinarith [(lt_div_iff₀ hq).1 hlength]
  have htau_length : tau * length ≤ ((beta - gamma) * q / 4) * length :=
    mul_le_mul_of_nonneg_right htau_le hlength_pos.le
  have hscaled_length : ((beta - gamma) * q / 4) * length <
      (beta - gamma) * d / 4 := by
    nlinarith [mul_lt_mul_of_pos_left hq_length hgap]
  have htau_gap : tau < (beta - gamma) / 4 := by
    calc
      tau ≤ (beta - gamma) * q / 4 := htau_le
      _ < (beta - gamma) / 4 := by nlinarith [mul_lt_mul_of_pos_left hq_one hgap]
  have htau_d : tau * d < (beta - gamma) * d / 4 :=
    lt_of_lt_of_eq (mul_lt_mul_of_pos_right htau_gap hd) (by ring)
  nlinarith

private theorem measure_rootBallUnion_sdiff_le
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {outside : Set (EuclideanSpace ℝ (Fin 2))}
    {x y : (EuclideanSpace ℝ (Fin 2))} {beta gamma q d length tau : ℝ}
    (hq : 0 < q) (hq_one : q < 1)
    (hgamma : gamma < beta) (hd : 0 < d) (hd_length : d ≤ length)
    (hlength_eq : dist x y = length) (hlength : length < d / q)
    (htau : 0 < tau) (htau_le : tau ≤ (beta - gamma) * q / 4)
    (hnot : ¬ENNReal.ofReal tau * Metric.ediam (rootBallUnion x y d) <
      mu (rootBallUnion x y d \ outside)) :
    mu (rootBallUnion x y d \ outside) ≤ ENNReal.ofReal (2 * (beta - gamma) * d) := by
  calc
    _ ≤ ENNReal.ofReal tau * Metric.ediam (rootBallUnion x y d) := le_of_not_gt hnot
    _ ≤ ENNReal.ofReal tau * ENNReal.ofReal (length + 2 * d) := by
      gcongr
      simpa only [hlength_eq] using ediam_rootBallUnion_le x y d
    _ = ENNReal.ofReal (tau * (length + 2 * d)) := by rw [ENNReal.ofReal_mul htau.le]
    _ ≤ _ := ENNReal.ofReal_le_ofReal <|
      root_leakage_real_bound hq hq_one hgamma hd hd_length hlength htau_le

private theorem exists_approximate_roots {e₁ e₂ : Set (EuclideanSpace ℝ (Fin 2))} {d q : ℝ}
    (he₁ : e₁.Nonempty) (he₂ : e₂.Nonempty) (hd : 0 < d) (hq : 0 < q)
    (hq_one : q < 1) (hd_set : d = (setEDist e₁ e₂).toReal) :
    ∃ x ∈ e₁, ∃ y ∈ e₂, d ≤ dist x y ∧ dist x y < d / q := by
  have hd_div : (setEDist e₁ e₂).toReal < d / q := by
    rw [← hd_set]
    apply (lt_div_iff₀ hq).2
    nlinarith
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_dist_lt_of_setEDist_toReal_lt he₁ he₂ hd_div
  exact ⟨x, hx, y, hy, hd_set.trans_le (setEDist_toReal_le_dist he₁ he₂ hx hy), hxy⟩

private theorem score_gap_lt {total diameter beta margin : ℝ} (hbeta : 0 < beta)
    (hscore : margin < total - diameter / (2 * beta)) :
    diameter + 2 * beta * margin < 2 * beta * total := by
  have hmul := mul_lt_mul_of_pos_left hscore (show 0 < 2 * beta by positivity)
  field_simp at hmul
  nlinarith

private theorem leakage_factor_lt_of_score {total diameter beta margin tau : ℝ}
    (hbeta : 0 < beta) (htau : 0 ≤ tau) (htau_le : tau ≤ beta * margin / 10)
    (hdiameter : diameter ≤ 5)
    (hscore : margin < total - diameter / (2 * beta)) :
    (1 + tau) * diameter < 2 * beta * total := by
  have htau_diameter : tau * diameter ≤ tau * 5 :=
    mul_le_mul_of_nonneg_left hdiameter htau
  have htau_five : tau * 5 ≤ beta * margin / 2 := by nlinarith
  have hgap := score_gap_lt hbeta hscore
  nlinarith

private theorem configuration_of_children {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    (root : SixPointColor → (EuclideanSpace ℝ (Fin 2))) {d gamma : ℝ}
    {redLeft redRight blueLeft blueRight : (EuclideanSpace ℝ (Fin 2))}
    (hroot : ∀ color, root color ∈ e color)
    (hredLeft : redLeft ∈ e .red ∩ Metric.ball (root .red) d)
    (hredRight : redRight ∈ e .red ∩ Metric.ball (root .red) d)
    (hblueLeft : blueLeft ∈ e .blue ∩ Metric.ball (root .blue) d)
    (hblueRight : blueRight ∈ e .blue ∩ Metric.ball (root .blue) d)
    (hredSibling : 2 * gamma * d < dist redLeft redRight)
    (hblueSibling : 2 * gamma * d < dist blueLeft blueRight) :
    ∃ configuration : SixPointConfiguration,
      configuration .red .root = root .red ∧ configuration .blue .root = root .blue ∧
        (∀ color label, configuration color label ∈ e color) ∧
        (∀ color label, label ≠ .root →
          dist (configuration color .root) (configuration color label) ≤ d) ∧
        ∀ color, 2 * gamma * d <
          dist (configuration color .left) (configuration color .right) := by
  let configuration := SixPointConfiguration.ofPoints (root .red) redLeft redRight
    (root .blue) blueLeft blueRight
  refine ⟨configuration, rfl, rfl, ?_, ?_, ?_⟩
  · intro color label
    cases color <;> cases label <;> simp_all [configuration, SixPointConfiguration.ofPoints]
  · intro color label hlabel
    cases color <;> cases label
    · exact (hlabel rfl).elim
    · simpa [configuration, SixPointConfiguration.ofPoints, dist_comm] using
        (Metric.mem_ball.mp hredLeft.2).le
    · simpa [configuration, SixPointConfiguration.ofPoints, dist_comm] using
        (Metric.mem_ball.mp hredRight.2).le
    · exact (hlabel rfl).elim
    · simpa [configuration, SixPointConfiguration.ofPoints, dist_comm] using
        (Metric.mem_ball.mp hblueLeft.2).le
    · simpa [configuration, SixPointConfiguration.ofPoints, dist_comm] using
        (Metric.mem_ball.mp hblueRight.2).le
  · intro color
    cases color
    · exact hredSibling
    · exact hblueSibling

private theorem exists_physical_configuration
    {mu : Measure (EuclideanSpace ℝ (Fin 2))} (hmu : IsStraightMeasure mu)
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    (hmeasurable : ∀ color, MeasurableSet (e color))
    (hnonempty : ∀ color, (e color).Nonempty) {beta gamma d : ℝ} (hd : 0 < d)
    (hgamma_pos : 0 < gamma) (hgamma : gamma < beta)
    (hdistance : d = (setEDist (e .red) (e .blue)).toReal)
    (root : SixPointColor → (EuclideanSpace ℝ (Fin 2)))
    (hroot : ∀ color, root color ∈ e color)
    (hdensity : ∀ color,
      ENNReal.ofReal (2 * beta * d) < mu (Metric.ball (root color) d))
    (hleakage : mu (rootBallUnion (root .red) (root .blue) d \ (e .red ∪ e .blue)) ≤
      ENNReal.ofReal (2 * (beta - gamma) * d)) :
    ∃ configuration : SixPointConfiguration,
      configuration .red .root = root .red ∧ configuration .blue .root = root .blue ∧
        (∀ color label, configuration color label ∈ e color) ∧
        (∀ color label, label ≠ .root →
          dist (configuration color .root) (configuration color label) ≤ d) ∧
        ∀ color, 2 * gamma * d <
          dist (configuration color .left) (configuration color .right) := by
  have ha : 0 ≤ 2 * gamma * d := by positivity
  have hb : 0 ≤ 2 * (beta - gamma) * d := by positivity
  have red_disjoint : Disjoint (Metric.ball (root .red) d) (e .blue) := by
    apply ball_disjoint_of_le_setEDist_toReal (hnonempty .red) (hnonempty .blue) (hroot .red)
    rw [← hdistance]
  have blue_disjoint : Disjoint (Metric.ball (root .blue) d) (e .red) := by
    apply ball_disjoint_of_le_setEDist_toReal (hnonempty .blue) (hnonempty .red) (hroot .blue)
    rw [setEDist_comm, ← hdistance]
  have red_mass : ENNReal.ofReal (2 * gamma * d) <
      mu (e .red ∩ Metric.ball (root .red) d) := by
    apply measure_inter_gt_of_ball_gt_of_leakage mu (e := e .red) (other := e .blue)
      (ball := Metric.ball (root .red) d)
      (ambient := rootBallUnion (root .red) (root .blue) d) ha hb subset_union_left red_disjoint
    · simpa only [show 2 * gamma * d + 2 * (beta - gamma) * d = 2 * beta * d by ring]
        using hdensity .red
    · exact hleakage
  have blue_mass : ENNReal.ofReal (2 * gamma * d) <
      mu (e .blue ∩ Metric.ball (root .blue) d) := by
    apply measure_inter_gt_of_ball_gt_of_leakage mu (e := e .blue) (other := e .red)
      (ball := Metric.ball (root .blue) d)
      (ambient := rootBallUnion (root .red) (root .blue) d) ha hb subset_union_right blue_disjoint
    · simpa only [show 2 * gamma * d + 2 * (beta - gamma) * d = 2 * beta * d by ring]
        using hdensity .blue
    · simpa [union_comm] using hleakage
  obtain ⟨redLeft, hredLeft, redRight, hredRight, hredSibling⟩ :=
    hmu.exists_children (hmeasurable .red) red_mass
  obtain ⟨blueLeft, hblueLeft, blueRight, hblueRight, hblueSibling⟩ :=
    hmu.exists_children (hmeasurable .blue) blue_mass
  exact configuration_of_children root hroot hredLeft hredRight hblueLeft hblueRight
    hredSibling hblueSibling

private theorem exists_uniform_positive_packing {configuration : SixPointConfiguration}
    {s beta q₀ q : ℝ} (hfinite : SixPointFiniteProperty s) (hs : 0 < s)
    (hbeta : 0 < beta) (hq₀ : 0 < q₀) (hq₀q : q₀ < q) (hq_one : q ≤ 1)
    (hgain₀ : s < beta * q₀)
    (hadmissible : configuration.IsAdmissibleAt s)
    (hcross : ∀ redLabel blueLabel,
      q₀ ≤ dist (configuration .red redLabel) (configuration .blue blueLabel)) :
    ∃ packing : SixPointPacking configuration, packing.HasPositiveRadii ∧
      (∀ i : packing.support, (packing.radius i : ℝ) ≤ q) ∧
      q₀ * (beta * q₀ - s) / (4 * s * beta) < packing.score beta := by
  obtain ⟨packing, hscore⟩ := hfinite configuration hadmissible
  have hlower : q₀ ≤ packing.virtualDiameter :=
    packing.crossColor_le_virtualDiameter fun redLabel blueLabel _ _ ↦
      hcross redLabel blueLabel
  have hq : 0 < q := hq₀.trans hq₀q
  let scaled := packing.scaleRadii q hq.le hq_one
  have hcap : ∀ i : scaled.support, (scaled.radius i : ℝ) ≤ q := by
    intro i
    dsimp only [scaled, SixPointPacking.scaleRadii]
    exact mul_le_of_le_one_right hq.le (packing.radius i).property.2
  have hscore_scaled : q₀ * (beta * q₀ - s) / (4 * s * beta) <
      scaled.score beta := by
    apply lt_of_lt_of_le ?_
      (packing.scaleRadii_score_ge hs hbeta hq.le hq_one (by nlinarith) hscore hlower)
    have hden : 0 < 4 * s * beta := by positivity
    have hqq := mul_lt_mul_of_pos_left hq₀q hbeta
    apply (div_lt_iff₀ hden).2
    field_simp
    nlinarith [mul_pos hq₀ hden]
  exact scaled.exists_positiveRadii_score_gt hbeta hq hq_one hcap hscore_scaled

private theorem normalized_admissible_and_cross {physical : SixPointConfiguration}
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    {s q₀ gamma d length q : ℝ} {origin : (EuclideanSpace ℝ (Fin 2))}
    (hlength : 0 < length) (hq_eq : q = d / length) (hq₀q : q₀ < q) (hq_one : q ≤ 1)
    (hgamma : 0 < gamma) (hs_gamma : s < gamma * q₀)
    (hroot : dist (physical .red .root) (physical .blue .root) = length)
    (hchild : ∀ color label, label ≠ .root →
      dist (physical color .root) (physical color label) ≤ d)
    (hsibling : ∀ color,
      2 * gamma * d < dist (physical color .left) (physical color .right))
    (hnonempty : ∀ color, (e color).Nonempty)
    (hcenter : ∀ color label, physical color label ∈ e color)
    (hd_set : d = (setEDist (e .red) (e .blue)).toReal) :
    (physical.normalize origin length).IsAdmissibleAt s ∧
      ∀ redLabel blueLabel, q₀ ≤
        dist (physical.normalize origin length .red redLabel)
          (physical.normalize origin length .blue blueLabel) := by
  have hs_gamma_q : s ≤ gamma * q := by
    have hscaled := mul_lt_mul_of_pos_left hq₀q hgamma
    exact (hs_gamma.trans hscaled).le
  constructor
  · exact physical.isAdmissibleAt_normalize_of_distances origin hlength hroot hchild hsibling
      hq_eq hq_one hs_gamma_q
  · intro redLabel blueLabel
    rw [physical.dist_normalize origin hlength]
    apply hq₀q.le.trans
    rw [hq_eq]
    apply div_le_div_of_nonneg_right _ hlength.le
    exact hd_set.trans_le <| setEDist_toReal_le_dist (hnonempty .red) (hnonempty .blue)
      (hcenter .red redLabel) (hcenter .blue blueLabel)

private theorem SixPointPacking.ballUnionAt_inter_nonempty
    {normalized physical : SixPointConfiguration} (packing : SixPointPacking normalized)
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))} {length : ℝ} (hlength : 0 < length)
    (hpositive : packing.HasPositiveRadii)
    (hcenter : ∀ color label, physical color label ∈ e color) (color : SixPointColor) :
    (packing.ballUnionAt physical length ∩ e color).Nonempty := by
  obtain ⟨label, hlabel⟩ := packing.meets_color color
  let i : packing.support := ⟨(color, label), hlabel⟩
  refine ⟨physical color label, ?_, hcenter color label⟩
  exact mem_finiteBallUnion.mpr ⟨i, Metric.mem_ball_self (mul_pos hlength (hpositive i))⟩

private theorem packing_leakage_gt {normalized physical : SixPointConfiguration}
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {s beta tau margin length d scale : ℝ}
    (hadmissible : normalized.IsAdmissibleAt s) (hmu : IsStraightMeasure mu)
    (hbeta : 0 < beta) (htau : 0 < tau) (htau_le : tau ≤ beta * margin / 10)
    (hlength : 0 < length) (hd_scale : d < scale)
    (hd_set : d = (setEDist (e .red) (e .blue)).toReal)
    (hnonempty : ∀ color, (e color).Nonempty)
    (hcenter : ∀ color label, physical color label ∈ e color)
    (hdistance : ∀ i j : SixPointIndex,
      dist (physical i.1 i.2) (physical j.1 j.2) =
        length * dist (normalized i.1 i.2) (normalized j.1 j.2))
    (hdensity : ∀ x ∈ e .red ∪ e .blue, ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * beta * r) < mu (Metric.ball x r))
    (packing : SixPointPacking normalized) (hpositive : packing.HasPositiveRadii)
    (hradius : ∀ i : packing.support, length * (packing.radius i : ℝ) ≤ d)
    (hscore : margin < packing.score beta) :
    ENNReal.ofReal tau * Metric.ediam (packing.ballUnionAt physical length) <
      mu (packing.ballUnionAt physical length \ (e .red ∪ e .blue)) := by
  by_contra hleakage
  have hmeasure := density_sum_lt_one_add_leakage_mul_ediam packing.support_nonempty
    (fun i ↦ physical i.1.1 i.1.2) (fun i ↦ length * (packing.radius i : ℝ)) e mu hbeta.le
    hnonempty (fun i ↦ hcenter i.1.1 i.1.2) (fun i ↦ mul_pos hlength (hpositive i))
    (fun i ↦ (hradius i).trans_lt hd_scale) (fun i ↦ (hradius i).trans_eq hd_set)
    (fun i j hij hcolor ↦ packing.disjoint_ballAt physical hlength.le
      (fun i j ↦ hdistance i j) i j hij hcolor) hdensity hmu (le_of_not_gt hleakage)
  have hsum : (∑ i : packing.support, length * (packing.radius i : ℝ)) =
      length * packing.totalRadius := by
    simpa using packing.sum_radiusAt length
  change ENNReal.ofReal
      (2 * beta * ∑ i : packing.support, length * (packing.radius i : ℝ)) <
    (1 + ENNReal.ofReal tau) * Metric.ediam (packing.ballUnionAt physical length) at hmeasure
  rw [hsum] at hmeasure
  have hed := packing.ediam_ballUnionAt_le physical hlength.le fun i j ↦ hdistance i j
  have hmeasure' : ENNReal.ofReal (2 * beta * (length * packing.totalRadius)) <
      ENNReal.ofReal ((1 + tau) * (length * packing.virtualDiameter)) := by
    calc
      _ < (1 + ENNReal.ofReal tau) * Metric.ediam
          (packing.ballUnionAt physical length) := hmeasure
      _ ≤ (1 + ENNReal.ofReal tau) *
          ENNReal.ofReal (length * packing.virtualDiameter) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + tau),
          ENNReal.ofReal_add zero_le_one htau.le]
        simp
  have hreal_measure : 2 * beta * (length * packing.totalRadius) <
      (1 + tau) * (length * packing.virtualDiameter) := by
    have hlhs : 0 ≤ 2 * beta * (length * packing.totalRadius) := by
      positivity [packing.totalRadius_nonneg]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlhs] at hmeasure'
    exact hmeasure'
  have hfactor := leakage_factor_lt_of_score hbeta htau.le htau_le
    (packing.virtualDiameter_le_five hadmissible) hscore
  have hreal_score : (1 + tau) * (length * packing.virtualDiameter) <
      2 * beta * (length * packing.totalRadius) := by
    have hscaled := mul_lt_mul_of_pos_left hfactor hlength
    nlinarith
  exact (not_lt_of_ge hreal_measure.le) hreal_score

private theorem exists_packing_neighborhood {normalized physical : SixPointConfiguration}
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {s beta q₀ q tau length d scale : ℝ} (hfinite : SixPointFiniteProperty s)
    (hs : 0 < s) (hbeta : 0 < beta) (hq₀ : 0 < q₀) (hq₀q : q₀ < q) (hq_one : q ≤ 1)
    (hgain₀ : s < beta * q₀) (htau : 0 < tau)
    (htau_score : tau ≤ beta * (q₀ * (beta * q₀ - s) / (4 * s * beta)) / 10)
    (hlength : 0 < length) (hq_eq : q = d / length) (hd_scale : d < scale)
    (hd_set : d = (setEDist (e .red) (e .blue)).toReal)
    (hadmissible : normalized.IsAdmissibleAt s)
    (hcross : ∀ redLabel blueLabel,
      q₀ ≤ dist (normalized .red redLabel) (normalized .blue blueLabel))
    (hmu : IsStraightMeasure mu) (hnonempty : ∀ color, (e color).Nonempty)
    (hcenter : ∀ color label, physical color label ∈ e color)
    (hdistance : ∀ i j : SixPointIndex,
      dist (physical i.1 i.2) (physical j.1 j.2) =
        length * dist (normalized i.1 i.2) (normalized j.1 j.2))
    (hdensity : ∀ x ∈ e .red ∪ e .blue, ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * beta * r) < mu (Metric.ball x r)) :
    ∃ v : Set (EuclideanSpace ℝ (Fin 2)), IsOpen v ∧
      (v ∩ e .red).Nonempty ∧ (v ∩ e .blue).Nonempty ∧
      ENNReal.ofReal tau * Metric.ediam v < mu (v \ (e .red ∪ e .blue)) := by
  obtain ⟨packing, hpositive, hradius_q, hscore⟩ :=
    exists_uniform_positive_packing hfinite hs hbeta hq₀ hq₀q hq_one hgain₀
      hadmissible hcross
  have hradius_d : ∀ i : packing.support, length * (packing.radius i : ℝ) ≤ d := by
    intro i
    calc
      length * (packing.radius i : ℝ) ≤ length * q :=
        mul_le_mul_of_nonneg_left (hradius_q i) hlength.le
      _ = d := by
        rw [hq_eq]
        field_simp
  let union := packing.ballUnionAt physical length
  refine ⟨union, packing.isOpen_ballUnionAt physical length, ?_, ?_, ?_⟩
  · exact packing.ballUnionAt_inter_nonempty hlength hpositive hcenter .red
  · exact packing.ballUnionAt_inter_nonempty hlength hpositive hcenter .blue
  · exact packing_leakage_gt hadmissible hmu hbeta htau htau_score hlength hd_scale hd_set
      hnonempty hcenter hdistance hdensity packing hpositive hradius_d hscore

private theorem exists_neighborhood_of_root_bound
    {e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2))}
    {mu : Measure (EuclideanSpace ℝ (Fin 2))} {s beta q₀ gamma tau scale d length q : ℝ}
    (hfinite : SixPointFiniteProperty s) (hs : 0 < s) (hbeta : 0 < beta)
    (hgain₀ : s < beta * q₀) (hq₀ : 0 < q₀) (hq₀q : q₀ < q) (hq_one : q ≤ 1)
    (hgamma : 0 < gamma) (hgamma_beta : gamma < beta)
    (hs_gamma : s < gamma * q₀) (htau : 0 < tau)
    (htau_score : tau ≤ beta * (q₀ * (beta * q₀ - s) / (4 * s * beta)) / 10)
    (hmu : IsStraightMeasure mu) (hmeasurable : ∀ color, MeasurableSet (e color))
    (hnonempty : ∀ color, (e color).Nonempty) (hd : 0 < d) (hd_scale : d < scale)
    (hlength : 0 < length) (hq_eq : q = d / length)
    (hd_set : d = (setEDist (e .red) (e .blue)).toReal)
    (root : SixPointColor → (EuclideanSpace ℝ (Fin 2)))
    (hroot : ∀ color, root color ∈ e color)
    (hroot_length : dist (root .red) (root .blue) = length)
    (hdensity_root : ∀ color,
      ENNReal.ofReal (2 * beta * d) < mu (Metric.ball (root color) d))
    (hroot_bound : mu (rootBallUnion (root .red) (root .blue) d \ (e .red ∪ e .blue)) ≤
      ENNReal.ofReal (2 * (beta - gamma) * d))
    (hdensity : ∀ x ∈ e .red ∪ e .blue, ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * beta * r) < mu (Metric.ball x r)) :
    ∃ v : Set (EuclideanSpace ℝ (Fin 2)), IsOpen v ∧
      (v ∩ e .red).Nonempty ∧ (v ∩ e .blue).Nonempty ∧
      ENNReal.ofReal tau * Metric.ediam v < mu (v \ (e .red ∪ e .blue)) := by
  obtain ⟨physical, hphysical_red, hphysical_blue, hcenter, hchild, hsibling⟩ :=
    exists_physical_configuration hmu hmeasurable hnonempty hd hgamma hgamma_beta
      hd_set root hroot hdensity_root hroot_bound
  let normalized := physical.normalize (root .red) length
  have hphysical_root : dist (physical .red .root) (physical .blue .root) = length := by
    rw [hphysical_red, hphysical_blue, hroot_length]
  obtain ⟨hadmissible, hcross⟩ := normalized_admissible_and_cross hlength hq_eq hq₀q
    hq_one hgamma hs_gamma hphysical_root hchild hsibling hnonempty hcenter hd_set
  apply exists_packing_neighborhood hfinite hs hbeta hq₀ hq₀q hq_one hgain₀ htau
    htau_score hlength hq_eq hd_scale hd_set hadmissible hcross hmu hnonempty hcenter
  · intro i j
    exact physical.dist_eq_scale_mul_dist_normalize (root .red) hlength i.1 j.1 i.2 j.2
  · exact hdensity

private theorem exists_pair_neighborhood {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {s beta q₀ gamma tau scale : ℝ} (hfinite : SixPointFiniteProperty s) (hs : 0 < s)
    (hbeta : 0 < beta) (hgain₀ : s < beta * q₀) (hq₀ : 0 < q₀) (hq₀_one : q₀ < 1)
    (hgamma : 0 < gamma) (hgamma_beta : gamma < beta) (hs_gamma : s < gamma * q₀)
    (htau : 0 < tau) (htau_root : tau ≤ (beta - gamma) * q₀ / 4)
    (htau_score : tau ≤ beta * (q₀ * (beta * q₀ - s) / (4 * s * beta)) / 10)
    (hmu : IsStraightMeasure mu) {e₁ e₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (he₁ : MeasurableSet e₁) (he₂ : MeasurableSet e₂) (he₁_nonempty : e₁.Nonempty)
    (he₂_nonempty : e₂.Nonempty) (hset_pos : 0 < setEDist e₁ e₂)
    (hset_lt : setEDist e₁ e₂ < ENNReal.ofReal scale)
    (hdensity : ∀ x ∈ e₁ ∪ e₂, ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * beta * r) < mu (Metric.ball x r)) :
    ∃ v : Set (EuclideanSpace ℝ (Fin 2)), IsOpen v ∧
      (v ∩ e₁).Nonempty ∧ (v ∩ e₂).Nonempty ∧
      ENNReal.ofReal tau * Metric.ediam v < mu (v \ (e₁ ∪ e₂)) := by
  let e : SixPointColor → Set (EuclideanSpace ℝ (Fin 2)) | .red => e₁ | .blue => e₂
  have he_nonempty : ∀ color, (e color).Nonempty := by
    intro color
    cases color <;> simp_all [e]
  have he_measurable : ∀ color, MeasurableSet (e color) := by
    intro color
    cases color <;> simp_all [e]
  let d := (setEDist e₁ e₂).toReal
  have hd : 0 < d := setEDist_toReal_pos he₁_nonempty he₂_nonempty hset_pos
  have hd_scale : d < scale := ENNReal.toReal_lt_of_lt_ofReal hset_lt
  obtain ⟨redRoot, hredRoot, blueRoot, hblueRoot, hd_length, hroot_length⟩ :=
    exists_approximate_roots he₁_nonempty he₂_nonempty hd hq₀ hq₀_one (by rfl)
  let length := dist redRoot blueRoot
  change d ≤ length at hd_length
  change length < d / q₀ at hroot_length
  have hlength : 0 < length := hd.trans_le hd_length
  let q := d / length
  have hq₀q : q₀ < q := (lt_div_iff₀ hlength).2 <| by
    simpa [mul_comm] using (lt_div_iff₀ hq₀).1 hroot_length
  have hq_one : q ≤ 1 := (div_le_one hlength).2 hd_length
  let root : SixPointColor → (EuclideanSpace ℝ (Fin 2)) | .red => redRoot | .blue => blueRoot
  let rootUnion := rootBallUnion redRoot blueRoot d
  by_cases hleakage : ENNReal.ofReal tau * Metric.ediam rootUnion <
      mu (rootUnion \ (e₁ ∪ e₂))
  · exact ⟨rootUnion, isOpen_rootBallUnion _ _ _,
      ⟨redRoot, Or.inl (Metric.mem_ball_self hd), hredRoot⟩,
      ⟨blueRoot, Or.inr (Metric.mem_ball_self hd), hblueRoot⟩, hleakage⟩
  · have hroot_bound := measure_rootBallUnion_sdiff_le hq₀ hq₀_one hgamma_beta hd
      hd_length rfl hroot_length htau htau_root (by simpa [rootUnion] using hleakage)
    have hroot_mem : ∀ color, root color ∈ e color := by
      intro color
      cases color <;> simp_all [root, e]
    have hroot_density : ∀ color,
        ENNReal.ofReal (2 * beta * d) < mu (Metric.ball (root color) d) := by
      intro color
      cases color
      · exact hdensity redRoot (Or.inl hredRoot) d hd hd_scale
      · exact hdensity blueRoot (Or.inr hblueRoot) d hd hd_scale
    apply exists_neighborhood_of_root_bound hfinite hs hbeta hgain₀ hq₀ hq₀q hq_one
      hgamma hgamma_beta hs_gamma htau htau_score hmu he_measurable he_nonempty hd hd_scale
      hlength rfl (by simp [d, e]) root hroot_mem rfl hroot_density
    · simpa [root, rootUnion, e] using hroot_bound
    · simpa [e] using hdensity

/-- The finite six-point property at `s` implies the Besicovitch pair condition above `s`. -/
theorem SixPointFiniteProperty.besicovitchPairCondition {s beta : ℝ} (hs : 0 < s)
    (hsbeta : s < beta) (hfinite : SixPointFiniteProperty s) :
    BesicovitchPairCondition beta := by
  obtain ⟨q₀, gamma, hq₀, hq₀_one, hs_div, hgamma, hgamma_beta, hs_gamma⟩ :=
    exists_transfer_parameters hs hsbeta
  have hbeta : 0 < beta := hs.trans hsbeta
  have hgain₀ : s < beta * q₀ := by
    simpa [mul_comm] using (div_lt_iff₀ hbeta).1 hs_div
  let margin := q₀ * (beta * q₀ - s) / (4 * s * beta)
  have hmargin : 0 < margin := by
    dsimp only [margin]
    positivity
  let tau := min ((beta - gamma) * q₀ / 4) (beta * margin / 10)
  have htau : 0 < tau := by
    dsimp only [tau]
    rw [lt_min_iff]
    exact ⟨by positivity, by positivity⟩
  have htau_root : tau ≤ (beta - gamma) * q₀ / 4 := min_le_left _ _
  have htau_score : tau ≤ beta * margin / 10 := min_le_right _ _
  intro mu hmu
  refine ⟨tau, htau, ?_⟩
  intro scale hscale
  refine ⟨scale, hscale, ?_⟩
  intro e₁ e₂ he₁ he₂ he₁_nonempty he₂_nonempty hset_pos hset_lt hdensity
  exact exists_pair_neighborhood hfinite hs hbeta hgain₀ hq₀ hq₀_one hgamma hgamma_beta
    hs_gamma htau htau_root (by simpa only [margin] using htau_score) hmu he₁ he₂
      he₁_nonempty he₂_nonempty hset_pos hset_lt hdensity

end LeanPool.Besicovitch
