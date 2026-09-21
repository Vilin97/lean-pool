/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.Transport

/-!
# Squared quantile transport for dyadic masses

For a dyadic probability mass `q`, this module proves

`∫₀¹ (q.quantile u - u)² du = ∫₀¹ (q.piecewiseCDF z - z)² dz`.

The proof keeps track of an affine spatial interval and a cumulative-mass
offset. On each leaf it is an elementary polynomial identity. At a branch,
the two boundary cubic terms cancel.
-/

namespace FD1D

noncomputable section

open Set MeasureTheory intervalIntegral

namespace DyadicMass

private theorem integral_sq_affine
    (alpha beta a b : ℝ) :
    (∫ x in a..b, (alpha * x + beta) ^ 2) =
      alpha ^ 2 * (b ^ 3 - a ^ 3) / 3 +
        alpha * beta * (b ^ 2 - a ^ 2) +
        beta ^ 2 * (b - a) := by
  have hpow :
      IntervalIntegrable (fun x : ℝ => x ^ 2) volume a b :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hid :
      IntervalIntegrable (fun x : ℝ => x) volume a b :=
    continuous_id.intervalIntegrable _ _
  have hconst :
      IntervalIntegrable (fun _ : ℝ => beta ^ 2) volume a b :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun x : ℝ => (alpha * x + beta) ^ 2) =
      fun x => alpha ^ 2 * x ^ 2 +
        (2 * alpha * beta) * x + beta ^ 2 by
    funext x
    ring]
  rw [intervalIntegral.integral_add
    ((hpow.const_mul _).add (hid.const_mul _)) hconst]
  rw [intervalIntegral.integral_add
    (hpow.const_mul _) (hid.const_mul _)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow,
    integral_id,
    intervalIntegral.integral_const]
  ring

/-- Squared quantile displacement on an affine subtree. -/
private def quantileEnergyAt {L : ℕ}
    (A P C : ℝ) (q : DyadicMass L) : ℝ :=
  ∫ u in C..C + q.total,
    (A + P * q.quantile (u - C) - u) ^ 2

/--
Spatial squared CDF discrepancy, recursively split into the physical leaf
intervals. The arguments are the left endpoint, width, and cumulative mass
to the left of the subtree.
-/
private def spatialEnergyAt :
    {L : ℕ} → ℝ → ℝ → ℝ → DyadicMass L → ℝ
  | 0, A, P, C, .leaf s =>
      ∫ z in A..A + P,
        (C + s * ((z - A) / P) - z) ^ 2
  | _ + 1, A, P, C, .branch l r =>
      spatialEnergyAt A (P / 2) C l +
        spatialEnergyAt (A + P / 2) (P / 2) (C + l.total) r

private theorem quantileIntegrand_intervalIntegrable
    {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    (A P C : ℝ) :
    IntervalIntegrable
      (fun u => (A + P * q.quantile (u - C) - u) ^ 2)
      volume C (C + q.total) := by
  have htotal : 0 ≤ q.total := q.total_nonneg hq
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  apply Measure.integrableOn_of_bounded
    (by simp [Real.volume_Icc])
    (((measurable_const.add
      (measurable_const.mul
        (q.quantile_measurable.comp
          (measurable_id.sub measurable_const)))).sub
      measurable_id).pow_const 2).aestronglyMeasurable
    (M := (|A| + |P| + |C| + q.total) ^ 2)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  have huLocal0 : 0 ≤ u - C := by linarith [hu.1]
  have huLocal1 : u - C ≤ q.total := by linarith [hu.2]
  have hquant := q.quantile_mem_unit hq huLocal0 huLocal1
  have hquantAbs : |q.quantile (u - C)| ≤ 1 := by
    rw [abs_of_nonneg hquant.1]
    exact hquant.2
  have huAbs : |u| ≤ |C| + q.total := by
    calc
      |u| = |C + (u - C)| := by ring_nf
      _ ≤ |C| + |u - C| := abs_add_le _ _
      _ = |C| + (u - C) := by rw [abs_of_nonneg huLocal0]
      _ ≤ |C| + q.total := by linarith
  have hPquant : |P * q.quantile (u - C)| ≤ |P| := by
    rw [abs_mul]
    nlinarith [abs_nonneg P]
  have hinner :
      |A + P * q.quantile (u - C) - u| ≤
        |A| + |P| + |C| + q.total := by
    calc
      |A + P * q.quantile (u - C) - u| ≤
          |A + P * q.quantile (u - C)| + |u| :=
        abs_sub _ _
      _ ≤ |A| + |P * q.quantile (u - C)| + |u| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |A| + |P| + (|C| + q.total) := by
        gcongr
      _ = _ := by ring
  change ‖(A + P * q.quantile (u - C) - u) ^ 2‖ ≤
    (|A| + |P| + |C| + q.total) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hB : 0 ≤ |A| + |P| + |C| + q.total := by positivity
  rw [sq_le_sq, abs_of_nonneg hB]
  exact hinner

private theorem cdfIntegrand_intervalIntegrable
    {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    (A P C : ℝ) (hP : 0 < P) :
    IntervalIntegrable
      (fun z =>
        (C + q.piecewiseCDF ((z - A) / P) - z) ^ 2)
      volume A (A + P) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  apply Measure.integrableOn_of_bounded
    (by simp [Real.volume_Icc])
    (((measurable_const.add
      (q.piecewiseCDF_measurable.comp
        ((measurable_id.sub measurable_const).div_const P))).sub
      measurable_id).pow_const 2).aestronglyMeasurable
    (M := (|C| + |q.total| + |A| + |P|) ^ 2)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro z hz
  have hlocal0 : 0 ≤ (z - A) / P :=
    div_nonneg (by linarith [hz.1]) hP.le
  have hlocal1 : (z - A) / P ≤ 1 := by
    apply (div_le_one hP).2
    linarith [hz.2]
  have hF0 := q.piecewiseCDF_nonneg hq hlocal0 hlocal1
  have hF1 := q.piecewiseCDF_le_total hq hlocal0 hlocal1
  have htotal : 0 ≤ q.total := q.total_nonneg hq
  have hzAbs : |z| ≤ |A| + |P| := by
    have ht : 0 ≤ z - A := by linarith [hz.1]
    have htP : z - A ≤ P := by linarith [hz.2]
    calc
      |z| = |A + (z - A)| := by ring_nf
      _ ≤ |A| + |z - A| := abs_add_le _ _
      _ = |A| + (z - A) := by rw [abs_of_nonneg ht]
      _ ≤ |A| + |P| := by
        rw [abs_of_pos hP]
        linarith
  have hFAbs :
      |q.piecewiseCDF ((z - A) / P)| ≤ |q.total| := by
    rw [abs_of_nonneg hF0, abs_of_nonneg htotal]
    exact hF1
  have hinner :
      |C + q.piecewiseCDF ((z - A) / P) - z| ≤
        |C| + |q.total| + |A| + |P| := by
    calc
      |C + q.piecewiseCDF ((z - A) / P) - z| ≤
          |C + q.piecewiseCDF ((z - A) / P)| + |z| :=
        abs_sub _ _
      _ ≤ |C| + |q.piecewiseCDF ((z - A) / P)| + |z| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |C| + |q.total| + (|A| + |P|) := by
        gcongr
      _ = _ := by ring
  change ‖(C + q.piecewiseCDF ((z - A) / P) - z) ^ 2‖ ≤
    (|C| + |q.total| + |A| + |P|) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hB : 0 ≤ |C| + |q.total| + |A| + |P| := by positivity
  rw [sq_le_sq, abs_of_nonneg hB]
  exact hinner

private theorem quantileEnergyAt_eq
    {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    (A P C : ℝ) (hP : 0 < P) :
    quantileEnergyAt A P C q =
      spatialEnergyAt A P C q +
        ((C + q.total - (A + P)) ^ 3 - (C - A) ^ 3) / 3 := by
  induction q generalizing A P C with
  | leaf s =>
      simp only [quantileEnergyAt, spatialEnergyAt, quantile, total]
      by_cases hs : s = 0
      · subst s
        rw [add_zero, intervalIntegral.integral_same]
        rw [show (fun z : ℝ =>
            (C + 0 * ((z - A) / P) - z) ^ 2) =
              fun z => ((-1) * z + C) ^ 2 by
          funext z
          ring]
        rw [integral_sq_affine]
        ring
      · have hspos : 0 < s := lt_of_le_of_ne hq (Ne.symm hs)
        rw [show (fun u : ℝ =>
            (A + P * ((u - C) / s) - u) ^ 2) =
              fun u => ((P / s - 1) * u +
                (A - P * C / s)) ^ 2 by
          funext u
          field_simp [hs]
          ring]
        rw [show (fun z : ℝ =>
            (C + s * ((z - A) / P) - z) ^ 2) =
              fun z => ((s / P - 1) * z +
                (C - s * A / P)) ^ 2 by
          funext z
          field_simp [hP.ne']
          ring]
        rw [integral_sq_affine, integral_sq_affine]
        field_simp [hs, hP.ne']
        ring
  | @branch L l r ihl ihr =>
      have hl0 : 0 ≤ l.total := l.total_nonneg hq.1
      have hr0 : 0 ≤ r.total := r.total_nonneg hq.2
      let f : ℝ → ℝ := fun u =>
        (A + P * (branch l r).quantile (u - C) - u) ^ 2
      have hfLeft :
          IntervalIntegrable f volume C (C + l.total) := by
        apply (quantileIntegrand_intervalIntegrable
          (branch l r) hq A P C).mono_set
        rw [uIcc_of_le (by linarith),
          uIcc_of_le (by simp only [total]; linarith)]
        exact Icc_subset_Icc (le_refl _) (by
          simp only [total]
          linarith)
      have hfRight :
          IntervalIntegrable f volume (C + l.total)
            (C + (branch l r).total) := by
        apply (quantileIntegrand_intervalIntegrable
          (branch l r) hq A P C).mono_set
        rw [uIcc_of_le (by simp only [total]; linarith),
          uIcc_of_le (by simp only [total]; linarith)]
        exact Icc_subset_Icc (by linarith) (le_refl _)
      have hsplit :
          (∫ u in C..C + (branch l r).total, f u) =
            (∫ u in C..C + l.total, f u) +
              ∫ u in C + l.total..C + (branch l r).total, f u := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hfLeft hfRight]
      have hleft :
          (∫ u in C..C + l.total, f u) =
            quantileEnergyAt A (P / 2) C l := by
        unfold quantileEnergyAt
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [f]
        simp only [DyadicMass.quantile]
        rw [ite_eq_left (by
          rw [uIcc_of_le (by linarith)] at hu
          linarith [hu.2])]
        ring_nf
      have hright :
          (∫ u in C + l.total..C + (branch l r).total, f u) =
            quantileEnergyAt (A + P / 2) (P / 2)
              (C + l.total) r := by
        unfold quantileEnergyAt
        simp only [DyadicMass.total]
        rw [show C + (l.total + r.total) =
            C + l.total + r.total by ring]
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro u hu
        dsimp [f]
        simp only [DyadicMass.quantile]
        rw [ite_eq_right (by linarith [hu.1])]
        ring_nf
      rw [quantileEnergyAt]
      change (∫ u in C..C + (l.total + r.total), f u) = _
      rw [show (∫ u in C..C + (l.total + r.total), f u) =
          (∫ u in C..C + (branch l r).total, f u) by rfl,
        hsplit, hleft, hright,
        ihl hq.1 A (P / 2) C (by positivity),
        ihr hq.2 (A + P / 2) (P / 2) (C + l.total)
          (by positivity)]
      simp only [spatialEnergyAt, total]
      ring

private theorem spatialEnergyAt_eq_cdfIntegral
    {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    (A P C : ℝ) (hP : 0 < P) :
    spatialEnergyAt A P C q =
      ∫ z in A..A + P,
        (C + q.piecewiseCDF ((z - A) / P) - z) ^ 2 := by
  induction q generalizing A P C with
  | leaf s => rfl
  | @branch L l r ihl ihr =>
      let f : ℝ → ℝ := fun z =>
        (C + (branch l r).piecewiseCDF ((z - A) / P) - z) ^ 2
      have hfLeft :
          IntervalIntegrable f volume A (A + P / 2) := by
        apply (cdfIntegrand_intervalIntegrable
          (branch l r) hq A P C hP).mono_set
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (le_refl _) (by linarith)
      have hfRight :
          IntervalIntegrable f volume (A + P / 2) (A + P) := by
        apply (cdfIntegrand_intervalIntegrable
          (branch l r) hq A P C hP).mono_set
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) (le_refl _)
      have hsplit :
          (∫ z in A..A + P, f z) =
            (∫ z in A..A + P / 2, f z) +
              ∫ z in A + P / 2..A + P, f z := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hfLeft hfRight]
      have hleft :
          (∫ z in A..A + P / 2, f z) =
            ∫ z in A..A + P / 2,
              (C + l.piecewiseCDF ((z - A) / (P / 2)) - z) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z hz
        dsimp [f]
        simp only [DyadicMass.piecewiseCDF]
        rw [
          ite_eq_left (by
            rw [uIcc_of_le (by linarith)] at hz
            apply (div_le_iff₀ hP).2
            linarith [hz.2])]
        congr 3
        field_simp [hP.ne']
      have hright :
          (∫ z in A + P / 2..A + P, f z) =
            ∫ z in A + P / 2..A + P,
              (C + l.total +
                r.piecewiseCDF
                  ((z - (A + P / 2)) / (P / 2)) - z) ^ 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro z hz
        dsimp [f]
        simp only [DyadicMass.piecewiseCDF]
        rw [
          ite_eq_right (by
            intro h
            have := (div_le_iff₀ hP).1 h
            linarith [hz.1])]
        have harg :
            2 * ((z - A) / P) - 1 =
              (z - (A + P / 2)) / (P / 2) := by
          field_simp [hP.ne']
          ring
        rw [harg]
        ring
      rw [spatialEnergyAt, ihl hq.1 A (P / 2) C (by positivity),
        ihr hq.2 (A + P / 2) (P / 2) (C + l.total)
          (by positivity)]
      rw [show A + P / 2 + P / 2 = A + P by ring,
        hsplit, hleft, hright]

private theorem haarCombination_sq_support
    {L : ℕ} (b : CompleteHaarNode L → ℝ) :
    Function.support
        (fun z =>
          haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L)) b z ^ 2) ⊆
      Ioc (0 : ℝ) 1 := by
  intro z hz
  by_contra hmem
  have hout : z ≤ 0 ∨ 1 ≤ z := by
    by_cases hz0 : z ≤ 0
    · exact Or.inl hz0
    · exact Or.inr (le_of_not_gt fun hz1 =>
        hmem ⟨lt_of_not_ge hz0, hz1.le⟩)
  apply hz
  change haarCombination (haarNodeLeft (L := L))
      (haarNodeWidth (L := L)) b z ^ 2 = 0
  rw [haarCombination_eq_zero_of_outside b hout]
  norm_num

/-- Exact conditional second moment for any dyadic probability mass. -/
theorem quantile_sq_integral_eq_haarL2
    {L : ℕ} (q : DyadicMass L) (hq : q.IsProbability) :
    (∫ u in Icc (0 : ℝ) 1, (q.quantile u - u) ^ 2) =
      haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
        q.nodeCoefficient := by
  have hquantile :=
    quantileEnergyAt_eq q hq.nonneg 0 1 0 (by norm_num)
  have hspatial :=
    spatialEnergyAt_eq_cdfIntegral q hq.nonneg 0 1 0 (by norm_num)
  simp only [quantileEnergyAt, hq.total_eq_one, zero_add, one_mul,
    zero_sub] at hquantile
  rw [hspatial] at hquantile
  norm_num at hquantile
  have hquantileSet :
      (∫ u in Icc (0 : ℝ) 1, (q.quantile u - u) ^ 2) =
        ∫ u in (0 : ℝ)..1, (q.quantile u - u) ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      integral_Icc_eq_integral_Ioc]
  rw [hquantileSet, hquantile]
  have hpoint :
      ∀ z ∈ Ioo (0 : ℝ) 1,
        (q.piecewiseCDF z - z) ^ 2 =
          haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L)) q.nodeCoefficient z ^ 2 := by
    intro z hz
    congr 1
    simpa [hq.total_eq_one] using
      q.cdf_sub_linear_eq_haarCombination hz.1.le hz.2.le
  calc
    (∫ z in (0 : ℝ)..1, (q.piecewiseCDF z - z) ^ 2) =
        ∫ z in (0 : ℝ)..1,
          haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L)) q.nodeCoefficient z ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      exact hpoint
    _ = ∫ z,
          haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L)) q.nodeCoefficient z ^ 2 :=
      intervalIntegral.integral_eq_integral_of_support_subset
        (haarCombination_sq_support q.nodeCoefficient)
    _ = _ := rfl

end DyadicMass

end

end FD1D
