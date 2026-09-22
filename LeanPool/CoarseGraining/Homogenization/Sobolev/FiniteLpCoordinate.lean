/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Finite-`p` coordinate bounds for direct Euclidean fields

These inequalities compare the project-vector coordinate functions with the
Euclidean Hilbert realization `HilbertVec.ofVec`, while leaving the project's
ambient product norm unchanged.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

private theorem finiteLpExponent_one_le (p : FiniteLpExponent) : 1 ≤ p.exponent :=
  p.one_lt.le

private theorem finiteLpExponent_toReal_nonneg (p : FiniteLpExponent) :
    0 ≤ p.exponent.toReal :=
  ENNReal.toReal_nonneg

private theorem finiteLpExponent_one_le_toReal (p : FiniteLpExponent) :
    1 ≤ p.exponent.toReal := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono p.lt_top.ne p.one_lt.le

/-- For a finite family of extended nonnegative reals and an exponent at
least one, the sum of the powers is bounded by the power of the sum. -/
theorem ennreal_sum_rpow_le_rpow_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, (a i) ^ p ≤ (∑ i, a i) ^ p := by
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      calc
        a x ^ p + ∑ i ∈ s, (a i) ^ p ≤ a x ^ p + (∑ i ∈ s, a i) ^ p := by
          gcongr
        _ ≤ (a x + ∑ i ∈ s, a i) ^ p :=
          ENNReal.add_rpow_le_rpow_add _ _ hp

/-- For a finite family of extended nonnegative reals and an exponent at
least one, the power of the sum is bounded by the cardinality Hölder factor
times the sum of the powers. -/
theorem ennreal_rpow_sum_le_card_rpow_mul_sum_rpow {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, a i) ^ p ≤
      (Fintype.card ι : ℝ≥0∞) ^ (p - 1) * ∑ i, (a i) ^ p := by
  simpa using
    ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ) (f := a) hp

/-- The lower finite-dimensional power-sum comparison at a campaign finite
`L^p` exponent. -/
theorem finiteLpExponent_sum_rpow_le_rpow_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0∞) (p : FiniteLpExponent) :
    ∑ i, (a i) ^ p.exponent.toReal ≤
      (∑ i, a i) ^ p.exponent.toReal :=
  ennreal_sum_rpow_le_rpow_sum a (finiteLpExponent_one_le_toReal p)

/-- The upper finite-dimensional power-sum comparison at a campaign finite
`L^p` exponent, valid also when one of the summands is infinite. -/
theorem finiteLpExponent_rpow_sum_le_card_rpow_mul_sum_rpow
    {ι : Type*} [Fintype ι] (a : ι → ℝ≥0∞) (p : FiniteLpExponent) :
    (∑ i, a i) ^ p.exponent.toReal ≤
      (Fintype.card ι : ℝ≥0∞) ^ (p.exponent.toReal - 1) *
        ∑ i, (a i) ^ p.exponent.toReal :=
  ennreal_rpow_sum_le_card_rpow_mul_sum_rpow a
    (finiteLpExponent_one_le_toReal p)

/-- A coordinate of a project vector is bounded by its explicit Euclidean
magnitude. -/
theorem abs_coordinate_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  rw [euclideanNorm_eq_norm_ofVec]
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
    HilbertVec.abs_apply_le_norm (HilbertVec.ofVec v) i

/-- The extended `L^p` norm of a scalar coordinate is bounded by that of the
direct Euclidean Hilbert realization, without a measurability premise. -/
theorem coordinate_eLpNorm_le_euclidean {α : Type*} [MeasurableSpace α]
    {d : ℕ} (μ : Measure α) (p : FiniteLpExponent)
    (F : α → Vec d) (i : Fin d) :
    eLpNorm (fun x => F x i) p.exponent μ ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ := by
  by_cases hF : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x)) μ
  · have hi : AEStronglyMeasurable (fun x => F x i) μ := by
      simpa only [HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using
        (continuous_apply i).comp_aestronglyMeasurable
          ((HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable hF)
    apply eLpNorm_mono_ae hi
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, HilbertVec.ofVec, PiLp.toLp_apply] using
      HilbertVec.abs_apply_le_norm (HilbertVec.ofVec (F x)) i
  · rw [eLpNorm_of_not_aestronglyMeasurable hF]
    exact le_top

/-- The finite sum of coordinate `p`-powers is bounded by `d` times the
direct Euclidean vector `p`-power. -/
theorem sum_coordinate_eLpNorm_rpow_le_dimension_mul {α : Type*}
    [MeasurableSpace α] {d : ℕ} (μ : Measure α) (p : FiniteLpExponent)
    (F : α → Vec d) :
    ∑ i : Fin d, (eLpNorm (fun x => F x i) p.exponent μ) ^ p.exponent.toReal ≤
      (d : ℝ≥0∞) *
        (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
          p.exponent.toReal := by
  calc
    ∑ i : Fin d, (eLpNorm (fun x => F x i) p.exponent μ) ^ p.exponent.toReal ≤
        ∑ _i : Fin d,
          (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
            p.exponent.toReal := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.rpow_le_rpow
        (coordinate_eLpNorm_le_euclidean μ p F i)
        (finiteLpExponent_toReal_nonneg p)
    _ = (d : ℝ≥0∞) *
        (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
          p.exponent.toReal := by
      simp [nsmul_eq_mul]

/-- A direct Euclidean vector `L^p` norm is bounded by a dimension factor
times the finite sum of coordinate `L^p` norms. -/
theorem euclidean_eLpNorm_le_dimension_mul_sum_coordinates
    {α : Type*} [MeasurableSpace α] {d : ℕ} (μ : Measure α)
    (p : FiniteLpExponent) (F : α → Vec d)
    (hcoord : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ ≤
      ‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ := by
  let D : α → ℝ := fun x => ∑ i : Fin d, ‖F x i‖
  have hcoord_norm_meas : ∀ i : Fin d,
      AEStronglyMeasurable (fun x => ‖F x i‖) μ := by
    intro i
    exact (hcoord i).norm
  have hpoint : ∀ᵐ x ∂μ,
      ‖HilbertVec.ofVec (F x)‖ ≤ ‖(d : ℝ) * D x‖ := by
    filter_upwards [] with x
    have hDnonneg : 0 ≤ D x :=
      Finset.sum_nonneg fun i _ => norm_nonneg (F x i)
    have hsup : ‖F x‖ ≤ D x := by
      refine (pi_norm_le_iff_of_nonneg hDnonneg).2 ?_
      intro i
      simpa only [Real.norm_eq_abs] using!
        Finset.single_le_sum (fun j _ => norm_nonneg (F x j)) (Finset.mem_univ i)
    have hhilbert : ‖HilbertVec.ofVec (F x)‖ ≤ (d : ℝ) * ‖F x‖ :=
      HilbertVec.norm_ofVec_le_mul_norm (F x)
    have hmain : ‖HilbertVec.ofVec (F x)‖ ≤ (d : ℝ) * D x :=
      hhilbert.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) hDnonneg)]
    exact hmain
  have hvec_le_D :
      eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ ≤
        eLpNorm (fun x => (d : ℝ) * D x) p.exponent μ :=
    eLpNorm_mono_ae
      ((HilbertVec.continuousLinearEquivVec d).symm.continuous.comp_aestronglyMeasurable
        (AEMeasurable.of_eval (fun i => (hcoord i).aemeasurable)).aestronglyMeasurable) hpoint
  have hDsum :
      eLpNorm D p.exponent μ ≤
        ∑ i : Fin d, eLpNorm (fun x => ‖F x i‖) p.exponent μ := by
    have hD : D = ∑ i : Fin d, (fun x => ‖F x i‖) := by
      funext x
      simp [D]
    rw [hD]
    exact eLpNorm_sum_le (finiteLpExponent_one_le p)
  calc
    eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ ≤
        eLpNorm ((d : ℝ) • D) p.exponent μ := by
      simpa only [Pi.smul_apply, smul_eq_mul] using! hvec_le_D
    _ = ‖(d : ℝ)‖ₑ * eLpNorm D p.exponent μ :=
      eLpNorm_const_smul _ _ _ _
    _ ≤ ‖(d : ℝ)‖ₑ *
        ∑ i : Fin d, eLpNorm (fun x => ‖F x i‖) p.exponent μ := by
      gcongr
    _ = ‖(d : ℝ)‖ₑ *
        ∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_norm (f := fun x => F x i) (p := p.exponent) (μ := μ) (hcoord i)

/-- Raising the coordinate-sum upper bound to the finite `p` power. -/
theorem euclidean_eLpNorm_rpow_le_dimension_sum_rpow
    {α : Type*} [MeasurableSpace α] {d : ℕ} (μ : Measure α)
    (p : FiniteLpExponent) (F : α → Vec d)
    (hcoord : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
        p.exponent.toReal ≤
      (‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ) ^
        p.exponent.toReal :=
  ENNReal.rpow_le_rpow
    (euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ p F hcoord)
    (finiteLpExponent_toReal_nonneg p)

/-- Expanded finite-`p` form of the coordinate-sum upper bound. -/
theorem euclidean_eLpNorm_rpow_le_dimension_rpow_mul_sum_rpow
    {α : Type*} [MeasurableSpace α] {d : ℕ} (μ : Measure α)
    (p : FiniteLpExponent) (F : α → Vec d)
    (hcoord : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
        p.exponent.toReal ≤
      ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
        (∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ) ^
          p.exponent.toReal := by
  calc
    (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent μ) ^
        p.exponent.toReal ≤
      (‖(d : ℝ)‖ₑ * ∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ) ^
        p.exponent.toReal :=
      euclidean_eLpNorm_rpow_le_dimension_sum_rpow μ p F hcoord
    _ = ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
        (∑ i : Fin d, eLpNorm (fun x => F x i) p.exponent μ) ^
          p.exponent.toReal :=
      ENNReal.mul_rpow_of_nonneg _ _ (finiteLpExponent_toReal_nonneg p)

end

end Homogenization
