/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import LeanPool.Isoperimetric.BrunnMinkowski

/-!
# The isoperimetric inequality

A direct application of the Brunn–Minkowski inequality to a measurable set `A`
and an `ε`-ball yields the standard form of the isoperimetric inequality
relating `volume A`, the volume of the unit ball, and the volume of the
`ε`-thickening of `A`.
-/

open MeasureTheory Set
open scoped Pointwise

/-- The volume of a Euclidean ball of radius `ε` raised to the `1/(d+1)`-th power equals the
corresponding power for the unit ball times `ε`. -/
lemma volume_ball_relation {d : ℕ} {ε : ℝ} :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) ε) ^ ((d:ℝ)+1)⁻¹
    = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ^ ((d:ℝ)+1)⁻¹
      * ENNReal.ofReal ε := by
  simp only [EuclideanSpace.volume_ball, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr (by linarith)), mul_comm]
  congr
  rw [show (d : ℝ) + 1 = (↑(d + 1) : ℝ) by simp]
  exact ENNReal.pow_rpow_inv_natCast (by linarith) (ENNReal.ofReal ε)

/-- The isoperimetric inequality on Euclidean space, deduced from Brunn–Minkowski. -/
theorem isoperimetric_inequality
    {d : ℕ} {ε : ℝ} (hε : ε > 0) {A : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A) (hA_finite : volume A ≠ ⊤)
    : (d + 1) * (volume A) ^ (1 - ((d:ℝ)+1)⁻¹)
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ^ ((d:ℝ)+1)⁻¹
      ≤ (volume (A + Metric.ball 0 ε) - volume A) / ENNReal.ofReal ε := by
  -- Apply Brunn-Minkowski to A and a ball of radius ε
  let Dnat : ℕ := d + 1
  let D : ℝ := (d:ℝ) + 1
  let unitBall : Set (EuclideanSpace ℝ (Fin (d + 1))) := Metric.ball 0 1
  let epsBall : Set (EuclideanSpace ℝ (Fin (d + 1))) := Metric.ball 0 ε
  have hAplusEpsBall_measurable: MeasurableSet (A + epsBall) := by
    rw [add_ball_zero]; exact Metric.isOpen_thickening.measurableSet
  have h_bm : volume A ^ D⁻¹ + volume epsBall ^ D⁻¹ ≤ volume (A + epsBall) ^ D⁻¹ :=
    brunn_minkowski_euclideanSpace hA_nonempty hA_measurable (Metric.nonempty_ball.mpr hε)
      measurableSet_ball hAplusEpsBall_measurable
  -- Raise both sides to the D power
  have h_bm_Dpow : (volume A ^ D⁻¹ + volume epsBall ^ D⁻¹) ^ Dnat ≤ volume (A + epsBall) := calc
    (volume A ^ D⁻¹ + volume epsBall ^ D⁻¹) ^ Dnat ≤ (volume (A + epsBall) ^ D⁻¹) ^ Dnat := by
      gcongr
    _ = volume (A + epsBall) ^ (D⁻¹ * Dnat) :=
      (ENNReal.rpow_mul_natCast (volume (A + epsBall)) D⁻¹ Dnat).symm
    _ = volume (A + epsBall) := by
      unfold Dnat D; rw [show (d : ℝ) + 1 = ↑(d + 1) by simp]; field_simp; apply ENNReal.rpow_one
  -- Apply binomial expansion to the LHS
  let F : ℕ → ENNReal :=
    fun i ↦ (volume epsBall ^ D⁻¹) ^ i * (volume A ^ D⁻¹) ^ (Dnat - i) * (Dnat.choose i)
  have h_F0 : F 0 = volume A := by
    unfold F D Dnat
    simp only [pow_zero, tsub_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [← ENNReal.rpow_mul_natCast, show (d : ℝ) + 1 = ↑(d + 1) by simp]
    field_simp; apply ENNReal.rpow_one
  have h_F1 : F 1 = Dnat * volume A ^ (1 - D⁻¹) * volume unitBall ^ D⁻¹ * ENNReal.ofReal ε := calc
    F 1 = (volume epsBall ^ D⁻¹) * (volume A ^ (1 - D⁻¹)) * Dnat := by
      unfold F D Dnat
      simp only [pow_one, add_tsub_cancel_right, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
      congr 2
      rw [← ENNReal.rpow_mul_natCast]
      field_simp; simp
    _ = _ := by rw [volume_ball_relation]; ring
  have h_expand : F 0 + F 1 ≤ volume (A + epsBall) := calc
    F 0 + F 1 = ∑ i ∈ Finset.range 2, F i := by
      symm
      apply Finset.sum_eq_add_of_mem
        0 1 (Finset.insert_eq_self.mp rfl) (Finset.self_mem_range_succ 1) Nat.zero_ne_one
      intro c _ _
      have : c = 0 ∨ c = 1 := by grind
      simp_all
    _ ≤ ∑ i ∈ Finset.range (Dnat + 1), F i := by gcongr; unfold Dnat; linarith
    _ ≤ volume (A + epsBall) := by rw [add_comm, add_pow] at h_bm_Dpow; exact h_bm_Dpow
  -- Rearrange and simplify to get the desired result
  calc
    (d + 1) * volume A ^ (1 - D⁻¹) * volume unitBall ^ D⁻¹
        = (F 0 + F 1 - volume A) / ENNReal.ofReal ε := by
      have : Dnat = (d : ENNReal) + 1 := Nat.cast_add_one d
      rw [h_F0, h_F1, this, ENNReal.add_sub_cancel_left hA_finite,
        ENNReal.mul_div_cancel_right (ENNReal.ofReal_ne_zero_iff.mpr hε) ENNReal.ofReal_ne_top]
    _ ≤ (volume (A + epsBall) - volume A) / ENNReal.ofReal ε := by gcongr
