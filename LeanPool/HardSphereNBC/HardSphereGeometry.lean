/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereFork
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# HardSphereGeometry

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

namespace HsVirial

open Set
open MeasureTheory
open intervalIntegral
open scoped Interval

noncomputable section

/-- The equal-unit-ball lens formula used by the two-member star block. -/
def hardSphereLens (s : ℝ) : ℝ :=
  Real.pi * (4 + s) * (2 - s) ^ 2 / 12

lemma hardSphereLens_eq_polynomial (s : ℝ) :
    hardSphereLens s = Real.pi / 12 * (16 - 12 * s + s ^ 3) := by
  unfold hardSphereLens
  ring

lemma intervalIntegral_hardSphereLens_mul_sq :
    (∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) =
      5 * Real.pi / 24 := by
  calc
    (∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) =
        ∫ s in (0 : ℝ)..1,
          (Real.pi / 12) * (16 * s ^ 2 - 12 * s ^ 3 + s ^ 5) := by
      apply intervalIntegral.integral_congr
      intro s hs
      change hardSphereLens s * s ^ 2 =
        (Real.pi / 12) * (16 * s ^ 2 - 12 * s ^ 3 + s ^ 5)
      rw [hardSphereLens_eq_polynomial]
      ring
    _ = (Real.pi / 12) *
        (16 * (∫ s in (0 : ℝ)..1, s ^ 2) -
          12 * (∫ s in (0 : ℝ)..1, s ^ 3) +
          ∫ s in (0 : ℝ)..1, s ^ 5) := by
      rw [intervalIntegral.integral_const_mul]
      have h23 : IntervalIntegrable
          (fun s : ℝ => 16 * s ^ 2 - 12 * s ^ 3) volume 0 1 :=
        (intervalIntegrable_pow 2).const_mul 16 |>.sub
          ((intervalIntegrable_pow 3).const_mul 12)
      rw [intervalIntegral.integral_add h23 (intervalIntegrable_pow 5)]
      rw [intervalIntegral.integral_sub
        ((intervalIntegrable_pow 2).const_mul 16)
        ((intervalIntegrable_pow 3).const_mul 12)]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = 5 * Real.pi / 24 := by
      rw [integral_pow, integral_pow, integral_pow]
      norm_num
      ring

lemma hardSphereLens_radial_identity :
    4 * Real.pi *
        (∫ s in (0 : ℝ)..1,
          (hardSphereKappa - hardSphereLens s) * s ^ 2) =
      17 * Real.pi ^ 2 / 18 := by
  have hlens : IntervalIntegrable
      (fun s : ℝ => hardSphereLens s * s ^ 2) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold hardSphereLens
    fun_prop
  calc
    4 * Real.pi *
        (∫ s in (0 : ℝ)..1,
          (hardSphereKappa - hardSphereLens s) * s ^ 2) =
      4 * Real.pi *
        (hardSphereKappa * (∫ s in (0 : ℝ)..1, s ^ 2) -
          ∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) := by
      congr 2
      have hpow : IntervalIntegrable (fun s : ℝ => s ^ 2) volume 0 1 :=
        intervalIntegrable_pow 2
      have hsub := intervalIntegral.integral_sub
        (hpow.const_mul hardSphereKappa) hlens
      have hpoint :
          (fun s : ℝ => (hardSphereKappa - hardSphereLens s) * s ^ 2) =
            (fun s : ℝ => hardSphereKappa * s ^ 2 -
              hardSphereLens s * s ^ 2) := by
        funext s
        ring
      rw [hpoint, hsub, intervalIntegral.integral_const_mul]
    _ = 4 * Real.pi *
        (hardSphereKappa * (1 / 3 : ℝ) - 5 * Real.pi / 24) := by
      rw [integral_pow, intervalIntegral_hardSphereLens_mul_sq]
      norm_num
    _ = 17 * Real.pi ^ 2 / 18 := by
      rw [hardSphereKappa_eq]
      ring

lemma hardSphereSeparatedVolume_ratio_identity :
    (17 / 32 : ℝ) * hardSphereKappa ^ 2 =
      17 * Real.pi ^ 2 / 18 := by
  rw [hardSphereKappa_eq]
  ring

/-- Independent unit-ball constraints on a finite product of position spaces. -/
def hardSphereProductBallRegion (n : Nat) :
    Set (Fin n → HSPosition 3) :=
  {r | ∀ i, r i ∈ Metric.ball 0 1}

lemma measurableSet_hardSphereProductBallRegion (n : Nat) :
    MeasurableSet (hardSphereProductBallRegion n) := by
  have hregion : hardSphereProductBallRegion n =
      Set.univ.pi (fun _ : Fin n => Metric.ball (0 : HSPosition 3) 1) := by
    ext r
    simp [hardSphereProductBallRegion]
  rw [hregion]
  exact MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_ball)

lemma hardSphereProductBallRegion_volume (n : Nat) :
    (volume : Measure (Fin n → HSPosition 3)).real
        (hardSphereProductBallRegion n) = hardSphereKappa ^ n := by
  change (volume (hardSphereProductBallRegion n)).toReal = _
  have hregion : hardSphereProductBallRegion n =
      Set.univ.pi (fun _ : Fin n => Metric.ball (0 : HSPosition 3) 1) := by
    ext r
    simp [hardSphereProductBallRegion]
  rw [hregion]
  rw [volume_pi_pi]
  rw [ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end

end HsVirial
