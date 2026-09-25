/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.KernelBasic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kernel Segment

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise

/-!
# Segment change of variables for Riesz-kernel Poincare integrals

Pulls the segment-blend integrand `φ(segmentBlend x t y) * ‖x - y‖` through a
dilation change of variables into an integral against `(1 - t)^(-(d+1))`,
optionally localised to a closed ball around `x`.
-/

section SegmentChangeOfVariables


variable {d : ℕ}

/-- File-level typeclass cache for `Nontrivial (Vec d)` under `[NeZero d]`.
Repeated inference of this head class dominates the file (~7s cumulative
typeclass before the cache). The cache fires during elaboration of theorems
in this section even when their type signatures don't use `[NeZero d]`,
because the variable-block instance is in scope for typeclass search. -/
instance instNontrivialVecSegCV (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := inferInstance

theorem setIntegral_segmentBlend_mul_norm_sub_eq_inv_pow_mul_setIntegral_scaled
    {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {x : Vec d} {t : ℝ} (ht1 : t < 1)
    {φ : Vec d → ℝ} :
    ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume =
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
        ∫ z in translateSet x ((1 - t) • translateSet (-x) U), φ z * ‖z - x‖
          ∂MeasureTheory.volume := by
  let a : ℝ := 1 - t
  let V : Set (Vec d) := translateSet (-x) U
  let g : Vec d → ℝ := fun z => φ (x + z) * ‖z‖
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith only [ht1]
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have hV_eq : translateSet x V = U := by
    dsimp [V]
    rw [translateSet_translateSet, show -x + x = (0 : Vec d) by abel, translateSet_zero]
  have hV_meas : MeasurableSet V := by
    dsimp [V]
    rw [← preimage_addNeg_eq_translateSet (d := d) (z := -x) U]
    exact hU_meas.preimage (Homeomorph.addRight (-(-x))).continuous.measurable
  have hsegment_eq (y : Vec d) : x + a • (y - x) = segmentBlend x t y := by
    rw [segmentBlend_eq_add_smul_sub]
    ext i
    simp [a, sub_eq_add_neg]
    ring_nf
  have hleft :
      ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume =
        ∫ w in V, φ (x + a • w) * ‖w‖ ∂MeasureTheory.volume := by
    calc
      ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume
          = ∫ y in U, (fun w => φ (x + a • w) * ‖w‖) (y - x) ∂MeasureTheory.volume := by
              refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
              intro y hy
              simp [hsegment_eq y, norm_sub_rev]
      _ = ∫ w in V, φ (x + a • w) * ‖w‖ ∂MeasureTheory.volume := by
            simpa [V, hV_eq] using
              (setIntegral_comp_subRight_translateSet (d := d) (E := ℝ) x V
                (fun w => φ (x + a • w) * ‖w‖))
  have hscale_fun :
      Set.EqOn
        (fun w : Vec d => φ (x + a • w) * ‖w‖)
        (fun w : Vec d => a⁻¹ * g (a • w))
        V := by
    intro w hw
    calc
      φ (x + a • w) * ‖w‖
          = a⁻¹ * (φ (x + a • w) * ‖a • w‖) := by
              rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
              field_simp [ha_pos.ne']
      _ = a⁻¹ * g (a • w) := by
            simp [g]
  have hscaled :
      ∫ w in V, φ (x + a • w) * ‖w‖ ∂MeasureTheory.volume =
        a⁻¹ * ∫ w in V, g (a • w) ∂MeasureTheory.volume := by
    rw [MeasureTheory.setIntegral_congr_fun hV_meas hscale_fun]
    rw [MeasureTheory.integral_const_mul]
  have hsmul :
      ∫ w in V, g (a • w) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ z in a • V, g z ∂MeasureTheory.volume := by
    simpa [g, smul_eq_mul, Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := g) (s := V) ha_pos)
  have hback :
      ∫ z in a • V, g z ∂MeasureTheory.volume =
        ∫ u in translateSet x (a • V), φ u * ‖u - x‖ ∂MeasureTheory.volume := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) x (a • V)
        (fun u => φ u * ‖u - x‖))
  have hcoeff :
      a⁻¹ * (a ^ d)⁻¹ = (a ^ (d + 1 : ℕ))⁻¹ := by
    field_simp [ha_pos.ne']
    ring
  calc
    ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume
        = ∫ w in V, φ (x + a • w) * ‖w‖ ∂MeasureTheory.volume := hleft
    _ = a⁻¹ * ∫ w in V, g (a • w) ∂MeasureTheory.volume := hscaled
    _ = a⁻¹ * ((a ^ d)⁻¹ * ∫ z in a • V, g z ∂MeasureTheory.volume) := by rw [hsmul]
    _ = (a⁻¹ * (a ^ d)⁻¹) * ∫ z in a • V, g z ∂MeasureTheory.volume := by ring
    _ = (a⁻¹ * (a ^ d)⁻¹) *
          ∫ u in translateSet x (a • V), φ u * ‖u - x‖ ∂MeasureTheory.volume := by
            rw [hback]
    _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in translateSet x ((1 - t) • translateSet (-x) U), φ z * ‖z - x‖
            ∂MeasureTheory.volume := by
            simp [a, V, hcoeff]

theorem setIntegral_segmentBlend_mul_norm_sub_le_inv_pow_mul_setIntegral_inter_closedBall
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x : Vec d} (hx : x ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : Vec d → ℝ}
    (hφ_int : MeasureTheory.IntegrableOn (fun z => φ z * ‖x - z‖) U MeasureTheory.volume)
    (hφ_nonneg : ∀ z, 0 ≤ φ z) :
    ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume ≤
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
        ∫ z in U ∩ Metric.closedBall x ((1 - t) * (2 * Classical.choose hU.isBoundedDomain)),
          φ z * ‖x - z‖ ∂MeasureTheory.volume := by
  let a : ℝ := 1 - t
  let R : ℝ := 2 * Classical.choose hU.isBoundedDomain
  let S : Set (Vec d) := translateSet x (a • translateSet (-x) U)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    linarith only [ht1]
  have hsegment_eq (y : Vec d) : x + a • (y - x) = segmentBlend x t y := by
    ext i
    simp [a, segmentBlend, AffineMap.lineMap_apply_module, sub_eq_add_neg]
    ring_nf
  have hsegment_eq' (y : Vec d) : a • (y - x) + x = segmentBlend x t y := by
    simpa [add_comm] using hsegment_eq y
  have hsub_ball : S ⊆ U ∩ Metric.closedBall x (a * R) := by
    intro u hu
    rcases hu with ⟨z, hz, rfl⟩
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, hwEq⟩
    subst hwEq
    constructor
    · change a • (y - x) + x ∈ U
      rw [hsegment_eq' y]
      exact segmentBlend_mem_of_isOpenBoundedConvexDomain hU hx hy ht0 ht1.le
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hdist :
          ‖y - x‖ ≤ 2 * Classical.choose hU.isBoundedDomain := by
        simpa [norm_sub_rev] using hU.isBoundedDomain.norm_sub_le_two_mul_choose hy hx
      change ‖a • (y - x) + x - x‖ ≤ a * R
      calc
        ‖a • (y - x) + x - x‖ = ‖a • (y - x)‖ := by simp
        _ = a * ‖y - x‖ := by rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
        _ ≤ a * R := by
              exact mul_le_mul_of_nonneg_left (by simpa [R] using hdist) ha_nonneg
  have hφ_int' :
      MeasureTheory.IntegrableOn (fun z => φ z * ‖z - x‖) U MeasureTheory.volume := by
    simpa [norm_sub_rev] using hφ_int
  have htarget_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * ‖z - x‖)
        (U ∩ Metric.closedBall x (a * R)) MeasureTheory.volume :=
    hφ_int'.mono_set (by intro z hz; exact hz.1)
  have hmono :
      ∫ u in S, φ u * ‖u - x‖ ∂MeasureTheory.volume ≤
        ∫ u in U ∩ Metric.closedBall x (a * R), φ u * ‖u - x‖ ∂MeasureTheory.volume := by
    exact MeasureTheory.setIntegral_mono_set htarget_int
      (Filter.Eventually.of_forall (fun u => mul_nonneg (hφ_nonneg u) (norm_nonneg _)))
      hsub_ball.eventuallyLE
  have hcoeff_nonneg : 0 ≤ ((1 - t) ^ (d + 1 : ℕ))⁻¹ := by
    positivity
  calc
    ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume
        = ((1 - t) ^ (d + 1 : ℕ))⁻¹ * ∫ z in S, φ z * ‖z - x‖ ∂MeasureTheory.volume := by
            simpa [a, S] using
              setIntegral_segmentBlend_mul_norm_sub_eq_inv_pow_mul_setIntegral_scaled
                hU.isOpen.measurableSet (x := x) (t := t) ht1
    _ ≤ ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x (a * R), φ z * ‖z - x‖ ∂MeasureTheory.volume := by
            exact mul_le_mul_of_nonneg_left hmono hcoeff_nonneg
    _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x ((1 - t) * (2 * Classical.choose hU.isBoundedDomain)),
            φ z * ‖x - z‖ ∂MeasureTheory.volume := by
            simp [a, R, norm_sub_rev]

end SegmentChangeOfVariables

end CKN
