/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Auxiliary `EReal` results

Most of the lemmas this project originally vendored under `ForMathlib/EReal.lean` have moved
to Mathlib; only the ones that are still unique to this project (or convenient aliases for
naming) remain here.
-/

open scoped ENNReal NNReal Topology
open Filter Set

namespace EReal

lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ :=
  top_mul_coe_ennreal hx

lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ :=
  coe_ennreal_mul_top hx

lemma lt_neg_iff_lt_neg {x y : EReal} : x < -y ↔ y < -x := by
  nth_rw 1 [← neg_neg x, neg_lt_neg_iff]

lemma le_neg_iff_le_neg {x y : EReal} : x ≤ -y ↔ y ≤ -x := by
  nth_rw 1 [← neg_neg x, neg_le_neg_iff]

lemma neg_le_iff_neg_le {x y : EReal} : -x ≤ y ↔ -y ≤ x := by
  nth_rw 1 [← neg_neg y, neg_le_neg_iff]

lemma add_ne_top_iff_of_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ EReal.add_ne_top h.1 h.2⟩
  induction x <;> simp_all
  induction y <;> simp_all

lemma add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ :=
  EReal.add_ne_bot_iff.mpr ⟨hx, hy⟩

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma add_mul_coe_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ (x : EReal)]
  exact EReal.coe_mul_add_of_nonneg hx_nonneg y z

lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := by
  induction x
  · simp
  · norm_cast
    ring
  · simp

lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := by
  rw [add_comm, EReal.add_sub_cancel]

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h =>
    refine absurd hy ?_
    exact not_le.mpr (mod_cast h)
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      apply lt_of_le_of_ne hx
      exact (Ne.symm (by exact_mod_cast hx0))
    have hy_pos : 0 < (y : EReal) := by
      apply lt_of_le_of_ne hy
      exact (Ne.symm (by exact_mod_cast hy0))
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact EReal.add_pos hx_pos hy_pos
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := by
      apply lt_of_le_of_ne (mod_cast hy)
      exact (Ne.symm (by exact_mod_cast hy0))
    have hz_pos : 0 < (z : EReal) := by
      apply lt_of_le_of_ne (mod_cast hz)
      exact (Ne.symm (by exact_mod_cast hz0))
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact EReal.add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

end EReal

namespace ENNReal

variable {a b c : ℝ≥0∞}

theorem min_mul : min a b * c = min (a * c) (b * c) := mul_left_mono.map_min

theorem mul_min : a * min b c = min (a * b) (a * c) := mul_right_mono.map_min

end ENNReal
