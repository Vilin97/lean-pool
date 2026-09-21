/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Pow
public import Mathlib.Algebra.Order.Ring.StandardPart

/-!
# Leading term and coefficient

We define `Surreal.leadingCoeff` and `Surreal.leadingTerm` for the leading coefficient/term of a
surreal's Hahn series.

We don't yet prove this characterization; rather, these functions are a key ingredient in defining
the map from surreals into Hahn series.
-/

@[expose] public noncomputable section
namespace Surreal

open ArchimedeanClass

/-! ### Leading coefficient -/

/-- The leading coefficient of a surreal's Hahn series. -/
def leadingCoeff (x : Surreal) : ℝ :=
  stdPart (x / ω^ x.wlog)

@[simp]
theorem leadingCoeff_realCast (r : ℝ) : leadingCoeff r = r := by
  rw [leadingCoeff, wlog_realCast, wpow_zero, div_one]
  exact stdPart_map_real Real.toSurrealRingHom r

@[simp]
theorem leadingCoeff_ratCast (q : ℚ) : leadingCoeff q = q :=
  mod_cast leadingCoeff_realCast q

@[simp]
theorem leadingCoeff_intCast (n : ℤ) : leadingCoeff n = n :=
  mod_cast leadingCoeff_realCast n

@[simp]
theorem leadingCoeff_natCast (n : ℕ) : leadingCoeff n = n :=
  mod_cast leadingCoeff_realCast n

@[simp]
theorem leadingCoeff_zero : leadingCoeff 0 = 0 :=
  mod_cast leadingCoeff_natCast 0

@[simp]
theorem leadingCoeff_one : leadingCoeff 1 = 1 :=
  mod_cast leadingCoeff_natCast 1

@[simp]
theorem leadingCoeff_neg (x : Surreal) : leadingCoeff (-x) = -leadingCoeff x := by
  simp [leadingCoeff, neg_div]

@[simp]
theorem leadingCoeff_mul (x y : Surreal) :
    leadingCoeff (x * y) = leadingCoeff x * leadingCoeff y := by
  unfold leadingCoeff
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [wlog_mul hx hy, wpow_add, ← stdPart_mul, mul_div_mul_comm]
  all_goals
    rw [archimedeanClassMk_div_wpow_wlog,
      LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top]
    simpa

@[simp]
theorem leadingCoeff_inv (x : Surreal) : leadingCoeff x⁻¹ = (leadingCoeff x)⁻¹ := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  apply eq_inv_of_mul_eq_one_left
  rw [← leadingCoeff_mul, inv_mul_cancel₀ hx, leadingCoeff_one]

@[simp]
theorem leadingCoeff_div (x y : Surreal) :
    leadingCoeff (x / y) = leadingCoeff x / leadingCoeff y := by
  simp [div_eq_mul_inv]

@[simp]
theorem leadingCoeff_wpow (x : Surreal) : leadingCoeff (ω^ x) = 1 := by
  simp [leadingCoeff]

@[simp]
theorem leadingCoeff_eq_zero {x : Surreal} : leadingCoeff x = 0 ↔ x = 0 := by
  simp [leadingCoeff]

private theorem leadingCoeff_nonneg {x : Surreal} (h : 0 ≤ x) : 0 ≤ leadingCoeff x :=
  stdPart_nonneg <| div_nonneg h (wpow_nonneg _)

private theorem leadingCoeff_nonpos {x : Surreal} (h : x ≤ 0) : leadingCoeff x ≤ 0 :=
  stdPart_nonpos <| div_nonpos_of_nonpos_of_nonneg h (wpow_nonneg _)

@[simp]
theorem leadingCoeff_nonneg_iff {x : Surreal} : 0 ≤ leadingCoeff x ↔ 0 ≤ x := by
  refine ⟨?_, leadingCoeff_nonneg⟩
  contrapose!
  refine fun h ↦ (leadingCoeff_nonpos h.le).lt_of_ne ?_
  rw [ne_eq, leadingCoeff_eq_zero]
  exact h.ne

@[simp]
theorem leadingCoeff_nonpos_iff {x : Surreal} : leadingCoeff x ≤ 0 ↔ x ≤ 0 := by
  simpa using leadingCoeff_nonneg_iff (x := -x)

@[simp]
theorem leadingCoeff_pos_iff {x : Surreal} : 0 < leadingCoeff x ↔ 0 < x := by
  simp [← not_le]

@[simp]
theorem leadingCoeff_neg_iff {x : Surreal} : leadingCoeff x < 0 ↔ x < 0 := by
  simp [← not_le]

theorem leadingCoeff_monotoneOn (x : Surreal) : MonotoneOn leadingCoeff (wlog ⁻¹' {x}) := by
  rintro y rfl z (hw : wlog _ = _) h
  obtain rfl | hy := eq_or_ne y 0; · simpa
  obtain rfl | hz := eq_or_ne z 0; · simpa
  · rw [leadingCoeff, leadingCoeff, hw]
    apply stdPart_monotoneOn
    · simp
    · rw [← hw]; simp
    · simpa [div_eq_mul_inv]

private theorem stdPart_eq' {x y : Surreal} {r : ℝ}
    (hL : ∀ s < r, s * ω^ y ≤ x) (hR : ∀ s > r, x ≤ s * ω^ y) : stdPart (x / ω^ y) = r := by
  apply stdPart_eq Real.toSurrealRingHom <;> intro s hs
  · rw [le_div_iff₀ (wpow_pos _)]
    exact hL s hs
  · rw [div_le_iff₀ (wpow_pos _)]
    exact hR s hs

theorem wlog_eq {x y : Surreal} {r : ℝ} (hr : r ≠ 0)
    (hL : ∀ s < r, s * ω^ y ≤ x) (hR : ∀ s > r, x ≤ s * ω^ y) : x.wlog = y := by
  apply wlog_eq_of_wpow_veq
  rw [veq_def, eq_comm, ← LinearOrderedAddCommGroupWithTop.sub_eq_zero (by simp),
    ← ArchimedeanClass.mk_div, ← stdPart_eq_zero.ne_left]
  exact (stdPart_eq' hL hR).trans_ne hr

theorem leadingCoeff_eq {x y : Surreal} {r : ℝ} (hr : r ≠ 0)
    (hL : ∀ s < r, s * ω^ y ≤ x) (hR : ∀ s > r, x ≤ s * ω^ y) : leadingCoeff x = r := by
  rw [leadingCoeff, wlog_eq hr hL hR, stdPart_eq' hL hR]

theorem leadingCoeff_add_eq_left {x y : Surreal} (h : y <ᵥ x) :
    leadingCoeff (x + y) = leadingCoeff x := by
  rw [leadingCoeff, leadingCoeff, add_div, wlog_add_eq_left h, stdPart_add_eq_left]
  rw [ArchimedeanClass.mk_div, LinearOrderedAddCommGroupWithTop.sub_pos]
  left
  rwa [veq_def.1 (wpow_wlog_veq h.ne_zero), ← vlt_def]

theorem leadingCoeff_add_eq_right {x y : Surreal} (h : y <ᵥ x) :
    leadingCoeff (y + x) = leadingCoeff x := by
  rw [add_comm, leadingCoeff_add_eq_left h]

theorem leadingCoeff_sub_eq_left {x y : Surreal} : y <ᵥ x →
    leadingCoeff (x - y) = leadingCoeff x := by
  simpa [sub_eq_add_neg] using @leadingCoeff_add_eq_left x (-y)

theorem leadingCoeff_sub_eq_right {x y : Surreal} : y <ᵥ x →
    leadingCoeff (y - x) = -leadingCoeff x := by
  simpa [sub_eq_add_neg] using @leadingCoeff_add_eq_right (-x) y

/-! ### Leading term -/

/-- The leading term of a surreal's Hahn series. -/
def leadingTerm (x : Surreal) : Surreal :=
  x.leadingCoeff * ω^ x.wlog

@[simp]
theorem leadingTerm_realCast (r : ℝ) : leadingTerm r = r := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_ratCast (q : ℚ) : leadingTerm q = q :=
  mod_cast leadingTerm_realCast q

@[simp]
theorem leadingTerm_intCast (n : ℤ) : leadingTerm n = n :=
  mod_cast leadingTerm_realCast n

@[simp]
theorem leadingTerm_natCast (n : ℕ) : leadingTerm n = n :=
  mod_cast leadingTerm_realCast n

@[simp]
theorem leadingTerm_zero : leadingTerm 0 = 0 :=
  mod_cast leadingTerm_natCast 0

@[simp]
theorem leadingTerm_one : leadingTerm 1 = 1 :=
  mod_cast leadingTerm_natCast 1

@[simp]
theorem leadingTerm_neg (x : Surreal) : leadingTerm (-x) = -leadingTerm x := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_mul (x y : Surreal) : leadingTerm (x * y) = leadingTerm x * leadingTerm y := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  simp [leadingTerm, wlog_mul hx hy, mul_mul_mul_comm]

@[simp]
theorem leadingTerm_inv (x : Surreal) : leadingTerm x⁻¹ = (leadingTerm x)⁻¹ := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  apply eq_inv_of_mul_eq_one_left
  rw [← leadingTerm_mul, inv_mul_cancel₀ hx, leadingTerm_one]

@[simp]
theorem leadingTerm_div (x y : Surreal) : leadingTerm (x / y) = leadingTerm x / leadingTerm y := by
  simp [div_eq_mul_inv]

@[simp]
theorem leadingTerm_wpow (x : Surreal) : leadingTerm (ω^ x) = ω^ x := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_eq_zero {x : Surreal} : leadingTerm x = 0 ↔ x = 0 := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_nonneg_iff {x : Surreal} : 0 ≤ leadingTerm x ↔ 0 ≤ x := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_nonpos_iff {x : Surreal} : leadingTerm x ≤ 0 ↔ x ≤ 0 := by
  simp [leadingTerm, mul_nonpos_iff]

@[simp]
theorem leadingTerm_pos_iff {x : Surreal} : 0 < leadingTerm x ↔ 0 < x := by
  simp [← not_le]

@[simp]
theorem leadingTerm_neg_iff {x : Surreal} : leadingTerm x < 0 ↔ x < 0 := by
  simp [← not_le]

theorem mk_lt_mk_sub_leadingTerm {x : Surreal} (hx : x ≠ 0) :
    ArchimedeanClass.mk x < .mk (x - x.leadingTerm) := by
  rw [← LinearOrderedAddCommGroupWithTop.sub_lt_sub_iff_left_of_ne_top
    (a := .mk <| ω^ x.wlog) (by simp)]
  simp_rw [← ArchimedeanClass.mk_div, sub_div, mk_div_wpow_wlog_of_ne_zero hx]
  convert mk_sub_stdPart_pos Real.toSurrealRingHom _
  · simp [leadingTerm, leadingCoeff]
  · rw [mk_div_wpow_wlog_of_ne_zero hx]

@[simp]
theorem mk_leadingTerm (x : Surreal) : ArchimedeanClass.mk x.leadingTerm = .mk x := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  simpa using mk_sub_eq_mk_left (mk_lt_mk_sub_leadingTerm hx)

theorem leadingTerm_veq (x : Surreal) : x.leadingTerm =ᵥ x :=
  veq_def.2 (mk_leadingTerm x)

@[simp]
theorem wlog_leadingTerm (x : Surreal) : x.leadingTerm.wlog = x.wlog :=
  wlog_congr x.leadingTerm_veq

@[simp]
theorem leadingCoeff_leadingTerm (x : Surreal) : x.leadingTerm.leadingCoeff = x.leadingCoeff := by
  simp [leadingTerm]

@[simp]
theorem leadingTerm_leadingTerm (x : Surreal) : x.leadingTerm.leadingTerm = x.leadingTerm := by
  apply (leadingTerm_mul ..).trans
  simp [leadingTerm]

private theorem leadingTerm_mono' {x y : Surreal} (hx : 0 ≤ x) (h : x ≤ y) :
    x.leadingTerm ≤ y.leadingTerm := by
  have hy := hx.trans h
  obtain hxy | hxy := (mk_antitoneOn hx hy h).eq_or_lt
  · have hxy' := wlog_congr (veq_def.2 hxy)
    unfold leadingTerm
    rw [hxy', mul_le_mul_iff_left₀ (wpow_pos _), Real.toSurreal_le_iff]
    exact leadingCoeff_monotoneOn _ rfl hxy' h
  · apply (lt_of_mk_lt_mk_of_nonneg ..).le <;> simpa

theorem leadingTerm_mono : Monotone leadingTerm := by
  intro x y h
  obtain hx | hx := le_total 0 x
  · exact leadingTerm_mono' hx h
  · obtain hy | hy := le_total 0 y
    · exact (leadingTerm_nonpos_iff.2 hx).trans (leadingTerm_nonneg_iff.2 hy)
    · rw [← neg_le_neg_iff, ← leadingTerm_neg, ← leadingTerm_neg]
      apply leadingTerm_mono' <;> simpa

theorem leadingTerm_eq {x y : Surreal} {r : ℝ} (hr : r ≠ 0)
    (hL : ∀ s < r, s * ω^ y ≤ x) (hR : ∀ s > r, x ≤ s * ω^ y) : leadingTerm x = r * ω^ y := by
  rw [leadingTerm, leadingCoeff_eq hr hL hR, wlog_eq hr hL hR]

theorem leadingTerm_add_eq_left {x y : Surreal} (h : y <ᵥ x) :
    leadingTerm (x + y) = leadingTerm x := by
  rw [leadingTerm, leadingTerm, leadingCoeff_add_eq_left h, wlog_add_eq_left h]

theorem leadingTerm_add_eq_right {x y : Surreal} (h : y <ᵥ x) :
    leadingTerm (y + x) = leadingTerm x := by
  rw [add_comm, leadingTerm_add_eq_left h]

theorem leadingTerm_sub_eq_left {x y : Surreal} : y <ᵥ x →
    leadingTerm (x - y) = leadingTerm x := by
  simpa [sub_eq_add_neg] using @leadingTerm_add_eq_left x (-y)

theorem leadingTerm_sub_eq_right {x y : Surreal} : y <ᵥ x →
    leadingTerm (y - x) = -leadingTerm x := by
  simpa [sub_eq_add_neg] using @leadingTerm_add_eq_right (-x) y

end Surreal
end
