/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.LocalPolicy

/-!
# Feasibility and invariant domain of the v5 local policy
-/

@[expose] public section

namespace FD1D.V5.LocalPolicy

noncomputable section

theorem discrepancy_le_half_iff_regularizedMass_le
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    discrepancy a p h x y ≤ h / 2 ↔
      regularizedMass a p x y ≤ h := by
  have hden : 0 < inventory x y + a / 2 := by
    have := inventory_nonneg x y
    linarith
  unfold discrepancy regularizedMass parentMass
  constructor
  · intro ht
    apply (div_le_iff₀ hden).2
    have hmul := (div_le_iff₀ ha).1 ht
    nlinarith
  · intro hZ
    apply (div_le_iff₀ ha).2
    have hmul := (div_le_iff₀ hden).1 hZ
    nlinarith

theorem parent_interval_bound
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (ht : discrepancy a p h x y ≤ h / 2) :
    p ≤ h * (inventory x y + a / 2) := by
  have hden : 0 < inventory x y + a / 2 := by
    have := inventory_nonneg x y
    linarith
  have hZ :=
    (discrepancy_le_half_iff_regularizedMass_le ha).1 ht
  have := (div_le_iff₀ hden).1 hZ
  nlinarith

private theorem orderedBias_eq_caps
    {a p h : ℝ} {x y : ℕ}
    (hxy : y < x) (hy : 0 < y) :
    orderedBias a p h x y =
      min (feedbackCandidate a h x y)
        (min (uniformCandidate h x y) (floorCandidate a p h x y)) := by
  unfold orderedBias
  rw [ite_eq_right (by omega : x ≠ y)]
  rw [ite_eq_right (by omega : x + y ≠ 0)]
  rw [ite_eq_right (by omega : y ≠ 0)]

private theorem feedbackCandidate_nonneg
    {a h : ℝ} {x y : ℕ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hxy : y ≤ x) (hy : 0 < y) :
    0 ≤ feedbackCandidate a h x y := by
  have hx : 0 < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le hy hxy
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 ≤ inventory x y := inventory_nonneg x y
  have hgap : 0 ≤ (x : ℝ) - y := by
    exact sub_nonneg.mpr (by exact_mod_cast hxy)
  unfold feedbackCandidate parentMass
  positivity

private theorem uniformCandidate_nonneg
    {h : ℝ} {x y : ℕ}
    (hh : 0 ≤ h) (hxy : y ≤ x) (hy : 0 < y) :
    0 ≤ uniformCandidate h x y := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hgap : 0 ≤ (x : ℝ) - y := by
    exact sub_nonneg.mpr (by exact_mod_cast hxy)
  unfold uniformCandidate parentMass
  positivity

private theorem floorCandidate_pos
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 < floorCandidate a p h x y := by
  have hx : 0 < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le hy hxy
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hden : 0 < 2 * (y : ℝ) + a := by positivity
  have hp := parent_interval_bound ha ht
  unfold floorCandidate parentMass inventory at *
  apply sub_pos.mpr
  apply (div_lt_iff₀ hden).2
  nlinarith [mul_pos ha (mul_pos hh hx)]

theorem orderedBias_nonneg
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ orderedBias a p h x y := by
  by_cases heq : x = y
  · simp [orderedBias, heq]
  have hlt : y < x := lt_of_le_of_ne hxy (Ne.symm heq)
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by omega
    rw [orderedBias, ite_eq_right hx, ite_eq_right (by omega), ite_eq_left rfl]
    exact mul_nonneg (inventory_nonneg x 0) hh.le
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    rw [orderedBias_eq_caps hlt hypos]
    apply le_min
    · exact feedbackCandidate_nonneg ha.le hh.le hxy hypos
    · apply le_min
      · exact uniformCandidate_nonneg hh.le hxy hypos
      · exact (floorCandidate_pos ha hh hxy hypos ht).le

theorem bias_nonneg_of_ordered
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ bias a p h x y := by
  rw [bias, ite_eq_left hxy]
  exact orderedBias_nonneg ha hh hxy ht

theorem orderedBias_le_uniform
    {a p h : ℝ} {x y : ℕ}
    (hxy : y ≤ x) (hy : 0 < y) :
    orderedBias a p h x y ≤ uniformCandidate h x y := by
  by_cases heq : x = y
  · subst x
    simp [orderedBias, uniformCandidate]
  · rw [orderedBias_eq_caps (lt_of_le_of_ne hxy (Ne.symm heq)) hy]
    exact (min_le_right _ _).trans (min_le_left _ _)

theorem orderedBias_lt_parentMass_of_pos
    {a p h : ℝ} {x y : ℕ}
    (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y) :
    orderedBias a p h x y < parentMass h x y := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hq : 0 < parentMass h x y := mul_pos hN hh
  by_cases heq : x = y
  · subst x
    simpa [orderedBias] using hq
  have hbU : orderedBias a p h x y ≤ uniformCandidate h x y :=
    orderedBias_le_uniform (a := a) (p := p) (h := h) hxy hy
  have hgap :
      ((x : ℝ) - y) / inventory x y < 1 := by
    have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
    apply (div_lt_one hN).2
    unfold inventory
    linarith
  unfold uniformCandidate at hbU
  calc
    orderedBias a p h x y
        ≤ parentMass h x y * ((x : ℝ) - y) /
            inventory x y := hbU
    _ = parentMass h x y *
          (((x : ℝ) - y) / inventory x y) := by ring
    _ < parentMass h x y * 1 :=
      mul_lt_mul_of_pos_left hgap hq
    _ = parentMass h x y := mul_one _

private theorem child_regularized_le_rate
    {a p q : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n)
    (hmass : p * (n : ℝ) ≤ q * (2 * (n : ℝ) + a)) :
    (p / 2) / ((n : ℝ) + a / 2) ≤ q / n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 2 * (n : ℝ) + a := by positivity
  have heq : (p / 2) / ((n : ℝ) + a / 2) =
      p / (2 * (n : ℝ) + a) := by
    field_simp
  rw [heq]
  exact (div_le_div_iff₀ hden hn').2 hmass

private theorem ordered_child_invariants
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    regularizedMassLeft a p x ≤ rateLeft a p h x y ∧
      regularizedMassRight a p y ≤ rateRight a p h x y := by
  by_cases hy : y = 0
  · subst y
    by_cases hx0 : x = 0
    · subst x
      have ht' : p / a ≤ h / 2 := by
        simpa [discrepancy, parentMass, inventory] using ht
      have heq : p / 2 / (a / 2) = p / a := by
        field_simp
      constructor <;>
        simp [regularizedMassLeft, regularizedMassRight, rateLeft,
          rateRight, heq] <;>
        linarith
    have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hsum : x + 0 ≠ 0 := by omega
    have hb : bias a p h x 0 = parentMass h x 0 := by
      simp [bias, orderedBias, hxy, hx.ne']
    have hML : massLeft a p h x 0 = parentMass h x 0 := by
      simp [massLeft, hb]
    have hMR : massRight a p h x 0 = 0 := by
      simp [massRight, hb]
    constructor
    · rw [rateLeft, ite_eq_right hsum, ite_eq_right (by omega : x ≠ 0), hML]
      apply child_regularized_le_rate ha hx
      have hpbound := parent_interval_bound ha ht
      unfold parentMass inventory at *
      nlinarith [mul_nonneg hp.le (Nat.cast_nonneg x)]
    · rw [rateRight, ite_eq_right hsum, ite_eq_left rfl]
      unfold regularizedMassRight
      have heq : (p / 2) / ((0 : ℝ) + a / 2) = p / a := by
        field_simp
        ring
      norm_num only [Nat.cast_zero, zero_add] at *
      rw [heq]
      exact le_max_right _ _
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    have hsum : x + y ≠ 0 := by omega
    have hb0 := bias_nonneg_of_ordered ha hh hxy ht
    have hbU : bias a p h x y ≤ uniformCandidate h x y := by
      rw [bias, ite_eq_left hxy]
      exact orderedBias_le_uniform hxy hypos
    have hbF : bias a p h x y ≤ floorCandidate a p h x y := by
      rw [bias, ite_eq_left hxy]
      by_cases heq : x = y
      · subst x
        simpa [orderedBias] using
          (floorCandidate_pos ha hh (le_refl y) hypos ht).le
      · rw [orderedBias_eq_caps (lt_of_le_of_ne hxy (Ne.symm heq)) hypos]
        exact (min_le_right _ _).trans (min_le_right _ _)
    have hq0 : 0 ≤ parentMass h x y := by
      exact mul_nonneg (inventory_nonneg x y) hh.le
    have hMLhalf : parentMass h x y / 2 ≤ massLeft a p h x y := by
      unfold massLeft
      nlinarith
    have hMRfloor :
        p * (y : ℝ) ≤
          massRight a p h x y * (2 * (y : ℝ) + a) := by
      unfold floorCandidate at hbF
      unfold massRight
      have hden : 0 < 2 * (y : ℝ) + a := by positivity
      have hmul := (div_le_iff₀ hden).1 (show
        2 * p * (y : ℝ) / (2 * (y : ℝ) + a) ≤
          parentMass h x y - bias a p h x y by linarith)
      nlinarith
    have hMLfloor :
        p * (x : ℝ) ≤
          massLeft a p h x y * (2 * (x : ℝ) + a) := by
      have hpbound := parent_interval_bound ha ht
      have hfactor : 0 ≤ 2 * (x : ℝ) + a := by positivity
      have hx' : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
      have hy' : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
      have hpMul := mul_le_mul_of_nonneg_right hpbound hx'
      have hmassMul := mul_le_mul_of_nonneg_right hMLhalf hfactor
      unfold parentMass inventory at hpMul hmassMul
      nlinarith [mul_nonneg hh.le hy']
    constructor
    · rw [rateLeft, ite_eq_right hsum, ite_eq_right (by omega : x ≠ 0)]
      exact child_regularized_le_rate ha hxpos hMLfloor
    · rw [rateRight, ite_eq_right hsum, ite_eq_right hy]
      exact child_regularized_le_rate ha hypos hMRfloor

theorem massLeft_eq_count_mul_rateLeft
    (a p h : ℝ) (x y : ℕ) :
    massLeft a p h x y = (x : ℝ) * rateLeft a p h x y := by
  by_cases hzero : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [massLeft, rateLeft, bias, orderedBias, parentMass, inventory]
  · by_cases hx : x = 0
    · subst x
      have hy : y ≠ 0 := by omega
      have hxy : ¬y ≤ 0 := by omega
      simp [massLeft, rateLeft, bias, orderedBias, hy, hxy,
        parentMass, inventory]
    · rw [rateLeft, ite_eq_right hzero, ite_eq_right hx]
      field_simp

theorem massRight_eq_count_mul_rateRight
    (a p h : ℝ) (x y : ℕ) :
    massRight a p h x y = (y : ℝ) * rateRight a p h x y := by
  calc
    massRight a p h x y = massLeft a p h y x :=
      (massLeft_swap a p h x y).symm
    _ = (y : ℝ) * rateLeft a p h y x :=
      massLeft_eq_count_mul_rateLeft a p h y x
    _ = (y : ℝ) * rateRight a p h x y := by
      rw [rateLeft_swap]

private theorem discrepancyLeft_le_half_of_regularized
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (hZ : regularizedMassLeft a p x ≤ rateLeft a p h x y) :
    discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 := by
  have hden : 0 < (x : ℝ) + a / 2 := by positivity
  have hmul := (div_le_iff₀ hden).1 hZ
  unfold discrepancyLeft
  apply (div_le_iff₀ ha).2
  rw [massLeft_eq_count_mul_rateLeft]
  nlinarith

private theorem discrepancyRight_le_half_of_regularized
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (hZ : regularizedMassRight a p y ≤ rateRight a p h x y) :
    discrepancyRight a p h x y ≤ rateRight a p h x y / 2 := by
  have hden : 0 < (y : ℝ) + a / 2 := by positivity
  have hmul := (div_le_iff₀ hden).1 hZ
  unfold discrepancyRight
  apply (div_le_iff₀ ha).2
  rw [massRight_eq_count_mul_rateRight]
  nlinarith

theorem child_invariants
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 ∧
      regularizedMassLeft a p x ≤ rateLeft a p h x y ∧
      discrepancyRight a p h x y ≤ rateRight a p h x y / 2 ∧
      regularizedMassRight a p y ≤ rateRight a p h x y := by
  have hZ :
      regularizedMassLeft a p x ≤ rateLeft a p h x y ∧
        regularizedMassRight a p y ≤ rateRight a p h x y := by
    by_cases hxy : y ≤ x
    · exact ordered_child_invariants ha hp hh hxy ht
    · have hyx : x ≤ y := Nat.le_of_not_ge hxy
      have htSwap :
          discrepancy a p h y x ≤ h / 2 := by
        simpa [discrepancy, parentMass_swap] using ht
      have hs := ordered_child_invariants ha hp hh hyx htSwap
      constructor
      · calc
          regularizedMassLeft a p x =
              regularizedMassRight a p x := by
                rfl
          _ ≤ rateRight a p h y x := hs.2
          _ = rateLeft a p h x y := rateRight_swap a p h x y
      · calc
          regularizedMassRight a p y =
              regularizedMassLeft a p y := by
                rfl
          _ ≤ rateLeft a p h y x := hs.1
          _ = rateRight a p h x y := rateLeft_swap a p h x y
  have htL :
      discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 :=
    discrepancyLeft_le_half_of_regularized ha hZ.1
  have htR :
      discrepancyRight a p h x y ≤ rateRight a p h x y / 2 :=
    discrepancyRight_le_half_of_regularized ha hZ.2
  exact ⟨htL, hZ.1, htR, hZ.2⟩

theorem child_rates_nonneg
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ rateLeft a p h x y ∧ 0 ≤ rateRight a p h x y := by
  have hchild := child_invariants ha hp hh ht
  have hZL : 0 ≤ regularizedMassLeft a p x := by
    unfold regularizedMassLeft
    positivity
  have hZR : 0 ≤ regularizedMassRight a p y := by
    unfold regularizedMassRight
    positivity
  exact ⟨hZL.trans hchild.2.1, hZR.trans hchild.2.2.2⟩

private theorem ordered_child_rate_average_ge
    {a p h : ℝ} {x y : ℕ}
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ≤ (rateLeft a p h x y + rateRight a p h x y) / 2 := by
  by_cases hzero : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [rateLeft, rateRight]
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by omega
    have hb : bias a p h x 0 = parentMass h x 0 := by
      simp [bias, orderedBias, hxy, hx]
    have hleft : rateLeft a p h x 0 = h := by
      rw [rateLeft, ite_eq_right hzero, ite_eq_right hx]
      unfold massLeft
      rw [hb]
      simp [parentMass, inventory, hx]
    have hright : rateRight a p h x 0 = max h (p / a) := by
      rw [rateRight, ite_eq_right hzero, ite_eq_left rfl]
    rw [hleft, hright]
    linarith [le_max_left h (p / a)]
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hx : x ≠ 0 := by omega
    have hbU : bias a p h x y ≤ uniformCandidate h x y := by
      rw [bias, ite_eq_left hxy]
      exact orderedBias_le_uniform hxy hypos
    have hN : 0 < inventory x y := inventory_pos hzero
    have hx' : 0 < (x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hx
    have hy' : 0 < (y : ℝ) := by exact_mod_cast hypos
    have hgap : 0 ≤ (x : ℝ) - y := by
      exact sub_nonneg.mpr (by exact_mod_cast hxy)
    have hbMul :
        bias a p h x y * inventory x y ≤
          parentMass h x y * ((x : ℝ) - y) := by
      unfold uniformCandidate at hbU
      exact (le_div_iff₀ hN).1 hbU
    have hmassL :
        (x : ℝ) * rateLeft a p h x y =
          massLeft a p h x y :=
      (massLeft_eq_count_mul_rateLeft a p h x y).symm
    have hmassR :
        (y : ℝ) * rateRight a p h x y =
          massRight a p h x y :=
      (massRight_eq_count_mul_rateRight a p h x y).symm
    have hweighted :
        (x : ℝ) * rateLeft a p h x y +
            (y : ℝ) * rateRight a p h x y =
          inventory x y * h := by
      rw [hmassL, hmassR, massLeft_add_massRight]
      rfl
    have hrateOrder :
        rateLeft a p h x y ≤ rateRight a p h x y := by
      have hid :
          2 * (x : ℝ) * y *
              (rateLeft a p h x y - rateRight a p h x y) =
            bias a p h x y * inventory x y -
              parentMass h x y * ((x : ℝ) - y) := by
        calc
          2 * (x : ℝ) * y *
              (rateLeft a p h x y - rateRight a p h x y) =
              2 * (y : ℝ) *
                  ((x : ℝ) * rateLeft a p h x y) -
                2 * (x : ℝ) *
                  ((y : ℝ) * rateRight a p h x y) := by ring
          _ = 2 * (y : ℝ) * massLeft a p h x y -
                2 * (x : ℝ) * massRight a p h x y := by
              rw [hmassL, hmassR]
          _ = bias a p h x y * inventory x y -
                parentMass h x y * ((x : ℝ) - y) := by
              unfold massLeft massRight inventory
              ring
      have hprod : 0 < 2 * (x : ℝ) * y := by positivity
      nlinarith
    have hproduct :
        0 ≤ ((x : ℝ) - y) *
          (rateRight a p h x y - rateLeft a p h x y) :=
      mul_nonneg hgap (sub_nonneg.mpr hrateOrder)
    unfold inventory at hweighted hN
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).2
    nlinarith

theorem child_rate_average_ge
    {a p h : ℝ} {x y : ℕ}
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ≤ (rateLeft a p h x y + rateRight a p h x y) / 2 := by
  by_cases hxy : y ≤ x
  · exact ordered_child_rate_average_ge hxy ht
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    have htSwap :
        discrepancy a p h y x ≤ h / 2 := by
      simpa [discrepancy, parentMass_swap] using ht
    have hs := ordered_child_rate_average_ge hyx htSwap
    calc
      h ≤ (rateLeft a p h y x + rateRight a p h y x) / 2 := hs
      _ = (rateLeft a p h x y + rateRight a p h x y) / 2 := by
        rw [rateLeft_swap a p h x y, rateRight_swap a p h x y]
        ring

theorem child_rate_energy_ge
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ^ 2 ≤
      (rateLeft a p h x y ^ 2 + rateRight a p h x y ^ 2) / 2 := by
  have havg := child_rate_average_ge ht
  have hnonneg := child_rates_nonneg ha hp hh ht
  nlinarith [sq_nonneg
    (rateLeft a p h x y - rateRight a p h x y)]

end

end FD1D.V5.LocalPolicy
