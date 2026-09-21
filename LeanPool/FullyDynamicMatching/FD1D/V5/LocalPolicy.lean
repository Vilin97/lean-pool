/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.Parameters

/-!
# The local three-cap policy from manuscript bundle v5

The two child counts are ordered only inside `orderedBias`.  `bias` restores
the fixed left/right spatial sign.  Empty-child rates are auxiliary analytic
rates; empty children still receive zero deletion mass.
-/

namespace FD1D.V5.LocalPolicy

noncomputable section

/-- Parent inventory, coerced to `ℝ`. -/
def inventory (x y : ℕ) : ℝ :=
  (x : ℝ) + (y : ℝ)

/-- Parent deletion mass under the identity `q = Nh`. -/
def parentMass (h : ℝ) (x y : ℕ) : ℝ :=
  inventory x y * h

/-- The feedback candidate, for ordered positive counts `x ≥ y > 0`. -/
def feedbackCandidate (a h : ℝ) (x y : ℕ) : ℝ :=
  2 * a * parentMass h x y * ((x : ℝ) - y) / ((x : ℝ) * y)

/-- The uniform-deletion cap, for ordered counts. -/
def uniformCandidate (h : ℝ) (x y : ℕ) : ℝ :=
  parentMass h x y * ((x : ℝ) - y) / inventory x y

/-- The rate-floor cap, for ordered counts and parent interval mass `p`. -/
def floorCandidate (a p h : ℝ) (x y : ℕ) : ℝ :=
  parentMass h x y - 2 * p * y / (2 * (y : ℝ) + a)

/-- Nonnegative bias magnitude after temporarily ordering `x ≥ y`. -/
def orderedBias (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x = y then 0
  else if x + y = 0 then 0
  else if y = 0 then parentMass h x y
  else min (feedbackCandidate a h x y)
    (min (uniformCandidate h x y) (floorCandidate a p h x y))

/-- Signed left-minus-right deletion bias in fixed spatial labels. -/
def bias (a p h : ℝ) (x y : ℕ) : ℝ :=
  if y ≤ x then orderedBias a p h x y else -orderedBias a p h y x

/-- Left-child deletion mass. -/
def massLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  (parentMass h x y + bias a p h x y) / 2

/-- Right-child deletion mass. -/
def massRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  (parentMass h x y - bias a p h x y) / 2

/-- Auxiliary child rate on the spatial left. -/
def rateLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h
  else if x = 0 then max h (p / a)
  else massLeft a p h x y / x

/-- Auxiliary child rate on the spatial right. -/
def rateRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h
  else if y = 0 then max h (p / a)
  else massRight a p h x y / y

/-- Discrepancy `t = (p-q)/a`. -/
def discrepancy (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p - parentMass h x y) / a

/-- Regularized inverse inventory `Z = p/(N+a/2)`. -/
def regularizedMass (a p : ℝ) (x y : ℕ) : ℝ :=
  p / (inventory x y + a / 2)

/-- Left-child discrepancy. -/
def discrepancyLeft (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p / 2 - massLeft a p h x y) / a

/-- Right-child discrepancy. -/
def discrepancyRight (a p h : ℝ) (x y : ℕ) : ℝ :=
  (p / 2 - massRight a p h x y) / a

/-- Left-child regularized inverse inventory. -/
def regularizedMassLeft (a p : ℝ) (x y : ℕ) : ℝ :=
  (p / 2) / ((x : ℝ) + a / 2)

/-- Right-child regularized inverse inventory. -/
def regularizedMassRight (a p : ℝ) (x y : ℕ) : ℝ :=
  (p / 2) / ((y : ℝ) + a / 2)

/-- The quadratic Bellman correction in equation (15). -/
def bellman (h t Z : ℝ) : ℝ :=
  (t - h / 2) * Z - t ^ 2 / 6

theorem inventory_nonneg (x y : ℕ) :
    0 ≤ inventory x y := by
  unfold inventory
  positivity

theorem inventory_pos {x y : ℕ} (hne : x + y ≠ 0) :
    0 < inventory x y := by
  unfold inventory
  exact_mod_cast Nat.pos_of_ne_zero hne

theorem parentMass_swap (h : ℝ) (x y : ℕ) :
    parentMass h y x = parentMass h x y := by
  simp [parentMass, inventory, add_comm]

theorem bias_swap (a p h : ℝ) (x y : ℕ) :
    bias a p h y x = -bias a p h x y := by
  unfold bias
  by_cases hxy : y ≤ x
  · by_cases hyx : x ≤ y
    · have hEq : x = y := Nat.le_antisymm hyx hxy
      subst y
      simp [orderedBias]
    · simp [hxy, hyx]
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    simp [hxy, hyx]

theorem massLeft_swap (a p h : ℝ) (x y : ℕ) :
    massLeft a p h y x = massRight a p h x y := by
  unfold massLeft massRight
  rw [parentMass_swap, bias_swap]
  ring

theorem massRight_swap (a p h : ℝ) (x y : ℕ) :
    massRight a p h y x = massLeft a p h x y := by
  unfold massLeft massRight
  rw [parentMass_swap, bias_swap]
  ring

theorem rateLeft_swap (a p h : ℝ) (x y : ℕ) :
    rateLeft a p h y x = rateRight a p h x y := by
  unfold rateLeft rateRight
  rw [Nat.add_comm]
  by_cases hzero : x + y = 0
  · simp [hzero]
  · simp only [if_neg hzero]
    by_cases hx : x = 0
    · subst x
      simp at hzero
      simp [hzero, massLeft_swap]
    · by_cases hy : y = 0
      · subst y
        simp [hx]
      · simp [hx, hy, massLeft_swap]

theorem rateRight_swap (a p h : ℝ) (x y : ℕ) :
    rateRight a p h y x = rateLeft a p h x y := by
  rw [← rateLeft_swap a p h y x]

theorem massLeft_add_massRight (a p h : ℝ) (x y : ℕ) :
    massLeft a p h x y + massRight a p h x y =
      parentMass h x y := by
  unfold massLeft massRight
  ring

theorem bias_eq_massLeft_sub_massRight (a p h : ℝ) (x y : ℕ) :
    bias a p h x y =
      massLeft a p h x y - massRight a p h x y := by
  unfold massLeft massRight
  ring

theorem discrepancyLeft_eq (a p h : ℝ) (x y : ℕ) :
    discrepancyLeft a p h x y =
      (discrepancy a p h x y - bias a p h x y / a) / 2 := by
  unfold discrepancyLeft discrepancy massLeft
  ring

theorem discrepancyRight_eq (a p h : ℝ) (x y : ℕ) :
    discrepancyRight a p h x y =
      (discrepancy a p h x y + bias a p h x y / a) / 2 := by
  unfold discrepancyRight discrepancy massRight
  ring

theorem bellman_nonpos {h t Z : ℝ}
    (hZ : 0 ≤ Z) (ht : t ≤ h / 2) :
    bellman h t Z ≤ 0 := by
  unfold bellman
  have hfirst : (t - h / 2) * Z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hZ
  nlinarith [sq_nonneg t]

end

end FD1D.V5.LocalPolicy
