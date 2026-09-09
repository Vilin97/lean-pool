/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Reference pulse growth

This file verifies the scalar reference growth calculation in Lemma 8.5 and
Proposition A.4 of the supplied manuscript. The denominator `(1 + u^2)^(3/2)`
is written as `(1 + u^2) * sqrt (1 + u^2)` to avoid fractional-power notation.
These results do not assert bounds on the actual variable-coefficient ODE or
on its parameter derivatives.
-/

@[expose] public section


namespace NavierStokes.PulseGrowth

/-- Scalar growth of the positive reference mode after the chosen viscous damping. -/
noncomputable def netGrowth (lam u s : ℝ) : ℝ :=
  lam / Real.sqrt (1 + s ^ 2) -
    lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by
  positivity

theorem radius_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2) :=
  Real.sqrt_pos.2 (one_add_sq_pos s)

theorem dampingDenominator_pos (u : ℝ) :
    0 < (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) :=
  mul_pos (one_add_sq_pos u) (radius_pos u)

/-- The three-halves denominator is the cube of the positive square root. -/
theorem dampingDenominator_eq_radius_cube (u : ℝ) :
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = (Real.sqrt (1 + u ^ 2)) ^ 3 := by
  calc
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) =
        (Real.sqrt (1 + u ^ 2)) ^ 2 * Real.sqrt (1 + u ^ 2) := by
          rw [Real.sq_sqrt (le_of_lt (one_add_sq_pos u))]
    _ = (Real.sqrt (1 + u ^ 2)) ^ 3 := by ring

/-- Squaring the proposed positive eigenvalue gives the reference discriminant. -/
theorem reference_eigenvalue_square (lam s : ℝ) :
    (lam / Real.sqrt (1 + s ^ 2)) ^ 2 = lam ^ 2 / (1 + s ^ 2) := by
  rw [div_pow, Real.sq_sqrt (le_of_lt (one_add_sq_pos s))]

/-- Characteristic equation for the two off-diagonal reference coefficients.

Here `a = 2 F₀ Nθ` and `b = -(2 F₀ Nθ + |g₀|)` in the manuscript.
The hypothesis is the manuscript's definition of the squared reference rate;
its positivity from the geometric cone is not assumed to have been established.
-/
theorem reference_characteristic_equation {a b lam s : ℝ} (hdisc : lam ^ 2 = a * b) :
    (lam / Real.sqrt (1 + s ^ 2)) ^ 2 - (a / (1 + s ^ 2)) * b = 0 := by
  rw [reference_eigenvalue_square, hdisc]
  ring

/-- Reversing the sign of the slot parameter does not change the growth. -/
theorem netGrowth_even (lam u s : ℝ) :
    netGrowth lam u (-s) = netGrowth lam u s := by
  simp [netGrowth]

/-- The prescribed damping exactly cancels growth at the threshold. -/
theorem netGrowth_at_threshold (lam u : ℝ) : netGrowth lam u u = 0 := by
  unfold netGrowth
  field_simp [ne_of_gt (one_add_sq_pos u), ne_of_gt (radius_pos u)]; ring

/-- Strict decrease in squared distance from zero, for a positive reference rate. -/
theorem netGrowth_strictAnti_sq {lam u s t : ℝ} (hlam : 0 < lam)
    (hst : s ^ 2 < t ^ 2) : netGrowth lam u t < netGrowth lam u s := by
  have hst' : 1 + s ^ 2 < 1 + t ^ 2 := by linarith
  have hr : Real.sqrt (1 + s ^ 2) < Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_lt_sqrt (le_of_lt (one_add_sq_pos s)) hst'
  have hg : lam / Real.sqrt (1 + t ^ 2) < lam / Real.sqrt (1 + s ^ 2) := by
    apply (div_lt_div_iff₀ (radius_pos t) (radius_pos s)).2
    exact mul_lt_mul_of_pos_left hr hlam
  have hd : lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) <
      lam * (1 + t ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hst' hlam) (dampingDenominator_pos u)
  exact sub_lt_sub hg hd

theorem netGrowth_eq_of_sq_eq {lam u s t : ℝ} (hst : s ^ 2 = t ^ 2) :
    netGrowth lam u s = netGrowth lam u t := by
  simp only [netGrowth, hst]

/-- Growth is positive strictly inside either threshold. -/
theorem netGrowth_pos_of_abs_lt {lam u s : ℝ} (hlam : 0 < lam)
    (hs : |s| < |u|) : 0 < netGrowth lam u s := by
  have h := netGrowth_strictAnti_sq (u := u) hlam (sq_lt_sq.2 hs)
  simpa only [netGrowth_at_threshold] using h

/-- Growth vanishes at both signed thresholds. -/
theorem netGrowth_zero_of_abs_eq {lam u s : ℝ} (hs : |s| = |u|) :
    netGrowth lam u s = 0 := by
  have hsq : s ^ 2 = u ^ 2 := by
    calc
      s ^ 2 = |s| ^ 2 := (sq_abs s).symm
      _ = |u| ^ 2 := by rw [hs]
      _ = u ^ 2 := sq_abs u
  rw [netGrowth_eq_of_sq_eq hsq, netGrowth_at_threshold]

/-- Growth is negative outside either threshold. -/
theorem netGrowth_neg_of_abs_gt {lam u s : ℝ} (hlam : 0 < lam)
    (hs : |u| < |s|) : netGrowth lam u s < 0 := by
  have h := netGrowth_strictAnti_sq (u := u) hlam (sq_lt_sq.2 hs)
  simpa only [netGrowth_at_threshold] using h

/-- A complete positive/zero/negative classification for a positive reference rate. -/
theorem netGrowth_sign {lam u s : ℝ} (hlam : 0 < lam) :
    (0 < netGrowth lam u s ↔ |s| < |u|) ∧
    (netGrowth lam u s = 0 ↔ |s| = |u|) ∧
    (netGrowth lam u s < 0 ↔ |u| < |s|) := by
  rcases lt_trichotomy |s| |u| with hs | hs | hs
  · have hg := netGrowth_pos_of_abs_lt (lam := lam) hlam hs
    constructor
    · exact ⟨fun _ => hs, fun _ => hg⟩
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  · have hg : netGrowth lam u s = 0 := netGrowth_zero_of_abs_eq hs
    constructor
    · constructor <;> intro h <;> linarith
    constructor
    · exact ⟨fun _ => hs, fun _ => hg⟩
    · constructor <;> intro h <;> linarith
  · have hg := netGrowth_neg_of_abs_gt (lam := lam) hlam hs
    constructor
    · constructor <;> intro h <;> linarith
    constructor
    · constructor <;> intro h <;> linarith
    · exact ⟨fun _ => hs, fun _ => hg⟩

/-- For positive magnitudes the reference growth is strictly decreasing. -/
theorem netGrowth_strictAntiOn_nonneg {lam u : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (netGrowth lam u) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  have ht0 : 0 ≤ t := ht
  apply netGrowth_strictAnti_sq hlam
  apply sq_lt_sq.2
  simpa only [abs_of_nonneg hs0, abs_of_nonneg ht0] using hst

/-- Magnitude of either signed schedule, in the slot-time variable. -/
noncomputable def slotMagnitude (u ell v : ℝ) : ℝ := u / 2 + u * v / ell

theorem slotMagnitude_midpoint (u ell : ℝ) (hell : ell ≠ 0) :
    slotMagnitude u ell (ell / 2) = u := by
  unfold slotMagnitude
  field_simp; ring

theorem slotMagnitude_nonneg {u ell v : ℝ} (hu : 0 ≤ u) (hell : 0 < ell)
    (hv : 0 ≤ v) : 0 ≤ slotMagnitude u ell v := by
  unfold slotMagnitude
  positivity

theorem slotMagnitude_lt_threshold {u ell v : ℝ} (hu : 0 < u) (hell : 0 < ell)
    (hv : v < ell / 2) : slotMagnitude u ell v < u := by
  have hdiv : u * v / ell < u / 2 := (div_lt_iff₀ hell).2 (by nlinarith)
  unfold slotMagnitude
  linarith

theorem slotMagnitude_gt_threshold {u ell v : ℝ} (hu : 0 < u) (hell : 0 < ell)
    (hv : ell / 2 < v) : u < slotMagnitude u ell v := by
  have hdiv : u / 2 < u * v / ell := (lt_div_iff₀ hell).2 (by nlinarith)
  unfold slotMagnitude
  linarith

/-- Positive reference growth on the first half of a slot. -/
theorem netGrowth_slot_positive {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hell : 0 < ell) (hv : 0 ≤ v) (hmid : v < ell / 2) :
    0 < netGrowth lam u (slotMagnitude u ell v) := by
  apply netGrowth_pos_of_abs_lt hlam
  rw [abs_of_nonneg (slotMagnitude_nonneg (le_of_lt hu) hell hv), abs_of_pos hu]
  exact slotMagnitude_lt_threshold hu hell hmid

/-- Zero reference growth at the slot midpoint. -/
theorem netGrowth_slot_midpoint (lam u ell : ℝ) (hell : ell ≠ 0) :
    netGrowth lam u (slotMagnitude u ell (ell / 2)) = 0 := by
  rw [slotMagnitude_midpoint u ell hell, netGrowth_at_threshold]

/-- Negative reference growth on the second half of a slot (and beyond). -/
theorem netGrowth_slot_negative {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hell : 0 < ell) (hmid : ell / 2 < v) :
    netGrowth lam u (slotMagnitude u ell v) < 0 := by
  have hv : 0 ≤ v := by linarith
  apply netGrowth_neg_of_abs_gt hlam
  rw [abs_of_pos hu, abs_of_nonneg (slotMagnitude_nonneg (le_of_lt hu) hell hv)]
  exact slotMagnitude_gt_threshold hu hell hmid

end NavierStokes.PulseGrowth
