/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionArithmetic

/-!
# Two canonical ramps meeting at an interior chip

`SubdivisionArithmetic.potential` realizes a rise over a slot by the convex
two-slope interpolation, whose unit slopes are nondecreasing.  That convexity
is exactly what makes `DegSpec.interpolatedScript`'s interior Laplacian
nonnegative -- and exactly what makes a single ramp useless for a divisor whose
chip sits *inside* a slot: a convex script never draws on that chip, so the row
would have to succeed with the remaining core-supported chips alone.

Atanasov--Ranganathan's sixth and seventh genus-five families (rows `05` and
`08` of the atlas) are of that kind: no core-supported degree-four divisor
covers either row, and the figures place two of the four chips at interior
points whose offset is a length.

This file supplies the replacement slot value.  `splitPotential L t first
second` is the canonical ramp of rise `first` over the first `t` unit steps,
followed by the canonical ramp of rise `second` over the remaining `L - t`.
It is convex on each side of `t`, and it may be concave exactly at `t`, where
the divisor's chip pays for the deficit.  `splitStep_kink_ge_neg_one` bounds
that deficit by one chip, under a hypothesis every intended configuration has
anyway: neither ramp is steeper than one unit per step, and one of the two is
flat -- the chip is placed exactly where a flat stretch meets a full ramp.

Everything here is arithmetic on `ℕ` and `ℤ`.  The layer that turns it into a
firing script is generic already -- `DegSpec.slotValueScript`,
`DegSpec.SlotValueCompatible` and `DegSpec.IsStepSlope` in
`Utilities/Subdivision/DegenerateSlopeScript.lean` are stated for an
arbitrary slot-value function, `interpolatedScript` being merely the instance
whose value is one ramp.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionArithmetic

variable {L t i j : ℕ} {first second : ℤ}

/-- Admissibility of a split point.  The two degeneracy clauses say that a ramp
of length zero carries no rise; they hold in every intended use, where the split
point is the position of a chip and a collapsed half means that chip has reached
the core vertex at that end. -/
structure SplitRamp (L t : ℕ) (first second : ℤ) : Prop where
  le : t ≤ L
  first_zero : t = 0 → first = 0
  second_zero : t = L → second = 0

/-- The value at offset `i` of the ramp of rise `first` over `[0, t]` followed
by the ramp of rise `second` over `[t, L]`. -/
def splitPotential (L t : ℕ) (first second : ℤ) (i : ℕ) : ℤ :=
  if i < t then potential t first i else first + potential (L - t) second (i - t)

/-- The slope on the unit step from offset `i` to offset `i + 1`. -/
def splitStep (L t : ℕ) (first second : ℤ) (i : ℕ) : ℤ :=
  splitPotential L t first second (i + 1) - splitPotential L t first second i

@[simp] theorem potential_zero_zero_zero : potential 0 0 0 = 0 := by
  norm_num [potential, quotient, remainder, bend]

/-! ## The two regimes -/

theorem splitPotential_of_lt (h : i < t) :
    splitPotential L t first second i = potential t first i := if_pos h

theorem splitPotential_of_le (h : t ≤ i) :
    splitPotential L t first second i = first + potential (L - t) second (i - t) :=
  if_neg (by omega)

/-- The second ramp starts at zero: either it has positive length, or the split
point is the head and its rise vanishes. -/
theorem potential_second_zero (h : SplitRamp L t first second) :
    potential (L - t) second 0 = 0 := by
  rcases Nat.lt_or_ge t L with hlt | hge
  · exact potential_zero second (by omega)
  · have ht : t = L := le_antisymm h.le hge
    have hsecond : second = 0 := h.second_zero ht
    have hzero : L - t = 0 := by omega
    rw [hzero, hsecond]
    exact potential_zero_zero_zero

/-! ## Endpoint values -/

theorem splitPotential_zero (h : SplitRamp L t first second) :
    splitPotential L t first second 0 = 0 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · have hfirst : first = 0 := h.first_zero ht
    have hpz : potential (L - t) second 0 = 0 := potential_second_zero h
    rw [splitPotential_of_le (by omega), hfirst]
    simpa using hpz
  · rw [splitPotential_of_lt ht]
    exact potential_zero first ht

theorem splitPotential_length (h : SplitRamp L t first second) :
    splitPotential L t first second L = first + second := by
  rw [splitPotential_of_le h.le]
  rcases Nat.lt_or_ge t L with hlt | hge
  · rw [potential_length second (by omega)]
  · have ht : t = L := le_antisymm h.le hge
    have hzero : L - t = 0 := by omega
    rw [hzero, h.second_zero ht, potential_zero_zero_zero]

/-! ## The two slope regimes -/

/-- At and above the split point the slope is the second ramp's, shifted. -/
theorem splitStep_right (hi : t ≤ i) :
    splitStep L t first second i = step (L - t) second (i - t) := by
  have hsucc : i + 1 - t = (i - t) + 1 := by omega
  rw [splitStep, splitPotential_of_le (by omega), splitPotential_of_le hi, hsucc]
  simp only [step]
  ring

/-- Strictly below the split point the slope is the first ramp's. -/
theorem splitStep_left_of_lt (h : i + 1 < t) :
    splitStep L t first second i = step t first i := by
  rw [splitStep, splitPotential_of_lt h, splitPotential_of_lt (by omega)]
  rfl

/-- The step ending at the split point is the first ramp's last step: the value
at the split point is `first`, by `potential_length`. -/
theorem splitStep_left_of_succ_eq (h : SplitRamp L t first second)
    (hi : i + 1 = t) :
    splitStep L t first second i = step t first i := by
  have ht : 0 < t := by omega
  have hidx : i + 1 - t = 0 := by omega
  have hstep : step t first i = potential t first (i + 1) - potential t first i := rfl
  rw [splitStep, splitPotential_of_le (by omega), hidx, potential_second_zero h,
    splitPotential_of_lt (by omega), add_zero, hstep, hi,
    potential_length first ht]

/-- An *unmarked* slot -- split point at the tail -- is the ordinary canonical
ramp.  This is what lets a row mark only the slots that carry an interior chip
and keep the single-ramp ledger everywhere else. -/
@[simp] theorem splitStep_mark_zero (L : ℕ) (first second : ℤ) (k : ℕ) :
    splitStep L 0 first second k = step L second k := by
  rw [splitStep_right (Nat.zero_le k)]
  simp

/-- Below the split point the slope is the first ramp's. -/
theorem splitStep_left (h : SplitRamp L t first second) (hi : i + 1 ≤ t) :
    splitStep L t first second i = step t first i := by
  rcases Nat.lt_or_ge (i + 1) t with hlt | hge
  · exact splitStep_left_of_lt hlt
  · exact splitStep_left_of_succ_eq h (le_antisymm hi hge)

/-! ## The endpoint slopes are the surviving half's own endpoint slopes -/

theorem splitStep_first (h : SplitRamp L t first second) :
    splitStep L t first second 0 =
      if 0 < t then step t first 0 else step L second 0 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · rw [if_neg (by omega), splitStep_right (by omega), ht]
    simp
  · rw [if_pos ht, splitStep_left h (by omega)]

theorem splitStep_last (h : SplitRamp L t first second) (hL : 0 < L) :
    splitStep L t first second (L - 1) =
      if t < L then step (L - t) second (L - 1 - t) else step L first (L - 1) := by
  rcases Nat.lt_or_ge t L with hlt | hge
  · rw [if_pos hlt, splitStep_right (by omega)]
  · have ht : t = L := le_antisymm h.le hge
    subst ht
    rw [if_neg (by omega)]
    exact splitStep_left h (by omega)

/-! ## Convexity away from the split point, and the kink at it -/

theorem splitStep_mono_left (h : SplitRamp L t first second)
    (hij : i ≤ j) (hj : j + 1 ≤ t) :
    splitStep L t first second i ≤ splitStep L t first second j := by
  rw [splitStep_left h (by omega), splitStep_left h hj]
  exact step_mono hij

theorem splitStep_mono_right (hij : i ≤ j) (hi : t ≤ i) :
    splitStep L t first second i ≤ splitStep L t first second j := by
  rw [splitStep_right hi, splitStep_right (by omega)]
  exact step_mono (by omega)

/-- **The kink.**  Across the split point the slope can drop, but by at most
one, provided neither half is steeper than one unit per step and one of the two
is flat.  A divisor with one chip at the split point therefore stays
effective. -/
theorem splitStep_kink_ge_neg_one (h : SplitRamp L t first second)
    (ht : 0 < t) (htL : t < L)
    (hfirstLe : first ≤ (t : ℤ))
    (hsecond : -((L - t : ℕ) : ℤ) ≤ second)
    (hflat : first = 0 ∨ second = 0) :
    -1 ≤ splitStep L t first second t - splitStep L t first second (t - 1) := by
  have hleft : splitStep L t first second (t - 1) = step t first (t - 1) :=
    splitStep_left h (by omega)
  have hright : splitStep L t first second t = step (L - t) second 0 := by
    rw [splitStep_right le_rfl]
    simp
  rw [hleft, hright]
  rcases hflat with hz | hz
  · have hzero : step t first (t - 1) = 0 := by
      rw [hz]
      exact step_zero_of_lt (by omega)
    have hlow : -1 ≤ step (L - t) second 0 := by
      refine lower_le_step_of_mul_le second (-1) (by omega) ?_
      have hcast : (-1 : ℤ) * ((L - t : ℕ) : ℤ) = -((L - t : ℕ) : ℤ) := by ring
      rw [hcast]
      exact hsecond
    omega
  · have hzero : step (L - t) second 0 = 0 := by
      rw [hz]
      exact step_zero_of_lt (by omega)
    have hhigh : step t first (t - 1) ≤ 1 := by
      refine step_le_upper_of_le_mul first 1 ht (by omega) ?_
      simpa using hfirstLe
    omega

/-- Convexity at every interior offset other than the split point.  This is
what the `DegSpec` interior Laplacian consumes; at the split point itself the
residual is paid for by the chip, via `splitStep_kink_ge_neg_one`. -/
theorem splitStep_diff_nonneg_of_ne (h : SplitRamp L t first second)
    (hk : 0 < i) (hne : i ≠ t) :
    0 ≤ splitStep L t first second i - splitStep L t first second (i - 1) := by
  rcases Nat.lt_or_ge i t with hlt | hge
  · have hmono := splitStep_mono_left (L := L) (t := t) (first := first)
      (second := second) h (i := i - 1) (j := i) (by omega) (by omega)
    omega
  · have hgt : t < i := lt_of_le_of_ne hge (fun hEq => hne hEq.symm)
    have hmono := splitStep_mono_right (L := L) (t := t) (first := first)
      (second := second) (i := i - 1) (j := i) (by omega) (by omega)
    omega

end Utilities.Certificate.SubdivisionArithmetic
