/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic

/-!
# Integer interpolation along a subdivided edge

This file isolates the arithmetic needed to turn integral endpoint potentials
into a convex integral potential on a path.  It deliberately contains no graph
construction.

For a positive length `L` and an integral rise `T`, write

`T = q * L + r`, with `0 <= r < L`.

The potential below has slope `q` for the first `L - r` unit steps and slope
`q + 1` for the final `r` steps.  Thus it has endpoint values `0` and `T`, and
its slopes are nondecreasing.  The sign convention is chosen for the future
chip-firing application: at an interior path vertex, `prin` will be the next
slope minus the previous slope.
-/

namespace Utilities.Certificate.SubdivisionArithmetic

/-- The lower of the two slopes used to realize rise `T` over length `L`. -/
def quotient (L : ℕ) (T : ℤ) : ℤ :=
  T / (L : ℤ)

/-- The number of final steps on which the slope is `quotient L T + 1`. -/
def remainder (L : ℕ) (T : ℤ) : ℤ :=
  T % (L : ℤ)

/-- The integral offset at which the slope changes from `q` to `q + 1`. -/
def bend (L : ℕ) (T : ℤ) : ℤ :=
  (L : ℤ) - remainder L T

/-- The two-slope potential at integral offset `i` from the tail endpoint. -/
def potential (L : ℕ) (T : ℤ) (i : ℕ) : ℤ :=
  quotient L T * (i : ℤ) + max 0 ((i : ℤ) - bend L T)

/-- The slope on the unit step from offset `i` to offset `i + 1`. -/
def step (L : ℕ) (T : ℤ) (i : ℕ) : ℤ :=
  potential L T (i + 1) - potential L T i

/-- The canonical unit slopes telescope to the difference of the endpoint
values.  Unlike `potential_length`, this identity is also meaningful at
length zero. -/
theorem sum_steps (L : ℕ) (T : ℤ) :
    ∑ i ∈ Finset.range L, step L T i =
      potential L T L - potential L T 0 := by
  simpa only [step] using Finset.sum_range_sub (potential L T) L

theorem remainder_nonneg {L : ℕ} (T : ℤ) (hL : 0 < L) :
    0 ≤ remainder L T := by
  apply Int.emod_nonneg
  exact_mod_cast hL.ne'

theorem remainder_lt {L : ℕ} (T : ℤ) (hL : 0 < L) :
    remainder L T < (L : ℤ) := by
  apply Int.emod_lt_of_pos
  exact_mod_cast hL

theorem bend_pos {L : ℕ} (T : ℤ) (hL : 0 < L) :
    0 < bend L T := by
  have hr := remainder_lt T hL
  simp only [bend]
  omega

theorem bend_le_length {L : ℕ} (T : ℤ) (hL : 0 < L) :
    bend L T ≤ (L : ℤ) := by
  have hr := remainder_nonneg T hL
  simp only [bend]
  omega

/-- The potential is normalized to zero at the tail endpoint. -/
@[simp] theorem potential_zero {L : ℕ} (T : ℤ) (hL : 0 < L) :
    potential L T 0 = 0 := by
  have hb : 0 < bend L T := bend_pos T hL
  simp only [potential, Nat.cast_zero, mul_zero, zero_add]
  rw [max_eq_left]
  omega

/-- The potential realizes the prescribed rise at the head endpoint. -/
@[simp] theorem potential_length {L : ℕ} (T : ℤ) (hL : 0 < L) :
    potential L T L = T := by
  have hr : 0 ≤ remainder L T := remainder_nonneg T hL
  rw [potential, max_eq_right]
  · simpa [quotient, remainder, bend, sub_sub_cancel, Int.mul_comm] using
      Int.mul_ediv_add_emod T (L : ℤ)
  · simp only [bend]
    omega

/-- On a nonempty block, the canonical unit slopes realize its declared
rise.  This is the telescoping fact used when concatenating piecewise blocks.
-/
theorem sum_steps_eq_rise {L : ℕ} (T : ℤ) (hL : 0 < L) :
    ∑ i ∈ Finset.range L, step L T i = T := by
  rw [sum_steps, potential_length T hL, potential_zero T hL, sub_zero]

/-- Before the bend, the unit-step slope is exactly the quotient `q`. -/
theorem step_eq_quotient_of_succ_le_bend {L i : ℕ} {T : ℤ}
    (hi : ((i + 1 : ℕ) : ℤ) ≤ bend L T) :
    step L T i = quotient L T := by
  have hi' : (i : ℤ) ≤ bend L T := by omega
  simp only [step, potential]
  rw [max_eq_left (sub_nonpos.mpr hi),
      max_eq_left (sub_nonpos.mpr hi')]
  push_cast
  ring

/-- At and after the bend, the unit-step slope is `q + 1`. -/
theorem step_eq_quotient_add_one_of_bend_le {L i : ℕ} {T : ℤ}
    (hi : bend L T ≤ (i : ℤ)) :
    step L T i = quotient L T + 1 := by
  have hi' : bend L T ≤ ((i + 1 : ℕ) : ℤ) := by omega
  simp only [step, potential]
  rw [max_eq_right (sub_nonneg.mpr hi'),
      max_eq_right (sub_nonneg.mpr hi)]
  push_cast
  ring

/-- Every unit-step slope is one of the two consecutive integers `q`, `q+1`. -/
theorem step_eq_quotient_or_add_one (L i : ℕ) (T : ℤ) :
    step L T i = quotient L T ∨
      step L T i = quotient L T + 1 := by
  by_cases hi : ((i + 1 : ℕ) : ℤ) ≤ bend L T
  · exact Or.inl (step_eq_quotient_of_succ_le_bend hi)
  · exact Or.inr (step_eq_quotient_add_one_of_bend_le (by omega))

/-- The two-slope sequence is nondecreasing. -/
theorem step_mono {L i j : ℕ} {T : ℤ} (hij : i ≤ j) :
    step L T i ≤ step L T j := by
  by_cases hi : bend L T ≤ (i : ℤ)
  · have hij' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    have hj : bend L T ≤ (j : ℤ) := le_trans hi hij'
    rw [step_eq_quotient_add_one_of_bend_le hi,
        step_eq_quotient_add_one_of_bend_le hj]
  · have hi' : ((i + 1 : ℕ) : ℤ) ≤ bend L T := by omega
    rw [step_eq_quotient_of_succ_le_bend hi']
    rcases step_eq_quotient_or_add_one L j T with hj | hj <;> omega

/-- A canonical unit slope is at least any declared lower endpoint bound
whose total rise is feasible.  This is the W2 arithmetic bridge used when a
piecewise block contributes the outgoing slope at a merged boundary. -/
theorem lower_le_step_of_mul_le {L i : ℕ} (rise lo : ℤ) (hL : 0 < L)
    (hLower : lo * (L : ℤ) ≤ rise) :
    lo ≤ step L rise i := by
  have hLZ : 0 < (L : ℤ) := by exact_mod_cast hL
  have hQuot : lo ≤ quotient L rise :=
    (Int.le_ediv_iff_mul_le hLZ).mpr (by
      simpa [quotient, Int.mul_comm] using hLower)
  rcases step_eq_quotient_or_add_one L i rise with hStep | hStep
  · rw [hStep]
    exact hQuot
  · rw [hStep]
    omega

/-- A canonical unit slope is at most any declared upper endpoint bound
whose total rise is feasible.  The strict case uses the quotient bound; at
equality the Euclidean remainder vanishes, so every genuine unit step is the
quotient itself. -/
theorem step_le_upper_of_le_mul {L i : ℕ} (rise hi : ℤ) (hL : 0 < L)
    (hiStep : i < L) (hUpper : rise ≤ hi * (L : ℤ)) :
    step L rise i ≤ hi := by
  have hLZ : 0 < (L : ℤ) := by exact_mod_cast hL
  have hQuotLe : quotient L rise ≤ hi :=
    (Int.ediv_le_iff_le_mul hLZ).mpr (by omega)
  by_cases hStrict : rise < hi * (L : ℤ)
  · have hQuotLt : quotient L rise < hi :=
      (Int.ediv_lt_iff_lt_mul hLZ).mpr (by
        simpa [quotient, Int.mul_comm] using hStrict)
    rcases step_eq_quotient_or_add_one L i rise with hStep | hStep
    · rw [hStep]
      omega
    · rw [hStep]
      omega
  · have hEq : rise = hi * (L : ℤ) := by omega
    have hRem : remainder L rise = 0 := by
      rw [hEq]
      simp [remainder]
    rw [step_eq_quotient_of_succ_le_bend]
    · exact hQuotLe
    · rw [bend, hRem]
      simp only [sub_zero]
      exact_mod_cast (Nat.succ_le_iff.mpr hiStep)

/-- Convexity in the form needed at an interior path vertex: the next slope
minus the previous slope is nonnegative.  Offset `i + 1` is interior whenever
`i + 1 < L`; the inequality itself holds without that extra restriction. -/
theorem secondDifference_nonneg (L i : ℕ) (T : ℤ) :
    0 ≤ potential L T i - 2 * potential L T (i + 1) +
      potential L T (i + 2) := by
  have hmono : step L T i ≤ step L T (i + 1) :=
    step_mono (Nat.le_succ i)
  have hmono' :
      potential L T (i + 1) - potential L T i ≤
        potential L T (i + 2) - potential L T (i + 1) := by
    simpa [step, Nat.add_assoc] using hmono
  omega

/-- Centered form of `secondDifference_nonneg`, ready to identify with
`prin` at a positive interior offset. -/
theorem interiorSecondDifference_nonneg {L i : ℕ} (T : ℤ) (hi : 0 < i) :
    0 ≤ potential L T (i - 1) - 2 * potential L T i +
      potential L T (i + 1) := by
  have hOne : i - 1 + 1 = i := by omega
  have hTwo : i - 1 + 2 = i + 1 := by omega
  simpa only [hOne, hTwo] using secondDifference_nonneg L (i - 1) T

/-- The first slope is the Euclidean quotient. -/
theorem firstStep_eq_quotient {L : ℕ} (T : ℤ) (hL : 0 < L) :
    step L T 0 = quotient L T := by
  apply step_eq_quotient_of_succ_le_bend
  have hb := bend_pos T hL
  norm_num
  omega

/-- The final slope is `q` when the rise is divisible by the length and
`q + 1` otherwise. -/
theorem lastStep_eq_ite {L : ℕ} (T : ℤ) (hL : 0 < L) :
    step L T (L - 1) =
      if remainder L T = 0 then quotient L T else quotient L T + 1 := by
  split_ifs with hr
  · apply step_eq_quotient_of_succ_le_bend
    simp only [bend, hr, sub_zero]
    omega
  · apply step_eq_quotient_add_one_of_bend_le
    have hr0 := remainder_nonneg T hL
    have hrpos : 0 < remainder L T := lt_of_le_of_ne hr0 (Ne.symm hr)
    simp only [bend]
    omega

/-- Equivalently, the final slope is the ceiling of `T / L`, expressed using
integer Euclidean division and no rational arithmetic. -/
theorem lastStep_eq_neg_ediv_neg {L : ℕ} (T : ℤ) (hL : 0 < L) :
    step L T (L - 1) = -((-T) / (L : ℤ)) := by
  rw [lastStep_eq_ite T hL, Int.neg_ediv]
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  rw [Int.sign_eq_one_of_pos hLz]
  simp only [quotient, remainder]
  by_cases hdvd : (L : ℤ) ∣ T
  · have hmod : T % (L : ℤ) = 0 := Int.emod_eq_zero_of_dvd hdvd
    simp [hdvd, hmod]
  · have hmod : T % (L : ℤ) ≠ 0 := by
      rwa [Int.dvd_iff_emod_eq_zero] at hdvd
    simp [hdvd, hmod, Int.add_comm]

/-- Lower bounds on the two outgoing endpoint slopes follow from the
homogeneous rise bounds used by local subdivision certificates. -/
theorem endpointSlopeBounds {L : ℕ} (T alpha beta : ℤ) (hL : 0 < L)
    (hlower : alpha * (L : ℤ) ≤ T)
    (hupper : T ≤ -beta * (L : ℤ)) :
    alpha ≤ step L T 0 ∧
      beta ≤ -step L T (L - 1) := by
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  constructor
  · rw [firstStep_eq_quotient T hL, quotient]
    exact (Int.le_ediv_iff_mul_le hLz).2 hlower
  · rw [lastStep_eq_neg_ediv_neg T hL, neg_neg]
    apply (Int.le_ediv_iff_mul_le hLz).2
    calc
      beta * (L : ℤ) = -(-beta * (L : ℤ)) := by ring
      _ ≤ -T := neg_le_neg hupper

/-! ## Closed arithmetic regressions -/

/-- A negative, nondivisible rise uses the floor quotient first and the next
integer on the remaining steps. -/
theorem negativeNondivisible_steps :
    step 3 (-1) 0 = -1 ∧ step 3 (-1) 1 = 0 ∧
      step 3 (-1) 2 = 0 := by
  norm_num [step, potential, quotient, remainder, bend]

/-- A negative rise divisible by the path length has constant slope. -/
theorem negativeDivisible_steps :
    step 3 (-6) 0 = -2 ∧ step 3 (-6) 1 = -2 ∧
      step 3 (-6) 2 = -2 := by
  norm_num [step, potential, quotient, remainder, bend]

/-- On a path of length one, the unique step realizes every integral rise. -/
theorem lengthOne_step (T : ℤ) :
    step 1 T 0 = T := by
  calc
    step 1 T 0 = potential 1 T 1 - potential 1 T 0 := rfl
    _ = T - 0 := by
      rw [potential_length T (by norm_num), potential_zero T (by norm_num)]
    _ = T := sub_zero T

/-- A path with equal endpoint potentials has zero slope on each of its
actual unit steps. -/
theorem step_zero_of_lt {L i : ℕ} (hi : i < L) :
    step L 0 i = 0 := by
  have hsucc : (i : ℤ) + 1 ≤ (L : ℤ) := by exact_mod_cast hi
  have hle : i ≤ L := Nat.le_of_lt hi
  simp [step, potential, quotient, remainder, bend,
    sub_nonpos.mpr hsucc, hle]

/-! ## A truncated negative ramp

The loop lemma needs the potential of rise `-k` along a path of length `L`,
where `0 < k ≤ L`.  It falls with slope `-1` for exactly `k` steps and is
constant afterwards.  Thus it places one unit of Laplacian at distance `k`
from the zero endpoint (unless that point is the far endpoint).
-/

/-- Euclidean division of `-k` by a positive `L`, for `0 < k ≤ L`. -/
theorem quotient_neg_eq_neg_one {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    quotient L (-(k : ℤ)) = -1 := by
  have hL : 0 < L := lt_of_lt_of_le hk hkL
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  have hDivision :
      (-(k : ℤ)) / (L : ℤ) = -1 ∧
        (-(k : ℤ)) % (L : ℤ) = (L : ℤ) - (k : ℤ) := by
    apply (Int.ediv_emod_unique'' (by exact_mod_cast hL.ne')).2
    constructor
    · ring
    constructor
    · omega
    · rw [abs_of_pos hLz]
      omega
  exact hDivision.1

/-- The complementary remainder in the same negative division. -/
theorem remainder_neg_eq_sub {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    remainder L (-(k : ℤ)) = (L : ℤ) - (k : ℤ) := by
  have hL : 0 < L := lt_of_lt_of_le hk hkL
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  have hDivision :
      (-(k : ℤ)) / (L : ℤ) = -1 ∧
        (-(k : ℤ)) % (L : ℤ) = (L : ℤ) - (k : ℤ) := by
    apply (Int.ediv_emod_unique'' (by exact_mod_cast hL.ne')).2
    constructor
    · ring
    constructor
    · omega
    · rw [abs_of_pos hLz]
      omega
  exact hDivision.2

/-- The unique bend of the truncated negative ramp is at offset `k`. -/
theorem bend_neg_eq {L k : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    bend L (-(k : ℤ)) = (k : ℤ) := by
  rw [bend, remainder_neg_eq_sub hk hkL]
  ring

/-- The truncated negative ramp has slope `-1` before `k` and zero from `k`
onwards. -/
theorem step_neg_eq_ite {L k i : ℕ} (hk : 0 < k) (hkL : k ≤ L) :
    step L (-(k : ℤ)) i = if i < k then -1 else 0 := by
  split_ifs with hik
  · rw [step_eq_quotient_of_succ_le_bend]
    · exact quotient_neg_eq_neg_one hk hkL
    · rw [bend_neg_eq hk hkL]
      exact_mod_cast hik
  · rw [step_eq_quotient_add_one_of_bend_le]
    · rw [quotient_neg_eq_neg_one hk hkL]
      omega
    · rw [bend_neg_eq hk hkL]
      exact_mod_cast Nat.le_of_not_gt hik

end Utilities.Certificate.SubdivisionArithmetic
