/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization

/-!
# Parabolic fibers are aperiodic in characteristic zero

Finite periodicity of a point does not imply finite order of the ambient rotation matrix.  The
opening therefore needs a point-level argument at normalized traces `2` and `-2`.  The explicit
parabolic-line translations give that argument in characteristic zero.
-/

namespace BGS.Markoff

universe u

variable {K : Type u} [Field K] [CharZero K]

private theorem root_neg_one_ne_zero {i : K} (hi : i ^ 2 = -1) : i ≠ 0 := by
  intro hzero
  subst i
  norm_num at hi

/-- No positive iterate of the trace-`2` rotation fixes a point on either parabolic line in
characteristic zero. -/
theorem iterate_normalizedRotate1_parabolicLineAtTwo_ne_self_of_pos
    (n : ℕ) (hn : 0 < n) (i t : K) (hi : i ^ 2 = -1) :
    (normalizedRotate1^[n]) (parabolicLineAtTwo i t) ≠ parabolicLineAtTwo i t := by
  rw [iterate_normalizedRotate1_parabolicLineAtTwo]
  intro hreturn
  have hparameter := congrArg NormalizedPoint.u2 hreturn
  change t + (n : K) * (2 * i) = t at hparameter
  have hnCast : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have htwo : (2 : K) ≠ 0 := by norm_num
  exact (mul_ne_zero hnCast (mul_ne_zero htwo (root_neg_one_ne_zero hi))) <| by
    linear_combination hparameter

/-- No positive iterate of the trace-`-2` rotation fixes a point on either parabolic line in
characteristic zero. -/
theorem iterate_normalizedRotate1_parabolicLineAtNegTwo_ne_self_of_pos
    (n : ℕ) (hn : 0 < n) (i t : K) (hi : i ^ 2 = -1) :
    (normalizedRotate1^[n]) (parabolicLineAtNegTwo i t) ≠ parabolicLineAtNegTwo i t := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · rw [iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo]
    intro hreturn
    have hparameter := congrArg NormalizedPoint.u2 hreturn
    change t - (k : K) * (4 * i) = t at hparameter
    have hk : 0 < k := by omega
    have hkCast : (k : K) ≠ 0 := by exact_mod_cast hk.ne'
    have hfour : (4 : K) ≠ 0 := by norm_num
    exact (mul_ne_zero hkCast (mul_ne_zero hfour (root_neg_one_ne_zero hi))) <| by
      linear_combination -hparameter
  · rw [iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo]
    intro hreturn
    have hsecond := congrArg NormalizedPoint.u2 hreturn
    have hthird := congrArg NormalizedPoint.u3 hreturn
    change -(t - (k : K) * (4 * i)) + 2 * i = t at hsecond
    change -(-(t - (k : K) * (4 * i)) + 2 * i) + 2 * (-i) = -t + 2 * i at hthird
    rw [hsecond] at hthird
    have hfour : (4 : K) ≠ 0 := by norm_num
    exact (mul_ne_zero hfour (root_neg_one_ne_zero hi)) <| by
      linear_combination -hthird

/-- Every point of the normalized trace-`2` fiber is aperiodic once a square root of `-1` is
fixed. -/
theorem iterate_normalizedRotate1_ne_self_of_mem_fiber1_two
    (i : K) (hi : i ^ 2 = -1) {x : NormalizedPoint K}
    (hx : x ∈ normalizedFiber1 (2 : K)) (n : ℕ) (hn : 0 < n) :
    (normalizedRotate1^[n]) x ≠ x := by
  rw [normalizedFiber1_two_eq_parabolic_lines i hi] at hx
  rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact iterate_normalizedRotate1_parabolicLineAtTwo_ne_self_of_pos n hn i t hi
  · exact iterate_normalizedRotate1_parabolicLineAtTwo_ne_self_of_pos n hn (-i) t <| by
      rw [neg_sq, hi]

/-- Every point of the normalized trace-`-2` fiber is aperiodic once a square root of `-1` is
fixed. -/
theorem iterate_normalizedRotate1_ne_self_of_mem_fiber1_neg_two
    (i : K) (hi : i ^ 2 = -1) {x : NormalizedPoint K}
    (hx : x ∈ normalizedFiber1 (-2 : K)) (n : ℕ) (hn : 0 < n) :
    (normalizedRotate1^[n]) x ≠ x := by
  rw [normalizedFiber1_neg_two_eq_parabolic_lines i hi] at hx
  rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact iterate_normalizedRotate1_parabolicLineAtNegTwo_ne_self_of_pos n hn i t hi
  · exact iterate_normalizedRotate1_parabolicLineAtNegTwo_ne_self_of_pos n hn (-i) t <| by
      rw [neg_sq, hi]

end BGS.Markoff
