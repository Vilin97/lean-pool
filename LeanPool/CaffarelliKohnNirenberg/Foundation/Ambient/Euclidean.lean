/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Positivity

/-!
# Euclidean functions on the native ambient carrier

`Space` is a reducible abbreviation of the existing `CKN.Vec 3` carrier, so
all native-space statements use the same type as the Sobolev interfaces. The
body of `spaceEuclideanNorm` is kept definitionally identical to the
finite-sum expression used by the parabolic spatial norm.
-/

@[expose] public section

namespace CKN

/-- The native three-dimensional carrier, definitionally equal to `Vec 3`. -/
abbrev Space := Vec 3

/-- The Euclidean length given by the finite sum of coordinate squares. -/
noncomputable def spaceEuclideanNorm (x : Space) : ℝ := Real.sqrt (∑ k, x k ^ 2)

theorem space_norm_le_euclideanNorm (x : Space) :
    ‖x‖ ≤ spaceEuclideanNorm x := by
  change ‖x‖ ≤ Real.sqrt (∑ k, x k ^ 2)
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro k
  have hk : (x k) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (x j) ^ 2)
      (fun j hj => sq_nonneg (x j)) (Finset.mem_univ k)
  have hsum : 0 ≤ ∑ j, (x j) ^ 2 :=
    Finset.sum_nonneg fun j hj => sq_nonneg (x j)
  have hsq := Real.sq_sqrt hsum
  have hsqrt := Real.sqrt_nonneg (∑ j, (x j) ^ 2)
  have habs : |x k| ≤ Real.sqrt (∑ j, (x j) ^ 2) := by
    exact abs_le_of_sq_le_sq (by simpa only [hsq] using hk) hsqrt
    
  simpa only [Real.norm_eq_abs] using
    habs

theorem euclideanNorm_le_three_mul_space_norm (x : Space) :
    spaceEuclideanNorm x ≤ 3 * ‖x‖ := by
  have hsum : (∑ k, x k ^ 2) ≤ 3 * ‖x‖ ^ 2 := by
    calc
      ∑ k, x k ^ 2 ≤ ∑ k, ‖x‖ ^ 2 := by
        exact Finset.sum_le_sum fun k hk => by
          have hk' := norm_le_pi_norm x k
          have hk'' : |x k| ≤ ‖x‖ := by
            simpa only [Real.norm_eq_abs] using hk'
          have hsq : (x k) ^ 2 ≤ ‖x‖ ^ 2 := by
            apply (sq_le_sq).2
            simpa only [abs_of_nonneg (norm_nonneg x)] using hk''
          simpa only [pow_two] using hsq
      _ = 3 * ‖x‖ ^ 2 := by simp
  change Real.sqrt (∑ k, x k ^ 2) ≤ 3 * ‖x‖
  have hsum_nonneg : 0 ≤ ∑ k, x k ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg (x k)
  have hsq := Real.sq_sqrt hsum_nonneg
  have hsqrt := Real.sqrt_nonneg (∑ k, x k ^ 2)
  have hnorm := norm_nonneg x
  apply le_of_sq_le_sq _ (by positivity)
  calc
    Real.sqrt (∑ k, x k ^ 2) ^ 2 = ∑ k, x k ^ 2 := hsq
    _ ≤ 3 * ‖x‖ ^ 2 := hsum
    _ ≤ (3 * ‖x‖) ^ 2 := by nlinarith only [sq_nonneg ‖x‖]

end CKN
