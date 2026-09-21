/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions

/-!
# Finiteness for periodic affine inversion sets
-/

namespace Bananas

open Utilities

/-- Iterating the defining affine-period identity by a natural number. -/
theorem IsKAffine.iterate_nat {k : ℕ} {τ : ℤ → ℤ}
    (hAffine : IsKAffine k τ) (x : ℤ) : ∀ n : ℕ,
      τ (x + n * k) = τ x + n * k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      τ (x + (n + 1) * k) = τ ((x + n * k) + k) := by congr 1; ring
      _ = τ (x + n * k) + k := hAffine _
      _ = τ x + (n + 1) * k := by rw [ih]; ring

/-- The affine identity extends to arbitrary integral period shifts. -/
theorem IsKAffine.iterate_int {k : ℕ} {τ : ℤ → ℤ}
    (hAffine : IsKAffine k τ) (x q : ℤ) :
      τ (x + q * k) = τ x + q * k := by
  refine Int.induction_on q (by simp) ?_ ?_
  · intro n ih
    calc
      τ (x + (n + 1) * k) = τ ((x + n * k) + k) := by congr 1 ; ring
      _ = τ (x + n * k) + k := hAffine _
      _ = τ x + (n + 1) * k := by rw [ih]; ring
  · intro n ih
    have hArg : x + (-(n : ℤ)) * k =
        (x + (-(n : ℤ) - 1) * k) + k := by ring
    have hForward := hAffine (x + (-(n : ℤ) - 1) * k)
    have hStep : τ (x + (-(n : ℤ) - 1) * k) =
        τ (x + (-(n : ℤ)) * k) - k := by
      rw [← hArg] at hForward
      omega
    calc
      τ (x + (-((n : ℤ)) - 1) * k) =
          τ (x + (-(n : ℤ)) * k) - k := hStep
      _ = τ x + (-((n : ℤ)) - 1) * k := by rw [ih]; ring

/-- Euclidean residue form, stated in the shape used for affine-period
calculations. -/
theorem int_eq_emod_add_ediv_period {k : ℕ} {b : ℤ} (_hk : 0 < k) :
    b = b % k + k * (b / k) := by
  simpa [add_comm] using (Int.emod_add_mul_ediv b (k : ℤ)).symm

/-- Every residue value is bounded by the finite sum of absolute values of
the values on one period. -/
theorem abs_le_residue_sum (k : ℕ) (τ : ℤ → ℤ) (r : ℕ) (hr : r < k) :
    |τ r| ≤ ∑ i ∈ Finset.range k, |τ i| := by
  exact Finset.single_le_sum (s := Finset.range k) (f := fun i : ℕ => |τ i|)
    (fun i _ => abs_nonneg (τ i)) (by simpa using hr)

/-- The inversion representatives of a positive-period affine function form a
finite set.  The order condition bounds the quotient of the second coordinate,
while the inversion condition bounds it from above. -/
theorem kInversions_finite_of_isKAffine {k : ℕ} {τ : ℤ → ℤ}
    (hk : 0 < k) (hAffine : IsKAffine k τ) :
    (kInversions k τ).Finite := by
  let S : ℤ := ∑ i ∈ Finset.range k, |τ i|
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hkz : 0 < (k : ℤ) := by exact_mod_cast hk
  have hfirst : ∀ x : ℤ, 0 ≤ x → x < k → τ x ≤ S := by
    intro x hx0 hxk
    have hxn : x.toNat < k := by omega
    have habs := abs_le_residue_sum k τ x.toNat hxn
    have hcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    rw [hcast] at habs
    exact (le_abs_self _).trans habs
  have hsecond : ∀ y : ℤ, -S ≤ τ (y % k) := by
    intro y
    have hr0 : 0 ≤ y % (k : ℤ) := Int.emod_nonneg _ (by omega)
    have hrk : y % (k : ℤ) < k := Int.emod_lt_of_pos _ hkz
    have hrn : (y % (k : ℤ)).toNat < k := by omega
    have habs := abs_le_residue_sum k τ (y % (k : ℤ)).toNat hrn
    have hcast : ((y % (k : ℤ)).toNat : ℤ) = y % (k : ℤ) :=
      Int.toNat_of_nonneg hr0
    rw [hcast] at habs
    have hneg : -|τ (y % (k : ℤ))| ≤ τ (y % (k : ℤ)) := neg_abs_le _
    omega
  let B : ℤ := (k : ℤ) - 1 + (k : ℤ) * (2 * S)
  apply Set.Finite.subset
    ((Set.finite_Icc (0 : ℤ) ((k : ℤ) - 1)).prod
      (Set.finite_Icc (1 : ℤ) B))
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hlt, hinv, hx0, hxk⟩
  have htx : τ x ≤ S := hfirst x hx0 hxk
  have hry : -S ≤ τ (y % k) := hsecond y
  have hyrepr : y = y % k + k * (y / k) :=
    int_eq_emod_add_ediv_period hk
  have hyrepr' : y = y % k + (y / k) * k := by
    calc
      y = y % k + k * (y / k) := hyrepr
      _ = y % k + (y / k) * k := by ring
  have htauy : τ y = τ (y % k) + (y / k) * k := by
    calc
      τ y = τ (y % k + (y / k) * k) := congrArg τ hyrepr'
      _ = τ (y % k) + (y / k) * k := hAffine.iterate_int _ _
  have hqmul : (y / k) * (k : ℤ) < 2 * S := by
    change τ x > τ y at hinv
    rw [htauy] at hinv
    omega
  have hq : y / k ≤ 2 * S := by
    by_cases hq0 : y / k ≤ 0
    · omega
    · have hqnonneg : 0 ≤ y / k := by omega
      have hkle : (1 : ℤ) ≤ k := by omega
      have hmul : y / k ≤ (y / k) * k := by
        calc
          y / k = (y / k) * 1 := by ring
          _ ≤ (y / k) * k := Int.mul_le_mul_of_nonneg_left hkle hqnonneg
      omega
  have hrk : y % (k : ℤ) < k := Int.emod_lt_of_pos _ hkz
  have hyupper : y ≤ B := by
    have hprod : (y / k) * (k : ℤ) ≤ (2 * S) * k :=
      Int.mul_le_mul_of_nonneg_right hq (by omega)
    have hprod' : (y / k) * (k : ℤ) ≤ k * (2 * S) := by
      simpa [mul_comm] using hprod
    calc
      y = y % k + (y / k) * k := hyrepr'
      _ ≤ (k : ℤ) - 1 + k * (2 * S) := by omega
      _ = B := rfl
  constructor
  · constructor <;> omega
  · constructor
    · omega
    · exact hyupper

end Bananas
