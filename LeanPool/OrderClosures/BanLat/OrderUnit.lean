/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Disjoint


/-!
# Order units

This file introduces the two standard notions of order unit in a vector
lattice. A **weak order unit** is a non-negative element disjoint only from
zero, while a **strong order unit** is a non-negative element which dominates
every other element up to a positive scalar multiple. Every strong order unit
is a weak order unit.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- An element `e` of a vector lattice is a **weak order unit** if it is
non-negative and the only element disjoint from `e` is `0`. -/
def WeakOrderUnit (e : X) : Prop :=
  0 ≤ e ∧ ∀ x : X, IsVLDisjoint x e → x = 0

/-- An element `e` of a vector lattice is a **strong order unit** if it is
non-negative and every element of `X` is dominated, in absolute value, by some
non-negative real multiple of `e`. -/
def StrongOrderUnit (e : X) : Prop :=
  0 ≤ e ∧ ∀ x : X, ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • e

/-- For a non-negative element `e`, disjointness from `e` implies disjointness
from every natural scalar multiple of `e`. -/
private lemma abs_inf_natCast_smul_eq_zero {x e : X} (he : 0 ≤ e)
    (hxe : |x| ⊓ e = 0) : ∀ k : ℕ, |x| ⊓ ((k : ℝ) • e) = 0
  | 0 => by simp
  | k + 1 => by
      have ih := abs_inf_natCast_smul_eq_zero he hxe k
      have hke : 0 ≤ ((k : ℝ) • e) :=
        smul_nonneg (Nat.cast_nonneg k) he
      have hsucc : ((k + 1 : ℕ) : ℝ) • e = (k : ℝ) • e + e := by
        push_cast; rw [add_smul, one_smul]
      rw [hsucc]
      refine le_antisymm ?_
        (le_inf (abs_nonneg _) (add_nonneg hke he))
      calc |x| ⊓ ((k : ℝ) • e + e)
          ≤ |x| ⊓ ((k : ℝ) • e) + |x| ⊓ e :=
            inf_le_inf_add_inf_of_nonneg |x| ((k : ℝ) • e) e (abs_nonneg x) hke he
        _ = 0 := by rw [ih, hxe, add_zero]

/-- Every strong order unit is a weak order unit. -/
theorem WeakOrderUnit.of_strongOrderUnit {e : X} (he : StrongOrderUnit e) :
    WeakOrderUnit e := by
  refine ⟨he.1, fun x hxe => ?_⟩
  rw [IsVLDisjoint, abs_of_nonneg he.1] at hxe
  obtain ⟨c, hc, hxc⟩ := he.2 x
  obtain ⟨n, hn⟩ := exists_nat_ge c
  have hxn : |x| ≤ (n : ℝ) • e :=
    hxc.trans (smul_le_smul_of_nonneg_right hn he.1)
  have hkey := abs_inf_natCast_smul_eq_zero he.1 hxe n
  have habs : |x| = 0 := by rw [← inf_eq_left.mpr hxn, hkey]
  exact (abs_eq_zero_iff_zero x).mp habs
