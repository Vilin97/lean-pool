/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.UnitConjecture.GardamGroup

namespace LeanPool.Polylean
-- import Mathlib.Algebra.GroupPower.Basic

/-!
## Torsion-freeness of `P`

This file contains a proof that the group `P` defined is in fact torsion-free.

Roughly, the steps are as follows (further details can be found in the corresponding `.md` file):
1. Define a function `sq : P -> K` taking a group element `(q, k)` to its square. This element lies in the kernel as the group `ℤ/2 × ℤ/2` has exponent `2`.
2. Show that elements in `K`, which are integer triples of the form `(a, b, c)`, do not have torsion. This requires the fact that the group `ℤ`, and hence `ℤ³`, is torsion-free.
3. Show that no element of `P` has order precisely `2`. This is an argument by cases on the `Q` part of a general element of `P`.
4. Finally, show that if an element `g : G` of a group `G` satisfies `g ^ n = (1 : G)`, then it also satisfies `(g ^ 2) ^ n = (1 : G)`.
5. Together, these statements show that `P` is torsion-free.
-/

section TorsionFree

/-!
### Torsion-free groups
-/

/-- The definition of a torsion-free group. -/
class TorsionFree (G : Type _) [Group G] where
  /-- A group is *torsion-free* if the only element with non-trivial torsion is the identity element. -/
  torsionFree : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1

/-- The definition of torsion-free additive groups. -/
class AddTorsionFree (A : Type _) [AddGroup A] where
  /-- An additive group is *torsion-free* if the only element with non-trivial torsion is the identity element. -/
  torsionFree : ∀ a : A, ∀ n : ℕ, n.succ • a = 0 → a = 0

/-- ℤ is torsion-free, since it is an integral domain. -/
instance : AddTorsionFree ℤ where
  torsionFree := by
    intro a n (h : n.succ * a = 0)
    cases Int.mul_eq_zero.mp h with
    | inl hyp => injection hyp; contradiction
    | inr _ => assumption

/-- The product of torsion-free additive groups is torsion-free. -/
instance {A B : Type _} [AddGroup A] [AddGroup B] [AddTorsionFree A] [AddTorsionFree B] : AddTorsionFree (A × B) where
  torsionFree := by
    intro (a, b) n
    rw [show n.succ • (a, b) = (n.succ • a, n.succ • b) from rfl, Prod.ext_iff, Prod.ext_iff]
    intro ⟨_, _⟩; refine' ⟨_, _⟩ <;>
      (apply AddTorsionFree.torsionFree; assumption)

end TorsionFree

/-! ### **Step 1:** Defining the square of an element of `P`. -/

/-- The function taking an element of `P` to its square, which lies in the kernel `K`. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def P.sq : P → K
  | ((p, q, r), .e) => (p + p, q + q, r + r)
  | ((_, q, _), .b) => (0, q + q + 1, 0)
  | ((p, _, _), .a) => (p + p + 1, 0, 0)
  | ((_, _, r), .c) => (0, 0, r + r + 1)

open P

/-- A proof that the function `sq` indeed takes an element of `P` to its square in `K`. -/
@[aesop norm apply (rule_sets := [P]), simp]
theorem sq_square : ∀ g : P, g * g = (P.sq g, .e)
  | ((p, q, r), x) =>
    match x with
    | .e | .a | .b | .c => by
      aesop (rule_sets := [P])
      rw [P.mul]
      aesop (rule_sets := [P])

/-! ### **Step 2:** Proving that `K` (= `ℤ³`) is torsion-free. -/

/-- The kernel `ℤ³` is torsion-free. -/
instance K.torsionFree : AddTorsionFree K := inferInstance

/-! ### **Step 3:** Showing that no element of `P` has order precisely two. -/

namespace Int

/-! Some basic lemmas about integers needed to prove facts about `P`. -/

lemma add_twice_eq_mul_two {a : ℤ} : a + a = a * 2 := by
  rw [show (2 : ℤ) = 1 + 1 by rfl, mul_add, mul_one]

attribute [local simp] add_twice_eq_mul_two

/-- No odd integer is zero. -/
lemma odd_ne_zero : ∀ a : ℤ, ¬(a + a + 1 = 0) := by
  intro a h
  have : (a + a + 1) % 2 = 0 % 2 := congrArg (· % 2) h
  simp [Int.add_emod] at this

/-- If the sum of an integer with itself is zero, then the integer is itself zero. -/
lemma zero_of_twice_zero : ∀ a : ℤ, a + a = 0 → a = 0 := by simp

end Int

/-- The only element of `P` with order dividing `2` is the identity. -/
theorem square_free : ∀ {g : P}, g * g = (1 : P) → g = (1 : P)
  | ((p, q, r), x) => by
    match x with
    | .e =>
      intro h
      aesop (rule_sets := [P]) (add norm [Int.zero_of_twice_zero])
      rw [Prod.mk.injEq] at h
      rw [Prod.mk.injEq] at h
      rw [Prod.mk.injEq] at h
      aesop (rule_sets := [P]) (add norm [Int.zero_of_twice_zero])
    | .a | .b | .c =>
      intro h
      aesop (rule_sets := [P]) (add norm [Int.odd_ne_zero])
      all_goals (rw [Prod.mk.injEq] at h; rw [Prod.mk.injEq] at h; rw [Prod.mk.injEq] at h)
      aesop (rule_sets := [P]) (add norm [Int.odd_ne_zero])


/-! ### **Step 4:** Showing that if the `n`-th power of a group element is trivial, then so is that of its square. -/

/-- If `g` is a torsion element of a group, then so is `g ^ 2`. -/
lemma torsion_implies_square_torsion {G : Type _} [Group G] (g : G) (n : ℕ) (g_tor : g ^ n = 1) : (g ^ 2) ^ n = 1 :=
  calc  (g ^ 2) ^ n  = g ^ (2 * n) := by rw [← pow_mul]
              _      = g ^ (n * 2) := by rw [mul_comm]
              _      = (g ^ n) ^ 2 := by rw [pow_mul]
              _      = (1 : G) ^ 2 := by rw [← g_tor]
              _      = (1 : G)     := by rw [one_pow]

/-! ### **Step 5:** Putting the facts together. -/

/-- `P` is torsion-free. -/
instance P.torsionFree : TorsionFree P where
  torsionFree := by
    intros g n g_tor -- assume `g` is a torsion element
    -- then `g ^ 2` is also a torsion element
    have square_tor : (g ^ 2) ^ n.succ = ((0, 0, 0), Q.e) := torsion_implies_square_torsion g n.succ g_tor
    erw [pow_two, sq_square, P.kernel_pow, Prod.mk.injEq] at square_tor
    -- since `g ^ 2 = s g`, we have that `s g` is a torsion element
    have s_tor : n.succ • (sq g) = 0 := square_tor.left
    -- since `s g` lies in the kernel and the kernel is torsion-free, `s g = 0`
    have square_zero : (sq g, Q.e) = (0, Q.e) := congrArg (·, Q.e) (K.torsionFree.torsionFree (sq g) n s_tor)
    rw [← sq_square] at square_zero
    -- this means `g ^ 2 = e`, and also `g = e` because `P` has no order 2 elements
    exact square_free square_zero

end LeanPool.Polylean
