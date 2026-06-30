/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic.Ring

/-!
# Exercise 4.21 (Scott 1981, PRG-19, Lecture IV) — `≤` as a unique fixed point;
addition & multiplication

Scott asks to show that the **less-than-or-equal-to relation** `ℓ ⊆ ℕ × ℕ` is
*uniquely* determined
by the fixed-point equation

  `ℓ = {(n, n) ∣ n ∈ ℕ} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}`.

Working in the power-set domain `P(ℕ × ℕ)` (a complete lattice, Exercise 4.14),
the right-hand side
is a monotone operator `leOp`. We show:

* `leRel = {(n, m) ∣ n ≤ m}` solves the equation (`leRel_isFixed`);
* the solution is **unique** (`leOp_unique`): for *any* fixed point `u` one
proves, by induction on
  the second coordinate, that `(n, m) ∈ u ↔ n ≤ m`. (Unlike a general
  least-fixed-point situation,
  here the equation pins the relation down completely, because the clause `(n,
  m⁺)` never produces a
  pair with second coordinate `0`.)

Scott then considers `⟨P ℕ, ℕ, ⁺⟩` with `x⁺ = {n⁺ ∣ n ∈ x}` and the **unique
function**
`[·] : ℕ → P ℕ` of 4.13(3) determined by `[0] = ℕ` and `[m⁺] = [m]⁺`. We identify
it as the up-set
`[m] = {k ∣ m ≤ k}` (`upSet`), with `upSet_zero`/`upSet_succ` the two recursion
equations and
`upSet_unique` their uniqueness (4.13(3)).

The structures `⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` are **uniquely isomorphic** via `n ↦
m + n`
(`addIso`), connecting the isomorphism with **ordinary addition**
(`addIso_apply`): the unique
structure-preserving bijection sends `n` to `m + n`.

Finally, **multiplication**: the hint equation `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}`
has, as its least
solution in `P ℕ`, exactly the set of multiples of `n` (`mulOp_lfp_eq_multiples`).

All set-level constructions are **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`).
-/

namespace Domain.Neighborhood.Exercise421

open Domain.Neighborhood.Exercise414

/-! ### The order relation as a unique fixed point. -/

/-- Scott's operator `ℓ ↦ {(n, n)} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}` on `P(ℕ × ℕ)`. -/
def leOp (u : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | p.1 = p.2} ∪ {p | ∃ m, (p.1, m) ∈ u ∧ p.2 = m + 1}

theorem leOp_monotone : Monotone leOp := by
  intro u v huv p hp
  rcases hp with hp | ⟨m, hm, hpm⟩
  · exact Or.inl hp
  · exact Or.inr ⟨m, huv hm, hpm⟩

/-- The relation `≤` itself, as a subset of `ℕ × ℕ`. -/
def leRel : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

/-- **Exercise 4.21 (Scott 1981, PRG-19).** `≤` solves Scott's fixed-point
equation. -/
theorem leRel_isFixed : leOp leRel = leRel := by
  apply Set.Subset.antisymm
  · rintro ⟨n, m⟩ (h | ⟨k, hk, rfl⟩)
    · exact le_of_eq (h : n = m)
    · exact Nat.le_succ_of_le (hk : n ≤ k)
  · rintro ⟨n, m⟩ (h : n ≤ m)
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨m - 1, ?_, ?_⟩
      · change n ≤ m - 1; omega
      · omega

/-- The key step toward uniqueness: any fixed point `u` of `leOp` agrees with `≤`
pointwise.
By induction on the second coordinate `m`; the base case `m = 0` uses that the
successor clause
cannot produce a `0` on the right. -/
theorem mem_fixedPoint_iff {u : Set (ℕ × ℕ)} (hu : leOp u = u) (n m : ℕ) :
    (n, m) ∈ u ↔ n ≤ m := by
  induction m with
  | zero =>
    rw [← hu]
    constructor
    · rintro (h | ⟨k, _, hk⟩)
      · exact le_of_eq h
      · exact absurd hk (Nat.succ_ne_zero k).symm
    · intro h
      exact Or.inl (Nat.le_zero.mp h)
  | succ k ih =>
    rw [← hu]
    constructor
    · rintro (h | ⟨j, hj, hjk⟩)
      · exact le_of_eq h
      · have hjk' : j = k := by omega
        subst hjk'
        exact Nat.le_succ_of_le (ih.mp hj)
    · intro h
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨k, ih.mpr (Nat.lt_succ_iff.mp h'), rfl⟩

/-- **Exercise 4.21 (Scott 1981, PRG-19).** The order relation `≤` is the
**unique** fixed point of
Scott's equation: any `u` with `leOp u = u` equals `leRel`. -/
theorem leOp_unique {u : Set (ℕ × ℕ)} (hu : leOp u = u) : u = leRel := by
  ext ⟨n, m⟩
  rw [mem_fixedPoint_iff hu]
  rfl

/-! ### The function `[·] : ℕ → P ℕ` of 4.13(3): the up-sets. -/

/-- Scott's `x⁺ = {n⁺ ∣ n ∈ x}` on `P ℕ`. -/
def succImage (x : Set ℕ) : Set ℕ := {k | ∃ j ∈ x, k = j + 1}

/-- The up-set `[m] = {k ∣ m ≤ k}` — the value of Scott's unique function `[·]` of
4.13(3). -/
def upSet (m : ℕ) : Set ℕ := {k | m ≤ k}

/-- `[0] = ℕ`: the recursion base of 4.13(3). -/
theorem upSet_zero : upSet 0 = Set.univ := by
  ext k; simp [upSet]

/-- `[m⁺] = [m]⁺`: the recursion step of 4.13(3). -/
theorem upSet_succ (m : ℕ) : upSet (m + 1) = succImage (upSet m) := by
  ext k
  simp only [upSet, succImage, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

/-- **Exercise 4.21 / 4.13(3) (Scott 1981, PRG-19).** `[·] = upSet` is the
*unique* function with
`[0] = ℕ` and `[m⁺] = [m]⁺`. -/
theorem upSet_unique (s : ℕ → Set ℕ) (h0 : s 0 = Set.univ)
    (hsucc : ∀ m, s (m + 1) = succImage (s m)) : s = upSet := by
  funext m
  induction m with
  | zero => rw [h0, upSet_zero]
  | succ k ih => rw [hsucc k, ih, upSet_succ]

/-! ### The isomorphism `⟨ℕ, 0, ⁺⟩ ≅ ⟨[m], m, ⁺⟩` is addition. -/

/-- **Exercise 4.21 (Scott 1981, PRG-19).** The structure-preserving bijection
between
`⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` (where `[m] = {k ∣ m ≤ k}`, with distinguished
element `m` and the
successor `⁺`). It is **ordinary addition** by `m`: `n ↦ m + n`. -/
def addIso (m : ℕ) : ℕ ≃ {k : ℕ // k ∈ upSet m} where
  toFun n := ⟨m + n, Nat.le_add_right m n⟩
  invFun k := k.1 - m
  left_inv n := by change m + n - m = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    have : m ≤ k := hk
    simp only [Subtype.mk.injEq]
    omega

/-- The isomorphism is given by addition: `addIso m n = m + n`. -/
theorem addIso_apply (m n : ℕ) : (addIso m n : ℕ) = m + n := rfl

/-- The isomorphism sends `0` to the distinguished element `m` of `[m]`. -/
theorem addIso_zero (m : ℕ) : (addIso m 0 : ℕ) = m := by simp [addIso]

/-- The isomorphism preserves the successor: `addIso m (n⁺) = (addIso m n)⁺`. -/
theorem addIso_succ (m n : ℕ) : (addIso m (n + 1) : ℕ) = (addIso m n : ℕ) + 1 := by
  simp only [addIso_apply]; omega

/-! ### Multiplication via the hint fixed-point equation. -/

/-- Scott's hint operator `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` on `P ℕ` (for fixed
`n`). -/
def mulOp (n : ℕ) (u : Set ℕ) : Set ℕ := {0} ∪ {k | ∃ m ∈ u, k = n + m}

theorem mulOp_monotone (n : ℕ) : Monotone (mulOp n) := by
  rintro u v huv k (hk | ⟨m, hm, rfl⟩)
  · exact Or.inl hk
  · exact Or.inr ⟨m, huv hm, rfl⟩

/-- **Exercise 4.21 (Scott 1981, PRG-19).** The least solution of the
multiplication equation
`n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` is exactly the set of **multiples of `n`**. -/
theorem mulOp_lfp_eq_multiples (n : ℕ) :
    lfpSet (mulOp n) = {k | ∃ i, k = n * i} := by
  apply Set.Subset.antisymm
  · -- `lfpSet ⊆ multiples`: the multiples form a pre-fixed point.
    have hpre : mulOp n {k | ∃ i, k = n * i} ⊆ {k | ∃ i, k = n * i} := by
      rintro k (rfl | ⟨m, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by ring⟩
    exact lfpSet_subset (mulOp n) hpre
  · -- `multiples ⊆ lfpSet`: each `n * i` is reached by induction on `i`.
    have hfix : mulOp n (lfpSet (mulOp n)) = lfpSet (mulOp n) :=
      lfpSet_isFixed (mulOp n) (mulOp_monotone n)
    rintro k ⟨i, rfl⟩
    induction i with
    | zero =>
      rw [← hfix]; exact Or.inl (by simp)
    | succ j ih =>
      rw [← hfix]
      exact Or.inr ⟨n * j, ih, by ring⟩

end Domain.Neighborhood.Exercise421
