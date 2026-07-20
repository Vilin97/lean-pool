/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Hom.Set
import Mathlib.Data.Set.Image
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# Exercise 5.13 (Scott 1981, PRG-19, Lecture V) — a one-one pairing `num : N × N →
N`

> Prove the existence of a one-one function `num : ℕ × ℕ → ℕ` such that
>
> * `num(0, 0) = 0`,
> * `num(n, m+1) = num(n+1, m) + 1`,
> * `num(n+1, 0) = num(0, n) + 1`.
>
> Draw a picture (an infinite matrix) for the function and find a closed form for
its values.
> Use the function to prove the isomorphism of the domains `P N`, `P(N × N)`, `P N
× P N`.

## The picture

Reading `n` down the rows and `m` across the columns, the three recurrences walk
the **anti-diagonals**
`n + m = const`, climbing one step (`+1`) each move and jumping to the start of
the next diagonal at
the left edge:

```
        m=0   m=1   m=2   m=3
n=0      0     2     5     9
n=1      1     4     8
n=2      3     7
n=3      6
```

## The closed form

On the anti-diagonal `s = n + m` the values run `T(s), T(s)+1, …, T(s)+s` where
`T(s) = s(s+1)/2`
is the `s`-th triangular number; the offset within the diagonal is exactly `m`.
Hence

  `num n m = (n + m) * (n + m + 1) / 2 + m`

— the **Cantor pairing function**. We take this as the definition (`num`), verify
Scott's three
recurrences (`num_zero_zero`, `num_succ_right`, `num_succ_left`), and prove it is
one-one
(`num_injective`). In fact it is a *bijection*: we build a choice-free inverse
`unnum` (iterate the
diagonal walk `nextCell` from `(0,0)`) and package the bijection as `numEquiv : ℕ
× ℕ ≃ ℕ`.

## The domain isomorphisms

Following Exercise 4.17, the power-set domain `P A` is modelled by the complete
lattice `(Set A, ⊆)`.
Order-isomorphisms of these domains are then induced by bijections of the index
types
(`setCongr`). Since `ℕ × ℕ ≃ ℕ` (via `numEquiv`) and `ℕ ⊕ ℕ ≃ ℕ` (Mathlib's
`Equiv.natSumNatEquivNat`), all three domains are isomorphic:

  `P N ≅ P(N × N)`            (`pnOrderIsoPNN`),
  `P N ≅ P N × P N`          (`pnOrderIsoProd`),
  `P(N × N) ≅ P N × P N`     (`pnnOrderIsoProd`).

Everything (including `numEquiv` and the order-isomorphisms) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood.Exercise513

/-! ### Triangular numbers -/

/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `k(k+1)` is even (choice-free, by induction). -/
theorem two_dvd_mul_succ (k : ℕ) : 2 ∣ k * (k + 1) := by
  induction k with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + (n + 1), ?_⟩
      have hexp : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [hexp, hc]; ring

/-- The defining doubling identity `2·T(k) = k(k+1)` — the division is exact
because `k(k+1)` is
even. -/
theorem tri_mul_two (k : ℕ) : tri k * 2 = k * (k + 1) := by
  unfold tri
  exact Nat.div_mul_cancel (two_dvd_mul_succ k)

/-- The triangular recurrence `T(k+1) = T(k) + (k+1)`. -/
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have e1 : tri k * 2 = k * (k + 1) := tri_mul_two k
  have e2 : tri (k + 1) * 2 = (k + 1) * (k + 1 + 1) := tri_mul_two (k + 1)
  have key : tri (k + 1) * 2 = (tri k + (k + 1)) * 2 := by
    have hexp : (tri k + (k + 1)) * 2 = tri k * 2 + (k + 1) * 2 := by ring
    rw [hexp, e1, e2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key

theorem tri_le_succ (k : ℕ) : tri k ≤ tri (k + 1) := by
  rw [tri_succ]; omega

/-- `T` is monotone (proved by hand on `≤` to stay choice-free). -/
theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (tri_le_succ _)

/-! ### The pairing function `num` -/

/-- The pairing function `num n m = (n+m)(n+m+1)/2 + m` (Cantor's diagonal
enumeration). -/
def num (n m : ℕ) : ℕ := tri (n + m) + m

/-- Its uncurried form, the actual `N × N → N` of the exercise. -/
def numP (p : ℕ × ℕ) : ℕ := num p.1 p.2

theorem num_zero_zero : num 0 0 = 0 := rfl

theorem num_succ_right (n m : ℕ) : num n (m + 1) = num (n + 1) m + 1 := by
  unfold num
  have h : n + (m + 1) = (n + 1) + m := by omega
  rw [h]; omega

theorem num_succ_left (n : ℕ) : num (n + 1) 0 = num 0 n + 1 := by
  unfold num
  have h0 : (n + 1) + 0 = n + 1 := by omega
  have h1 : 0 + n = n := by omega
  rw [h0, h1, tri_succ]; omega

/-- The value `num n m` sits in the half-open diagonal block `[T(n+m), T(n+m+1))`:
the upper
bound. -/
theorem num_lt_tri_succ (n m : ℕ) : num n m < tri (n + m + 1) := by
  rw [tri_succ]; unfold num; omega

/-- **The function is one-one.** The diagonal `s = n+m` is recovered as the unique
`s` with
`T(s) ≤ num n m < T(s+1)`; then `m` is the offset and `n = s - m`. -/
theorem num_injective : Function.Injective numP := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
  have h' : num n₁ m₁ = num n₂ m₂ := h
  have hs : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · exfalso
      have h1 : num n₁ m₁ < tri (n₁ + m₁ + 1) := num_lt_tri_succ n₁ m₁
      have h2 : tri (n₁ + m₁ + 1) ≤ tri (n₂ + m₂) := tri_mono (by omega)
      have h3 : tri (n₂ + m₂) ≤ num n₂ m₂ := by unfold num; omega
      omega
    · exact heq
    · exfalso
      have h1 : num n₂ m₂ < tri (n₂ + m₂ + 1) := num_lt_tri_succ n₂ m₂
      have h2 : tri (n₂ + m₂ + 1) ≤ tri (n₁ + m₁) := tri_mono (by omega)
      have h3 : tri (n₁ + m₁) ≤ num n₁ m₁ := by unfold num; omega
      omega
  have hbase : tri (n₁ + m₁) + m₁ = tri (n₂ + m₂) + m₂ := h'
  simp_all

/-! ### The inverse: walking the diagonals -/

/-- One step of the diagonal walk: the cell holding `num c + 1`. Moving up-right
within a diagonal,
or to the start of the next diagonal at the top edge. -/
def nextCell : ℕ × ℕ → ℕ × ℕ
  | (n + 1, m) => (n, m + 1)
  | (0, m) => (m + 1, 0)

theorem numP_nextCell (c : ℕ × ℕ) : numP (nextCell c) = numP c + 1 := by
  obtain ⟨n, m⟩ := c
  cases n with
  | zero => exact num_succ_left m
  | succ k => exact num_succ_right k m

/-- The inverse `unnum v = nextCellᵛ (0, 0)`. -/
def unnum : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | v + 1 => nextCell (unnum v)

theorem numP_unnum (v : ℕ) : numP (unnum v) = v := by
  induction v with
  | zero => exact num_zero_zero
  | succ k ih =>
      change numP (nextCell (unnum k)) = k + 1
      rw [numP_nextCell, ih]

theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])

/-- **Exercise 5.13.** The pairing function packaged as a bijection `ℕ × ℕ ≃ ℕ`
(choice-free,
via the
explicit inverse `unnum`). -/
def numEquiv : ℕ × ℕ ≃ ℕ where
  toFun := numP
  invFun := unnum
  left_inv := unnum_numP
  right_inv := numP_unnum

@[simp] theorem numEquiv_apply (p : ℕ × ℕ) : numEquiv p = num p.1 p.2 := rfl

/-! ### The domain isomorphisms

The power-set domain `P A` is the complete lattice `(Set A, ⊆)` (Exercise 4.17). A
bijection of
index types lifts to an order-isomorphism of power-set domains. -/

variable {α β : Type*}

/-- A bijection `α ≃ β` induces an order-isomorphism `P α ≅ P β` of power-set
domains, by direct
image. -/
def setCongr (e : α ≃ β) : Set α ≃o Set β where
  toFun S := e '' S
  invFun T := e.symm '' T
  left_inv := e.symm_image_image
  right_inv := e.symm.symm_image_image
  map_rel_iff' := by
    simp_all

/-- `P N ≅ P(N × N)` — induced by the pairing bijection `numEquiv`. -/
def pnOrderIsoPNN : Set ℕ ≃o Set (ℕ × ℕ) := setCongr numEquiv.symm

/-- `P N ≅ P N × P N` — `N ≅ N ⊕ N` together with `P(A ⊕ B) ≅ P A × P B`
(`Set.sumEquiv`). -/
def pnOrderIsoProd : Set ℕ ≃o Set ℕ × Set ℕ :=
  (setCongr Equiv.natSumNatEquivNat.symm).trans Set.sumEquiv

/-- `P(N × N) ≅ P N × P N` — by composing the two isomorphisms above. -/
def pnnOrderIsoProd : Set (ℕ × ℕ) ≃o Set ℕ × Set ℕ :=
  pnOrderIsoPNN.symm.trans pnOrderIsoProd

end Domain.Neighborhood.Exercise513
