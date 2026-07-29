/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {M : Type*} [CommMonoidWithZero M]

/-- A prime value hom used in the Odlyzko-bound argument. -/
noncomputable def primeValueHom (a : ℕ → M) : ℕ →*₀ M where
  toFun n :=
    if n = 0 then 0 else
      n.factorization.prod fun p e ↦ a p ^ e
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [hm, hn, mul_ne_zero hm hn, ↓reduceIte]
    rw [Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index'
      (f := m.factorization) (g := n.factorization)
      (h := fun p e ↦ a p ^ e)
      (fun p ↦ pow_zero (a p))
      (fun p e₁ e₂ ↦ pow_add (a p) e₁ e₂)

@[simp] theorem primeValueHom_one (a : ℕ → M) :
    primeValueHom a 1 = 1 :=
  map_one _

@[simp] theorem primeValueHom_apply_of_prime (a : ℕ → M) {p : ℕ}
    (hp : p.Prime) :
    primeValueHom a p = a p := by
  rw [primeValueHom]
  simp [hp.ne_zero, hp.factorization]

@[simp] theorem primeValueHom_apply_prime_subtype (a : ℕ → M)
    (p : Nat.Primes) :
    primeValueHom a p = a p :=
  primeValueHom_apply_of_prime a p.prop

theorem primeValueHom_multiset_prod_of_prime (a : ℕ → M)
    {m : Multiset ℕ} (hm : ∀ p ∈ m, p.Prime) :
    primeValueHom a m.prod = (m.map a).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons p m ih =>
      simp_all

end NumberField.Odlyzko
