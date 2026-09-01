/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod

/-!
# Big-operator lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- Factor a constant out of an indicator-weighted sum: `∑ g x · [p x]·c = c · ∑_{p x} g x`. -/
theorem Finset.sum_mul_ite_const {ι R : Type*} [CommSemiring R] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → R) (c : R) :
    ∑ x ∈ s, g x * (if p x then c else 0) = c * ∑ x ∈ s with p x, g x := by
  simp_rw [mul_ite, mul_zero, ← Finset.sum_filter]
  rw [← Finset.sum_mul, mul_comm]

/-- An `𝔽₂`-linear combination is the sum over the support of the coefficient function. -/
theorem sum_zmod_two_smul_eq_sum_filter {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    [Module (ZMod 2) M] (m : ι → M) (g : ι → ZMod 2) :
    ∑ i, g i • m i = ∑ i ∈ Finset.univ with g i = 1, m i := by
  have h01 : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
  rw [← Finset.sum_subset (Finset.filter_subset (fun i ↦ g i = 1) Finset.univ)
    (fun i _ hi ↦ by rw [h01 (g i) (by simpa using hi), zero_smul])]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2, one_smul]
