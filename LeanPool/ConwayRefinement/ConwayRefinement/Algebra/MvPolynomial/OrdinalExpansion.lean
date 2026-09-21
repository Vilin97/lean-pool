/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Expansion
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic

/-!
# Expansion in one variable, for ordinal degrees

The coefficient `xCoeff x k p` of `X x ^ k` in `p`
(`ConwayRefinement.Algebra.MvPolynomial.Expansion`) for a polynomial graded by ordinal
degrees `wt : σ → NatOrdinal`: homogeneity of the coefficients,
`xCoeff` of a product with a factor not involving `x`, `xCoeff` of `X x * p`, and the fact that a
polynomial of degree below `wt x` does not involve `x`.
-/

universe u v

open MvPolynomial

public noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] [DecidableEq σ] (x : σ) (wt : σ → NatOrdinal)

omit [DecidableEq σ] in
/-- A monomial involving `x` has degree at least `wt x`. -/
theorem le_weight_of_ne_zero {d : σ →₀ ℕ} (hd : d x ≠ 0) : wt x ≤ Finsupp.weight wt d := by
  calc wt x ≤ d x • wt x := by
        simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal) ≤ wt x)
          (Nat.one_le_iff_ne_zero.mpr hd)
    _ ≤ Finsupp.weight wt d := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact Finset.single_le_sum (f := fun i ↦ d i • wt i) (fun _ _ ↦ bot_le)
          (Finsupp.mem_support_iff.mpr hd)

omit [DecidableEq σ] in
/-- A polynomial all of whose monomials have degree below `wt x` does not involve `x`. -/
theorem mem_supported_of_forall_weight_lt {p : MvPolynomial σ R}
    (hp : ∀ d ∈ p.support, Finsupp.weight wt d < wt x) : p ∈ supported R {x}ᶜ := by
  rw [mem_supported]
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  obtain ⟨d, hd, hdy⟩ := (mem_vars_iff_mem_support y).mp hy
  exact (hp d hd).not_ge (le_weight_of_ne_zero y wt (Finsupp.mem_support_iff.mp hdy))

omit [DecidableEq σ] in
/-- A polynomial homogeneous of degree below `wt x` does not involve `x`. -/
theorem IsWeightedHomogeneous.mem_supported_of_lt' {p : MvPolynomial σ R} {w : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p w) (hw : w < wt x) : p ∈ supported R {x}ᶜ :=
  mem_supported_of_forall_weight_lt x wt fun _ hd ↦ (hp (mem_support_iff.mp hd)).symm ▸ hw

/-- The coefficient of `X x ^ k` in a polynomial homogeneous of degree `w' ⊕ k ⊙ wt x` is
homogeneous of degree `w'`. -/
theorem xCoeff_isWeightedHomogeneous' {p : MvPolynomial σ R} {w w' : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p w) (k : ℕ) (hw : w' + k • wt x = w) :
    IsWeightedHomogeneous wt (xCoeff x k p) w' := by
  intro m hm
  rw [coeff_xCoeff] at hm
  split_ifs at hm with h
  · have := hp hm
    rw [map_add, Finsupp.weight_single, ← hw] at this
    exact add_right_cancel this
  · exact absurd rfl hm

/-- A nonzero coefficient of `X x ^ k` in a polynomial homogeneous of degree `w` has a degree `w'`
with `w' ⊕ k ⊙ wt x = w`. -/
theorem exists_add_nsmul_eq_of_xCoeff_ne_zero {p : MvPolynomial σ R} {w : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p w) {k : ℕ} (h : xCoeff x k p ≠ 0) :
    ∃ w' : NatOrdinal, w' + k • wt x = w := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero h
  rw [coeff_xCoeff] at hm
  split_ifs at hm with hmx
  · refine ⟨Finsupp.weight wt m, ?_⟩
    have := hp hm
    rwa [map_add, Finsupp.weight_single] at this
  · exact absurd rfl hm

/-- `xCoeff` of a product with a factor not involving `x`. -/
theorem xCoeff_mul_of_mem_supported {a : MvPolynomial σ R} (ha : a ∈ supported R {x}ᶜ) (k : ℕ)
    (p : MvPolynomial σ R) : xCoeff x k (a * p) = a * xCoeff x k p := by
  obtain ⟨q, rfl⟩ := exists_rename_val_eq_of_mem_supported x ha
  rw [xCoeff_apply, xCoeff_apply, map_mul, expandEquiv_rename_val, Polynomial.coeff_C_mul,
    map_mul]

/-- `xCoeff` of `X x * p`, positive index. -/
theorem xCoeff_succ_X_mul (k : ℕ) (p : MvPolynomial σ R) :
    xCoeff x (k + 1) (X x * p) = xCoeff x k p := by
  rw [xCoeff_apply, xCoeff_apply, map_mul, expandEquiv_X_self, Polynomial.coeff_X_mul]

/-- `xCoeff` of `X x * p`, index zero. -/
theorem xCoeff_zero_X_mul (p : MvPolynomial σ R) : xCoeff x 0 (X x * p) = 0 := by
  rw [xCoeff_apply, map_mul, expandEquiv_X_self, Polynomial.coeff_X_mul_zero, map_zero]

/-- `xCoeff` of a polynomial not involving `x`: itself in index zero, zero otherwise. -/
theorem xCoeff_of_mem_supported {a : MvPolynomial σ R} (ha : a ∈ supported R {x}ᶜ) (k : ℕ) :
    xCoeff x k a = if k = 0 then a else 0 := by
  have := xCoeff_mul_X_pow x ha k 0
  rwa [pow_zero, mul_one] at this

/-- The monomials of `xCoeff x k p * X x ^ k` are monomials of `p`. -/
theorem support_xCoeff_mul_X_pow_subset (k : ℕ) (p : MvPolynomial σ R) :
    (xCoeff x k p * X x ^ k).support ⊆ p.support := by
  classical
  intro m hm
  rw [mem_support_iff] at hm ⊢
  rw [X_pow_eq_monomial, coeff_mul_monomial'] at hm
  split_ifs at hm with h
  · rw [coeff_xCoeff] at hm
    split_ifs at hm with h0
    · have hm' : m - Finsupp.single x k + Finsupp.single x k = m := by
        rw [tsub_add_cancel_of_le h]
      rwa [hm', mul_one] at hm
    · rw [zero_mul] at hm
      exact absurd rfl hm
  · exact absurd rfl hm

end MvPolynomial
