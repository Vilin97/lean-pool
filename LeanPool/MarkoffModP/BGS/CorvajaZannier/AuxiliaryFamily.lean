/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.FieldSimp

/-!
# The Corvaja--Zannier auxiliary family

The proof of Corvaja--Zannier's Proposition 2 considers the family

`u ^ i * (1 - u) / (1 - v)` for `0 ≤ i < k`, together with
`u ^ r * v ^ s` for `0 ≤ r ≤ k` and `0 ≤ s < h`.

This file formalizes the purely algebraic first half of their linear-
independence argument.  Any dependence of that family produces a nonzero
bivariate polynomial of the exact source form

`P₁(U) * (1 - U) + P₂(U, V) * (1 - V)`

which vanishes at `(u, v)`.  Bivariate polynomials are represented as
polynomials in `V` whose coefficients are polynomials in `U`.  Excluding the
resulting relation by a resultant and degree argument is deliberately left as
the next boundary; it is not assumed here through a typeclass or an axiom.

Source provenance: published pages 1933--1934; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 518--570.  The
dependence-to-relation step formalized here is lines 518--545.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- The exact auxiliary family used in Corvaja--Zannier's Proposition 2.

The left summand indexes `u ^ i * (1 - u) / (1 - v)` for `i < k`; the right
summand indexes the rectangular family `u ^ r * v ^ s` for `r ≤ k`, `s < h`.
-/
def auxiliaryFamily (u v : L) (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → L
  | Sum.inl i => u ^ (i : ℕ) * ((1 - u) / (1 - v))
  | Sum.inr rs => u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

/-- The polynomial `Σ i, c i * U ^ i`. -/
noncomputable def auxiliaryPowerPolynomial {k : ℕ}
    (c : Fin k → C) : Polynomial C := by
  classical
  exact Polynomial.ofFn k c

/-- The bivariate polynomial `Σ (r,s), d (r,s) * U ^ r * V ^ s`, represented
as a polynomial in `V` over `C[U]`. -/
noncomputable def auxiliaryGridPolynomial {h k : ℕ}
    (d : Fin (k + 1) × Fin h → C) : Polynomial (Polynomial C) := by
  classical
  exact Polynomial.ofFn h fun s =>
    Polynomial.ofFn (k + 1) fun r => d (r, s)

/-- The bivariate relation obtained after clearing the denominator `1 - v`
from a dependence of the auxiliary family. -/
def auxiliaryRelationPolynomial {h k : ℕ}
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C) :
    Polynomial (Polynomial C) :=
  Polynomial.C
      (auxiliaryPowerPolynomial c * (1 - Polynomial.X)) +
    auxiliaryGridPolynomial d * (1 - Polynomial.X)

/-- Evaluate a bivariate polynomial, represented as a polynomial in `V` over
`C[U]`, at `(u, v)`. -/
def evalBivariate (u v : L) (P : Polynomial (Polynomial C)) : L :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap C L) u) v

private theorem one_sub_X_ne_zero (R : Type*) [Ring R] [Nontrivial R] :
    (1 - Polynomial.X : Polynomial R) ≠ 0 := by
  intro h
  have hatZero := congrArg (fun P : Polynomial R => P.eval 0) h
  simp at hatZero

@[simp]
theorem evalBivariate_auxiliaryPowerPolynomial
    {k : ℕ} (u : L) (c : Fin k → C) :
    (auxiliaryPowerPolynomial c).eval₂ (algebraMap C L) u =
      ∑ i, algebraMap C L (c i) * u ^ (i : ℕ) := by
  classical
  change (Polynomial.eval₂RingHom (algebraMap C L) u)
    (auxiliaryPowerPolynomial c) = _
  rw [auxiliaryPowerPolynomial, Polynomial.ofFn_eq_sum_monomial, map_sum]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

@[simp]
theorem evalBivariate_auxiliaryGridPolynomial
    {h k : ℕ} (u v : L) (d : Fin (k + 1) × Fin h → C) :
    evalBivariate u v (auxiliaryGridPolynomial d) =
      ∑ rs, algebraMap C L (d rs) *
        (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) := by
  classical
  change (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap C L) u) v)
    (auxiliaryGridPolynomial d) = _
  rw [Fintype.sum_prod_type_right'
    (fun (r : Fin (k + 1)) (s : Fin h) => algebraMap C L (d (r, s)) *
      (u ^ (r : ℕ) * v ^ (s : ℕ)))]
  rw [auxiliaryGridPolynomial, Polynomial.ofFn_eq_sum_monomial, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  rw [Polynomial.ofFn_eq_sum_monomial]
  change (Polynomial.eval₂RingHom (algebraMap C L) u)
      (∑ r : Fin (k + 1), Polynomial.monomial (r : ℕ) (d (r, s))) *
        v ^ (s : ℕ) = _
  rw [map_sum]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

@[simp]
theorem evalBivariate_auxiliaryRelationPolynomial
    {h k : ℕ} (u v : L) (c : Fin k → C)
    (d : Fin (k + 1) × Fin h → C) :
    evalBivariate u v (auxiliaryRelationPolynomial c d) =
      (∑ i, algebraMap C L (c i) * u ^ (i : ℕ)) * (1 - u) +
      (∑ rs, algebraMap C L (d rs) *
        (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) * (1 - v) := by
  unfold evalBivariate auxiliaryRelationPolynomial
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_one,
    Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom]
  rw [evalBivariate_auxiliaryPowerPolynomial]
  change _ + evalBivariate u v (auxiliaryGridPolynomial d) * (1 - v) = _
  rw [evalBivariate_auxiliaryGridPolynomial]

/-- The first coefficient polynomial has degree strictly less than `k`, as in
the source's bound `deg P₁ ≤ k - 1`. -/
theorem auxiliaryPowerPolynomial_natDegree_lt
    {k : ℕ} (hk : 0 < k) (c : Fin k → C) :
    (auxiliaryPowerPolynomial c).natDegree < k := by
  classical
  simpa [auxiliaryPowerPolynomial] using
    Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hk.ne') c

/-- The rectangular polynomial has degree strictly less than `h` in its outer
variable `V`, as in the source's bound `deg_V P₂ ≤ h - 1`. -/
theorem auxiliaryGridPolynomial_natDegree_lt
    {h k : ℕ} (hh : 0 < h) (d : Fin (k + 1) × Fin h → C) :
    (auxiliaryGridPolynomial d).natDegree < h := by
  classical
  simpa [auxiliaryGridPolynomial] using
    Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hh.ne')
      (fun s : Fin h => Polynomial.ofFn (k + 1) fun r => d (r, s))

/-- Every coefficient of the rectangular polynomial, viewed as a polynomial
in `V`, has degree at most `k` in `U`. -/
theorem auxiliaryGridPolynomial_coeff_natDegree_le
    {h k : ℕ} (d : Fin (k + 1) × Fin h → C) (s : ℕ) :
    ((auxiliaryGridPolynomial d).coeff s).natDegree ≤ k := by
  classical
  by_cases hs : s < h
  · have hcoeff :
        (auxiliaryGridPolynomial d).coeff s =
          Polynomial.ofFn (k + 1) (fun r => d (r, ⟨s, hs⟩)) := by
      simp [auxiliaryGridPolynomial, hs]
    rw [hcoeff]
    have hdegree := Polynomial.ofFn_natDegree_lt
      (n := k + 1) (by omega : 1 ≤ k + 1)
      (fun r : Fin (k + 1) => d (r, ⟨s, hs⟩))
    omega
  · have hge : h ≤ s := Nat.le_of_not_gt hs
    have hcoeff : (auxiliaryGridPolynomial d).coeff s = 0 := by
      simp [auxiliaryGridPolynomial,
        Polynomial.ofFn_coeff_eq_zero_of_ge, hge]
    rw [hcoeff, Polynomial.natDegree_zero]
    exact Nat.zero_le k

/-- The power polynomial is zero exactly when all of its coefficients are
zero. -/
theorem auxiliaryPowerPolynomial_eq_zero_iff
    {k : ℕ} (c : Fin k → C) :
    auxiliaryPowerPolynomial c = 0 ↔ ∀ i, c i = 0 := by
  classical
  constructor
  · intro hc i
    have hcoeff := congrArg (fun P : Polynomial C => P.coeff (i : ℕ)) hc
    simpa [auxiliaryPowerPolynomial] using hcoeff
  · intro hc
    have hc' : c = 0 := funext hc
    change Polynomial.ofFn k c = 0
    rw [hc']
    exact Polynomial.ofFn_zero k

/-- The grid polynomial is zero exactly when all of its coefficients are
zero. -/
theorem auxiliaryGridPolynomial_eq_zero_iff
    {h k : ℕ} (d : Fin (k + 1) × Fin h → C) :
    auxiliaryGridPolynomial d = 0 ↔ ∀ rs, d rs = 0 := by
  classical
  constructor
  · intro hd rs
    have hcoeff := congrArg
      (fun P : Polynomial (Polynomial C) =>
        (P.coeff (rs.2 : ℕ)).coeff (rs.1 : ℕ)) hd
    simp only [auxiliaryGridPolynomial,
      Polynomial.ofFn_coeff_eq_val_of_lt _ rs.2.isLt] at hcoeff
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ rs.1.isLt] at hcoeff
    exact hcoeff
  · intro hd
    change Polynomial.ofFn h
      (fun s => Polynomial.ofFn (k + 1) fun r => d (r, s)) = 0
    have hinner :
        (fun s : Fin h => Polynomial.ofFn (k + 1) fun r => d (r, s)) = 0 := by
      funext s
      apply Polynomial.ext
      intro n
      by_cases hn : n < k + 1
      · simpa [hn] using hd (⟨n, hn⟩, s)
      · simp [Polynomial.ofFn_coeff_eq_zero_of_ge, Nat.le_of_not_gt hn]
    rw [hinner]
    exact Polynomial.ofFn_zero h

/-- The source's relation polynomial is identically zero only for the trivial
pair of coefficient families.  This is the formal version of evaluating at
`V = 1` first and then using that both polynomial rings are domains. -/
theorem auxiliaryRelationPolynomial_eq_zero_iff
    {h k : ℕ} (c : Fin k → C) (d : Fin (k + 1) × Fin h → C) :
    auxiliaryRelationPolynomial c d = 0 ↔
      (∀ i, c i = 0) ∧ ∀ rs, d rs = 0 := by
  constructor
  · intro hrel
    have hatOne := congrArg
      (fun P : Polynomial (Polynomial C) => P.eval 1) hrel
    have hpowerMul :
        auxiliaryPowerPolynomial c * (1 - Polynomial.X) = 0 := by
      simpa [auxiliaryRelationPolynomial] using hatOne
    have hpower : auxiliaryPowerPolynomial c = 0 :=
      (mul_eq_zero.mp hpowerMul).resolve_right (one_sub_X_ne_zero C)
    have hgridMul : auxiliaryGridPolynomial d * (1 - Polynomial.X) = 0 := by
      simpa [auxiliaryRelationPolynomial, hpower] using hrel
    have hgrid : auxiliaryGridPolynomial d = 0 :=
      (mul_eq_zero.mp hgridMul).resolve_right (one_sub_X_ne_zero (Polynomial C))
    exact ⟨(auxiliaryPowerPolynomial_eq_zero_iff c).mp hpower,
      (auxiliaryGridPolynomial_eq_zero_iff d).mp hgrid⟩
  · rintro ⟨hc, hd⟩
    simp only [auxiliaryRelationPolynomial]
    rw [(auxiliaryPowerPolynomial_eq_zero_iff c).mpr hc,
      (auxiliaryGridPolynomial_eq_zero_iff d).mpr hd]
    simp

/-- A dependence of the Corvaja--Zannier auxiliary family produces a nonzero
bivariate relation of the exact source form which vanishes at `(u, v)`.

This is the algebraic input to the subsequent resultant argument. -/
theorem exists_nonzero_auxiliaryRelationPolynomial_of_not_linearIndependent
    {h k : ℕ} (u v : L) (hv : v ≠ 1)
    (hdep : ¬ LinearIndependent C (auxiliaryFamily u v h k)) :
    ∃ (c : Fin k → C) (d : Fin (k + 1) × Fin h → C),
      auxiliaryRelationPolynomial c d ≠ 0 ∧
      evalBivariate u v (auxiliaryRelationPolynomial c d) = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  let c : Fin k → C := fun j => g (Sum.inl j)
  let d : Fin (k + 1) × Fin h → C := fun rs => g (Sum.inr rs)
  refine ⟨c, d, ?_, ?_⟩
  · intro hzero
    have hcoeffs := (auxiliaryRelationPolynomial_eq_zero_iff c d).mp hzero
    cases i with
    | inl j => exact hi (by simpa [c] using hcoeffs.1 j)
    | inr rs => exact hi (by simpa [d] using hcoeffs.2 rs)
  · have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv.symm
    have hcleared := congrArg (fun x : L => x * (1 - v)) hg
    simp only [Fintype.sum_sum_type, auxiliaryFamily, Algebra.smul_def] at hcleared
    rw [add_mul, Finset.sum_mul, Finset.sum_mul] at hcleared
    field_simp [hden] at hcleared
    simpa [c, d, div_mul_eq_mul_div, hden, mul_assoc, mul_left_comm, mul_comm,
      Finset.mul_sum] using hcleared

/-- The dependence-to-relation implication together with all three degree
bounds used by the source's resultant estimate. -/
theorem exists_nonzero_bounded_auxiliaryRelationPolynomial_of_not_linearIndependent
    {h k : ℕ} (u v : L) (hh : 0 < h) (hk : 0 < k) (hv : v ≠ 1)
    (hdep : ¬ LinearIndependent C (auxiliaryFamily u v h k)) :
    ∃ (c : Fin k → C) (d : Fin (k + 1) × Fin h → C),
      auxiliaryRelationPolynomial c d ≠ 0 ∧
      evalBivariate u v (auxiliaryRelationPolynomial c d) = 0 ∧
      (auxiliaryPowerPolynomial c).natDegree < k ∧
      (auxiliaryGridPolynomial d).natDegree < h ∧
      ∀ s, ((auxiliaryGridPolynomial d).coeff s).natDegree ≤ k := by
  obtain ⟨c, d, hnonzero, heval⟩ :=
    exists_nonzero_auxiliaryRelationPolynomial_of_not_linearIndependent
      u v hv hdep
  exact ⟨c, d, hnonzero, heval,
    auxiliaryPowerPolynomial_natDegree_lt hk c,
    auxiliaryGridPolynomial_natDegree_lt hh d,
    auxiliaryGridPolynomial_coeff_natDegree_le d⟩

/-- If the resultant step excludes every nonzero relation polynomial of the
source form, then the auxiliary family is linearly independent. -/
theorem auxiliaryFamily_linearIndependent_of_no_relation
    {h k : ℕ} (u v : L) (hv : v ≠ 1)
    (hNoRelation :
      ∀ (c : Fin k → C) (d : Fin (k + 1) × Fin h → C),
        auxiliaryRelationPolynomial c d ≠ 0 →
          evalBivariate u v (auxiliaryRelationPolynomial c d) ≠ 0) :
    LinearIndependent C (auxiliaryFamily u v h k) := by
  by_contra hdep
  obtain ⟨c, d, hnonzero, heval⟩ :=
    exists_nonzero_auxiliaryRelationPolynomial_of_not_linearIndependent
      u v hv hdep
  exact hNoRelation c d hnonzero heval

end

end BGS.CorvajaZannier
