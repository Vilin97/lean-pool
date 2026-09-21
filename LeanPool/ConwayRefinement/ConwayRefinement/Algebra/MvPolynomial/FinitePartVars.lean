/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalDerivation

/-!
# Variables carrying the constant Cantor coefficient of a weighted degree

The coefficient of `1 = ω^0` in the Cantor normal form of the degree of a monomial is the sum of
the corresponding coefficients of the degrees of its variables. Thus, in a polynomial homogeneous
of degree `δ`, a variable whose degree has the same constant Cantor coefficient as `δ` carries that
coefficient on its own.

This module collects the elementary degree facts about those variables and the finite set
`varsOfFinitePart` that contains them.

None of it depends on where the variables are evaluated. Both the real-exponent argument and the
Cantor–Bendixson germ argument need these statements, so they are stated once here over an
arbitrary commutative ring.
-/

universe u v

open scoped NatOrdinal

public section

namespace NatOrdinal

/-- If `b + a = c` and `a` and `c` have the same constant Cantor coefficient, then `b` has
constant Cantor coefficient zero. -/
theorem constantCoeff_eq_zero_of_add_eq {a b c : NatOrdinal.{u}}
    (ha : a.constantCoeff = c.constantCoeff) (h : b + a = c) : b.constantCoeff = 0 := by
  have hc := congrArg NatOrdinal.constantCoeff h
  rw [constantCoeff_add, ha] at hc
  omega

end NatOrdinal

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] {wt : σ → NatOrdinal}

/-- The constant Cantor coefficient of the degree of a variable of a homogeneous polynomial is at
most that of the degree of the polynomial. -/
theorem constantCoeff_wt_le_of_mem_vars {F : MvPolynomial σ R} {δ : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F δ) {i : σ} (hi : i ∈ F.vars) :
    (wt i).constantCoeff ≤ δ.constantCoeff := by
  classical
  obtain ⟨d, hd, hdi⟩ := (mem_vars_iff_mem_support i).mp hi
  rw [← hF (mem_support_iff.mp hd), Finsupp.constantCoeff_weight]
  calc (wt i).constantCoeff ≤ d i * (wt i).constantCoeff :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdi))
    _ ≤ _ := Finset.single_le_sum (f := fun i ↦ d i * (wt i).constantCoeff)
        (fun _ _ ↦ Nat.zero_le _) hdi

/-- The degree of a variable `X_i` in a homogeneous polynomial of degree `δ` precedes `δ` in the
algebraic order: there is `β` with `β + wt i = δ`. -/
theorem exists_add_wt_eq_of_mem_vars {F : MvPolynomial σ R} {δ : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F δ) {i : σ} (hi : i ∈ F.vars) : ∃ β, β + wt i = δ := by
  classical
  obtain ⟨d, hd, hdi⟩ := (mem_vars_iff_mem_support i).mp hi
  exact ⟨_, (Finsupp.weight_sub_single_add (w := wt) (Finsupp.mem_support_iff.mp hdi)).trans
    (hF (mem_support_iff.mp hd))⟩

/-- If the degree of a homogeneous polynomial has constant Cantor coefficient zero, so does the
degree of each of its variables. -/
theorem constantCoeff_wt_eq_zero_of_mem_vars {G : MvPolynomial σ R} {lam : NatOrdinal}
    (hG : IsWeightedHomogeneous wt G lam) (hlam : lam.constantCoeff = 0) {i : σ}
    (hi : i ∈ G.vars) : (wt i).constantCoeff = 0 :=
  Nat.eq_zero_of_le_zero ((constantCoeff_wt_le_of_mem_vars hG hi).trans hlam.le)

/-- For `F` homogeneous of degree `δ` and `β + wt t = δ`, the partial derivative `∂F/∂X_t` is
homogeneous of degree `β`. -/
theorem isWeightedHomogeneous_pderiv_of_add_wt_eq {F : MvPolynomial σ R} {δ : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F δ) {t : σ} {β : NatOrdinal} (hβ : β + wt t = δ) :
    IsWeightedHomogeneous wt (pderiv t F) β :=
  isWeightedHomogeneous_pderiv wt hF t hβ

/-- A homogeneous polynomial of nonzero degree has zero constant coefficient. -/
theorem coeff_zero_eq_zero_of_isWeightedHomogeneous {p : MvPolynomial σ R} {β : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p β) (hβ : β ≠ 0) : AddMonoidAlgebra.coeff p 0 = 0 := by
  by_contra h
  exact hβ ((hp h).symm.trans (map_zero _))

/-- A polynomial whose variable degrees have constant Cantor coefficient zero has no homogeneous
component whose degree has nonzero constant Cantor coefficient. -/
theorem weightedHomogeneousComponent_eq_zero_of_forall_vars {G : MvPolynomial σ R}
    (hG : ∀ i ∈ G.vars, (wt i).constantCoeff = 0) {β : NatOrdinal} (hβ : β.constantCoeff ≠ 0) :
    weightedHomogeneousComponent wt β G = 0 := by
  classical
  refine weightedHomogeneousComponent_eq_zero' β G fun d hd hw ↦ hβ ?_
  rw [← hw, Finsupp.constantCoeff_weight]
  exact Finset.sum_eq_zero fun i hi ↦ by
    rw [hG i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩), mul_zero]

variable (wt) in
/-- The variables of `F` whose degrees have the same constant Cantor coefficient as `δ`. -/
noncomputable def varsOfFinitePart (F : MvPolynomial σ R) (δ : NatOrdinal) : Finset σ :=
  F.vars.filter fun i ↦ (wt i).constantCoeff = δ.constantCoeff

theorem mem_varsOfFinitePart_iff {F : MvPolynomial σ R} {δ : NatOrdinal} {i : σ} :
    i ∈ varsOfFinitePart wt F δ ↔ i ∈ F.vars ∧ (wt i).constantCoeff = δ.constantCoeff := by
  rw [varsOfFinitePart, Finset.mem_filter]

end MvPolynomial

end
