/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

/-!
# The part of a polynomial of degree at least `τ`

For `P ∈ R[X_i]` graded by `deg X_i = wt i` with ordinal degrees `wt : σ → NatOrdinal`,
`componentsGE wt τ P` is the sum of the monomials of `P` of degree at least `τ`: the part
`P_{≥τ} := ∑_{β ≥ τ} P_β` of `P` *at or above the degree `τ`* (by the degree of its monomials, not
by exponent as for the parts of an ordinal). It is additive, vanishes on polynomials of degree
below `τ`, and fixes homogeneous polynomials of degree at least `τ`.
-/

universe u v

open Finsupp

public section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] (wt : σ → NatOrdinal)

/-- The part `P_{≥τ}` of `P` at or above the degree `τ`: the sum of the monomials of `P` of degree
at least `τ`. -/
noncomputable def componentsGE (τ : NatOrdinal) (P : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact ∑ d ∈ P.support.filter fun d ↦ τ ≤ Finsupp.weight wt d, monomial d (AddMonoidAlgebra.coeff P d)

open Classical in
theorem coeff_componentsGE (τ : NatOrdinal) (P : MvPolynomial σ R) (d : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (componentsGE wt τ P) d = if τ ≤ Finsupp.weight wt d then AddMonoidAlgebra.coeff P d else 0 := by
  classical
  rw [componentsGE]
  simp only [coeff_sum, coeff_monomial]
  split_ifs with hτ
  · rw [Finset.sum_eq_single d]
    · rw [ite_eq_left rfl]
    · intro d' _ hd'
      rw [ite_eq_right hd']
    · intro hd
      rw [ite_eq_left rfl]
      by_contra h
      exact hd (Finset.mem_filter.mpr ⟨mem_support_iff.mpr h, hτ⟩)
  · refine Finset.sum_eq_zero fun d' hd' ↦ ?_
    rw [ite_eq_right]
    rintro rfl
    exact hτ (Finset.mem_filter.mp hd').2

theorem componentsGE_add (τ : NatOrdinal) (P Q : MvPolynomial σ R) :
    componentsGE wt τ (P + Q) = componentsGE wt τ P + componentsGE wt τ Q := by
  classical
  ext d
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_componentsGE]
  split_ifs <;> simp

theorem componentsGE_neg (τ : NatOrdinal) (P : MvPolynomial σ R) :
    componentsGE wt τ (-P) = -componentsGE wt τ P := by
  classical
  ext d
  have hneg : ∀ Q : MvPolynomial σ R, AddMonoidAlgebra.coeff (-Q) d = -AddMonoidAlgebra.coeff Q d := fun Q ↦ by
    change (coeffAddMonoidHom d) (-Q) = -(coeffAddMonoidHom d) Q
    exact map_neg _ _
  rw [hneg, coeff_componentsGE, coeff_componentsGE, hneg]
  split_ifs <;> simp

theorem componentsGE_sub (τ : NatOrdinal) (P Q : MvPolynomial σ R) :
    componentsGE wt τ (P - Q) = componentsGE wt τ P - componentsGE wt τ Q := by
  rw [sub_eq_add_neg, componentsGE_add, componentsGE_neg, sub_eq_add_neg]

theorem componentsGE_zero (τ : NatOrdinal) : componentsGE wt τ (0 : MvPolynomial σ R) = 0 := by
  classical
  ext d
  simp [coeff_componentsGE]

theorem componentsGE_sum {ι : Type*} (τ : NatOrdinal) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    componentsGE wt τ (∑ i ∈ s, f i) = ∑ i ∈ s, componentsGE wt τ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, componentsGE_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, componentsGE_add, ih]

/-- The part at or above `τ` of a polynomial all of whose monomials have degree below `τ` is
`0`. -/
theorem componentsGE_eq_zero_of_forall_lt {τ : NatOrdinal} {P : MvPolynomial σ R}
    (hP : ∀ d ∈ P.support, Finsupp.weight wt d < τ) : componentsGE wt τ P = 0 := by
  classical
  ext d
  rw [coeff_componentsGE, AddMonoidAlgebra.coeff_zero]
  split_ifs with hτ
  · by_contra h
    exact absurd (hP d (mem_support_iff.mpr h)) (not_lt.mpr hτ)
  · rfl

/-- A homogeneous polynomial of degree at least `τ` is its own part at or above `τ`. -/
theorem componentsGE_eq_self_of_isWeightedHomogeneous {τ β : NatOrdinal} {P : MvPolynomial σ R}
    (hP : IsWeightedHomogeneous wt P β) (hβ : τ ≤ β) : componentsGE wt τ P = P := by
  classical
  ext d
  rw [coeff_componentsGE]
  split_ifs with hτ
  · rfl
  · by_contra h
    exact hτ (hβ.trans_eq (hP (Ne.symm h)).symm)

end MvPolynomial

end
