/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.JointRecurrence
public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation

/-!
# Associated L-relations with polynomial correction coefficients

A polynomial R-relation valid as the exponent varies differentiates to an
inhomogeneous L-relation. The correction coefficients are formal derivatives of
the original coefficient polynomials. This is applied to Carlson's homogeneity
recurrence, with a single nonzero polynomial family valid for all parameters and
slit-plane nodes. It is a concrete instance of Carlson (1987), Theorem 3.1, not
yet that theorem for an arbitrary list of associated shifts.
-/

open Complex Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Differentiation of a parameter-polynomial R-relation. The exponent convention
`-a + e` accounts for the positive sign of the R-correction on the right. -/
theorem polynomial_R_relation_implies_L_relation {κ : Type*} (s : Finset κ)
    (A : κ → MvPolynomial (Option (ι ⊕ ι)) ℂ) (e : κ → ℂ)
    (B : κ → ι → ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    (hrel : ∀ a : ℂ, ∑ j ∈ s, (A j).eval (carlsonRecurrencePoint a b z) *
      regCarlsonRSlit (-a + e j) (B j) z = 0) (a : ℂ) :
    ∑ j ∈ s, (A j).eval (carlsonRecurrencePoint a b z) * regCarlsonLSlit (-a + e j) (B j) z =
      ∑ j ∈ s, (MvPolynomial.pderiv none (A j)).eval (carlsonRecurrencePoint a b z) *
        regCarlsonRSlit (-a + e j) (B j) z := by
  have hd (j : κ) : HasDerivAt
      (fun w => (A j).eval (carlsonRecurrencePoint w b z) * regCarlsonRSlit (-w + e j) (B j) z)
      ((MvPolynomial.pderiv none (A j)).eval (carlsonRecurrencePoint a b z) *
          regCarlsonRSlit (-a + e j) (B j) z -
        (A j).eval (carlsonRecurrencePoint a b z) * regCarlsonLSlit (-a + e j) (B j) z) a := by
    have hr := (hasDerivAt_regCarlsonRSlit_L (-a + e j) (B j) hz).comp_of_eq a
      ((hasDerivAt_id a).neg.add_const (e j)) rfl
    simpa [Function.comp_def, sub_eq_add_neg] using!
      (hasDerivAt_carlsonRecurrencePoint_eval (A j) a b z).mul hr
  have h := HasDerivAt.fun_sum (u := s) (fun j _ => hd j)
  have heq : (fun w => ∑ j ∈ s, (A j).eval (carlsonRecurrencePoint w b z) *
      regCarlsonRSlit (-w + e j) (B j) z) = fun _ : ℂ => 0 := funext hrel
  rw [heq] at h
  have H := h.unique (hasDerivAt_const a 0)
  rw [Finset.sum_sub_distrib] at H
  exact (sub_eq_zero.mp H).symm

/-- The L homogeneity recurrence, with explicit polynomial R-correction terms,
valid for all complex parameters and all slit-plane nodes, including an empty index type. -/
theorem sum_carlsonAssociatedRecurrenceJointPolynomial_mul_lSlit
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrenceJointPolynomial n).eval (carlsonRecurrencePoint a b z) *
        regCarlsonLSlit (-a - n) b z =
      ∑ n ∈ Finset.range (Fintype.card ι + 1),
        (MvPolynomial.pderiv none (carlsonAssociatedRecurrenceJointPolynomial n)).eval
          (carlsonRecurrencePoint a b z) * regCarlsonRSlit (-a - n) b z := by
  simpa only [sub_eq_add_neg] using polynomial_R_relation_implies_L_relation
    (Finset.range (Fintype.card ι + 1)) carlsonAssociatedRecurrenceJointPolynomial
    (fun n => -(n : ℂ)) (fun _ => b) b hz
    (fun a => by simpa only [sub_eq_add_neg] using
      sum_carlsonAssociatedRecurrenceJointPolynomial_mul_rSlit a b hz) a

end DirichletTransform
