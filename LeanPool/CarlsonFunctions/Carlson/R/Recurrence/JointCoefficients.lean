/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Recurrence.Coefficients
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.PolynomialDerivatives

/-! # Universal polynomial recurrence coefficients and specialization

The coordinates are `none` for the exponent parameter, `some (inl i)` for
Dirichlet parameters and `some (inr i)` for nodes. No R-function dependence
or recurrence theorem is imported here. -/

open Complex Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Coordinates for a polynomial in the exponent parameter, Dirichlet parameters, and nodes. -/
def carlsonRecurrencePoint (a : ℂ) (b z : ι → ℂ) : Option (ι ⊕ ι) → ℂ :=
  fun i => i.elim a (Sum.elim b z)

/-- Substitute a joint parameter polynomial into an ascending Pochhammer polynomial. -/
def recurrencePochhammer (n : ℕ) (p : MvPolynomial (Option (ι ⊕ ι)) ℂ) :=
  (ascPochhammer ℂ n).eval₂ MvPolynomial.C p

omit [Fintype ι] in
private theorem eval_recurrencePochhammer (n : ℕ)
    (p : MvPolynomial (Option (ι ⊕ ι)) ℂ) (w : Option (ι ⊕ ι) → ℂ) :
    (recurrencePochhammer n p).eval w = (ascPochhammer ℂ n).eval (p.eval w) := by
  unfold recurrencePochhammer
  rw [Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval w).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    simp
  rw [hc]
  rfl

/-- The coefficient of `R_{-a-n}` as one polynomial in all parameters and nodes. -/
def carlsonAssociatedRecurrenceJointPolynomial (n : ℕ) : MvPolynomial (Option (ι ⊕ ι)) ℂ :=
  let a : MvPolynomial (Option (ι ⊕ ι)) ℂ := MvPolynomial.X none
  let b : ι → MvPolynomial (Option (ι ⊕ ι)) ℂ := fun i => MvPolynomial.X (some (.inl i))
  let a' := (∑ i, b i) - a
  let lift : MvPolynomial ι ℂ → MvPolynomial (Option (ι ⊕ ι)) ℂ :=
    MvPolynomial.rename (fun i => some (Sum.inr i))
  if n = 0 then recurrencePochhammer (Fintype.card ι - 1)
    (a' - (Fintype.card ι : MvPolynomial (Option (ι ⊕ ι)) ℂ) + 1)
  else if n = Fintype.card ι then
    -recurrencePochhammer (Fintype.card ι - 1) (a + 1) * lift (MvPolynomial.esymm ι ℂ n)
  else
    recurrencePochhammer (n - 1) (a + 1) *
      recurrencePochhammer (Fintype.card ι - n - 1)
        (a' - (Fintype.card ι : MvPolynomial (Option (ι ⊕ ι)) ℂ) + 1) *
      ((a + (n : MvPolynomial (Option (ι ⊕ ι)) ℂ)) * lift (MvPolynomial.esymm ι ℂ n) -
        ∑ i, b i * MvPolynomial.X (some (.inr i)) *
          lift (MvPolynomial.pderiv i (MvPolynomial.esymm ι ℂ n)))

/-- Specialization recovers the existing division-free recurrence coefficients. -/
theorem eval_carlsonAssociatedRecurrenceJointPolynomial (n : ℕ) (a : ℂ) (b z : ι → ℂ) :
    (carlsonAssociatedRecurrenceJointPolynomial (ι := ι) n).eval (carlsonRecurrencePoint a b z) =
      (carlsonAssociatedRecurrencePolynomial n a ((∑ i, b i) - a) b).eval z := by
  simp only [carlsonAssociatedRecurrenceJointPolynomial, carlsonAssociatedRecurrencePolynomial]
  split_ifs <;>
    simp [eval_recurrencePochhammer, MvPolynomial.eval_rename, carlsonRecurrencePoint,
      Function.comp_def]

/-- The universal family is not the zero polynomial family. This is polynomial
nontriviality; specializations may still have vanishing coefficients. -/
theorem carlsonAssociatedRecurrenceJointPolynomial_zero_ne_zero :
    carlsonAssociatedRecurrenceJointPolynomial (ι := ι) 0 ≠ 0 := by
  intro h
  have H := congrArg (MvPolynomial.eval (carlsonRecurrencePoint (-1) (fun _ : ι => 1)
    (fun _ => 1))) h
  rw [eval_carlsonAssociatedRecurrenceJointPolynomial] at H
  simp only [carlsonAssociatedRecurrencePolynomial, ↓reduceIte, MvPolynomial.eval_C,
    map_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at H
  have heq : (Fintype.card ι : ℂ) - -1 - Fintype.card ι + 1 = 2 := by ring
  rw [heq] at H
  have hreg : IsCarlsonGammaRegular (2 : ℂ) := by
    intro n hn
    have hn' := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hn'
    norm_num at hn'
    linarith
  exact (hreg.ascPochhammer_ne_zero (Fintype.card ι - 1)) H

omit [Fintype ι] in
/-- Formal differentiation supplies a polynomial coefficient derivative, including
at exceptional parameter values. -/
theorem hasDerivAt_carlsonRecurrencePoint_eval (p : MvPolynomial (Option (ι ⊕ ι)) ℂ)
    (a : ℂ) (b z : ι → ℂ) :
    HasDerivAt (fun s => p.eval (carlsonRecurrencePoint s b z))
      ((MvPolynomial.pderiv none p).eval (carlsonRecurrencePoint a b z)) a := by
  have h := p.hasDerivAt_eval_update (carlsonRecurrencePoint a b z) none a
  convert h using 1
  · funext s
    congr 2
    ext i
    cases i <;> simp [carlsonRecurrencePoint]
  · congr 2
    ext i
    cases i <;> simp [carlsonRecurrencePoint]

end DirichletTransform
