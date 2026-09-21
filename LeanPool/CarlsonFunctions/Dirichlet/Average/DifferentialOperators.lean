/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Differential operators and pointwise Carlson kernels

This file defines Carlson's partial derivatives and Euler--Poisson operators, and proves
their action on the pointwise averaging kernels. Compatibility lemmas identify the coordinate
and iterated derivatives with the general SCV operators, preserving Carlson's public names.
The integral differentiation formulas in
`Associated` and the integration-by-parts proof in `Deriv` both use this lower-level layer.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Sections 5.3--5.4,
  Academic Press, 1977.
-/

@[expose] public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

open Complex

variable {ι : Type*} [Fintype ι]

/-! ## Pointwise differentiation of the averaging kernel -/

open scoped Classical in
/-- Updating one parameter of Carlson's affine form changes its value by the corresponding
simplex coordinate times the change in that parameter. -/
theorem carlsonAffineForm_update (z : ι → ℂ) (u : ι → ℝ) (i : ι) (w : ℂ) :
    carlsonAffineForm (Function.update z i w) u =
      carlsonAffineForm z u + (u i : ℂ) * (w - z i) := by
  classical
  unfold carlsonAffineForm
  calc
    ∑ j, (u j : ℂ) * Function.update z i w j =
        ∑ j, ((u j : ℂ) * z j + if j = i then (u i : ℂ) * (w - z i) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp
        ring
      · simp [hji]
    _ = ∑ j, (u j : ℂ) * z j + (u i : ℂ) * (w - z i) := by
      rw [Finset.sum_add_distrib]
      simp

open scoped Classical in
/-- As a function of one variable `z i`, Carlson's affine form has derivative `u i`. -/
theorem hasDerivAt_carlsonAffineForm_update (z : ι → ℂ) (u : ι → ℝ) (i : ι) :
    HasDerivAt (fun w ↦ carlsonAffineForm (Function.update z i w) u) (u i : ℂ) (z i) := by
  have h := (hasDerivAt_const (x := z i) (c := carlsonAffineForm z u)).add
    ((hasDerivAt_id (x := z i)).sub_const (z i) |>.const_mul (u i : ℂ))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
  · simpa only [Pi.add_apply, id_eq] using carlsonAffineForm_update z u i w
  · ring

open scoped Classical in
/-- Differentiating a composed Carlson kernel with respect to `z i` introduces the factor
`u i`.  This is the pointwise identity underlying Carlson's formula (5.3-2). -/
theorem HasDerivAt.comp_carlsonAffineForm_update {f : ℂ → ℂ} {f' : ℂ}
    {z : ι → ℂ} {u : ι → ℝ} (i : ι)
    (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    HasDerivAt (fun w ↦ f (carlsonAffineForm (Function.update z i w) u))
      ((u i : ℂ) * f') (z i) := by
  have hf' : HasDerivAt f f'
      (carlsonAffineForm (Function.update z i (z i)) u) := by simpa using hf
  have h := hf'.comp (z i) (hasDerivAt_carlsonAffineForm_update z u i)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ rfl)).congr_deriv ?_
  ring

/-! ## Differential operators -/

open scoped Classical in
/-- The partial derivative in the Carlson variable `z i`, defined by updating that coordinate
while holding all other coordinates fixed. -/
def carlsonPartialDeriv (i : ι)
    (G : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  deriv (fun w ↦ G (Function.update z i w)) (z i)

omit [Fintype ι] in
open scoped Classical in
/-- Carlson's coordinate derivative is the scalar specialization of the SCV derivative. -/
theorem carlsonPartialDeriv_eq_partialDeriv (i : ι) (G : (ι → ℂ) → ℂ) :
    carlsonPartialDeriv i G = SeveralComplexVariables.partialDeriv i G := rfl

/-- The partial derivative of a Carlson kernel is the derivative of the univariate function
times the corresponding simplex coordinate.  This is the pointwise form of Carlson's
formula (5.3-2). -/
theorem carlsonPartialDeriv_comp_carlsonAffineForm {f : ℂ → ℂ} {f' : ℂ}
    {z : ι → ℂ} {u : ι → ℝ} (i : ι)
    (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    carlsonPartialDeriv i (fun z ↦ f (carlsonAffineForm z u)) z = (u i : ℂ) * f' := by
  unfold carlsonPartialDeriv
  exact (HasDerivAt.comp_carlsonAffineForm_update i hf).deriv

/-- Mixed partial differentiation of a Carlson kernel introduces the product of the two
corresponding simplex coordinates. -/
theorem carlsonPartialDeriv_carlsonPartialDeriv_comp_carlsonAffineForm
    {f f' : ℂ → ℂ} {f'' : ℂ} {z : ι → ℂ} {u : ι → ℝ} (i j : ι)
    (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf' : HasDerivAt f' f'' (carlsonAffineForm z u)) :
    carlsonPartialDeriv i
        (carlsonPartialDeriv j (fun z ↦ f (carlsonAffineForm z u))) z =
      (u i : ℂ) * (u j : ℂ) * f'' := by
  have hinner : carlsonPartialDeriv j (fun z ↦ f (carlsonAffineForm z u)) =
      fun z ↦ (u j : ℂ) * f' (carlsonAffineForm z u) := by
    funext z'
    exact carlsonPartialDeriv_comp_carlsonAffineForm j
      (hf (carlsonAffineForm z' u))
  rw [hinner]
  unfold carlsonPartialDeriv
  have hcomp := HasDerivAt.comp_carlsonAffineForm_update i hf'
  simpa [mul_assoc, mul_left_comm] using (hcomp.const_mul (u j : ℂ)).deriv

/-- Successive Carlson partial derivatives, in the order specified by a list of coordinate
indices.  The head of the list is applied last. -/
def carlsonIteratedPartialDeriv : List ι → ((ι → ℂ) → ℂ) → (ι → ℂ) → ℂ
  | [], G, z => G z
  | i :: is, G, z => carlsonPartialDeriv i (fun w => carlsonIteratedPartialDeriv is G w) z

omit [Fintype ι] in
/-- Carlson and SCV use the same order convention for repeated coordinate differentiation. -/
theorem carlsonIteratedPartialDeriv_eq_iteratedPartialDeriv (is : List ι)
    (G : (ι → ℂ) → ℂ) :
    carlsonIteratedPartialDeriv is G = SeveralComplexVariables.iteratedPartialDeriv is G := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change carlsonPartialDeriv i (carlsonIteratedPartialDeriv is G) = _
    rw [ih, carlsonPartialDeriv_eq_partialDeriv]
    rfl

/-- Mixed Carlson derivatives of a holomorphic function are independent of their order. -/
theorem carlsonIteratedPartialDeriv_perm {U : Set (ι → ℂ)} {G : (ι → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G U) (hU : IsOpen U) {is js : List ι} (h : is.Perm js) :
    Set.EqOn (carlsonIteratedPartialDeriv is G) (carlsonIteratedPartialDeriv js G) U := by
  simp only [carlsonIteratedPartialDeriv_eq_iteratedPartialDeriv]
  exact SeveralComplexVariables.iteratedPartialDeriv_perm hG hU h

/-- Iterated partial differentiation of a Carlson kernel introduces the corresponding product
of simplex coordinates.  This is the pointwise core of Carlson's formula (5.3-2). -/
theorem carlsonIteratedPartialDeriv_comp_carlsonAffineForm
    {f : ℂ → ℂ}
    (hf : ∀ n w, HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f w) w)
    (is : List ι) (z : ι → ℂ) (u : ι → ℝ) :
    carlsonIteratedPartialDeriv is (fun z => f (carlsonAffineForm z u)) z =
      (is.map fun i => (u i : ℂ)).prod *
        iteratedDeriv is.length f (carlsonAffineForm z u) := by
  induction is generalizing z with
  | nil => simp [carlsonIteratedPartialDeriv]
  | cons i is ih =>
      rw [carlsonIteratedPartialDeriv]
      have hfun : (fun w => carlsonIteratedPartialDeriv is
          (fun z => f (carlsonAffineForm z u)) w) =
          fun w => (is.map fun j => (u j : ℂ)).prod *
            iteratedDeriv is.length f (carlsonAffineForm w u) := by
        funext w
        exact ih w
      rw [hfun]
      unfold carlsonPartialDeriv
      have hcomp := HasDerivAt.comp_carlsonAffineForm_update i
        (hf is.length (carlsonAffineForm z u))
      rw [(hcomp.const_mul (is.map fun j => (u j : ℂ)).prod).deriv]
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      ring

/-- The sum of the coordinate partial derivatives used in Carlson's equation (5.3-3). -/
def carlsonTotalDeriv (G : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ i, carlsonPartialDeriv i G z

/-- The total Carlson derivative of a pointwise kernel is the ordinary derivative of the
averaged function, because simplex coordinates sum to one. -/
theorem carlsonTotalDeriv_comp_carlsonAffineForm
    {f : ℂ → ℂ} {f' : ℂ} {z : ι → ℂ} {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    carlsonTotalDeriv (fun z => f (carlsonAffineForm z u)) z = f' := by
  simp_rw [carlsonTotalDeriv, carlsonPartialDeriv_comp_carlsonAffineForm _ hf,
    ← Finset.sum_mul]
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  rw [hsum, one_mul]

/-- A constant-coefficient directional differential operator in Carlson's variables. -/
def carlsonDirectionalDeriv (a : ι → ℂ) (G : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ i, a i * carlsonPartialDeriv i G z

/-- Evaluation of a constant-coefficient directional derivative on a Carlson kernel.  This is
the first-order pointwise identity behind Carlson's more general formula (5.3-4). -/
theorem carlsonDirectionalDeriv_comp_carlsonAffineForm
    (a : ι → ℂ) {f : ℂ → ℂ} {f' : ℂ} {z : ι → ℂ} {u : ι → ℝ}
    (hf : HasDerivAt f f' (carlsonAffineForm z u)) :
    carlsonDirectionalDeriv a (fun z => f (carlsonAffineForm z u)) z =
      (∑ i, a i * (u i : ℂ)) * f' := by
  unfold carlsonDirectionalDeriv
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [carlsonPartialDeriv_comp_carlsonAffineForm i hf]
  ring

/-- Carlson's Euler--Poisson differential expression for a twice differentiable function of
the variables `z`.  The equation in Theorem 5.4-1 asserts that this expression vanishes. -/
def carlsonEulerPoissonOperator (i j : ι) (b z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) : ℂ :=
  (z i - z j) * carlsonPartialDeriv i (carlsonPartialDeriv j G) z +
    b i * carlsonPartialDeriv j G z - b j * carlsonPartialDeriv i G z

omit [Fintype ι] in
/-- The Euler--Poisson operator commutes with multiplication of the dependent function by
a constant. -/
theorem carlsonEulerPoissonOperator_const_mul (c : ℂ) (i j : ι) (b z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) :
    carlsonEulerPoissonOperator i j b z (fun w => c * G w) =
      c * carlsonEulerPoissonOperator i j b z G := by
  simp only [carlsonEulerPoissonOperator, carlsonPartialDeriv,
    deriv_const_mul_field]
  ring

omit [Fintype ι] in
/-- The diagonal members of the Euler--Poisson system vanish identically. -/
@[simp] theorem carlsonEulerPoissonOperator_self (i : ι) (b z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) :
    carlsonEulerPoissonOperator i i b z G = 0 := by
  simp [carlsonEulerPoissonOperator]

/-- Evaluation of the Euler--Poisson operator on a Carlson kernel.  The integral of this
expression is the quantity killed by Carlson's integration-by-parts argument in the proof of
Theorem 5.4-1. -/
theorem carlsonEulerPoissonOperator_comp_carlsonAffineForm
    (i j : ι) (b z : ι → ℂ) (u : ι → ℝ)
    {f f' : ℂ → ℂ} {f'' : ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf' : HasDerivAt f' f'' (carlsonAffineForm z u)) :
    carlsonEulerPoissonOperator i j b z
        (fun z ↦ f (carlsonAffineForm z u)) =
      (z i - z j) * ((u i : ℂ) * (u j : ℂ) * f'') +
        b i * ((u j : ℂ) * f' (carlsonAffineForm z u)) -
        b j * ((u i : ℂ) * f' (carlsonAffineForm z u)) := by
  rw [carlsonEulerPoissonOperator,
    carlsonPartialDeriv_carlsonPartialDeriv_comp_carlsonAffineForm i j hf hf',
    carlsonPartialDeriv_comp_carlsonAffineForm j (hf (carlsonAffineForm z u)),
    carlsonPartialDeriv_comp_carlsonAffineForm i (hf (carlsonAffineForm z u))]

end DirichletTransform

end CarlsonDirichletAverage
