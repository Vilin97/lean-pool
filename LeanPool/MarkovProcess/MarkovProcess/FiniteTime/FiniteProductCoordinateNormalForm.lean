/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteProductCompactSupportApproximation


/-!
# Explicit coordinate-product normal forms

This file replaces abstract membership in the coordinate `C₀` algebra by a concrete finite
sum of finite products.  Factors are stored in lists, so the normal form can subsequently be
consumed by recursion (for example, by iterated kernel integration).  The empty factor list is
the constant function `1`; in particular the representation treats constants and an empty
coordinate type without exceptional cases.
-/

@[expose] public section

open scoped CompactlySupported ZeroAtInfty

namespace MarkovProcess.PiContinuousMap

variable {I α : Type*} [TopologicalSpace α]

/-- A scalar coefficient together with a finite ordered list of one-coordinate `C₀` factors. -/
structure CoordinateProductTerm (I α : Type*) [TopologicalSpace α] where
  /-- The scalar multiplier of the coordinate product. -/
  coefficient : ℝ
  /-- The coordinate indices and compactly supported factors, in product order. -/
  factors : List (I × C₀(α, ℝ))

/-- The continuous function represented by one coordinate-product term. -/
def CoordinateProductTerm.toContinuousMap (t : CoordinateProductTerm I α) : C(I → α, ℝ) :=
  t.coefficient • (t.factors.map (fun p ↦ coordinate p.1 (p.2 : C(α, ℝ)))).prod

@[simp]
theorem CoordinateProductTerm.toContinuousMap_apply
    (t : CoordinateProductTerm I α) (x : I → α) :
    t.toContinuousMap x = t.coefficient * (t.factors.map (fun p ↦ p.2 (x p.1))).prod := by
  rw [CoordinateProductTerm.toContinuousMap, ContinuousMap.smul_apply, smul_eq_mul]
  congr 1
  induction t.factors with
  | nil => rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons, ContinuousMap.mul_apply, coordinate_apply]
      change p.2 (x p.1) * _ = p.2 (x p.1) * _
      exact congrArg (fun z ↦ p.2 (x p.1) * z) ih

/-- Evaluate a finite list of coordinate-product terms by summing its terms. -/
def coordinatePolynomial (terms : List (CoordinateProductTerm I α)) : C(I → α, ℝ) :=
  (terms.map CoordinateProductTerm.toContinuousMap).sum

@[simp]
theorem coordinatePolynomial_apply (terms : List (CoordinateProductTerm I α)) (x : I → α) :
    coordinatePolynomial terms x =
      (terms.map fun t ↦ t.coefficient * (t.factors.map fun p ↦ p.2 (x p.1)).prod).sum := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      rw [coordinatePolynomial]
      simp only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
        CoordinateProductTerm.toContinuousMap_apply]
      change _ + coordinatePolynomial terms x = _
      rw [ih]

@[simp]
theorem coordinatePolynomial_nil :
    coordinatePolynomial ([] : List (CoordinateProductTerm I α)) = 0 :=
  rfl

@[simp]
theorem coordinatePolynomial_cons (t : CoordinateProductTerm I α)
    (terms : List (CoordinateProductTerm I α)) :
    coordinatePolynomial (t :: terms) = t.toContinuousMap + coordinatePolynomial terms :=
  rfl

@[simp]
theorem coordinatePolynomial_append (left right : List (CoordinateProductTerm I α)) :
    coordinatePolynomial (left ++ right) = coordinatePolynomial left + coordinatePolynomial
        right := by
  simp only [coordinatePolynomial, List.map_append, List.sum_append]

/-- Multiply two terms by multiplying coefficients and concatenating their factor lists. -/
def CoordinateProductTerm.mul (s t : CoordinateProductTerm I α) :
    CoordinateProductTerm I α :=
  ⟨s.coefficient * t.coefficient, s.factors ++ t.factors⟩

@[simp]
theorem CoordinateProductTerm.toContinuousMap_mul
    (s t : CoordinateProductTerm I α) :
    (s.mul t).toContinuousMap = s.toContinuousMap * t.toContinuousMap := by
  ext x
  simp only [CoordinateProductTerm.toContinuousMap_apply, CoordinateProductTerm.mul,
    List.map_append, List.prod_append, ContinuousMap.mul_apply]
  ac_rfl

@[simp]
theorem coordinatePolynomial_map_mul (s : CoordinateProductTerm I α)
    (terms : List (CoordinateProductTerm I α)) :
    coordinatePolynomial (terms.map s.mul) =
      s.toContinuousMap * coordinatePolynomial terms := by
  induction terms with
  | nil => simp only [List.map_nil, coordinatePolynomial_nil, mul_zero]
  | cons t terms ih =>
      simp only [List.map_cons, coordinatePolynomial_cons,
        CoordinateProductTerm.toContinuousMap_mul, ih, mul_add]

/-- Distributive product of two finite coordinate polynomials. -/
def coordinatePolynomialMul (left right : List (CoordinateProductTerm I α)) :
    List (CoordinateProductTerm I α) :=
  left.flatMap fun s ↦ right.map s.mul

@[simp]
theorem coordinatePolynomial_coordinatePolynomialMul
    (left right : List (CoordinateProductTerm I α)) :
    coordinatePolynomial (coordinatePolynomialMul left right) =
      coordinatePolynomial left * coordinatePolynomial right := by
  induction left with
  | nil => simp only [coordinatePolynomialMul, List.flatMap_nil, coordinatePolynomial_nil, zero_mul]
  | cons s left ih =>
      simp only [coordinatePolynomialMul, List.flatMap_cons, coordinatePolynomial_append,
        coordinatePolynomial_map_mul, coordinatePolynomial_cons, add_mul]
      change s.toContinuousMap * coordinatePolynomial right +
        coordinatePolynomial (coordinatePolynomialMul left right) = _
      rw [ih]

/-- Every member of the coordinate `C₀` algebra is an explicit finite sum of scalar multiples
of finite products of one-coordinate `C₀` functions. -/
theorem exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra
    {h : C(I → α, ℝ)} (hh : h ∈ coordinateC0Subalgebra (I := I) (α := α)) :
    ∃ terms : List (CoordinateProductTerm I α), h = coordinatePolynomial terms := by
  change h ∈ Algebra.adjoin ℝ
    {g | ∃ (i : I) (f : C₀(α, ℝ)), g = coordinate i (f : C(α, ℝ))} at hh
  induction hh using Algebra.adjoin_induction with
  | mem g hg =>
      obtain ⟨i, f, rfl⟩ := hg
      exact ⟨[⟨1, [(i, f)]⟩], by ext x; simp [coordinatePolynomial,
        CoordinateProductTerm.toContinuousMap]⟩
  | algebraMap r =>
      exact ⟨[⟨r, []⟩], by ext x; simp [coordinatePolynomial,
        CoordinateProductTerm.toContinuousMap]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨left, hleft⟩ := ihx
      obtain ⟨right, hright⟩ := ihy
      exact ⟨left ++ right, by rw [coordinatePolynomial_append, ← hleft, ← hright]⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨left, hleft⟩ := ihx
      obtain ⟨right, hright⟩ := ihy
      exact ⟨coordinatePolynomialMul left right, by
        rw [coordinatePolynomial_coordinatePolynomialMul, ← hleft, ← hright]⟩

/-- Every compactly supported continuous finite-product test is uniformly approximable on the
whole product by an explicit finite sum of scalar multiples of coordinate products. -/
theorem exists_coordinateProductTerms_near_compactlySupported
    [Finite I] [T3Space α] [LocallyCompactSpace α]
    (f : C_c(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ terms : List (CoordinateProductTerm I α),
      ∀ x, ‖(terms.map fun t ↦
        t.coefficient * (t.factors.map fun p ↦ p.2 (x p.1)).prod).sum - f x‖ < epsilon := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨h, hh, hnear⟩ :=
    exists_coordinateC0Subalgebra_near_compactlySupported f hepsilon
  obtain ⟨terms, rfl⟩ := exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra hh
  refine ⟨terms, fun x ↦ ?_⟩
  rw [← coordinatePolynomial_apply]
  exact hnear x

end MarkovProcess.PiContinuousMap
