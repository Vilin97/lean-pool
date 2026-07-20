/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Basic definitions for Pythagorean polynomial parametrizations

This file contains the shared definitions used by the Frisch--Vaserstein
formalization setup.
-/

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial



/-- A triple of integers (x,y,z) is a Pythagorean triple if x² + y² = z². -/
def IsPythagoreanTriple (x y z : ℤ) : Prop := x^2 + y^2 = z^2

/-- The set of all Pythagorean triples. -/
def pythagoreanTriples : Set (ℤ × ℤ × ℤ) := {(x, y, z) | IsPythagoreanTriple x y z}

/-- The set of all positive Pythagorean triples (x,y,z > 0). -/
def positivePythagoreanTriples : Set (ℤ × ℤ × ℤ) :=
  {(x, y, z) | 0 < x ∧ 0 < y ∧ 0 < z ∧ IsPythagoreanTriple x y z}

/-- Multivariate polynomials with integer coefficients in n variables. -/
abbrev IntPoly (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- Multivariate polynomials with rational coefficients in n variables. -/
abbrev RatPoly (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- A rational-coefficient polynomial is integer-valued if it evaluates to an integer
at every integer tuple. -/
def IsIntValued {n : ℕ} (p : RatPoly n) : Prop :=
  ∀ a : Fin n → ℤ, ∃ k : ℤ, eval (fun i => (a i : ℚ)) p = (k : ℚ)

/-- The paper's ring `Int(ℤⁿ)` of integer-valued rational polynomials, represented as
a subring of `ℚ[x₁, ..., xₙ]`. -/
def IntValuedSubring (n : ℕ) : Subring (RatPoly n) where
  carrier := {p | IsIntValued p}
  zero_mem' := by
    intro a
    use 0
    simp
  one_mem' := by
    intro a
    use 1
    simp
  add_mem' := by
    intro p q hp hq a
    rcases hp a with ⟨m, hm⟩
    rcases hq a with ⟨l, hl⟩
    use m + l
    simp [hm, hl]
  neg_mem' := by
    intro p hp a
    rcases hp a with ⟨m, hm⟩
    use -m
    simp [hm]
  mul_mem' := by
    intro p q hp hq a
    rcases hp a with ⟨m, hm⟩
    rcases hq a with ⟨l, hl⟩
    use m * l
    simp [hm, hl]

/-- The type of integer-valued rational polynomials in `n` variables. -/
abbrev IntegerValuedPoly (n : ℕ) : Type := IntValuedSubring n

/-- Evaluate an integer-coefficient polynomial at an integer tuple. -/
noncomputable def intPolyEval {n : ℕ} (p : IntPoly n) (a : Fin n → ℤ) : ℤ :=
  eval a p

/-- Evaluate a rational-coefficient polynomial at an integer tuple. -/
noncomputable def ratPolyEval {n : ℕ} (p : RatPoly n) (a : Fin n → ℤ) : ℚ :=
  eval (fun i => (a i : ℚ)) p

/-- General `k`-tuple version of parametrization by one tuple of integer-coefficient
polynomials, matching `pyth.tex` lines 104--116. -/
def IntPolyTupleParametrizes {n k : ℕ} (F : Fin k → IntPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  S = {v | ∃ a : Fin n → ℤ, ∀ i : Fin k, intPolyEval (F i) a = v i}

/-- General `k`-tuple version of parametrization by one tuple of integer-valued
polynomials, matching `pyth.tex` lines 104--116. -/
def IntValuedTupleParametrizes {n k : ℕ} (F : Fin k → RatPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  (∀ i : Fin k, IsIntValued (F i)) ∧
    S = {v | ∃ a : Fin n → ℤ, ∀ i : Fin k, ratPolyEval (F i) a = (v i : ℚ)}

/-- Parametrization by a finite number of `k`-tuples of integer-coefficient
polynomials, matching `pyth.tex` lines 118--125. -/
def FiniteIntPolyTupleParametrizes {m n k : ℕ} (F : Fin m → Fin k → IntPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  S = {v | ∃ j : Fin m, ∃ a : Fin n → ℤ, ∀ i : Fin k,
    intPolyEval (F j i) a = v i}

/-- Parametrization by a finite number of `k`-tuples of integer-valued polynomials,
matching `pyth.tex` lines 118--125. -/
def FiniteIntValuedTupleParametrizes {m n k : ℕ} (F : Fin m → Fin k → RatPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  (∀ j : Fin m, ∀ i : Fin k, IsIntValued (F j i)) ∧
    S = {v | ∃ j : Fin m, ∃ a : Fin n → ℤ, ∀ i : Fin k,
      ratPolyEval (F j i) a = (v i : ℚ)}

/-- A triple of integer-coefficient polynomials parametrizes a set S ⊆ ℤ³
if S equals the image of the polynomial map ℤⁿ → ℤ³. -/
def IntPolyParametrizes {n : ℕ} (f g h : IntPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    intPolyEval f a = x ∧ intPolyEval g a = y ∧ intPolyEval h a = z}

/-- A triple of rational-coefficient polynomials parametrizes a set S ⊆ ℤ³
if each is integer-valued and S equals the image of the polynomial map. -/
def IntValuedParametrizes {n : ℕ} (f g h : RatPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  IsIntValued f ∧ IsIntValued g ∧ IsIntValued h ∧
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    ratPolyEval f a = (x : ℚ) ∧ ratPolyEval g a = (y : ℚ) ∧ ratPolyEval h a = (z : ℚ)}

end LeanPool.PythagoreanPolynomialParametrization
