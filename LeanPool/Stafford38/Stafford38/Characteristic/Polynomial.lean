/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic

/-!
# Polynomial phase space for characteristic support

The order symbol ring of the `n`th Weyl algebra has base variables of fibre
weight zero and cotangent variables of fibre weight one. This file introduces
that ring and its canonical polynomial Poisson bracket without assuming any
characteristic-variety theorem.
-/

namespace Stafford38.Characteristic

/-- Indices for base and cotangent variables. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- Coordinate ring of affine cotangent space. -/
abbrev SymbolRing (k : Type*) [CommRing k] (n : ℕ) :=
  MvPolynomial (PhaseVar n) k

/-- Fibre degree: base variables have weight zero and covariables weight one. -/
def fibreWeight {n : ℕ} : PhaseVar n → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The standard Poisson bracket on affine cotangent space. -/
noncomputable def poissonBracket
    {k : Type*} [CommRing k] {n : ℕ}
    (f g : SymbolRing k n) : SymbolRing k n :=
  ∑ i : Fin n,
    (MvPolynomial.pderiv (Sum.inl i : PhaseVar n) f *
        MvPolynomial.pderiv (Sum.inr i : PhaseVar n) g -
      MvPolynomial.pderiv (Sum.inr i : PhaseVar n) f *
        MvPolynomial.pderiv (Sum.inl i : PhaseVar n) g)

/-- An ideal is Poisson when it is stable under bracketing with every symbol. -/
def IsPoisson
    {k : Type*} [CommRing k] {n : ℕ}
    (J : Ideal (SymbolRing k n)) : Prop :=
  ∀ f ∈ J, ∀ g, poissonBracket f g ∈ J

@[simp]
theorem poissonBracket_self
    {k : Type*} [CommRing k] {n : ℕ} (f : SymbolRing k n) :
    poissonBracket f f = 0 := by
  simp [poissonBracket, mul_comm]

end Stafford38.Characteristic
