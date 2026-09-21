/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.IteratedTower
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Left-field PBW bases for the finite Ore tower

This is the noncentral left-module layer.  Scalars act through the canonical
coefficient embedding at every stage; no centrality of the coefficient field
inside the Ore ring is used.
-/

namespace AlgebraicAnalysis.OreIteratedPBW

open Polynomial
open Module
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreIteratedTower

noncomputable section


variable {K : Type*} [Field K]

/-- A derivation of the field coefficient ring for an Ore stage. -/
abbrev KDerivation (K : Type*) [Ring K] := OreDivisionDerivation K

/-- The coefficient embedding into a finite iterated Ore tower. -/
def towerCoefficient : (Ds : List (KDerivation K)) →
    (hDs : PairwiseCommutes Ds) → K →+* OreTower Ds hDs
  | [], _ => RingHom.id K
  | D :: Ds, hDs =>
      let T := build Ds hDs.2
      let hD : CommutesWith D Ds := pairwise_head hDs
      (normalCoefficient (T.extend D hD)).comp
        (towerCoefficient Ds hDs.2)

instance towerKModule (Ds : List (KDerivation K))
    (hDs : PairwiseCommutes Ds) : Module K (OreTower Ds hDs) :=
  Module.compHom (OreTower Ds hDs) (towerCoefficient Ds hDs)

/-- The nested natural-number index type for tower monomials. -/
def exponentIndex : List (KDerivation K) → Type
  | [] => PUnit
  | _ :: Ds => ℕ × exponentIndex Ds

instance polynomialKSMul (R : Type*) [Semiring R] [Module K R] :
    SMul K (Polynomial R) :=
  Polynomial.distribSMul.toSMul

instance polynomialKModule (R : Type*) [Semiring R] [Module K R] :
    Module K (Polynomial R) :=
  Polynomial.module

lemma polynomial_smul_eq_C_mul {R : Type*} [Ring R] [Module K R]
    (φ : K →+* R) (hφ : ∀ c : K, ∀ r : R, c • r = φ c * r)
    (c : K) (p : Polynomial R) :
    c • p = Polynomial.C (φ c) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [smul_add, mul_add, hp, hq]
  | monomial n r =>
      apply (Polynomial.toFinsuppIso R).injective
      simp [Polynomial.toFinsuppIso, hφ]

/-- The coefficient-wise additive coordinates of a polynomial. -/
def polynomialToFinsuppLinearEquiv {R : Type*} [Ring R]
    [Module K R] :
    Polynomial R ≃ₗ[K] (ℕ →₀ R) := by
  exact
    { (Polynomial.toFinsuppIso R).toAddEquiv.trans
        (AddMonoidAlgebra.coeffLinearEquiv K).toAddEquiv with
      map_smul' := by
        intro c p
        rfl }

/-- Lift a coefficient basis to the standard polynomial basis. -/
def polynomialBasis (R : Type*) [Ring R] [Module K R]
    (b : Basis ι K R) :
    Basis (ℕ × ι) K (Polynomial R) := by
  let e : Polynomial R ≃ₗ[K] (ℕ × ι →₀ K) :=
    (polynomialToFinsuppLinearEquiv (K := K)).trans
      ((Finsupp.mapRange.linearEquiv b.repr).trans
        (Finsupp.curryLinearEquiv K).symm)
  exact Basis.ofRepr e

/-- The tower normal form as a linear equivalence over the coefficient field. -/
def normalFormLinearEquivK {R : Type*} [Ring R]
    (D : OreDivisionDerivation R) (φ : K →+* R)
    (ψ : K →+* NormalOre D)
    (hψ : ψ = (normalCoefficient D).comp φ)
    [Module K R] [Module K (NormalOre D)]
    (hφ : ∀ c : K, ∀ r : R, c • r = φ c * r)
    (hsmul : ∀ c : K, ∀ z : NormalOre D, c • z = ψ c * z) :
    Polynomial R ≃ₗ[K] NormalOre D := by
  exact
    { normalFormAddEquiv D with
      map_smul' := by
        intro c p
        change normalForm D (c • p) = c • normalForm D p
        rw [polynomial_smul_eq_C_mul φ hφ]
        rw [hsmul, hψ]
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
            rw [mul_add, normalForm_add, hp, hq, normalForm_add]
            noncomm_ring
        | monomial n b =>
            rw [Polynomial.C_mul_monomial, normalForm_monomial]
            rw [normalForm_monomial]
            simp [mul_assoc] }

/-- The PBW basis indexed by nested exponent tuples. -/
def towerPBWBasis : (Ds : List (KDerivation K)) →
    (hDs : PairwiseCommutes Ds) →
    letI : Module K (OreTower Ds hDs) := towerKModule Ds hDs
    Basis (exponentIndex Ds) K (OreTower Ds hDs)
  | [], _ => Basis.singleton PUnit K
  | D :: Ds, hDs => by
      letI : Module K (OreTower (D :: Ds) hDs) :=
        towerKModule (D :: Ds) hDs
      let T := build Ds hDs.2
      let hD : CommutesWith D Ds := pairwise_head hDs
      let φ : K →+* T.carrier := towerCoefficient Ds hDs.2
      let ψ : K →+* NormalOre (T.extend D hD) :=
        (normalCoefficient (T.extend D hD)).comp φ
      letI : Module K T.carrier := towerKModule Ds hDs.2
      letI : Module K (NormalOre (T.extend D hD)) :=
        towerKModule (D :: Ds) hDs
      let b : Basis (exponentIndex Ds) K T.carrier :=
        towerPBWBasis Ds hDs.2
      let pb : Basis (ℕ × exponentIndex Ds) K (Polynomial T.carrier) :=
        polynomialBasis (K := K) T.carrier b
      exact (pb.map (normalFormLinearEquivK (K := K)
        (T.extend D hD) φ ψ rfl (by intro c r; rfl) (by intro c z; rfl)))


end
end AlgebraicAnalysis.OreIteratedPBW
