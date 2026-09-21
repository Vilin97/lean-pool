/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Ore.ScalarAlgebra
import LeanPool.Stafford38.Stafford38.Ore.PairStage
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Scalar-linear Ore normal forms

The additive normal-form equivalence is linear over every central scalar ring
killed by the coefficient derivation.  This is the scalar interface needed to
turn the iterated Ore normal form into a PBW basis.
-/

namespace Stafford38.OreLinearNormalForm

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreScalarAlgebra
open Stafford38.OreCoordinateStage
open Stafford38.OrePairStage

noncomputable section

/-- Polynomials are linearly equivalent to their coefficient finsupps. -/
def polynomialFinsuppLinearEquiv
    {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R] :
    Polynomial R ≃ₗ[k] (ℕ →₀ R) :=
  { (Polynomial.toFinsuppIso R).toAddEquiv.trans
      (AddMonoidAlgebra.coeffLinearEquiv k).toAddEquiv with
    map_smul' := by
      intro c p
      rfl }

/-- Apply a linear equivalence independently to every polynomial
coefficient. -/
def polynomialMapRangeLinearEquiv
    {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S) :
    Polynomial R ≃ₗ[k] Polynomial S :=
  (polynomialFinsuppLinearEquiv (k := k) (R := R)).trans
    ((Finsupp.mapRange.linearEquiv e).trans
      (polynomialFinsuppLinearEquiv (k := k) (R := S)).symm)

@[simp] theorem polynomialMapRangeLinearEquiv_C
    {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S) (r : R) :
    polynomialMapRangeLinearEquiv e (Polynomial.C r) =
      Polynomial.C (e r) := by
  apply (Polynomial.toFinsuppIso S).injective
  simp [polynomialMapRangeLinearEquiv, polynomialFinsuppLinearEquiv]

@[simp] theorem polynomialMapRangeLinearEquiv_monomial
    {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S) (n : ℕ) (r : R) :
    polynomialMapRangeLinearEquiv e (Polynomial.monomial n r) =
      Polynomial.monomial n (e r) := by
  apply (Polynomial.toFinsuppIso S).injective
  simp [polynomialMapRangeLinearEquiv, polynomialFinsuppLinearEquiv]

@[simp] theorem polynomialMapRangeLinearEquiv_X
    {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S)
    (h1 : e 1 = 1) :
    polynomialMapRangeLinearEquiv e Polynomial.X = Polynomial.X := by
  apply (Polynomial.toFinsuppIso S).injective
  simp [polynomialMapRangeLinearEquiv, polynomialFinsuppLinearEquiv, h1]

@[simp] theorem polynomialMapRangeLinearEquiv_one
    {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S)
    (h1 : e 1 = 1) :
    polynomialMapRangeLinearEquiv e 1 = 1 := by
  change polynomialMapRangeLinearEquiv e (Polynomial.C 1) = Polynomial.C 1
  rw [polynomialMapRangeLinearEquiv_C, h1]

/-- A univariate polynomial is a multivariate polynomial in one `PUnit`
variable, linearly over any central ground ring. -/
def univariateMvPolynomialLinearEquiv
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] :
    Polynomial R ≃ₗ[k] MvPolynomial PUnit.{1} R :=
  ((MvPolynomial.pUnitAlgEquiv R).symm.toLinearEquiv).restrictScalars k

@[simp] theorem univariateMvPolynomialLinearEquiv_C
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (r : R) :
    univariateMvPolynomialLinearEquiv (k := k) (R := R) (Polynomial.C r) =
      MvPolynomial.C r := by
  simp [univariateMvPolynomialLinearEquiv, MvPolynomial.pUnitAlgEquiv]

@[simp] theorem univariateMvPolynomialLinearEquiv_X
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] :
    univariateMvPolynomialLinearEquiv (k := k) (R := R) Polynomial.X =
      MvPolynomial.X (PUnit.unit : PUnit.{1}) := by
  simp [univariateMvPolynomialLinearEquiv, MvPolynomial.pUnitAlgEquiv]

/-- Flatten two nested univariate polynomial layers into two commuting symbol
variables as an algebra equivalence over the coefficient ring. -/
def nestedPolynomialAlgEquiv (R : Type*) [CommRing R] :
    Polynomial (Polynomial R) ≃ₐ[R]
      MvPolynomial (PUnit.{1} ⊕ PUnit.{1}) R :=
  (Polynomial.mapAlgEquiv ((MvPolynomial.pUnitAlgEquiv R).symm)).trans
    ((((MvPolynomial.pUnitAlgEquiv (MvPolynomial PUnit.{1} R)).symm
      ).restrictScalars R).trans
        (MvPolynomial.sumAlgEquiv R PUnit.{1} PUnit.{1}).symm)

/-- The scalar-linear form of `nestedPolynomialAlgEquiv`. -/
def nestedPolynomialLinearEquiv
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] :
    Polynomial (Polynomial R) ≃ₗ[k]
      MvPolynomial (PUnit.{1} ⊕ PUnit.{1}) R :=
  (nestedPolynomialAlgEquiv R).toLinearEquiv.restrictScalars k

@[simp] theorem nestedPolynomialLinearEquiv_constant
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (r : R) :
    nestedPolynomialLinearEquiv (k := k) (R := R)
        (Polynomial.C (Polynomial.C r)) = MvPolynomial.C r := by
  simp [nestedPolynomialLinearEquiv, nestedPolynomialAlgEquiv]

@[simp] theorem nestedPolynomialLinearEquiv_coordinate
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] :
    nestedPolynomialLinearEquiv (k := k) (R := R)
        (Polynomial.C Polynomial.X) =
      MvPolynomial.X (.inr (PUnit.unit : PUnit.{1})) := by
  simp [nestedPolynomialLinearEquiv, nestedPolynomialAlgEquiv]

@[simp] theorem nestedPolynomialLinearEquiv_momentum
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] :
    nestedPolynomialLinearEquiv (k := k) (R := R) Polynomial.X =
      MvPolynomial.X (.inl (PUnit.unit : PUnit.{1})) := by
  simp [nestedPolynomialLinearEquiv, nestedPolynomialAlgEquiv]

private theorem nestedPolynomialLinearEquiv_mul
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (f g : Polynomial (Polynomial R)) :
    nestedPolynomialLinearEquiv (k := k) (R := R) (f * g) =
      nestedPolynomialLinearEquiv (k := k) (R := R) f *
        nestedPolynomialLinearEquiv (k := k) (R := R) g := by
  change nestedPolynomialAlgEquiv R (f * g) =
    nestedPolynomialAlgEquiv R f * nestedPolynomialAlgEquiv R g
  exact map_mul (nestedPolynomialAlgEquiv R) f g

private theorem nestedPolynomialLinearEquiv_pow
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (f : Polynomial (Polynomial R)) (n : ℕ) :
    nestedPolynomialLinearEquiv (k := k) (R := R) (f ^ n) =
      nestedPolynomialLinearEquiv (k := k) (R := R) f ^ n := by
  change nestedPolynomialAlgEquiv R (f ^ n) =
    nestedPolynomialAlgEquiv R f ^ n
  exact map_pow (nestedPolynomialAlgEquiv R) f n

/-- Nested univariate monomials become the two corresponding commuting symbol
powers, with the outer polynomial variable in the left summand. -/
theorem nestedPolynomialLinearEquiv_monomial
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (r : R) (a p : ℕ) :
    nestedPolynomialLinearEquiv (k := k) (R := R)
        (Polynomial.monomial p (Polynomial.monomial a r)) =
      MvPolynomial.X (.inl (PUnit.unit : PUnit.{1})) ^ p *
      MvPolynomial.X (.inr (PUnit.unit : PUnit.{1})) ^ a *
        MvPolynomial.C r := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [show Polynomial.C (Polynomial.C r * Polynomial.X ^ a) =
      Polynomial.C (Polynomial.C r) *
        Polynomial.C Polynomial.X ^ a by rw [map_mul, map_pow]]
  rw [nestedPolynomialLinearEquiv_mul,
    nestedPolynomialLinearEquiv_mul,
    nestedPolynomialLinearEquiv_pow,
    nestedPolynomialLinearEquiv_pow,
    nestedPolynomialLinearEquiv_constant,
    nestedPolynomialLinearEquiv_coordinate,
    nestedPolynomialLinearEquiv_momentum]
  ring

section OneVariable

variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (D : OreDivisionDerivation B)
variable [Algebra k (NormalOre D)]
variable (hAlg : algebraMap k (NormalOre D) =
  (normalCoefficient D).comp (algebraMap k B))

include hAlg

/-- The coefficient-left normal-form map respects central scalar
multiplication. -/
theorem normalForm_smul (c : k) (p : Polynomial B) :
    normalForm D (c • p) = c • normalForm D p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [smul_add, normalForm_add, normalForm_add, hp, hq,
        Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_add]
  | monomial n b =>
      rw [Polynomial.smul_monomial, normalForm_monomial,
        normalForm_monomial]
      rw [Algebra.smul_def c b]
      have hs : c • (normalCoefficient D b * normalVariable D ^ n) =
          algebraMap k (NormalOre D) c *
            (normalCoefficient D b * normalVariable D ^ n) :=
        Algebra.smul_def c _
      rw [hs, hAlg]
      change normalCoefficient D (algebraMap k B c * b) * normalVariable D ^ n =
        normalCoefficient D (algebraMap k B c) *
          (normalCoefficient D b * normalVariable D ^ n)
      rw [map_mul, mul_assoc]

/-- Ore normal forms are linearly equivalent to ordinary coefficient-left
polynomials. -/
def normalFormLinearEquiv : Polynomial B ≃ₗ[k] NormalOre D :=
  { normalFormAddEquiv D with
    map_smul' := normalForm_smul D hAlg }

@[simp] theorem normalFormLinearEquiv_apply (p : Polynomial B) :
    normalFormLinearEquiv D hAlg p = normalForm D p := rfl

@[simp] theorem normalFormLinearEquiv_symm_normalForm (p : Polynomial B) :
    (normalFormLinearEquiv D hAlg).symm (normalForm D p) = p :=
  (normalFormLinearEquiv D hAlg).symm_apply_apply p

@[simp] theorem normalFormLinearEquiv_symm_coefficient (b : B) :
    (normalFormLinearEquiv D hAlg).symm (normalCoefficient D b) =
      Polynomial.C b := by
  rw [← normalForm_C, normalFormLinearEquiv_symm_normalForm]

@[simp] theorem normalFormLinearEquiv_symm_variable :
    (normalFormLinearEquiv D hAlg).symm (normalVariable D) =
      Polynomial.X := by
  rw [normalVariable, normalFormLinearEquiv_symm_normalForm]

@[simp] theorem normalFormLinearEquiv_symm_one :
    (normalFormLinearEquiv D hAlg).symm 1 = 1 := by
  rw [← normalForm_one D, normalFormLinearEquiv_symm_normalForm]

end OneVariable

section Pair


/-- Expose the two coefficient-left polynomial layers of a pair stage and
apply a chosen linear coordinate system to the old coefficients. -/
def pairNormalFormLinearEquiv
    {k B S : Type*} [CommRing k] [Ring B] [Algebra k B]
    [CommRing S] [Algebra k S]
    [Algebra k (CoordinateStage (B := B))]
    [Algebra k (PairStage (B := B))]
    (hInner : algebraMap k (CoordinateStage (B := B)) =
      (normalCoefficient zeroDerivation).comp (algebraMap k B))
    (hOuter : algebraMap k (PairStage (B := B)) =
      (normalCoefficient coordinateDerivation).comp
        (algebraMap k (CoordinateStage (B := B))))
    (e : B ≃ₗ[k] S) :
    PairStage (B := B) ≃ₗ[k] Polynomial (Polynomial S) :=
  (normalFormLinearEquiv coordinateDerivation hOuter).symm.trans
    (polynomialMapRangeLinearEquiv
      ((normalFormLinearEquiv zeroDerivation hInner).symm.trans
        (polynomialMapRangeLinearEquiv e)))

@[simp] theorem pairNormalFormLinearEquiv_coefficient
    {k B S : Type*} [CommRing k] [Ring B] [Algebra k B]
    [CommRing S] [Algebra k S]
    [Algebra k (CoordinateStage (B := B))]
    [Algebra k (PairStage (B := B))]
    (hInner) (hOuter) (e : B ≃ₗ[k] S) (b : B) :
    pairNormalFormLinearEquiv hInner hOuter e (pairCoefficient b) =
      Polynomial.C (Polynomial.C (e b)) := by
  simp [pairNormalFormLinearEquiv, pairCoefficient]

@[simp] theorem pairNormalFormLinearEquiv_coordinate
    {k B S : Type*} [CommRing k] [Ring B] [Algebra k B]
    [CommRing S] [Algebra k S]
    [Algebra k (CoordinateStage (B := B))]
    [Algebra k (PairStage (B := B))]
    (hInner) (hOuter) (e : B ≃ₗ[k] S) (h1 : e 1 = 1) :
    pairNormalFormLinearEquiv hInner hOuter e pairCoordinate =
      Polynomial.C Polynomial.X := by
  simp [pairNormalFormLinearEquiv, pairCoordinate,
    polynomialMapRangeLinearEquiv_X _ h1]

@[simp] theorem pairNormalFormLinearEquiv_momentum
    {k B S : Type*} [CommRing k] [Ring B] [Algebra k B]
    [CommRing S] [Algebra k S]
    [Algebra k (CoordinateStage (B := B))]
    [Algebra k (PairStage (B := B))]
    (hInner) (hOuter) (e : B ≃ₗ[k] S) (h1 : e 1 = 1) :
    pairNormalFormLinearEquiv hInner hOuter e pairMomentum =
      Polynomial.X := by
  have hInnerOne :
      ((normalFormLinearEquiv zeroDerivation hInner).symm.trans
        (polynomialMapRangeLinearEquiv e)) 1 = 1 := by
    simp [h1, polynomialMapRangeLinearEquiv_one]
  simp [pairNormalFormLinearEquiv, pairMomentum,
    polynomialMapRangeLinearEquiv_X _ hInnerOne]

/-- The two-stage normal-form map sends a coefficient followed by powers of
the new coordinate and momentum to the corresponding nested monomial. -/
@[simp] theorem pairNormalFormLinearEquiv_orderedMonomial
    {k B S : Type*} [CommRing k] [Ring B] [Algebra k B]
    [CommRing S] [Algebra k S]
    [Algebra k (CoordinateStage (B := B))]
    [Algebra k (PairStage (B := B))]
    (hInner : algebraMap k (CoordinateStage (B := B)) =
      (normalCoefficient zeroDerivation).comp (algebraMap k B))
    (hOuter : algebraMap k (PairStage (B := B)) =
      (normalCoefficient coordinateDerivation).comp
        (algebraMap k (CoordinateStage (B := B))))
    (e : B ≃ₗ[k] S) (b : B) (a p : ℕ) :
    pairNormalFormLinearEquiv hInner hOuter e
        (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ p) =
      Polynomial.monomial p (Polynomial.monomial a (e b)) := by
  have hnormal :
      pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ p =
        normalForm coordinateDerivation
          (Polynomial.monomial p
            (normalForm zeroDerivation (Polynomial.monomial a b))) := by
    rw [normalForm_monomial, normalForm_monomial]
    change
      normalCoefficient coordinateDerivation (normalCoefficient zeroDerivation b) *
          (normalCoefficient coordinateDerivation (normalVariable zeroDerivation)) ^ a *
        normalVariable coordinateDerivation ^ p = _
    rw [map_mul, map_pow]
  rw [hnormal]
  simp [pairNormalFormLinearEquiv]

end Pair


end

end Stafford38.OreLinearNormalForm
