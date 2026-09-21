/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence
import LeanPool.Stafford38.Stafford38.Ore.LinearNormalForm
import LeanPool.Stafford38.Stafford38.Characteristic.Polynomial
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Ordered PBW basis from Ore normal forms

The checked iterated Ore normal form gives a scalar-linear equivalence with
the commutative polynomial symbol space.  Transport across the independently
proved presented/iterated algebra equivalence yields a free-module basis
indexed by commutative monomials, without using monomial independence in the
quotient presentation.  Recursive all-degree formulas identify those basis
vectors with ordered products of the named Weyl generators.
-/

namespace Stafford38.WeylPBW

open Stafford
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open Stafford38.Characteristic
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OreLinearNormalForm
open Stafford38.OrePairStage
open Stafford38.OreScalarAlgebra
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Reindex the two newest symbol variables followed by the old variables to
the standard newest-first coordinate/momentum indexing. -/
def phaseSuccEquiv (n : Nat) :
    ((PUnit.{1} ⊕ PUnit.{1}) ⊕ PhaseVar n) ≃ PhaseVar (n + 1) where
  toFun
    | .inl (.inl _) => .inr 0
    | .inl (.inr _) => .inl 0
    | .inr (.inl i) => .inl i.succ
    | .inr (.inr i) => .inr i.succ
  invFun
    | .inl i => Fin.cases (.inl (.inr PUnit.unit))
        (fun j => .inr (.inl j)) i
    | .inr i => Fin.cases (.inl (.inl PUnit.unit))
        (fun j => .inr (.inr j)) i
  left_inv x := by
    rcases x with (⟨⟨u⟩ | ⟨u⟩⟩ | ⟨i | i⟩) <;> rfl
  right_inv x := by
    rcases x with (i | i)
    · exact Fin.cases rfl (fun _ => rfl) i
    · exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem phaseSuccEquiv_old (n : Nat) (i : PhaseVar n) :
    phaseSuccEquiv n (.inr i) = oldIndex i := by
  cases i <;> rfl

/-- Flatten the two new univariate normal-form layers and the old symbol
coefficients into the standard rank-successor symbol ring. -/
def flattenPairSymbols (n : Nat) :
    Polynomial (Polynomial (SymbolRing k n)) ≃ₗ[k] SymbolRing k (n + 1) :=
  (nestedPolynomialLinearEquiv.{u, u}
      (k := k) (R := SymbolRing k n)).trans
    ((((MvPolynomial.sumAlgEquiv k (PUnit.{1} ⊕ PUnit.{1}) (PhaseVar n)).symm
      ).toLinearEquiv).trans
        (MvPolynomial.renameEquiv k (phaseSuccEquiv n)).toLinearEquiv)

@[simp] theorem flattenPairSymbols_coordinate (n : Nat) :
    flattenPairSymbols k n (Polynomial.C Polynomial.X) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) := by
  simp [flattenPairSymbols, nestedPolynomialLinearEquiv_coordinate,
    MvPolynomial.sumAlgEquiv_symm_X]
  rfl

@[simp] theorem flattenPairSymbols_momentum (n : Nat) :
    flattenPairSymbols k n Polynomial.X =
      MvPolynomial.X (.inr (0 : Fin (n + 1))) := by
  simp [flattenPairSymbols, nestedPolynomialLinearEquiv_momentum,
    MvPolynomial.sumAlgEquiv_symm_X]
  rfl

@[simp] theorem flattenPairSymbols_one (n : Nat) :
    flattenPairSymbols k n 1 = 1 := by
  change flattenPairSymbols k n (Polynomial.C (Polynomial.C 1)) = 1
  rw [flattenPairSymbols, LinearEquiv.trans_apply,
    nestedPolynomialLinearEquiv_constant]
  simp

@[simp] theorem flattenPairSymbols_oldGenerator (n : Nat) (i : PhaseVar n) :
    flattenPairSymbols k n
        (Polynomial.C (Polynomial.C (MvPolynomial.X i))) =
      MvPolynomial.X (oldIndex i) := by
  simp [flattenPairSymbols, nestedPolynomialLinearEquiv_constant,
    MvPolynomial.sumAlgEquiv_symm_C_X]

theorem iterToSum_C_eq_rename {R S₁ S₂ : Type*} [CommSemiring R]
    (r : MvPolynomial S₂ R) :
    MvPolynomial.iterToSum R S₁ S₂ (MvPolynomial.C r) =
      MvPolynomial.rename Sum.inr r := by
  induction r using MvPolynomial.induction_on with
  | C c =>
      simpa only [MvPolynomial.rename_C] using
        (MvPolynomial.iterToSum_C_C R S₁ S₂ c)
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.iterToSum_C_X,
        MvPolynomial.rename_X]

private theorem sumAlgEquiv_symm_C_eq_rename
    {R S₁ S₂ : Type*} [CommSemiring R] (r : MvPolynomial S₂ R) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂).symm (MvPolynomial.C r) =
      MvPolynomial.rename Sum.inr r := by
  induction r using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.sumAlgEquiv_symm_C_X,
        MvPolynomial.rename_X]

/-- Flattening a nested monomial preserves its two new exponents and embeds
the old symbol polynomial through `oldIndex`. -/
theorem flattenPairSymbols_monomial (n a p : ℕ) (r : SymbolRing k n) :
    flattenPairSymbols k n
        (Polynomial.monomial p (Polynomial.monomial a r)) =
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ p *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) ^ a *
        MvPolynomial.rename oldIndex r := by
  rw [flattenPairSymbols, LinearEquiv.trans_apply,
    nestedPolynomialLinearEquiv_monomial]
  simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    map_mul, map_pow, MvPolynomial.sumAlgEquiv_symm_X,
    sumAlgEquiv_symm_C_eq_rename,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rw [MvPolynomial.rename_rename]
  have hindex : (⇑(phaseSuccEquiv n) ∘ Sum.inr) = oldIndex := by
    funext i
    exact phaseSuccEquiv_old n i
  rw [hindex]
  rfl

/-- The finite exponent vector with coordinate exponents `a` and momentum
exponents `p`. -/
def phaseExponent {n : ℕ} (a p : Fin n → ℕ) : PhaseVar n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim a p)

@[simp] theorem phaseExponent_apply {n : ℕ} (a p : Fin n → ℕ)
    (i : PhaseVar n) : phaseExponent a p i = Sum.elim a p i := rfl

theorem oldIndex_injective {n : ℕ} :
    Function.Injective (@oldIndex n) := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [oldIndex] at h; subst j; rfl
      | inr j => simp [oldIndex] at h
  | inr i =>
      cases j with
      | inl j => simp [oldIndex] at h
      | inr j => simp [oldIndex] at h; subst j; rfl

theorem phaseExponent_succ (n : ℕ) (a p : Fin (n + 1) → ℕ) :
    phaseExponent a p =
      Finsupp.single (.inr (0 : Fin (n + 1))) (p 0) +
        Finsupp.single (.inl (0 : Fin (n + 1))) (a 0) +
        Finsupp.mapDomain oldIndex
          (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) := by
  ext i
  cases i with
  | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Finsupp.add_apply, Finsupp.add_apply,
          Finsupp.mapDomain_notin_range]
        · simp [phaseExponent]
        · rintro ⟨j, hj⟩
          cases j with
          | inl j => exact Fin.succ_ne_zero j (Sum.inl.inj hj)
          | inr j => simp [oldIndex] at hj
      · change a j.succ = _ + _ +
          Finsupp.mapDomain oldIndex
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ))
              (oldIndex (.inl j))
        rw [Finsupp.mapDomain_apply oldIndex_injective]
        simp [phaseExponent, oldIndex, Finsupp.single_apply,
          Fin.succ_ne_zero]
  | inr i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Finsupp.add_apply, Finsupp.add_apply,
          Finsupp.mapDomain_notin_range]
        · simp [phaseExponent]
        · rintro ⟨j, hj⟩
          cases j with
          | inl j => simp [oldIndex] at hj
          | inr j => exact Fin.succ_ne_zero j (Sum.inr.inj hj)
      · change p j.succ = _ + _ +
          Finsupp.mapDomain oldIndex
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ))
              (oldIndex (.inr j))
        rw [Finsupp.mapDomain_apply oldIndex_injective]
        simp [phaseExponent, oldIndex, Finsupp.single_apply,
          Fin.succ_ne_zero]

/-- Ordered monomials in the iterated tower: all older pairs occur first, and
within each pair the coordinate power precedes the momentum power. -/
def iteratedOrderedMonomial :
    (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → IteratedPairStage k n
  | 0, _, _ => 1
  | n + 1, a, p =>
      stageEmbedding k n
          (iteratedOrderedMonomial n (fun i => a i.succ) (fun i => p i.succ)) *
        stageCoordinate k n ^ a 0 * stageMomentum k n ^ p 0

theorem symbolMonomial_succ (n : ℕ) (a p : Fin (n + 1) → ℕ) :
    MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ p 0 *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) ^ a 0 *
        MvPolynomial.rename oldIndex
          (MvPolynomial.monomial
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) 1) =
      MvPolynomial.monomial (phaseExponent a p) (1 : k) := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.rename_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.monomial_mul, mul_one, mul_one, phaseExponent_succ]

/-- Scalar-linear normal-form coordinates for the recursively iterated Ore
tower. -/
def iteratedNormalFormLinearEquiv :
    (n : Nat) → IteratedPairStage k n ≃ₗ[k] SymbolRing k n
  | 0 => (MvPolynomial.isEmptyAlgEquiv k (PhaseVar 0)).symm.toLinearEquiv
  | n + 1 => by
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
        coordinateStageAlgebra
      letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      change PairStage (B := IteratedPairStage k n) ≃ₗ[k] SymbolRing k (n + 1)
      exact (pairNormalFormLinearEquiv
        (normalOreAlgebra_algebraMap zeroDerivation (fun c => by
          exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c)))
        (normalOreAlgebra_algebraMap coordinateDerivation
          coordinateDerivation_algebraMap)
        (iteratedNormalFormLinearEquiv n)).trans (flattenPairSymbols k n)

@[simp] theorem iteratedNormalFormLinearEquiv_one :
    ∀ n : Nat, iteratedNormalFormLinearEquiv k n 1 = 1 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
        coordinateStageAlgebra
      letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      let hInner : algebraMap k (CoordinateStage (B := IteratedPairStage k n)) =
          (normalCoefficient zeroDerivation).comp
            (algebraMap k (IteratedPairStage k n)) :=
        normalOreAlgebra_algebraMap zeroDerivation (fun c : k => by
          exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
      let hOuter : algebraMap k (PairStage (B := IteratedPairStage k n)) =
          (normalCoefficient coordinateDerivation).comp
            (algebraMap k (CoordinateStage (B := IteratedPairStage k n))) :=
        normalOreAlgebra_algebraMap coordinateDerivation
          (fun c : k => coordinateDerivation_algebraMap
            (B := IteratedPairStage k n) c)
      rw [iteratedNormalFormLinearEquiv]
      change flattenPairSymbols k n
        (pairNormalFormLinearEquiv hInner hOuter
          (iteratedNormalFormLinearEquiv k n) 1) = 1
      have hone : (1 : PairStage (B := IteratedPairStage k n)) =
          pairCoefficient (B := IteratedPairStage k n)
            (1 : IteratedPairStage k n) := by
        exact (pairCoefficient (B := IteratedPairStage k n)).map_one.symm
      rw [hone, pairNormalFormLinearEquiv_coefficient, ih]
      exact flattenPairSymbols_one k n

/-- The recursive normal-form coordinate map sends each named Weyl generator
to its corresponding commutative symbol variable. -/
@[simp] theorem iteratedNormalFormLinearEquiv_generator :
    ∀ (n : Nat) (i : PhaseVar n),
      iteratedNormalFormLinearEquiv k n (iteratedGenerator k n i) =
        MvPolynomial.X i := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Sum.elim Fin.elim0 Fin.elim0 i
  | succ n ih =>
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
        coordinateStageAlgebra
      letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      let hInner : algebraMap k (CoordinateStage (B := IteratedPairStage k n)) =
          (normalCoefficient zeroDerivation).comp
            (algebraMap k (IteratedPairStage k n)) :=
        normalOreAlgebra_algebraMap zeroDerivation (fun c : k => by
          exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
      let hOuter : algebraMap k (PairStage (B := IteratedPairStage k n)) =
          (normalCoefficient coordinateDerivation).comp
            (algebraMap k (CoordinateStage (B := IteratedPairStage k n))) :=
        normalOreAlgebra_algebraMap coordinateDerivation
          (fun c : k => coordinateDerivation_algebraMap
            (B := IteratedPairStage k n) c)
      intro i
      cases i with
      | inl i =>
          refine Fin.cases ?_ (fun j => ?_) i
          · change iteratedNormalFormLinearEquiv k (n + 1) (stageCoordinate k n) = _
            rw [iteratedNormalFormLinearEquiv]
            change flattenPairSymbols k n
              (pairNormalFormLinearEquiv hInner hOuter
                (iteratedNormalFormLinearEquiv k n) pairCoordinate) = _
            rw [pairNormalFormLinearEquiv_coordinate _ _ _
              (iteratedNormalFormLinearEquiv_one k n)]
            exact flattenPairSymbols_coordinate k n
          · change iteratedNormalFormLinearEquiv k (n + 1)
              (stageEmbedding k n (iteratedCoordinate k n j)) = _
            rw [iteratedNormalFormLinearEquiv]
            change flattenPairSymbols k n
              (pairNormalFormLinearEquiv hInner hOuter
                (iteratedNormalFormLinearEquiv k n)
                (pairCoefficient (iteratedCoordinate k n j))) = _
            have hij := ih (.inl j)
            change iteratedNormalFormLinearEquiv k n (iteratedCoordinate k n j) =
              MvPolynomial.X (.inl j) at hij
            rw [pairNormalFormLinearEquiv_coefficient, hij,
              flattenPairSymbols_oldGenerator]
            rfl

      | inr i =>
          refine Fin.cases ?_ (fun j => ?_) i
          · change iteratedNormalFormLinearEquiv k (n + 1) (stageMomentum k n) = _
            rw [iteratedNormalFormLinearEquiv]
            change flattenPairSymbols k n
              (pairNormalFormLinearEquiv hInner hOuter
                (iteratedNormalFormLinearEquiv k n) pairMomentum) = _
            rw [pairNormalFormLinearEquiv_momentum _ _ _
              (iteratedNormalFormLinearEquiv_one k n)]
            exact flattenPairSymbols_momentum k n
          · change iteratedNormalFormLinearEquiv k (n + 1)
              (stageEmbedding k n (iteratedMomentum k n j)) = _
            rw [iteratedNormalFormLinearEquiv]
            change flattenPairSymbols k n
              (pairNormalFormLinearEquiv hInner hOuter
                (iteratedNormalFormLinearEquiv k n)
                (pairCoefficient (iteratedMomentum k n j))) = _
            have hij := ih (.inr j)
            change iteratedNormalFormLinearEquiv k n (iteratedMomentum k n j) =
              MvPolynomial.X (.inr j) at hij
            rw [pairNormalFormLinearEquiv_coefficient, hij,
              flattenPairSymbols_oldGenerator]
            rfl

/-- Every recursively ordered product of the named iterated generators has
exactly the corresponding commutative symbol monomial as its normal form. -/
theorem iteratedOrderedMonomial_normal :
    ∀ (n : ℕ) (a p : Fin n → ℕ),
      iteratedNormalFormLinearEquiv k n (iteratedOrderedMonomial k n a p) =
        MvPolynomial.monomial (phaseExponent a p) 1 := by
  intro n
  induction n with
  | zero =>
      intro a p
      change 1 = MvPolynomial.monomial (phaseExponent a p) 1
      have hz : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hz]
      simp [MvPolynomial.monomial_zero']
  | succ n ih =>
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
        coordinateStageAlgebra
      letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      let hInner : algebraMap k (CoordinateStage (B := IteratedPairStage k n)) =
          (normalCoefficient zeroDerivation).comp
            (algebraMap k (IteratedPairStage k n)) :=
        normalOreAlgebra_algebraMap zeroDerivation (fun c : k => by
          exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
      let hOuter : algebraMap k (PairStage (B := IteratedPairStage k n)) =
          (normalCoefficient coordinateDerivation).comp
            (algebraMap k (CoordinateStage (B := IteratedPairStage k n))) :=
        normalOreAlgebra_algebraMap coordinateDerivation
          (fun c : k => coordinateDerivation_algebraMap
            (B := IteratedPairStage k n) c)
      intro a p
      rw [iteratedOrderedMonomial, iteratedNormalFormLinearEquiv]
      change flattenPairSymbols k n
        (pairNormalFormLinearEquiv hInner hOuter
          (iteratedNormalFormLinearEquiv k n)
          (pairCoefficient (B := IteratedPairStage k n)
              (iteratedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ)) *
            pairCoordinate (B := IteratedPairStage k n) ^ a 0 *
            pairMomentum (B := IteratedPairStage k n) ^ p 0)) = _
      rw [pairNormalFormLinearEquiv_orderedMonomial,
        ih (fun i => a i.succ) (fun i => p i.succ),
        flattenPairSymbols_monomial, symbolMonomial_succ]

/-- Append powers of the newest coordinate and momentum to an arbitrary old
coefficient in normal order. -/
def iteratedCoefficientOrdered (n a p : ℕ) (z : IteratedPairStage k n) :
    IteratedPairStage k (n + 1) :=
  stageEmbedding k n z * stageCoordinate k n ^ a * stageMomentum k n ^ p

/-- Appending a normal-ordered newest pair shifts the old symbol polynomial by
the corresponding two monomial powers. -/
theorem iteratedNormalFormLinearEquiv_coefficient_ordered
    (n a p : ℕ) (z : IteratedPairStage k n) :
    iteratedNormalFormLinearEquiv k (n + 1)
        (iteratedCoefficientOrdered k n a p z) =
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ p *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) ^ a *
        MvPolynomial.rename oldIndex (iteratedNormalFormLinearEquiv k n z) := by
  letI : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateStageAlgebra
  letI : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  let hInner : algebraMap k (CoordinateStage (B := IteratedPairStage k n)) =
      (normalCoefficient zeroDerivation).comp
        (algebraMap k (IteratedPairStage k n)) :=
    normalOreAlgebra_algebraMap zeroDerivation (fun c : k => by
      exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c))
  let hOuter : algebraMap k (PairStage (B := IteratedPairStage k n)) =
      (normalCoefficient coordinateDerivation).comp
        (algebraMap k (CoordinateStage (B := IteratedPairStage k n))) :=
    normalOreAlgebra_algebraMap coordinateDerivation
      (fun c : k => coordinateDerivation_algebraMap
        (B := IteratedPairStage k n) c)
  rw [iteratedCoefficientOrdered, iteratedNormalFormLinearEquiv]
  change flattenPairSymbols k n
      (pairNormalFormLinearEquiv (B := IteratedPairStage k n)
        hInner hOuter (iteratedNormalFormLinearEquiv k n)
        (stageEmbedding k n z * stageCoordinate k n ^ a *
          stageMomentum k n ^ p)) = _
  unfold stageEmbedding stageCoordinate stageMomentum
  have hpair := pairNormalFormLinearEquiv_orderedMonomial hInner hOuter
    (iteratedNormalFormLinearEquiv k n) z a p
  have hflat := congrArg (flattenPairSymbols k n) hpair
  rw [flattenPairSymbols_monomial] at hflat
  exact hflat

/-- Normal-form coordinates for the quotient presentation, obtained by
transport through the presented/iterated algebra equivalence. -/
def presentedNormalFormLinearEquiv (n : Nat) :
    PresentedWeyl k n ≃ₗ[k] SymbolRing k n :=
  (presentedIteratedEquiv k n).toLinearEquiv.trans
    (iteratedNormalFormLinearEquiv k n)

@[simp] theorem presentedNormalFormLinearEquiv_one (n : Nat) :
    presentedNormalFormLinearEquiv k n 1 = 1 := by
  rw [presentedNormalFormLinearEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, map_one, iteratedNormalFormLinearEquiv_one]

/-- The transported normal-form coordinates agree with the named generators
of the quotient presentation. -/
@[simp] theorem presentedNormalFormLinearEquiv_generator (n : Nat)
    (i : PhaseVar n) :
    presentedNormalFormLinearEquiv k n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) =
      MvPolynomial.X i := by
  rw [presentedNormalFormLinearEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, presentedIteratedEquiv_generator,
    iteratedNormalFormLinearEquiv_generator]

/-- Append powers of the newest named coordinate and momentum to an arbitrary
old presentation element in normal order. -/
def presentedCoefficientOrdered (n a p : ℕ) (z : PresentedWeyl k n) :
    PresentedWeyl k (n + 1) :=
  previousWeylEmbedding k n z * presentedCoordinate k n ^ a *
    presentedMomentum k n ^ p

/-- Normal-form coordinates of an arbitrary old presentation element followed
by powers of the newest named coordinate and momentum. -/
theorem presentedNormalFormLinearEquiv_previous_ordered
    (n a p : ℕ) (z : PresentedWeyl k n) :
    presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p z) =
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ p *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) ^ a *
        MvPolynomial.rename oldIndex
          (presentedNormalFormLinearEquiv k n z) := by
  letI : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateStageAlgebra
  letI : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  rw [presentedCoefficientOrdered]
  rw [presentedNormalFormLinearEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply]
  have hmap : presentedIteratedEquiv k (n + 1)
        (previousWeylEmbedding k n z *
          presentedCoordinate k n ^ a * presentedMomentum k n ^ p) =
      presentedIteratedEquiv k (n + 1) (previousWeylEmbedding k n z) *
        presentedIteratedEquiv k (n + 1) (presentedCoordinate k n) ^ a *
        presentedIteratedEquiv k (n + 1) (presentedMomentum k n) ^ p := by
    simp only [map_mul, map_pow]
  rw [hmap]
  change iteratedNormalFormLinearEquiv k (n + 1)
      (presentedToIterated k (n + 1) (previousWeylEmbedding k n z) *
        presentedToIterated k (n + 1) (presentedCoordinate k n) ^ a *
        presentedToIterated k (n + 1) (presentedMomentum k n) ^ p) = _
  have hprevious := DFunLike.congr_fun (presentedToIterated_previous k n) z
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at hprevious
  rw [hprevious, presentedToIterated_coordinate,
    presentedToIterated_momentum]
  change iteratedNormalFormLinearEquiv k (n + 1)
    (iteratedCoefficientOrdered k n a p (presentedToIterated k n z)) = _
  rw [iteratedNormalFormLinearEquiv_coefficient_ordered]
  rfl

/-- Exact normal-ordering formula for two newest-pair blocks.  Every correction
term lowers both the coordinate and momentum exponents by the same amount. -/
theorem presentedCoefficientOrdered_mul
    (n a b c d : ℕ) (z₁ z₂ : PresentedWeyl k n) :
    presentedCoefficientOrdered k n a b z₁ *
        presentedCoefficientOrdered k n c d z₂ =
      ∑ i ∈ Finset.range (b + 1),
        if i ≤ c then
          (b.choose i * c.descFactorial i) •
            presentedCoefficientOrdered k n (a + c - i) (b + d - i) (z₁ * z₂)
        else 0 := by
  let X := presentedCoordinate k n
  let P := presentedMomentum k n
  let Z₁ := previousWeylEmbedding k n z₁
  let Z₂ := previousWeylEmbedding k n z₂
  have hX : Commute X Z₂ := presentedCoordinate_commutes_previous k n z₂
  have hP : Commute P Z₂ := presentedMomentum_commutes_previous k n z₂
  have hblock : Commute (X ^ a * P ^ b) Z₂ :=
    (hX.pow_left a).mul_left (hP.pow_left b)
  have hPX : P * X - X * P = 1 := by
    rw [show P * X = X * P + 1 from presentedMomentum_mul_coordinate k n]
    noncomm_ring
  rw [presentedCoefficientOrdered, presentedCoefficientOrdered]
  change (Z₁ * X ^ a * P ^ b) * (Z₂ * X ^ c * P ^ d) = _
  calc
    (Z₁ * X ^ a * P ^ b) * (Z₂ * X ^ c * P ^ d) =
        Z₁ * ((X ^ a * P ^ b) * Z₂) * (X ^ c * P ^ d) := by
      noncomm_ring
    _ = (Z₁ * Z₂ * X ^ a) * (P ^ b * X ^ c) * P ^ d := by
      rw [hblock.eq]
      noncomm_ring
    _ = (Z₁ * Z₂ * X ^ a) *
          (∑ i ∈ Finset.range (b + 1),
            if i ≤ c then
              (b.choose i * c.descFactorial i) •
                (X ^ (c - i) * P ^ (b - i))
            else 0) * P ^ d := by
      rw [OreAmbient.commutator_pow_mul_pow P X hPX b c]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hib : i ≤ b := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hic : i ≤ c
      · simp only [if_pos hic, OreAmbient.mul_nsmul_left,
          OreAmbient.nsmul_mul_right, mul_nsmul]
        congr 1
        congr 1
        change (Z₁ * Z₂ * X ^ a) * (X ^ (c - i) * P ^ (b - i)) * P ^ d =
          previousWeylEmbedding k n (z₁ * z₂) * X ^ (a + c - i) *
            P ^ (b + d - i)
        rw [map_mul]
        rw [show a + c - i = a + (c - i) by omega,
          show b + d - i = (b - i) + d by omega,
          pow_add, pow_add]
        noncomm_ring
      · simp [hic]

-- Compile-time API contract: the exact contraction range, coefficient, and
-- exponent loss are part of the public normal-ordering statement.
example (n a b c d : ℕ) (z₁ z₂ : PresentedWeyl k n) :
    presentedCoefficientOrdered k n a b z₁ *
        presentedCoefficientOrdered k n c d z₂ =
      ∑ i ∈ Finset.range (b + 1),
        if i ≤ c then
          (b.choose i * c.descFactorial i) •
            presentedCoefficientOrdered k n (a + c - i) (b + d - i) (z₁ * z₂)
        else 0 :=
  presentedCoefficientOrdered_mul k n a b c d z₁ z₂

/-- Ordered monomials built recursively from the named generators in the
quotient presentation.  Older coordinate/momentum pairs occur first; within
each pair the coordinate power precedes the momentum power. -/
def presentedOrderedMonomial :
    (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → PresentedWeyl k n
  | 0, _, _ => 1
  | n + 1, a, p =>
      previousWeylEmbedding k n
          (presentedOrderedMonomial n
            (fun i => a i.succ) (fun i => p i.succ)) *
        presentedCoordinate k n ^ a 0 * presentedMomentum k n ^ p 0

/-- The presentation/Ore equivalence preserves the recursively ordered
monomials, not merely the degree-one generators. -/
theorem presentedIteratedEquiv_orderedMonomial :
    ∀ (n : ℕ) (a p : Fin n → ℕ),
      presentedIteratedEquiv k n (presentedOrderedMonomial k n a p) =
        iteratedOrderedMonomial k n a p := by
  intro n
  induction n with
  | zero =>
      intro a p
      simp [presentedOrderedMonomial, iteratedOrderedMonomial]
  | succ n ih =>
      intro a p
      rw [presentedOrderedMonomial, iteratedOrderedMonomial, map_mul, map_mul,
        map_pow, map_pow, presentedIteratedEquiv]
      change
        presentedToIterated k (n + 1)
              (previousWeylEmbedding k n
                (presentedOrderedMonomial k n
                  (fun i => a i.succ) (fun i => p i.succ))) *
            presentedToIterated k (n + 1) (presentedCoordinate k n) ^ a 0 *
          presentedToIterated k (n + 1) (presentedMomentum k n) ^ p 0 = _
      have hprevious := DFunLike.congr_fun
        (presentedToIterated_previous k n)
        (presentedOrderedMonomial k n
          (fun i => a i.succ) (fun i => p i.succ))
      rw [AlgHom.comp_apply, AlgHom.comp_apply] at hprevious
      have hih := ih (fun i => a i.succ) (fun i => p i.succ)
      change presentedToIterated k n
          (presentedOrderedMonomial k n
            (fun i => a i.succ) (fun i => p i.succ)) = _ at hih
      rw [hprevious, hih, presentedToIterated_coordinate,
        presentedToIterated_momentum]
      rfl

/-- Every ordered product of named presentation generators has the expected
commutative symbol monomial as its checked normal form. -/
theorem presentedOrderedMonomial_normal (n : ℕ) (a p : Fin n → ℕ) :
    presentedNormalFormLinearEquiv k n
        (presentedOrderedMonomial k n a p) =
      MvPolynomial.monomial (phaseExponent a p) 1 := by
  rw [presentedNormalFormLinearEquiv, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, presentedIteratedEquiv_orderedMonomial,
    iteratedOrderedMonomial_normal]

/-- A free-module basis on the presented Weyl algebra, pulled back from the
standard monomial basis of the symbol polynomial space. -/
def presentedNormalFormBasis (n : Nat) :
    Module.Basis (PhaseVar n →₀ ℕ) k (PresentedWeyl k n) :=
  (MvPolynomial.basisMonomials (PhaseVar n) k).map
    (presentedNormalFormLinearEquiv k n).symm

@[simp] theorem presentedNormalFormBasis_apply (n : Nat)
    (m : PhaseVar n →₀ ℕ) :
    presentedNormalFormBasis k n m =
      (presentedNormalFormLinearEquiv k n).symm (MvPolynomial.monomial m 1) := by
  rfl

/-- Split a finite phase exponent into its coordinate and momentum parts. -/
theorem phaseExponent_split {n : ℕ} (m : PhaseVar n →₀ ℕ) :
    phaseExponent (fun i => m (.inl i)) (fun i => m (.inr i)) = m := by
  ext i
  cases i <;> rfl

/-- The transported normal-form basis consists exactly of the recursively
ordered products of the named Weyl generators. -/
theorem presentedNormalFormBasis_eq_orderedMonomial (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    presentedNormalFormBasis k n m =
      presentedOrderedMonomial k n
        (fun i => m (.inl i)) (fun i => m (.inr i)) := by
  apply (presentedNormalFormLinearEquiv k n).injective
  rw [presentedNormalFormBasis_apply, LinearEquiv.apply_symm_apply,
    presentedOrderedMonomial_normal, phaseExponent_split]

/-- The PBW basis of the presented Weyl algebra, indexed by coordinate and
momentum exponent vectors. -/
def presentedPBWBasis (n : Nat) :
    Module.Basis (PhaseVar n →₀ ℕ) k (PresentedWeyl k n) :=
  presentedNormalFormBasis k n

@[simp] theorem presentedPBWBasis_apply (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    presentedPBWBasis k n m =
      presentedOrderedMonomial k n
        (fun i => m (.inl i)) (fun i => m (.inr i)) := by
  exact presentedNormalFormBasis_eq_orderedMonomial k n m


end

end Stafford38.WeylPBW
