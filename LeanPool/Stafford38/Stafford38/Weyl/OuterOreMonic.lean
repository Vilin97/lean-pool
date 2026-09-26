/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.Stafford38.Weyl.PBWMonicBridge


/-!
# PBW monicity as concrete outer-Ore monicity

The successor-rank iterated Weyl tower is an outer Ore extension in the newest
momentum. This file exposes its concrete coefficient-left polynomial, proves
the exact coefficient formula relating the nested PBW normal form to that
polynomial, and turns the checked PBW coefficient-one bound into
`Polynomial.Monic`.
-/

@[expose] public section

namespace Stafford38.WeylOuterOreMonic

open AlgebraicAnalysis.OreDivision
open Stafford38.Characteristic
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage
open Stafford38.OreLinearNormalForm
open Stafford38.OreScalarAlgebra
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylFiltration

noncomputable section
universe u
variable (k : Type u) [Field k]

/-- The base-field algebra structure on an iterated pair stage for outer Ore normalization. -/
local instance (n : ℕ) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

/-- The base-field algebra structure on the outer coordinate stage. -/
local instance (n : ℕ) :
    Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
  coordinateStageAlgebra

/-- The base-field algebra structure on the outer pair stage. -/
local instance (n : ℕ) :
    Algebra k (PairStage (B := IteratedPairStage k n)) :=
  pairStageAlgebra

/-- The polynomial in the outer Ore variable representing a presented Weyl element. -/
def presentedOuterPolynomial (n : ℕ) (d : PresentedWeyl k (n + 1)) :
    Polynomial (CoordinateStage (B := IteratedPairStage k n)) :=
  (normalFormAddEquiv
    (coordinateDerivation :
      AlgebraicAnalysis.OreDivisionDerivation
        (CoordinateStage (B := IteratedPairStage k n)))).symm
    (presentedToIterated k (n + 1) d)

/-- The coordinate-stage linear normal form with coefficients in the transverse symbol ring. -/
def coordinateCoefficientNormalForm (n : ℕ) :
    CoordinateStage (B := IteratedPairStage k n) ≃ₗ[k]
      Polynomial (SymbolRing k n) := by
  letI : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateStageAlgebra
  exact (normalFormLinearEquiv zeroDerivation
    (normalOreAlgebra_algebraMap zeroDerivation (fun c => by
      exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c)))).symm.trans
      (polynomialMapRangeLinearEquiv (iteratedNormalFormLinearEquiv k n))

/-- The two-variable nested polynomial normal form of the outer Weyl pair. -/
def presentedNestedNormalForm (n : ℕ) (d : PresentedWeyl k (n + 1)) :
    Polynomial (Polynomial (SymbolRing k n)) := by
  letI : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  letI : Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateStageAlgebra
  letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
    pairStageAlgebra
  exact pairNormalFormLinearEquiv
    (normalOreAlgebra_algebraMap zeroDerivation (fun c => by
      exact zeroDerivation_apply (algebraMap k (IteratedPairStage k n) c)))
    (normalOreAlgebra_algebraMap coordinateDerivation
      coordinateDerivation_algebraMap)
    (iteratedNormalFormLinearEquiv k n)
    (presentedToIterated k (n + 1) d)

theorem flatten_presentedNestedNormalForm (n : ℕ)
    (d : PresentedWeyl k (n + 1)) :
    flattenPairSymbols k n (presentedNestedNormalForm k n d) =
      presentedNormalFormLinearEquiv k (n + 1) d := by
  rfl

theorem presentedNestedNormalForm_eq_mapRange (n : ℕ)
    (d : PresentedWeyl k (n + 1)) :
    presentedNestedNormalForm k n d =
      polynomialMapRangeLinearEquiv (coordinateCoefficientNormalForm k n)
        (presentedOuterPolynomial k n d) := by
  rfl

/-- The PBW exponent combining outer momentum and coordinate powers with transverse exponents. -/
def pairExponent (n a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    PhaseVar (n + 1) →₀ ℕ :=
  Finsupp.single (.inr (0 : Fin (n + 1))) p +
    Finsupp.single (.inl (0 : Fin (n + 1))) a +
    Finsupp.mapDomain oldIndex m

@[simp]
theorem mapDomain_oldIndex_newCoordinate (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    Finsupp.mapDomain oldIndex m (.inl (0 : Fin (n + 1))) = 0 := by
  rw [Finsupp.mapDomain_of_notMem_range]
  rintro ⟨i, hi⟩
  cases i with
  | inl j => exact Fin.succ_ne_zero j (Sum.inl.inj hi)
  | inr j => simp [oldIndex] at hi

@[simp]
theorem mapDomain_oldIndex_newMomentum (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    Finsupp.mapDomain oldIndex m (.inr (0 : Fin (n + 1))) = 0 := by
  rw [Finsupp.mapDomain_of_notMem_range]
  rintro ⟨i, hi⟩
  cases i with
  | inl j => simp [oldIndex] at hi
  | inr j => exact Fin.succ_ne_zero j (Sum.inr.inj hi)

theorem coeff_flattenPairSymbols_monomial (n a p a' p' : ℕ)
    (m : PhaseVar n →₀ ℕ) (r : SymbolRing k n) :
    (flattenPairSymbols k n
          (Polynomial.monomial p' (Polynomial.monomial a' r))).coeff (pairExponent n a p m) =
      if p' = p ∧ a' = a then r.coeff m else 0 := by
  rw [flattenPairSymbols_monomial]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, mul_one]
  rw [MvPolynomial.coeff_monomial_mul']
  classical
  by_cases hp : p' = p
  · subst p'
    by_cases ha : a' = a
    · subst a'
      have hle :
          (Finsupp.single (.inr (0 : Fin (n + 1))) p +
              Finsupp.single (.inl (0 : Fin (n + 1))) a) ≤
            pairExponent n a p m := by
        intro i
        simp only [pairExponent, Finsupp.add_apply]
        omega
      rw [ite_eq_left hle]
      have hsub :
          (pairExponent n a p m -
            (Finsupp.single (.inr (0 : Fin (n + 1))) p +
              Finsupp.single (.inl (0 : Fin (n + 1))) a)) =
            Finsupp.mapDomain oldIndex m := by
        rw [pairExponent]
        exact add_tsub_cancel_left _ _
      rw [hsub, MvPolynomial.coeff_rename_mapDomain oldIndex oldIndex_injective]
      simp
    · by_cases hle :
          ((Finsupp.single (.inr (0 : Fin (n + 1))) p +
              Finsupp.single (.inl (0 : Fin (n + 1))) a') ≤
            pairExponent n a p m)
      · rw [ite_eq_left hle]
        have haa : a' ≤ a := by
          simpa [pairExponent, Finsupp.single_apply] using
            hle (.inl (0 : Fin (n + 1)))
        have hz : (MvPolynomial.rename oldIndex r).coeff ((pairExponent n a p m) -
              (Finsupp.single (.inr (0 : Fin (n + 1))) p +
                Finsupp.single (.inl (0 : Fin (n + 1))) a')) = 0 := by
          apply MvPolynomial.coeff_rename_eq_zero
          intro u hu
          have hnew := DFunLike.congr_fun hu (.inl (0 : Fin (n + 1)))
          simp [pairExponent] at hnew
          omega
        rw [hz]
        simp [ha]
      · rw [ite_eq_right hle]
        simp [ha]
  · by_cases hle :
        ((Finsupp.single (.inr (0 : Fin (n + 1))) p' +
            Finsupp.single (.inl (0 : Fin (n + 1))) a') ≤
          pairExponent n a p m)
    · rw [ite_eq_left hle]
      have hpp : p' ≤ p := by
        simpa [pairExponent, Finsupp.single_apply] using
          hle (.inr (0 : Fin (n + 1)))
      have hz : (MvPolynomial.rename oldIndex r).coeff ((pairExponent n a p m) -
            (Finsupp.single (.inr (0 : Fin (n + 1))) p' +
              Finsupp.single (.inl (0 : Fin (n + 1))) a')) = 0 := by
        apply MvPolynomial.coeff_rename_eq_zero
        intro u hu
        have hnew := DFunLike.congr_fun hu (.inr (0 : Fin (n + 1)))
        simp [pairExponent] at hnew
        omega
      rw [hz]
      simp [hp]
    · rw [ite_eq_right hle]
      simp [hp]

theorem coeff_flattenPairSymbols (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ)
    (q : Polynomial (Polynomial (SymbolRing k n))) :
    (flattenPairSymbols k n q).coeff (pairExponent n a p m) =
      ((q.coeff p).coeff a).coeff m := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | monomial p' r =>
      induction r using Polynomial.induction_on' with
      | add r₁ r₂ h₁ h₂ =>
          rw [map_add (Polynomial.monomial p') r₁ r₂]
          simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
            Polynomial.coeff_monomial, Polynomial.coeff_add]
          by_cases hp : p' = p
          · subst p'
            simp [h₁, h₂]
          · rw [h₁, h₂]
            simp [Polynomial.coeff_monomial, hp]
      | monomial a' s =>
          rw [coeff_flattenPairSymbols_monomial]
          simp only [Polynomial.coeff_monomial]
          by_cases hp : p' = p
          · subst p'
            by_cases ha : a' = a
            · subst a'
              simp
            · simp [Polynomial.coeff_monomial, ha]
          · simp [hp]

theorem coeff_polynomialMapRangeLinearEquiv
    {R S : Type*} [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₗ[k] S)
    (q : Polynomial R) (p : ℕ) :
    (polynomialMapRangeLinearEquiv e q).coeff p = e (q.coeff p) := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | monomial n r =>
      rw [polynomialMapRangeLinearEquiv_monomial]
      by_cases h : n = p <;> simp [Polynomial.coeff_monomial, h]

@[simp]
theorem degree_pairExponent (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    (pairExponent n a p m).degree =
      p + a + (Finsupp.mapDomain oldIndex m).degree := by
  simp [pairExponent]

@[simp]
theorem pairExponent_newMomentum (n a p : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    pairExponent n a p m (.inr (0 : Fin (n + 1))) = p := by
  simp [pairExponent]

theorem nested_coeff_eq_zero_of_outer_exponent_gt (n N : ℕ)
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p : ℕ} (hp : N < p) :
    (presentedNestedNormalForm k n d).coeff p = 0 := by
  ext a m
  simp only [Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero]
  rw [← coeff_flattenPairSymbols k n a p m]
  rw [flatten_presentedNestedNormalForm]
  exact coeff_normalForm_eq_zero_of_exponent_gt k
    (t := .inr (0 : Fin (n + 1))) (m := pairExponent n a p m)
    hd.1 (by simpa using hp)

theorem nested_coeff_eq_one_at_bound (n N : ℕ)
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedNestedNormalForm k n d).coeff N = 1 := by
  ext a m
  rw [← coeff_flattenPairSymbols k n a N m]
  rw [flatten_presentedNestedNormalForm]
  by_cases ha : a = 0
  · subst a
    by_cases hm : m = 0
    · subst m
      simpa [pairExponent] using hd.2
    · have hmap : Finsupp.mapDomain oldIndex m ≠ 0 := by
        exact (Finsupp.mapDomain_injective oldIndex_injective).ne hm
      have hdegree : N < (pairExponent n 0 N m).degree := by
        rw [degree_pairExponent]
        have hpos : 0 < (Finsupp.mapDomain oldIndex m).degree := by
          exact Nat.pos_of_ne_zero
            ((Finsupp.degree_eq_zero_iff _).not.mpr hmap)
        omega
      have hz : (presentedNormalFormLinearEquiv k (n + 1) d).coeff (pairExponent n 0 N m) = 0 := by
        by_contra hc
        have hle := (mem_presentedWeightPiece k (@bernsteinWeight (n + 1)) N d).mp
          hd.1 (pairExponent n 0 N m) hc
        have : (pairExponent n 0 N m).degree ≤ N := by
          change (pairExponent n 0 N m).sum (fun _ e => e) ≤ N
          simpa [monomialWeight, bernsteinWeight] using hle
        omega
      rw [hz]
      simp [Polynomial.coeff_one, MvPolynomial.coeff_one, Ne.symm hm]
  · have hdegree : N < (pairExponent n a N m).degree := by
      rw [degree_pairExponent]
      omega
    have hz : (presentedNormalFormLinearEquiv k (n + 1) d).coeff (pairExponent n a N m) = 0 := by
      by_contra hc
      have hle := (mem_presentedWeightPiece k (@bernsteinWeight (n + 1)) N d).mp
        hd.1 (pairExponent n a N m) hc
      have : (pairExponent n a N m).degree ≤ N := by
        change (pairExponent n a N m).sum (fun _ e => e) ≤ N
        simpa [monomialWeight, bernsteinWeight] using hle
      omega
    rw [hz]
    simp [Polynomial.coeff_one, ha]

theorem presentedNestedNormalForm_coeff (n p : ℕ)
    (d : PresentedWeyl k (n + 1)) :
    (presentedNestedNormalForm k n d).coeff p =
      coordinateCoefficientNormalForm k n
        ((presentedOuterPolynomial k n d).coeff p) := by
  rw [presentedNestedNormalForm_eq_mapRange,
    coeff_polynomialMapRangeLinearEquiv]

theorem coordinateCoefficientNormalForm_one (n : ℕ) :
    coordinateCoefficientNormalForm k n 1 = 1 := by
  change polynomialMapRangeLinearEquiv (iteratedNormalFormLinearEquiv k n)
      ((normalFormLinearEquiv zeroDerivation _).symm 1) = 1
  rw [normalFormLinearEquiv_symm_one]
  exact polynomialMapRangeLinearEquiv_one _ (iteratedNormalFormLinearEquiv_one k n)

theorem outer_coeff_eq_one_at_bound (n N : ℕ)
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedOuterPolynomial k n d).coeff N = 1 := by
  have h := nested_coeff_eq_one_at_bound k n N hd
  rw [presentedNestedNormalForm_coeff] at h
  apply (coordinateCoefficientNormalForm k n).injective
  rw [h, coordinateCoefficientNormalForm_one]

theorem outer_coeff_eq_zero_of_exponent_gt (n N : ℕ)
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p : ℕ} (hp : N < p) :
    (presentedOuterPolynomial k n d).coeff p = 0 := by
  have h := nested_coeff_eq_zero_of_outer_exponent_gt k n N hd hp
  rw [presentedNestedNormalForm_coeff] at h
  apply (coordinateCoefficientNormalForm k n).injective
  exact h.trans (LinearMap.map_zero (coordinateCoefficientNormalForm k n).toLinearMap).symm

theorem presentedOuterPolynomial_monic (n N : ℕ)
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (presentedOuterPolynomial k n d).Monic := by
  apply Polynomial.monic_of_degree_le N
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro p hp
    exact outer_coeff_eq_zero_of_exponent_gt k n N hd (by simpa using hp)
  · exact outer_coeff_eq_one_at_bound k n N hd

/- Exact declaration and trust-boundary report. -/

end
end Stafford38.WeylOuterOreMonic
