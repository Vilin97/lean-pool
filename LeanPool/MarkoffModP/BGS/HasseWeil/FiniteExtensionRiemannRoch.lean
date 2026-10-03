/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorClassRecurrence
public import LeanPool.MarkoffModP.BGS.HasseWeil.HeightOneValuationTransport
public import LeanPool.MarkoffModP.RiemannRoch.CoordinateFree.RiemannRoch

/-!
# Riemann--Roch for the exhaustive finite-extension place model

This file identifies the exhaustive finite and infinite places used by the BGS
function-field development with the two-chart place model of the vendored
Riemann--Roch library.  The identification transports residue degrees,
divisors, divisor degree, normalized valuations, and Riemann spaces.  It then
applies the axiom-clean Riemann--Roch theorem to discharge the eventual uniform
Riemann formula required by the divisor-class recurrence.

The only non-definitional chart issue is at infinity: the two developments
construct the same valuation subring using different `DecidableEq` instances.
We therefore record the identity-on-elements ring equivalence explicitly and
transport the integral closure and its height-one primes across it.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain Multiplicative WithZero
open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The algebra structure from `K` to `L` used in the finite extension riemann roch
    construction. -/
local instance riemannRochConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance riemannRochConstantRatFuncTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K[X]` to `L` used in the finite extension riemann roch
    construction. -/
local instance (priority := 10) riemannRochPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance riemannRochPolynomialRatFuncTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance riemannRochConstantPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K` to `(RatFuncInfinityIntegers K)` used in the finite
    extension riemann roch construction. -/
local instance riemannRochInfinityBaseConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance riemannRochInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance riemannRochInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

/-- The algebra structure from `K` to `(RatFuncInfinityIntegralClosure K L)` used in the
    finite extension riemann roch construction. -/
local instance riemannRochInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance riemannRochInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The BGS and Riemann--Roch infinity valuation subrings are the same
subring of `RatFunc K`; this equivalence makes the harmless instance-level
difference explicit. -/
def finiteExtensionInfinityBaseRingEquiv :
    RatFuncInfinityIntegers K ≃+*
      MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K where
  toFun x := ⟨x.1, by
    have hx := x.2
    unfold RatFuncInfinityIntegers at hx
    rw [Valuation.mem_integer_iff] at hx
    rw [Valuation.mem_valuationSubring_iff]
    have hdec : (inferInstance : DecidableEq (RatFunc K)) =
        Classical.decEq (RatFunc K) := Subsingleton.elim _ _
    cases hdec
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx := x.2
    unfold MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring at hx
    rw [Valuation.mem_valuationSubring_iff] at hx
    unfold RatFuncInfinityIntegers
    rw [Valuation.mem_integer_iff]
    have hdec : (inferInstance : DecidableEq (RatFunc K)) =
        Classical.decEq (RatFunc K) := Subsingleton.elim _ _
    cases hdec
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [Fintype K] [DecidableEq K] in
@[simp]
theorem finiteExtensionInfinityBaseRingEquiv_apply_coe
    (x : RatFuncInfinityIntegers K) :
    ((finiteExtensionInfinityBaseRingEquiv K x :
      MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K) : RatFunc K) = x :=
  rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
private theorem isIntegral_infinityBase_iff (x : L) :
    IsIntegral (RatFuncInfinityIntegers K) x ↔
      IsIntegral (MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K) x := by
  let e := finiteExtensionInfinityBaseRingEquiv K
  have hforward :
      (algebraMap (MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K) L).comp
          e.toRingHom =
        algebraMap (RatFuncInfinityIntegers K) L := by
    ext a
    rfl
  have hbackward :
      (algebraMap (RatFuncInfinityIntegers K) L).comp
          e.symm.toRingHom =
        algebraMap (MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K) L := by
    ext a
    rfl
  constructor
  · intro hx
    have hx' :
        ((algebraMap (MarkoffRiemannRoch.FunctionField.Chart.inftyValuationSubring K) L).comp
          e.toRingHom).IsIntegralElem x := by
      rw [hforward]
      exact hx
    exact hx'.of_comp
  · intro hx
    have hx' :
        ((algebraMap (RatFuncInfinityIntegers K) L).comp
          e.symm.toRingHom).IsIntegralElem x := by
      rw [hbackward]
      exact hx
    exact hx'.of_comp

/-- Identity-on-`L` equivalence between the two infinity integral closures. -/
def finiteExtensionInfinityIntegralClosureRingEquiv :
    RatFuncInfinityIntegralClosure K L ≃+*
      MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L where
  toFun x := ⟨x.1, by exact (isIntegral_infinityBase_iff K L x.1).mp x.2⟩
  invFun x := ⟨x.1, by exact (isIntegral_infinityBase_iff K L x.1).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionInfinityIntegralClosureRingEquiv_apply_coe
    (x : RatFuncInfinityIntegralClosure K L) :
    ((finiteExtensionInfinityIntegralClosureRingEquiv K L x :
      MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L) : L) = x :=
  rfl

/-- Constant-field-linear form of the infinity integral-closure equivalence. -/
def finiteExtensionInfinityIntegralClosureAlgEquiv :
    RatFuncInfinityIntegralClosure K L ≃ₐ[K]
      MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L where
  __ := finiteExtensionInfinityIntegralClosureRingEquiv K L
  commutes' c := by
    apply Subtype.ext
    rfl

/-- Places above the BGS infinity place are exactly the height-one primes of
the BGS infinity integral closure. -/
def finiteExtensionInfinityPrimesOverEquivHeightOne :
    FiniteExtensionInfinityPlace K L ≃
      HeightOneSpectrum (RatFuncInfinityIntegralClosure K L) where
  toFun P := primeOverHeightOne (ratFuncInfinityPlace K) P
  invFun q := ⟨q.asIdeal, q.isPrime, ⟨by
    let A := RatFuncInfinityIntegers K
    let : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
    have hq : q.asIdeal.under A = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q.asIdeal)
    have hp : (ratFuncInfinityPlace K).asIdeal =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        ((ratFuncInfinityPlace K).isPrime.isMaximal
          (ratFuncInfinityPlace K).ne_bot)
    exact (hq.trans hp.symm).symm⟩⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply HeightOneSpectrum.ext
    rfl

/-- Infinity places in the exhaustive BGS model and in the Riemann--Roch chart. -/
def finiteExtensionInfinityPlaceEquivChart :
    FiniteExtensionInfinityPlace K L ≃
      HeightOneSpectrum (MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L) :=
  (finiteExtensionInfinityPrimesOverEquivHeightOne K L).trans
    (HeightOneSpectrum.equivOfRingEquiv
      (finiteExtensionInfinityIntegralClosureRingEquiv K L))

/-- Equivalence from the exhaustive BGS place type to the Riemann--Roch
two-chart place type. -/
def finiteExtensionPlaceEquivChart :
    FiniteExtensionPlace K L ≃ MarkoffRiemannRoch.FunctionField.Chart.PlaceA K L :=
  Equiv.sumCongr (Equiv.refl _)
    (finiteExtensionInfinityPlaceEquivChart K L)

/-- The residue-field equivalence for the finite quotient in Riemann–Roch. -/
noncomputable def finiteExtensionFiniteQuotientResidueAlgEquiv
    (q : FiniteExtensionFinitePlace K L) :
    (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal) ≃ₐ[K]
      q.asIdeal.ResidueField := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K
      (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
      q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)

/-- The residue-field equivalence for the infinity quotient in Riemann–Roch. -/
noncomputable def finiteExtensionInfinityQuotientResidueAlgEquiv
    (q : HeightOneSpectrum (MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L)) :
    (MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal) ≃ₐ[K]
      q.asIdeal.ResidueField := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K
      (MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal)
      q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)

/-- The residue-field equivalence at infinity used in the Riemann–Roch comparison. -/
noncomputable def finiteExtensionInfinityResidueAlgEquiv
    (P : FiniteExtensionInfinityPlace K L) :
    P.1.ResidueField ≃ₐ[K]
      (finiteExtensionInfinityPlaceEquivChart K L P).asIdeal.ResidueField := by
  let e := finiteExtensionInfinityIntegralClosureAlgEquiv K L
  apply Ideal.residueFieldAlgEquiv P.1
    (finiteExtensionInfinityPlaceEquivChart K L P).asIdeal e
  change P.1 = (P.1.comap e.symm).comap e
  exact (Ideal.comap_of_equiv e.toRingEquiv).symm

omit [Fintype K] in
/-- The exhaustive place degree agrees with the Riemann--Roch chart degree. -/
theorem finiteExtensionPlaceDegree_eq_chart
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceDegree K L v =
      MarkoffRiemannRoch.FunctionField.Chart.placeDegree K L
        (finiteExtensionPlaceEquivChart K L v) := by
  rcases v with q | P
  · rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q]
    change Module.finrank K q.asIdeal.ResidueField =
      Module.finrank K (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
    exact (finiteExtensionFiniteQuotientResidueAlgEquiv K L q).toLinearEquiv.finrank_eq.symm
  · rw [finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P]
    let q := finiteExtensionInfinityPlaceEquivChart K L P
    change Module.finrank K P.1.ResidueField =
      Module.finrank K (MarkoffRiemannRoch.FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal)
    exact (finiteExtensionInfinityResidueAlgEquiv K L P).toLinearEquiv.finrank_eq.trans
      (finiteExtensionInfinityQuotientResidueAlgEquiv K L q).toLinearEquiv.finrank_eq.symm

omit [Fintype K] [DecidableEq K] in
/-- The normalized infinity valuation is unchanged by the identity-on-`L`
integral-closure transport. -/
theorem finiteExtensionInfinityPlaceValuation_eq_chart
    (P : FiniteExtensionInfinityPlace K L) :
    (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L =
      (finiteExtensionInfinityPlaceEquivChart K L P).valuation L := by
  let q := primeOverHeightOne
    (R := RatFuncInfinityIntegers K)
    (S := RatFuncInfinityIntegralClosure K L)
    (ratFuncInfinityPlace K) P
  let e := finiteExtensionInfinityIntegralClosureRingEquiv K L
  let q' := finiteExtensionInfinityPlaceEquivChart K L P
  have hideal : q'.asIdeal = q.asIdeal.comap e.symm := by
    rfl
  change q.valuation L = q'.valuation L
  exact heightOneValuation_eq_of_ringEquiv e (fun _ => rfl) q q' hideal

/-- The normalized valuation attached to an exhaustive BGS place. -/
def finiteExtensionPlaceValuation :
    FiniteExtensionPlace K L → Valuation L ℤᵐ⁰
  | .inl q => q.valuation L
  | .inr P =>
      (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L

omit [Fintype K] [DecidableEq K] in
/-- Every exhaustive BGS place carries exactly the normalized valuation of
its corresponding Riemann--Roch chart place. -/
theorem finiteExtensionPlaceValuation_eq_chart
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceValuation K L v =
      MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L
        (finiteExtensionPlaceEquivChart K L v) := by
  rcases v with q | P
  · rfl
  · exact finiteExtensionInfinityPlaceValuation_eq_chart K L P

/-- Transport of exhaustive divisors to the two-chart Riemann--Roch model. -/
def finiteExtensionDivisorEquivChart :
    FiniteExtensionDivisor K L ≃+
      MarkoffRiemannRoch.FunctionField.Chart.DivisorA K L :=
  Finsupp.domCongr (finiteExtensionPlaceEquivChart K L)

omit [Fintype K] in
/-- Divisor degree is preserved by the exhaustive-place/chart equivalence. -/
theorem finiteExtensionDivisorDegree_eq_chart
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L D =
      MarkoffRiemannRoch.FunctionField.Chart.deg K L
        (finiteExtensionDivisorEquivChart K L D) := by
  classical
  induction D using Finsupp.induction with
  | zero =>
      simp [finiteExtensionDivisorDegree, MarkoffRiemannRoch.FunctionField.Chart.deg,
        finiteExtensionDivisorEquivChart]
  | single_add v n D hv hn ih =>
      rw [map_add, finiteExtensionDivisorDegree_add,
        MarkoffRiemannRoch.FunctionField.Chart.deg_add, ih]
      congr 1
      simp [finiteExtensionDivisorDegree, MarkoffRiemannRoch.FunctionField.Chart.deg,
        finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single,
        finiteExtensionPlaceDegree_eq_chart]

omit [Fintype K] in
omit [DecidableEq K] in
/-- The valuation of a nonzero function is the exponential of the negative
coefficient of its exhaustive principal divisor. -/
theorem finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
    (x : L) (hx : x ≠ 0) (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceValuation K L v x =
      WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) := by
  classical
  rcases v with q | P
  · change q.valuation L x = _
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder,
      valuation_eq_exp_neg_finitePlaceOrder q x hx]
  · change (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L x = _
    rw [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder,
      valuation_eq_exp_neg_finitePlaceOrder
        (primeOverHeightOne (ratFuncInfinityPlace K) P) x hx]

/-- The BGS all-place Riemann space is the Riemann--Roch chart space after
transporting its divisor. -/
theorem finiteExtensionRiemannSpace_eq_chart
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionRiemannSpace K L D =
      MarkoffRiemannRoch.FunctionField.Chart.RRspace K L
        (finiteExtensionDivisorEquivChart K L D) := by
  classical
  ext x
  rw [mem_finiteExtensionRiemannSpace,
    MarkoffRiemannRoch.FunctionField.Chart.mem_RRspace_iff]
  constructor
  · rintro (rfl | ⟨hx, horders⟩)
    · intro w
      rw [Valuation.map_zero]
      exact zero_le
    · intro w
      let v := (finiteExtensionPlaceEquivChart K L).symm w
      have horder := horders v
      have hInt :
          -(finiteExtensionPrincipalDivisor K L x v) ≤ D v := by
        omega
      have hExp :
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) ≤
            WithZero.exp (D v) :=
        WithZero.exp_le_exp.mpr hInt
      have hprincipal : finiteExtensionPlaceValuation K L v x =
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
        finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
          K L x hx v
      have hplace : finiteExtensionPlaceValuation K L v x =
          MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L
            (finiteExtensionPlaceEquivChart K L v) x := by
        exact congrArg (fun u : Valuation L ℤᵐ⁰ => u x)
          (finiteExtensionPlaceValuation_eq_chart K L v)
      have hvw : finiteExtensionPlaceEquivChart K L v = w :=
        (finiteExtensionPlaceEquivChart K L).apply_symm_apply w
      calc
        MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L w x =
            MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L
              (finiteExtensionPlaceEquivChart K L v) x := by rw [hvw]
        _ = finiteExtensionPlaceValuation K L v x := hplace.symm
        _ = WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
            hprincipal
        _ ≤ WithZero.exp (D v) := hExp
        _ = WithZero.exp ((finiteExtensionDivisorEquivChart K L D) w) := by
            simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply, v]
  · intro hxchart
    by_cases hx : x = 0
    · exact Or.inl hx
    · refine Or.inr ⟨hx, ?_⟩
      intro v
      have hchart := hxchart (finiteExtensionPlaceEquivChart K L v)
      have hprincipal : finiteExtensionPlaceValuation K L v x =
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
        finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
          K L x hx v
      have hplace : finiteExtensionPlaceValuation K L v x =
          MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L
            (finiteExtensionPlaceEquivChart K L v) x := by
        exact congrArg (fun u : Valuation L ℤᵐ⁰ => u x)
          (finiteExtensionPlaceValuation_eq_chart K L v)
      have hExp :
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) ≤
            WithZero.exp (D v) := by
        calc
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) =
              finiteExtensionPlaceValuation K L v x :=
              hprincipal.symm
          _ = MarkoffRiemannRoch.FunctionField.Chart.placeValuation K L
                (finiteExtensionPlaceEquivChart K L v) x := hplace
          _ ≤ WithZero.exp
                ((finiteExtensionDivisorEquivChart K L D)
                  (finiteExtensionPlaceEquivChart K L v)) := hchart
          _ = WithZero.exp (D v) := by
              simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply]
      have hInt := WithZero.exp_le_exp.mp hExp
      omega

/-- Riemann--Roch supplies the uniform eventual formula with genus `g` and
threshold `2g` once the chosen finite constant field is full in `L`. -/
theorem hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField
    [MarkoffRiemannRoch.FunctionField.IsFullConstantField K L] :
    HasFiniteExtensionUniformEventualRiemannFormula K L
      (MarkoffRiemannRoch.FunctionField.Chart.genus K L)
      (2 * MarkoffRiemannRoch.FunctionField.Chart.genus K L) := by
  refine ⟨by omega, ?_⟩
  intro D n hn hdegree
  let Dchart := finiteExtensionDivisorEquivChart K L D
  have hspace : finiteExtensionRiemannSpace K L D =
      MarkoffRiemannRoch.FunctionField.Chart.RRspace K L Dchart :=
    finiteExtensionRiemannSpace_eq_chart K L D
  have hdegreeChart : MarkoffRiemannRoch.FunctionField.Chart.deg K L Dchart = (n : ℤ) := by
    rw [← finiteExtensionDivisorDegree_eq_chart K L D]
    exact hdegree
  constructor
  · rw [hspace]
    exact MarkoffRiemannRoch.FunctionField.Chart.finiteDimensional_RRspace K L Dchart
  · rw [hspace]
    change MarkoffRiemannRoch.FunctionField.Chart.ell K L Dchart =
      n + 1 - MarkoffRiemannRoch.FunctionField.Chart.genus K L
    obtain ⟨W, hW⟩ := MarkoffRiemannRoch.FunctionField.Chart.exists_isCanonical K L
    have hnZ : (2 : ℤ) * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) ≤
        (n : ℤ) := by
      exact_mod_cast hn
    have hlarge : MarkoffRiemannRoch.FunctionField.Chart.deg K L Dchart ≥
        2 * (MarkoffRiemannRoch.FunctionField.Chart.genus K L : ℤ) - 1 := by
      rw [hdegreeChart]
      omega
    have hRR := MarkoffRiemannRoch.FunctionField.Chart.ell_eq_of_deg_ge
      K L hW Dchart hlarge
    rw [hdegreeChart] at hRR
    have hgn : MarkoffRiemannRoch.FunctionField.Chart.genus K L ≤ n := by omega
    omega

/-- If the algebraic closure of the finite constant field inside `L` is
exactly the constants, the uniform eventual Riemann formula holds for a
canonical genus and threshold. -/
theorem exists_hasFiniteExtensionUniformEventualRiemannFormula_of_constants
    (hconstants : algebraicClosure K L = ⊥) :
    ∃ genus threshold,
      HasFiniteExtensionUniformEventualRiemannFormula
        K L genus threshold := by
  let : MarkoffRiemannRoch.FunctionField.IsFullConstantField K L :=
    (MarkoffRiemannRoch.FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  exact ⟨MarkoffRiemannRoch.FunctionField.Chart.genus K L,
    2 * MarkoffRiemannRoch.FunctionField.Chart.genus K L,
    hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField K L⟩

end

end BGS.HasseWeil
