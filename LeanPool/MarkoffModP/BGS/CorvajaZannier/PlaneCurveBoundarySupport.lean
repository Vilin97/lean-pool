/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityInertiaDegree
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationOrder
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCoordinatePowerHeight
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
import Mathlib.Tactic

/-!
# Weighted boundary support for a plane curve

This file proves the sharp coordinate-boundary estimate needed in the
Corvaja--Zannier middle game.  The exhaustive places are defined using the
first-coordinate `RatFunc` model.  To bound the positive divisor of the
second coordinate, each positive place is transported to the finite chart
of the second-coordinate model.  The transport preserves both the normalized
valuation and the residue degree; injectivity then compares the two weighted
positive-divisor sums.

The final theorem is stated directly for the zero/pole boundary
`propositionTwoExceptionalPlaces` of positive coordinate powers.
-/

open scoped Polynomial
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section


attribute [local instance high] Module.Free.of_divisionRing

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) probePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance probePolynomialScalarTower : IsScalarTower K[X] (RatFunc K) L :=
  .of_algebraMap_eq' rfl

local instance probeFiniteConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
    (algebraMap K K[X]))

local instance probeFiniteConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

local instance probeInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance probeInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  .of_algebraMap_eq' rfl

local instance probeInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance probeInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

local instance probeFiniteIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  integralClosure.isDedekindDomain K[X] (RatFunc K) L

local instance probeFiniteIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) L

local instance probeInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance probeInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) L

/-- The normalized valuation on `L` represented by an exhaustive place. -/
private noncomputable def probeFiniteExtensionPlaceValuation
    (w : FiniteExtensionPlace K L) :
    Valuation L (WithZero (Multiplicative ℤ)) :=
  match w with
  | .inl q => q.valuation L
  | .inr P => (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L

private theorem probeFiniteExtensionPlaceValuation_surjective
    (w : FiniteExtensionPlace K L) :
    Function.Surjective (probeFiniteExtensionPlaceValuation K L w) := by
  intro z
  cases w with
  | inl q =>
      exact q.valuation_surjective L z
  | inr P =>
      exact (primeOverHeightOne
        (ratFuncInfinityPlace K) P).valuation_surjective L z

private theorem probeFiniteExtensionPlaceValuation_eq_exp_neg_order
    (w : FiniteExtensionPlace K L) (x : L) (hx : x ≠ 0) :
    probeFiniteExtensionPlaceValuation K L w x =
      exp (-finiteExtensionPrincipalDivisor K L x w) := by
  cases w with
  | inl q =>
      have hord := fractionRingAlgEquiv_finitePlaceOrder_eq
        (L := L) q
        ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)
      have hord' : finitePlaceOrder q x = finitePlaceOrder q
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) := by
        simpa [ratFuncFiniteIntegralClosureFractionRingEquiv] using hord
      rw [finiteExtensionPrincipalDivisor_inl, ← hord']
      exact valuation_eq_exp_neg_finitePlaceOrder q x hx
  | inr P =>
      have hord := fractionRingAlgEquiv_finitePlaceOrder_eq
        (L := L) (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)
      have hord' : finitePlaceOrder
          (primeOverHeightOne (ratFuncInfinityPlace K) P) x =
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x) := by
        simpa [ratFuncInfinityIntegralClosureFractionRingEquiv] using hord
      rw [finiteExtensionPrincipalDivisor_inr, ← hord']
      exact valuation_eq_exp_neg_finitePlaceOrder
        (primeOverHeightOne (ratFuncInfinityPlace K) P) x hx

private theorem probe_finiteExtensionFinitePlace_X_le_one
    (q : FiniteExtensionFinitePlace K L) :
    q.valuation L (algebraMap (RatFunc K) L RatFunc.X) ≤ 1 := by
  change q.valuation L (algebraMap K[X] L Polynomial.X) ≤ 1
  rw [IsScalarTower.algebraMap_apply K[X]
    (RatFuncFiniteIntegralClosure K L) L]
  exact q.valuation_le_one _

private theorem probe_finiteExtensionInfinityPlace_X_gt_one
    (P : FiniteExtensionInfinityPlace K L) :
    1 < (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L
      (algebraMap (RatFunc K) L RatFunc.X) := by
  let q := primeOverHeightOne (ratFuncInfinityPlace K) P
  let pi := ratFuncInfinityUniformizer K
  have hpiBase : pi ∈ (ratFuncInfinityPlace K).asIdeal := by
    rw [ratFuncInfinityPlace_span_uniformizer]
    exact Ideal.mem_span_singleton_self pi
  have hpiP : algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) pi ∈ P.1 := by
    have hover : (ratFuncInfinityPlace K).asIdeal = Ideal.comap
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) P.1 := by
      exact Ideal.over_def P.1 (ratFuncInfinityPlace K).asIdeal
    exact Ideal.mem_comap.mp (hover ▸ hpiBase)
  have hpiLt : q.valuation L
      (algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) pi) < 1 :=
    (q.valuation_lt_one_iff_mem
      (algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) pi)).mpr hpiP
  have hpiImage : algebraMap
      (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L) pi) =
        (algebraMap (RatFunc K) L RatFunc.X)⁻¹ := by
    change algebraMap (RatFunc K) L (1 / RatFunc.X) =
      (algebraMap (RatFunc K) L RatFunc.X)⁻¹
    simp
  have hxinverse : q.valuation L
      (algebraMap (RatFunc K) L RatFunc.X)⁻¹ < 1 := by
    rw [← hpiImage]
    exact hpiLt
  exact ((q.valuation L).one_lt_val_iff
    (by
      simpa using
        (algebraMap (RatFunc K) L).injective.ne RatFunc.X_ne_zero)).mpr hxinverse

private theorem probeFiniteExtensionPlaceValuation_injective :
    Function.Injective (probeFiniteExtensionPlaceValuation K L) := by
  intro w₁ w₂ h
  cases w₁ with
  | inl q₁ =>
      cases w₂ with
      | inl q₂ =>
          apply congrArg Sum.inl
          apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := L)
          have hval : q₁.valuation L = q₂.valuation L := by
            simpa [probeFiniteExtensionPlaceValuation] using h
          rw [hval]
      | inr P₂ =>
          exfalso
          have hle := probe_finiteExtensionFinitePlace_X_le_one K L q₁
          have hgt := probe_finiteExtensionInfinityPlace_X_gt_one K L P₂
          have hval : q₁.valuation L =
              (primeOverHeightOne (ratFuncInfinityPlace K) P₂).valuation L := by
            simpa [probeFiniteExtensionPlaceValuation] using h
          rw [← hval] at hgt
          exact (not_lt_of_ge hle) hgt
  | inr P₁ =>
      cases w₂ with
      | inl q₂ =>
          exfalso
          have hgt := probe_finiteExtensionInfinityPlace_X_gt_one K L P₁
          have hle := probe_finiteExtensionFinitePlace_X_le_one K L q₂
          have hval :
              (primeOverHeightOne (ratFuncInfinityPlace K) P₁).valuation L =
                q₂.valuation L := by
            simpa [probeFiniteExtensionPlaceValuation] using h
          rw [hval] at hgt
          exact (not_lt_of_ge hle) hgt
      | inr P₂ =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hval :
              (primeOverHeightOne (ratFuncInfinityPlace K) P₁).valuation L =
                (primeOverHeightOne (ratFuncInfinityPlace K) P₂).valuation L := by
            simpa [probeFiniteExtensionPlaceValuation] using h
          have hprime :
              primeOverHeightOne (ratFuncInfinityPlace K) P₁ =
                primeOverHeightOne (ratFuncInfinityPlace K) P₂ := by
            apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := L)
            rw [hval]
          exact congrArg HeightOneSpectrum.asIdeal hprime

private theorem probeFiniteExtensionPlaceValuation_constant_le_one
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    (w : FiniteExtensionPlace K L) (c : K) :
    probeFiniteExtensionPlaceValuation K L w (algebraMap K L c) ≤ 1 := by
  cases w with
  | inl q =>
      have hrepr : algebraMap K L c =
          algebraMap (RatFuncFiniteIntegralClosure K L) L
            (algebraMap K (RatFuncFiniteIntegralClosure K L) c) := by
        rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
        rfl
      rw [hrepr]
      exact q.valuation_le_one _
  | inr P =>
      have hrepr : algebraMap K L c =
          algebraMap (RatFuncInfinityIntegralClosure K L) L
            (algebraMap K (RatFuncInfinityIntegralClosure K L) c) := by
        rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
        rfl
      rw [hrepr]
      exact (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation_le_one _

private noncomputable def residueFieldAlgEquivOfIdealEq
    {I J : Ideal K[X]} [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[K] J.ResidueField := by
  subst J
  exact AlgEquiv.refl

section ResidueTransport

variable {R F S E : Type*}
  [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing S] [IsDedekindDomain S] [Field E] [Algebra S E] [IsFractionRing S E]

private noncomputable def valuationSubringRingEquivOfComapEq
    (V : ValuationSubring F) (W : ValuationSubring E) (e : F ≃+* E)
    (h : W.comap e.toRingHom = V) : V ≃+* W where
  toFun x := ⟨e x, by
    change (x : F) ∈ W.comap e.toRingHom
    rw [h]
    exact x.2⟩
  invFun y := ⟨e.symm y, by
    rw [← h]
    change e (e.symm (y : E)) ∈ W
    simpa using y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add e (x : F) (y : F))

private noncomputable def heightOneSpectrumResidueFieldToValuationSubring
    (q : HeightOneSpectrum R) :
    q.asIdeal.ResidueField ≃+*
      IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F q) :=
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F q)).toRingEquiv

private noncomputable def heightOneSpectrumResidueFieldRingEquivOfComapEq
    (q : HeightOneSpectrum R) (r : HeightOneSpectrum S) (e : F ≃+* E)
    (h : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E r).comap
        e.toRingHom =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F q) :
    q.asIdeal.ResidueField ≃+* r.asIdeal.ResidueField :=
  (heightOneSpectrumResidueFieldToValuationSubring q).trans <|
    (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringRingEquivOfComapEq
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F q)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E r)
        e h)).trans
    (heightOneSpectrumResidueFieldToValuationSubring r).symm

end ResidueTransport

private theorem finrank_eq_of_ringEquiv_of_finite_base
    {k E F : Type*} [Field k] [Fintype k]
    [Field E] [Field F] [Algebra k E] [Algebra k F]
    [FiniteDimensional k E] [FiniteDimensional k F]
    (e : E ≃+* F) : Module.finrank k E = Module.finrank k F := by
  apply Nat.pow_right_injective (a := Nat.card k) (by
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_iff.mpr Fintype.one_lt_card)
  change Nat.card k ^ Module.finrank k E =
    Nat.card k ^ Module.finrank k F
  rw [← Module.natCard_eq_pow_finrank,
    ← Module.natCard_eq_pow_finrank]
  exact Nat.card_congr e.toEquiv

section ValuationCenter

variable {R S F : Type*} [CommRing R] [IsDomain R]
  [CommRing S] [Field F]
  [Algebra R F] [Algebra R S] [Algebra S F]
  [IsScalarTower R S F] [IsIntegralClosure S R F]
  [IsDedekindDomain S] [IsFractionRing S F]

private noncomputable def integralClosureToValuationSubring
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V) :
    S →+* V := by
  letI : IsIntegrallyClosedIn V.toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn V F)
  exact (Subring.inclusion ((Subring.integralClosure_le_iff).2 hbase)).comp
    (IsIntegralClosure.equiv R S F (integralClosure R F)).toRingEquiv.toRingHom

private def valuationCenterIdeal
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V) :
    Ideal S :=
  Ideal.comap (integralClosureToValuationSubring (S := S) V hbase)
    (IsLocalRing.maximalIdeal V)

private theorem valuationCenterIdeal_isPrime
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V) :
    (valuationCenterIdeal (S := S) V hbase).IsPrime := by
  exact Ideal.comap_isPrime _ _

private theorem valuationCenterIdeal_ne_bot_of_mem_nonunits
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V)
    (r : R) (hr0 : algebraMap R F r ≠ 0)
    (hr : algebraMap R F r ∈ V.nonunits) :
    valuationCenterIdeal (S := S) V hbase ≠ ⊥ := by
  intro hbot
  let a : S := algebraMap R S r
  have ha0 : a ≠ 0 := by
    intro ha
    apply hr0
    have hval : algebraMap S F a = algebraMap S F 0 :=
      congrArg (fun z : S => algebraMap S F z) ha
    rw [IsScalarTower.algebraMap_apply R S F]
    simpa [a] using hval
  have ha : a ∈ valuationCenterIdeal (S := S) V hbase := by
    change integralClosureToValuationSubring (S := S) V hbase a ∈
      IsLocalRing.maximalIdeal V
    rw [IsLocalRing.mem_maximalIdeal]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    all_goals
      have hφa :
          ((integralClosureToValuationSubring (S := S) V hbase a : V) : F) =
            algebraMap S F a :=
        IsIntegralClosure.algebraMap_equiv R S F (integralClosure R F) a
      have hSR : algebraMap S F a = algebraMap R F r := by
        rw [IsScalarTower.algebraMap_apply R S F]
      simpa only [hφa.trans hSR] using hr
  rw [hbot] at ha
  exact ha0 (Ideal.mem_bot.mp ha)

private noncomputable def valuationCenterPlace
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V)
    (hne : valuationCenterIdeal (S := S) V hbase ≠ ⊥) :
    HeightOneSpectrum S :=
  ⟨valuationCenterIdeal (S := S) V hbase,
    valuationCenterIdeal_isPrime (S := S) V hbase, hne⟩

private theorem valuationSubringAt_valuationCenterPlace_le
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V)
    (hne : valuationCenterIdeal (S := S) V hbase ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
      (valuationCenterPlace (S := S) V hbase hne) ≤ V := by
  let q := valuationCenterPlace (S := S) V hbase hne
  let φ : S →+* V :=
    integralClosureToValuationSubring (S := S) V hbase
  rintro x ⟨a, s, hs, rfl⟩
  have hsNotMem : s ∉ q.asIdeal := hs
  have hsUnit : IsUnit (φ s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact hsNotMem
  obtain ⟨u, hu⟩ := hsUnit
  let t : V := φ a * ↑(u⁻¹)
  have ht : algebraMap S F a * (algebraMap S F s)⁻¹ = (t : F) := by
    dsimp only [t]
    have hφa : ((φ a : V) : F) = algebraMap S F a := by
      exact IsIntegralClosure.algebraMap_equiv R S F
        (integralClosure R F) a
    have hφs : ((φ s : V) : F) = algebraMap S F s := by
      exact IsIntegralClosure.algebraMap_equiv R S F
        (integralClosure R F) s
    rw [← hφa, ← hφs, ← hu]
    change ((φ a : V) : F) * ((((u : V) : F))⁻¹) =
      ((φ a : V) : F) * (((↑(u⁻¹) : V) : F))
    congr 1
    exact (map_units_inv V.toSubring.subtype u).symm
  rw [ht]
  exact t.property

private theorem valuationSubringAt_valuationCenterPlace_eq
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V)
    (hne : valuationCenterIdeal (S := S) V hbase ≠ ⊥)
    (hV : V ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
      (valuationCenterPlace (S := S) V hbase hne) = V := by
  exact ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAt_valuationCenterPlace_le (S := S) V hbase hne) hV

end ValuationCenter

include L in
private theorem probe_ratFuncFinitePlaceDegree_eq_finrank_residue
    (p : HeightOneSpectrum K[X]) :
    Module.finrank K p.asIdeal.ResidueField = ratFuncFinitePlaceDegree p := by
  let r := finitePlaceNormalizedPrime p
  have hp : normalizedPrimeFinitePlace (K := K) r = p := by
    exact normalizedPrimeFinitePlace_finitePlaceNormalizedPrime p
  have hpIdeal : p.asIdeal = Ideal.span {(r : K[X])} := by
    rw [← show (normalizedPrimeFinitePlace (K := K) r).asIdeal = p.asIdeal by
      exact congrArg HeightOneSpectrum.asIdeal hp]
    rfl
  letI : (Ideal.span {(r : K[X])}).IsPrime :=
    (normalizedPrimeFinitePlace (K := K) r).isPrime
  letI : (Ideal.span {(r : K[X])}).IsMaximal :=
    (inferInstance : (Ideal.span {(r : K[X])}).IsPrime).isMaximal (by
      simpa only [ne_eq, Ideal.span_singleton_eq_bot] using r.property.1.ne_zero)
  let ep := residueFieldAlgEquivOfIdealEq (K := K) hpIdeal
  let e : (K[X] ⧸ Ideal.span {(r : K[X])}) ≃ₐ[K]
      (Ideal.span {(r : K[X])}).ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K
        (K[X] ⧸ Ideal.span {(r : K[X])})
        (Ideal.span {(r : K[X])}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  calc
    Module.finrank K p.asIdeal.ResidueField =
        Module.finrank K (Ideal.span {(r : K[X])}).ResidueField :=
      ep.toLinearEquiv.finrank_eq
    _ = Module.finrank K (K[X] ⧸ Ideal.span {(r : K[X])}) :=
      e.toLinearEquiv.finrank_eq.symm
    _ = (r : K[X]).natDegree :=
      (AdjoinRoot.powerBasis r.property.1.ne_zero).finrank
    _ = ratFuncFinitePlaceDegree p := by
      rw [ratFuncFinitePlaceDegree]

private theorem probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K L (.inl q) =
      Module.finrank K q.asIdeal.ResidueField := by
  let p := HeightOneSpectrum.under K[X] q
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : Localization.AtPrime.IsLiesOverAlgebra p.asIdeal q.asIdeal := ⟨rfl⟩
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq p.asIdeal q.asIdeal]
  rw [← probe_ratFuncFinitePlaceDegree_eq_finrank_residue K L p]
  rw [mul_comm, Module.finrank_mul_finrank]

private theorem probe_finiteExtensionPlaceDegree_inr_eq_finrank_residue
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K L (.inr P) =
      Module.finrank K P.1.ResidueField := by
  let p := (ratFuncInfinityPlace K).asIdeal
  letI hLocalAlg := Localization.AtPrime.algebraOfLiesOver p P.1
  letI : Localization.AtPrime.IsLiesOverAlgebra p P.1 := ⟨rfl⟩
  letI : Algebra p.ResidueField P.1.ResidueField :=
    IsLocalRing.ResidueField.instAlgebra
  letI : IsScalarTower K p.ResidueField P.1.ResidueField := inferInstance
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq p P.1]
  have hbase : Module.finrank K p.ResidueField = 1 :=
    by simpa [p] using
      (ratFuncInfinityPlaceResidueEquiv K).toLinearEquiv.finrank_eq
  calc
    Module.finrank p.ResidueField P.1.ResidueField =
        1 * Module.finrank p.ResidueField P.1.ResidueField := by simp
    _ = Module.finrank K p.ResidueField *
        Module.finrank p.ResidueField P.1.ResidueField := by rw [hbase]
    _ = Module.finrank K P.1.ResidueField :=
      Module.finrank_mul_finrank K p.ResidueField P.1.ResidueField

end

noncomputable section

section PlaneBoundaryProbe


variable {K₀ : Type*} [Field K₀] [Fintype K₀] [DecidableEq K₀]
  [DecidableEq (RatFunc K₀)]

theorem finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
    {f : MvPolynomial (Fin 2) K₀} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionPositiveDegree K₀ (PlaneCurveFunctionField f)
        (planeCurveFunction f 1) ≤ MvPolynomial.degreeOf 0 f := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L₀ := PlaneCurveFunctionField f
  let x : L₀ := planeCurveFunction f 0
  let y : L₀ := planeCurveFunction f 1
  have hxTrans : Transcendental K₀ x :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hyTrans : Transcendental K₀ y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  let firstAlg : Algebra (RatFunc K₀) L₀ :=
    planeCurveFirstCoordinateRatFuncAlgebra f hxTrans
  letI : Algebra (RatFunc K₀) L₀ := firstAlg
  letI : FiniteDimensional (RatFunc K₀) L₀ :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K₀) L₀ :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : IsScalarTower K₀ (RatFunc K₀) L₀ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap K₀ L₀ c =
      ratFuncSpecialization x hxTrans (RatFunc.C c)
    have h := DFunLike.congr_fun
      (ratFuncSpecialization_comp_polynomial_algebraMap x hxTrans)
      (Polynomial.C c)
    simpa using h.symm
  letI : Algebra K₀[X] L₀ :=
    RingHom.toAlgebra ((algebraMap (RatFunc K₀) L₀).comp
      (algebraMap K₀[X] (RatFunc K₀)))
  letI : IsScalarTower K₀[X] (RatFunc K₀) L₀ :=
    .of_algebraMap_eq' rfl
  letI : Algebra K₀ (RatFuncFiniteIntegralClosure K₀ L₀) :=
    RingHom.toAlgebra
      ((algebraMap K₀[X] (RatFuncFiniteIntegralClosure K₀ L₀)).comp
        (algebraMap K₀ K₀[X]))
  letI : IsScalarTower K₀ K₀[X]
      (RatFuncFiniteIntegralClosure K₀ L₀) :=
    .of_algebraMap_eq' rfl
  letI : Algebra K₀ (RatFuncInfinityIntegers K₀) :=
    (ratFuncInfinityConstantRingHom K₀).toAlgebra
  letI : IsScalarTower K₀ (RatFuncInfinityIntegers K₀) (RatFunc K₀) :=
    .of_algebraMap_eq' rfl
  letI : Algebra K₀ (RatFuncInfinityIntegralClosure K₀ L₀) :=
    RingHom.toAlgebra
      ((algebraMap (RatFuncInfinityIntegers K₀)
        (RatFuncInfinityIntegralClosure K₀ L₀)).comp
          (algebraMap K₀ (RatFuncInfinityIntegers K₀)))
  letI : IsScalarTower K₀ (RatFuncInfinityIntegers K₀)
      (RatFuncInfinityIntegralClosure K₀ L₀) :=
    .of_algebraMap_eq' rfl
  letI : IsDedekindDomain (RatFuncFiniteIntegralClosure K₀ L₀) :=
    integralClosure.isDedekindDomain K₀[X] (RatFunc K₀) L₀
  letI : IsFractionRing (RatFuncFiniteIntegralClosure K₀ L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K₀) L₀
  letI : IsDedekindDomain (RatFuncInfinityIntegralClosure K₀ L₀) :=
    IsIntegralClosure.isDedekindDomain
      (RatFuncInfinityIntegers K₀) (RatFunc K₀) L₀
      (RatFuncInfinityIntegralClosure K₀ L₀)
  letI : IsFractionRing (RatFuncInfinityIntegralClosure K₀ L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K₀) L₀
  let W₁ := FiniteExtensionPlace K₀ L₀
  let divisor₁ : W₁ →₀ ℤ :=
    finiteExtensionPrincipalDivisor K₀ L₀ y
  let D₁ : W₁ → ℤ := fun w =>
    divisor₁ w
  let S₁ : Finset W₁ := divisor₁.support.filter
    (fun w => 0 < D₁ w)
  let degree₁ : W₁ → ℕ := fun w =>
    finiteExtensionPlaceDegree K₀ L₀ w
  let infinityPrime₁ := fun P : FiniteExtensionInfinityPlace K₀ L₀ =>
    primeOverHeightOne (ratFuncInfinityPlace K₀) P
  have hdegree₁ : ∀ w : W₁, degree₁ w =
      match w with
      | .inl q => Module.finrank K₀ q.asIdeal.ResidueField
      | .inr P => Module.finrank K₀ P.1.ResidueField := by
    intro w
    cases w with
    | inl q =>
        exact probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue
          K₀ L₀ q
    | inr P =>
        exact probe_finiteExtensionPlaceDegree_inr_eq_finrank_residue
          K₀ L₀ P
  let v₁ : W₁ → Valuation L₀ (WithZero (Multiplicative ℤ)) :=
    probeFiniteExtensionPlaceValuation K₀ L₀
  have hv₁surj : ∀ w : W₁, Function.Surjective (v₁ w) := by
    intro w
    exact probeFiniteExtensionPlaceValuation_surjective K₀ L₀ w
  have hv₁y : ∀ w : W₁,
      v₁ w y = exp (-D₁ w) := by
    intro w
    exact probeFiniteExtensionPlaceValuation_eq_exp_neg_order
      K₀ L₀ w y hy0
  have hv₁const : ∀ (w : W₁) (c : K₀),
      v₁ w (algebraMap K₀ L₀ c) ≤ 1 := by
    intro w c
    exact (by
      change probeFiniteExtensionPlaceValuation K₀ L₀ w
        (algebraMap K₀ L₀ c) ≤ 1
      cases w with
      | inl q =>
          have hrepr : algebraMap K₀ L₀ c =
              algebraMap (RatFuncFiniteIntegralClosure K₀ L₀) L₀
                (algebraMap K₀
                  (RatFuncFiniteIntegralClosure K₀ L₀) c) := by
            rw [IsScalarTower.algebraMap_apply K₀ (RatFunc K₀) L₀]
            rfl
          rw [hrepr]
          exact q.valuation_le_one _
      | inr P =>
          have hrepr : algebraMap K₀ L₀ c =
              algebraMap (RatFuncInfinityIntegralClosure K₀ L₀) L₀
                (algebraMap K₀
                  (RatFuncInfinityIntegralClosure K₀ L₀) c) := by
            rw [IsScalarTower.algebraMap_apply K₀ (RatFunc K₀) L₀]
            rfl
          rw [hrepr]
          exact (primeOverHeightOne
            (ratFuncInfinityPlace K₀) P).valuation_le_one _)
  have hv₁inj : Function.Injective v₁ := by
    change Function.Injective
      (probeFiniteExtensionPlaceValuation K₀ L₀)
    exact probeFiniteExtensionPlaceValuation_injective K₀ L₀
  let secondAlg : Algebra (RatFunc K₀) L₀ :=
    planeCurveSecondCoordinateRatFuncAlgebra f hyTrans
  letI : Algebra (RatFunc K₀) L₀ := secondAlg
  letI : FiniteDimensional (RatFunc K₀) L₀ :=
    finiteDimensional_planeCurveFunctionField_over_secondRatFunc
      hf hpartialFirst
  letI : Algebra.IsSeparable (RatFunc K₀) L₀ :=
    separable_planeCurveFunctionField_over_secondRatFunc hf hpartialFirst
  letI : IsScalarTower K₀ (RatFunc K₀) L₀ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap K₀ L₀ c =
      ratFuncSpecialization y hyTrans (RatFunc.C c)
    have h := DFunLike.congr_fun
      (ratFuncSpecialization_comp_polynomial_algebraMap y hyTrans)
      (Polynomial.C c)
    simpa using h.symm
  letI : Algebra K₀[X] L₀ :=
    RingHom.toAlgebra ((algebraMap (RatFunc K₀) L₀).comp
      (algebraMap K₀[X] (RatFunc K₀)))
  letI : IsScalarTower K₀[X] (RatFunc K₀) L₀ :=
    .of_algebraMap_eq' rfl
  letI : Algebra K₀ (RatFuncFiniteIntegralClosure K₀ L₀) :=
    RingHom.toAlgebra
      ((algebraMap K₀[X] (RatFuncFiniteIntegralClosure K₀ L₀)).comp
        (algebraMap K₀ K₀[X]))
  letI : IsScalarTower K₀ K₀[X]
      (RatFuncFiniteIntegralClosure K₀ L₀) :=
    .of_algebraMap_eq' rfl
  letI : IsDedekindDomain (RatFuncFiniteIntegralClosure K₀ L₀) :=
    integralClosure.isDedekindDomain K₀[X] (RatFunc K₀) L₀
  letI : IsFractionRing (RatFuncFiniteIntegralClosure K₀ L₀) L₀ :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K₀) L₀
  have hpolyX : algebraMap K₀[X] L₀ Polynomial.X = y := by
    change ratFuncSpecialization y hyTrans RatFunc.X = y
    simp [ratFuncSpecialization, RatFunc.algEquivOfTranscendental_X]
  have hcenter : ∀ (w : W₁), 0 < D₁ w →
      ∃ q : FiniteExtensionFinitePlace K₀ L₀,
        q.valuation L₀ = v₁ w ∧
          finiteExtensionPlaceDegree K₀ L₀ (.inl q) = degree₁ w ∧
          finiteExtensionPrincipalDivisor K₀ L₀ y (.inl q) = D₁ w := by
    intro w hw
    let v := v₁ w
    let V := v.valuationSubring
    have hvylt : v y < 1 := by
      rw [hv₁y w, ← exp_zero, exp_lt_exp]
      omega
    have hyV : y ∈ V := by
      change v y ≤ 1
      exact le_of_lt hvylt
    have hconstV : ∀ c : K₀, algebraMap K₀ L₀ c ∈ V := by
      intro c
      change v (algebraMap K₀ L₀ c) ≤ 1
      exact hv₁const w c
    have hbase : ∀ P : K₀[X], algebraMap K₀[X] L₀ P ∈ V := by
      intro P
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ =>
          rw [map_add]
          exact add_mem hP hQ
      | monomial n c =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
            hpolyX]
          have hC : algebraMap K₀[X] L₀ (Polynomial.C c) =
              algebraMap K₀ L₀ c := by
            change algebraMap (RatFunc K₀) L₀
              (algebraMap K₀[X] (RatFunc K₀) (Polynomial.C c)) =
                algebraMap K₀ L₀ c
            rw [show algebraMap K₀[X] (RatFunc K₀) (Polynomial.C c) =
              algebraMap K₀ (RatFunc K₀) c by simp,
              IsScalarTower.algebraMap_apply K₀ (RatFunc K₀) L₀]
          rw [hC]
          exact mul_mem (hconstV c) (pow_mem hyV n)
    have hyNonunit : algebraMap K₀[X] L₀ Polynomial.X ∈ V.nonunits := by
      rw [hpolyX, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨hyV, (Valuation.mem_maximalIdeal_iff (v := v)).mpr hvylt⟩
    have hcenterNe : valuationCenterIdeal
        (S := RatFuncFiniteIntegralClosure K₀ L₀) V hbase ≠ ⊥ :=
      valuationCenterIdeal_ne_bot_of_mem_nonunits
        (S := RatFuncFiniteIntegralClosure K₀ L₀) V hbase
        Polynomial.X (by
          rw [hpolyX]
          intro hy0
          apply hyTrans
          rw [hy0]
          exact isAlgebraic_zero) hyNonunit
    let q : FiniteExtensionFinitePlace K₀ L₀ :=
      valuationCenterPlace (S := RatFuncFiniteIntegralClosure K₀ L₀)
        V hbase hcenterNe
    have hvNontrivial : v.IsNontrivial :=
      (Valuation.isNontrivial_iff_exists_lt_one v).mpr
        ⟨y, (by
          intro hy0
          apply hyTrans
          rw [hy0]
          exact isAlgebraic_zero), hvylt⟩
    have hVne : V ≠ ⊤ := by
      rw [ne_eq, Valuation.valuationSubring_eq_top_iff]
      exact not_not_intro hvNontrivial
    have hsubring :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L₀ q = V :=
      valuationSubringAt_valuationCenterPlace_eq
        (S := RatFuncFiniteIntegralClosure K₀ L₀)
        V hbase hcenterNe hVne
    have hequiv : (q.valuation L₀).IsEquiv v := by
      rw [Valuation.isEquiv_iff_valuationSubring,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hsubring
    have hqval : q.valuation L₀ = v₁ w :=
      valuation_eq_of_isEquiv_of_surjective hequiv
        (q.valuation_surjective L₀) (hv₁surj w)
    have hqOrderVal := probeFiniteExtensionPlaceValuation_eq_exp_neg_order
      K₀ L₀ (.inl q) y hy0
    have horder : finiteExtensionPrincipalDivisor K₀ L₀ y (.inl q) =
        D₁ w := by
      change q.valuation L₀ y =
          exp (-finiteExtensionPrincipalDivisor K₀ L₀ y (.inl q)) at hqOrderVal
      rw [hqval, hv₁y w] at hqOrderVal
      have hneg := exp_injective hqOrderVal
      omega
    refine ⟨q, hqval, ?_, horder⟩
    letI : Finite q.asIdeal.ResidueField :=
      finiteExtensionFinitePlace_residueField_finite
        (K := K₀) (L := L₀) q
    cases w with
    | inl q₁ =>
        let e := heightOneSpectrumResidueFieldRingEquivOfComapEq
          q₁ q (RingEquiv.refl L₀) (by
            have hqval' : q.valuation L₀ = q₁.valuation L₀ := by
              simpa [v₁, probeFiniteExtensionPlaceValuation] using hqval
            rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
            ext z
            change q.valuation L₀ z ≤ 1 ↔ q₁.valuation L₀ z ≤ 1
            rw [hqval'])
        letI : Finite q₁.asIdeal.ResidueField :=
          Finite.of_injective e e.injective
        letI : FiniteDimensional K₀ q.asIdeal.ResidueField := inferInstance
        letI : FiniteDimensional K₀ q₁.asIdeal.ResidueField := inferInstance
        rw [probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue
          K₀ L₀ q, hdegree₁]
        exact (finrank_eq_of_ringEquiv_of_finite_base e).symm
    | inr P₁ =>
        let q₁ := infinityPrime₁ P₁
        let e := heightOneSpectrumResidueFieldRingEquivOfComapEq
          q₁ q (RingEquiv.refl L₀) (by
            have hqval' : q.valuation L₀ = q₁.valuation L₀ := by
              simpa [v₁, probeFiniteExtensionPlaceValuation,
                q₁, infinityPrime₁] using hqval
            rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
            ext z
            change q.valuation L₀ z ≤ 1 ↔ q₁.valuation L₀ z ≤ 1
            rw [hqval'])
        letI : Finite q₁.asIdeal.ResidueField :=
          Finite.of_injective e e.injective
        letI : Fintype q.asIdeal.ResidueField := Fintype.ofFinite _
        letI : Fintype q₁.asIdeal.ResidueField := Fintype.ofFinite _
        letI : Module.Finite K₀ q.asIdeal.ResidueField := by
          rw [Module.finite_def]
          exact ⟨Finset.univ, by simp⟩
        letI : Module.Finite K₀ q₁.asIdeal.ResidueField := by
          rw [Module.finite_def]
          exact ⟨Finset.univ, by simp⟩
        rw [probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue
          K₀ L₀ q, hdegree₁]
        exact (finrank_eq_of_ringEquiv_of_finite_base e).symm
  let T₁ := {w : W₁ // w ∈ S₁}
  let centerFinite : T₁ → FiniteExtensionFinitePlace K₀ L₀ :=
    fun w => Classical.choose
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)
  have hcenterFiniteVal (w : T₁) :
      (centerFinite w).valuation L₀ = v₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).1
  have hcenterFiniteDegree (w : T₁) :
      finiteExtensionPlaceDegree K₀ L₀ (.inl (centerFinite w)) =
        degree₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).2.1
  have hcenterFiniteOrder (w : T₁) :
      finiteExtensionPrincipalDivisor K₀ L₀ y
          (.inl (centerFinite w)) = D₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).2.2
  let W₂ := FiniteExtensionPlace K₀ L₀
  let D₂ : W₂ → ℤ := fun w =>
    finiteExtensionPrincipalDivisor K₀ L₀ y w
  let degree₂ : W₂ → ℕ := fun w =>
    finiteExtensionPlaceDegree K₀ L₀ w
  let center : T₁ → W₂ := fun w => .inl (centerFinite w)
  have hcenterOrder (w : T₁) : D₂ (center w) = D₁ w.1 := by
    exact hcenterFiniteOrder w
  have hcenterDegree (w : T₁) :
      degree₂ (center w) = degree₁ w.1 := by
    exact hcenterFiniteDegree w
  have hcenterInj : Function.Injective center := by
    intro a b hab
    have hcf : centerFinite a = centerFinite b := by
      change Sum.inl (centerFinite a) = Sum.inl (centerFinite b) at hab
      exact Sum.inl.inj hab
    apply Subtype.ext
    apply hv₁inj
    rw [← hcenterFiniteVal a, ← hcenterFiniteVal b, hcf]
  let S₂ := (finiteExtensionPrincipalDivisor K₀ L₀ y).support.filter
    (fun w => 0 < D₂ w)
  have hcenterImageSubset : S₁.attach.image center ⊆ S₂ := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    apply Finset.mem_filter.mpr
    have hpos : 0 < D₁ w.1 := (Finset.mem_filter.mp w.2).2
    constructor
    · apply Finsupp.mem_support_iff.mpr
      change D₂ (center w) ≠ 0
      rw [hcenterOrder]
      exact ne_of_gt hpos
    · rw [hcenterOrder]
      exact hpos
  have hsumImage :
      (∑ z ∈ S₁.attach.image center,
          (D₂ z).toNat * degree₂ z) =
        ∑ w ∈ S₁.attach,
          (D₁ w.1).toNat * degree₁ w.1 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro w hw
      rw [hcenterOrder, hcenterDegree]
    · intro a ha b hb hab
      exact hcenterInj hab
  have hsource_le :
      (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤
        finiteExtensionPositiveDegree K₀ L₀ y := by
    calc
      _ = ∑ w ∈ S₁.attach,
          (D₁ w.1).toNat * degree₁ w.1 := by
            symm
            exact Finset.sum_attach S₁
              (fun w => (D₁ w).toNat * degree₁ w)
      _ = ∑ z ∈ S₁.attach.image center,
          (D₂ z).toNat * degree₂ z := hsumImage.symm
      _ ≤ ∑ z ∈ S₂, (D₂ z).toNat * degree₂ z :=
        Finset.sum_le_sum_of_subset hcenterImageSubset
      _ = finiteExtensionPositiveDegree K₀ L₀ y := by
        rfl
  have hySecondDegree :
      finiteExtensionPositiveDegree K₀ L₀ y =
        MvPolynomial.degreeOf 0 f := by
    have hheight := finiteExtensionPositiveDegree_polynomial
      K₀ L₀ Polynomial.X Polynomial.X_ne_zero
    change finiteExtensionPositiveDegree K₀ L₀
        (algebraMap K₀[X] L₀ Polynomial.X) =
          Module.finrank (RatFunc K₀) L₀ *
            Polynomial.X.natDegree at hheight
    rw [hpolyX,
      finrank_planeCurveFunctionField_over_secondRatFunc_eq_degreeOf_first
        hf hpartialFirst] at hheight
    simpa using hheight
  have hySourceBound :
      (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤
        MvPolynomial.degreeOf 0 f := by
    exact hsource_le.trans_eq hySecondDegree
  change (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤
    MvPolynomial.degreeOf 0 f
  exact hySourceBound

/-- The zero/pole boundary of positive powers of the two plane-curve
coordinates has degree at most twice the sum of the two coordinate degrees. -/
theorem planeCurve_propositionTwoExceptionalPlaces_weightedDegree_le
    {f : MvPolynomial (Fin 2) K₀} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∑ w ∈ propositionTwoExceptionalPlaces K₀ (PlaneCurveFunctionField f)
        ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
        finiteExtensionPlaceDegree K₀ (PlaneCurveFunctionField f) w ≤
      2 * (MvPolynomial.degreeOf 0 f + MvPolynomial.degreeOf 1 f) := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L₀ := PlaneCurveFunctionField f
  let x : L₀ := planeCurveFunction f 0
  let y : L₀ := planeCurveFunction f 1
  have hxTrans : Transcendental K₀ x :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hyTrans : Transcendental K₀ y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro h
    apply hxTrans
    rw [h]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  letI : Algebra (RatFunc K₀) L₀ :=
    planeCurveFirstCoordinateRatFuncAlgebra f hxTrans
  letI : FiniteDimensional (RatFunc K₀) L₀ :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K₀) L₀ :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hxDegree : finiteExtensionPositiveDegree K₀ L₀ x =
      MvPolynomial.degreeOf 1 f := by
    have hheight := finiteExtensionPositiveDegree_polynomial
      K₀ L₀ Polynomial.X Polynomial.X_ne_zero
    have hmap : algebraMap (RatFunc K₀) L₀
        (algebraMap K₀[X] (RatFunc K₀) Polynomial.X) = x := by
      change ratFuncSpecialization x hxTrans RatFunc.X = x
      exact planeCurveFirstCoordinateRatFuncAlgebra_X f hxTrans
    rw [hmap,
      finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
        hf hpartialSecond] at hheight
    simpa using hheight
  have hyDegree : finiteExtensionPositiveDegree K₀ L₀ y ≤
      MvPolynomial.degreeOf 0 f := by
    exact finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
      hf hpartialFirst hpartialSecond
  have hsupportX :
      (finiteExtensionPrincipalDivisor K₀ L₀ (x ^ m)).support =
        (finiteExtensionPrincipalDivisor K₀ L₀ x).support := by
    rw [finiteExtensionPrincipalDivisor_pow K₀ L₀ x hx0 m]
    ext w
    simp [Finsupp.mem_support_iff, hm.ne']
  have hsupportY :
      (finiteExtensionPrincipalDivisor K₀ L₀ (y ^ n)).support =
        (finiteExtensionPrincipalDivisor K₀ L₀ y).support := by
    rw [finiteExtensionPrincipalDivisor_pow K₀ L₀ y hy0 n]
    ext w
    simp [Finsupp.mem_support_iff, hn.ne']
  change (∑ w ∈
      (finiteExtensionPrincipalDivisor K₀ L₀ (x ^ m)).support ∪
        (finiteExtensionPrincipalDivisor K₀ L₀ (y ^ n)).support,
      finiteExtensionPlaceDegree K₀ L₀ w) ≤ _
  rw [hsupportX, hsupportY]
  calc
    _ ≤
        (∑ w ∈ (finiteExtensionPrincipalDivisor K₀ L₀ x).support,
          finiteExtensionPlaceDegree K₀ L₀ w) +
        ∑ w ∈ (finiteExtensionPrincipalDivisor K₀ L₀ y).support,
          finiteExtensionPlaceDegree K₀ L₀ w := by
      let s := (finiteExtensionPrincipalDivisor K₀ L₀ x).support
      let t := (finiteExtensionPrincipalDivisor K₀ L₀ y).support
      let g := fun w => finiteExtensionPlaceDegree K₀ L₀ w
      calc
        ∑ w ∈ s ∪ t, g w =
            (∑ w ∈ s, g w) + ∑ w ∈ t \ s, g w := by
          rw [show s ∪ t = s ∪ (t \ s) by ext i; simp,
            Finset.sum_union Finset.disjoint_sdiff]
        _ ≤ (∑ w ∈ s, g w) + ∑ w ∈ t, g w := by
          exact Nat.add_le_add_left
            (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _
    _ ≤ 2 * finiteExtensionPositiveDegree K₀ L₀ x +
        2 * finiteExtensionPositiveDegree K₀ L₀ y :=
      Nat.add_le_add
        (finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
          K₀ L₀ x hx0)
        (finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
          K₀ L₀ y hy0)
    _ ≤ 2 * (MvPolynomial.degreeOf 0 f +
        MvPolynomial.degreeOf 1 f) := by
      rw [hxDegree]
      omega

end PlaneBoundaryProbe

end
end BGS.CorvajaZannier
