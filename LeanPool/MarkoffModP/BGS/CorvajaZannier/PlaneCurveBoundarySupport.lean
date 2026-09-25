/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityInertiaDegree
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationOrder
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCoordinatePowerHeight
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
public import Mathlib.Tactic

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

@[expose] public section

open scoped Polynomial
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

universe u v

noncomputable section


attribute [local instance high] Module.Free.of_divisionRing

variable (K : Type u) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type v) [Field L] [Algebra (RatFunc K) L]
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

omit [DecidableEq K] in
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

omit [DecidableEq K] in
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

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem probe_finiteExtensionFinitePlace_X_le_one
    (q : FiniteExtensionFinitePlace K L) :
    q.valuation L (algebraMap (RatFunc K) L RatFunc.X) ≤ 1 := by
  change q.valuation L (algebraMap K[X] L Polynomial.X) ≤ 1
  rw [IsScalarTower.algebraMap_apply K[X]
    (RatFuncFiniteIntegralClosure K L) L]
  exact q.valuation_le_one _

omit [DecidableEq K] in
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

omit [DecidableEq K] in
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
    simp⟩
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
    {k E F : Type*} [Field k] [Finite k]
    [Field E] [Field F] [Algebra k E] [Algebra k F]
    [FiniteDimensional k E] [FiniteDimensional k F]
    (e : E ≃+* F) : Module.finrank k E = Module.finrank k F := by
  let : Fintype k := Fintype.ofFinite k
  apply Nat.pow_right_injective (a := Nat.card k) (by
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_iff.mpr Fintype.one_lt_card)
  change Nat.card k ^ Module.finrank k E =
    Nat.card k ^ Module.finrank k F
  rw [← Module.natCard_eq_pow_finrank,
    ← Module.natCard_eq_pow_finrank]
  exact Nat.card_congr e.toEquiv

/-- Equal normalized valuations have residue fields of the same degree over a finite base. -/
private theorem residueFinrank_eq_of_valuation_eq
    {k R S F : Type*} [Field k] [Finite k]
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Algebra S F] [IsFractionRing S F]
    (q : HeightOneSpectrum R) (r : HeightOneSpectrum S)
    [Algebra k q.asIdeal.ResidueField] [Algebra k r.asIdeal.ResidueField]
    [Finite r.asIdeal.ResidueField]
    (h : r.valuation F = q.valuation F) :
    Module.finrank k r.asIdeal.ResidueField = Module.finrank k q.asIdeal.ResidueField := by
  let e := heightOneSpectrumResidueFieldRingEquivOfComapEq q r (RingEquiv.refl F) (by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    ext z
    change r.valuation F z ≤ 1 ↔ q.valuation F z ≤ 1
    rw [h])
  let : Finite q.asIdeal.ResidueField := Finite.of_injective e e.injective
  let : FiniteDimensional k r.asIdeal.ResidueField := inferInstance
  let : FiniteDimensional k q.asIdeal.ResidueField := inferInstance
  exact (finrank_eq_of_ringEquiv_of_finite_base e).symm

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

omit [IsDomain R] [IsDedekindDomain S] [IsFractionRing S F] in
private theorem valuationCenterIdeal_isPrime
    (V : ValuationSubring F)
    (hbase : ∀ r : R, algebraMap R F r ∈ V) :
    (valuationCenterIdeal (S := S) V hbase).IsPrime := by
  exact Ideal.comap_isPrime _ _

omit [IsDomain R] [IsDedekindDomain S] in
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

omit [IsDomain R] in
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

omit [IsDomain R] in
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
omit [DecidableEq (RatFunc K)] [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
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
  let : (Ideal.span {(r : K[X])}).IsPrime :=
    (normalizedPrimeFinitePlace (K := K) r).isPrime
  let : (Ideal.span {(r : K[X])}).IsMaximal :=
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
  let : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have : IsScalarTower K[X] (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := inferInstance
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq p.asIdeal q.asIdeal]
  rw [← probe_ratFuncFinitePlaceDegree_eq_finrank_residue K L p]
  rw [mul_comm, Module.finrank_mul_finrank]

omit [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
private theorem probe_finiteExtensionPlaceDegree_inr_eq_finrank_residue
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K L (.inr P) =
      Module.finrank K P.1.ResidueField := by
  let p := (ratFuncInfinityPlace K).asIdeal
  let hLocalAlg := Localization.AtPrime.algebraOfLiesOver p P.1
  have : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  let : Algebra p.ResidueField P.1.ResidueField :=
    IsLocalRing.ResidueField.instAlgebra
  let : IsScalarTower K p.ResidueField P.1.ResidueField := inferInstance
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

/-- The place degree is determined by any finite residue field with the same valuation. -/
private theorem probe_placeDegree_eq_of_valuation_eq [Fintype K]
    {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Algebra S L] [IsFractionRing S L]
    (w : FiniteExtensionPlace K L) (q : HeightOneSpectrum S)
    [Algebra K q.asIdeal.ResidueField] [Finite q.asIdeal.ResidueField]
    (hq : q.valuation L = probeFiniteExtensionPlaceValuation K L w) :
    finiteExtensionPlaceDegree K L w = Module.finrank K q.asIdeal.ResidueField := by
  cases w with
  | inl r =>
      rw [probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue K L r]
      exact (residueFinrank_eq_of_valuation_eq (k := K) r q hq).symm
  | inr P =>
      rw [probe_finiteExtensionPlaceDegree_inr_eq_finrank_residue K L P]
      exact (residueFinrank_eq_of_valuation_eq (k := K)
        (primeOverHeightOne (ratFuncInfinityPlace K) P) q hq).symm

private theorem weightedSum_le_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (target : Finset β) (map : ↥source → β)
    (sourceWeight : α → ℕ) (targetWeight : β → ℕ)
    (injective : Function.Injective map)
    (weight : ∀ x, targetWeight (map x) = sourceWeight x)
    (membership : ∀ x, map x ∈ target) :
    ∑ x ∈ source, sourceWeight x ≤ ∑ y ∈ target, targetWeight y := by
  have imageSubset : source.attach.image map ⊆ target := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact membership x
  have imageSum : ∑ y ∈ source.attach.image map, targetWeight y =
      ∑ x ∈ source, sourceWeight x := by
    rw [Finset.sum_image]
    · simp only [weight, Finset.sum_attach]
    · intro x hx y hy hxy
      exact injective hxy
  rw [← imageSum]
  exact Finset.sum_le_sum_of_subset imageSubset

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem finitePlace_of_valuation_positive
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    (y : L) (hy0 : y ≠ 0) (hpolyX : algebraMap K[X] L Polynomial.X = y)
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (hvsurj : Function.Surjective v)
    (hvconst : ∀ c : K, v (algebraMap K L c) ≤ 1)
    (hvylt : v y < 1) :
    ∃ q : FiniteExtensionFinitePlace K L, q.valuation L = v := by
  let V := v.valuationSubring
  have hyV : y ∈ V := by
    change v y ≤ 1
    exact le_of_lt hvylt
  have hconstV : ∀ c : K, algebraMap K L c ∈ V := by
    intro c
    change v (algebraMap K L c) ≤ 1
    exact hvconst c
  have hbase : ∀ P : K[X], algebraMap K[X] L P ∈ V := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        rw [map_add]
        exact add_mem hP hQ
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          hpolyX]
        have hC : algebraMap K[X] L (Polynomial.C c) =
            algebraMap K L c := by
          change algebraMap (RatFunc K) L
            (algebraMap K[X] (RatFunc K) (Polynomial.C c)) =
              algebraMap K L c
          rw [show algebraMap K[X] (RatFunc K) (Polynomial.C c) =
            algebraMap K (RatFunc K) c by simp,
            IsScalarTower.algebraMap_apply K (RatFunc K) L]
        rw [hC]
        exact mul_mem (hconstV c) (pow_mem hyV n)
  have hyNonunit : algebraMap K[X] L Polynomial.X ∈ V.nonunits := by
    rw [hpolyX, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨hyV, (Valuation.mem_maximalIdeal_iff (v := v)).mpr hvylt⟩
  have hcenterNe : valuationCenterIdeal
      (S := RatFuncFiniteIntegralClosure K L) V hbase ≠ ⊥ :=
    valuationCenterIdeal_ne_bot_of_mem_nonunits
      (S := RatFuncFiniteIntegralClosure K L) V hbase
      Polynomial.X (by
        rw [hpolyX]
        exact hy0) hyNonunit
  let q : FiniteExtensionFinitePlace K L :=
    valuationCenterPlace (S := RatFuncFiniteIntegralClosure K L)
      V hbase hcenterNe
  have hvNontrivial : v.IsNontrivial :=
    (Valuation.isNontrivial_iff_exists_lt_one v).mpr
      ⟨y, hy0, hvylt⟩
  have hVne : V ≠ ⊤ := by
    rw [ne_eq, Valuation.valuationSubring_eq_top_iff]
    exact not_not_intro hvNontrivial
  have hsubring :
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q = V :=
    valuationSubringAt_valuationCenterPlace_eq
      (S := RatFuncFiniteIntegralClosure K L)
      V hbase hcenterNe hVne
  have hequiv : (q.valuation L).IsEquiv v := by
    rw [Valuation.isEquiv_iff_valuationSubring,
      ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hsubring
  have hqval : q.valuation L = v :=
    valuation_eq_of_isEquiv_of_surjective hequiv
      (q.valuation_surjective L) hvsurj
  exact ⟨q, hqval⟩


/-- An injective, degree-preserving transport of positive places bounds the positive degree. -/
private theorem positiveDegree_le_of_valuation_transport
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    {W : Type*} (divisor : W →₀ ℤ) (degree₁ : W → ℕ)
    (v₁ : W → Valuation L (WithZero (Multiplicative ℤ)))
    (y : L) (hy0 : y ≠ 0) (hpolyX : algebraMap K[X] L Polynomial.X = y)
    (hv₁surj : ∀ w, Function.Surjective (v₁ w))
    (hv₁y : ∀ w, v₁ w y = exp (-divisor w))
    (hv₁const : ∀ w c, v₁ w (algebraMap K L c) ≤ 1)
    (hv₁inj : Function.Injective v₁)
    (hdegree : ∀ w (q : FiniteExtensionFinitePlace K L), q.valuation L = v₁ w →
      finiteExtensionPlaceDegree K L (.inl q) = degree₁ w) :
    ∑ w ∈ divisor.support.filter (fun w => 0 < divisor w),
      (divisor w).toNat * degree₁ w ≤ finiteExtensionPositiveDegree K L y := by
  classical
  let D₁ : W → ℤ := divisor
  let S₁ := divisor.support.filter (fun w => 0 < D₁ w)
  have hcenter : ∀ (w : W), 0 < D₁ w →
      ∃ q : FiniteExtensionFinitePlace K L,
        q.valuation L = v₁ w ∧
          finiteExtensionPlaceDegree K L (.inl q) = degree₁ w ∧
          finiteExtensionPrincipalDivisor K L y (.inl q) = D₁ w := by
    intro w hw
    change 0 < divisor w at hw
    let v := v₁ w
    have hvylt : v y < 1 := by
      rw [hv₁y w, ← exp_zero, exp_lt_exp]
      omega
    obtain ⟨q, hqval⟩ := finitePlace_of_valuation_positive K L y hy0 hpolyX
      v (hv₁surj w) (hv₁const w) hvylt
    have hqOrderVal := probeFiniteExtensionPlaceValuation_eq_exp_neg_order
      K L (.inl q) y hy0
    have horder : finiteExtensionPrincipalDivisor K L y (.inl q) =
        D₁ w := by
      change q.valuation L y =
          exp (-finiteExtensionPrincipalDivisor K L y (.inl q)) at hqOrderVal
      rw [hqval, hv₁y w] at hqOrderVal
      have hneg := exp_injective hqOrderVal
      change -D₁ w = _ at hneg
      omega
    refine ⟨q, hqval, ?_, horder⟩
    exact hdegree w q hqval
  let T₁ := {w : W // w ∈ S₁}
  let centerFinite : T₁ → FiniteExtensionFinitePlace K L :=
    fun w => Classical.choose
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)
  have hcenterFiniteVal (w : T₁) :
      (centerFinite w).valuation L = v₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).1
  have hcenterFiniteDegree (w : T₁) :
      finiteExtensionPlaceDegree K L (.inl (centerFinite w)) =
        degree₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).2.1
  have hcenterFiniteOrder (w : T₁) :
      finiteExtensionPrincipalDivisor K L y
          (.inl (centerFinite w)) = D₁ w.1 := by
    exact (Classical.choose_spec
      (hcenter w.1 (Finset.mem_filter.mp w.2).2)).2.2
  let W₂ := FiniteExtensionPlace K L
  let D₂ : W₂ → ℤ := fun w =>
    finiteExtensionPrincipalDivisor K L y w
  let degree₂ : W₂ → ℕ := fun w =>
    finiteExtensionPlaceDegree K L w
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
  let S₂ := (finiteExtensionPrincipalDivisor K L y).support.filter
    (fun w => 0 < D₂ w)
  have hsource_le :
      (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤
        finiteExtensionPositiveDegree K L y := by
    change _ ≤ ∑ z ∈ S₂, (D₂ z).toNat * degree₂ z
    apply weightedSum_le_of_injective S₁ S₂ center
      (fun w => (D₁ w).toNat * degree₁ w)
      (fun z => (D₂ z).toNat * degree₂ z) hcenterInj
    · intro w
      rw [hcenterOrder, hcenterDegree]
    · intro w
      apply Finset.mem_filter.mpr
      have hpos : 0 < D₁ w.1 := (Finset.mem_filter.mp w.2).2
      constructor
      · apply Finsupp.mem_support_iff.mpr
        change D₂ (center w) ≠ 0
        rw [hcenterOrder]
        exact ne_of_gt hpos
      · rw [hcenterOrder]
        exact hpos
  exact hsource_le



/-- Passing to a second rational-function model cannot decrease the positive degree. -/
private theorem positiveDegree_le_in_secondModel [Fintype K]
    [Algebra K L] [IsScalarTower K (RatFunc K) L]
    (second : RatFunc K →+* L) (y : L) (hy0 : y ≠ 0) :
    let source := finiteExtensionPositiveDegree K L y
    let : Algebra (RatFunc K) L := second.toAlgebra
    ∀ (_ : FiniteDimensional (RatFunc K) L) (_ : Algebra.IsSeparable (RatFunc K) L)
      (_ : IsScalarTower K (RatFunc K) L),
      algebraMap K[X] L Polynomial.X = y → source ≤ finiteExtensionPositiveDegree K L y := by
  classical
  let W₁ := FiniteExtensionPlace K L
  let divisor₁ : W₁ →₀ ℤ :=
    finiteExtensionPrincipalDivisor K L y
  let D₁ : W₁ → ℤ := fun w =>
    divisor₁ w
  let S₁ : Finset W₁ := divisor₁.support.filter
    (fun w => 0 < D₁ w)
  let degree₁ : W₁ → ℕ := fun w =>
    finiteExtensionPlaceDegree K L w
  let v₁ : W₁ → Valuation L (WithZero (Multiplicative ℤ)) :=
    probeFiniteExtensionPlaceValuation K L
  have hdegree₁ {S : Type v} [CommRing S] [IsDedekindDomain S]
      [Algebra S L] [IsFractionRing S L]
      (w : W₁) (q : HeightOneSpectrum S)
      [Algebra K q.asIdeal.ResidueField] [Finite q.asIdeal.ResidueField]
      (hq : q.valuation L = v₁ w) :
      degree₁ w = Module.finrank K q.asIdeal.ResidueField :=
    probe_placeDegree_eq_of_valuation_eq K L w q hq
  have hv₁surj : ∀ w : W₁, Function.Surjective (v₁ w) := by
    intro w
    exact probeFiniteExtensionPlaceValuation_surjective K L w
  have hv₁y : ∀ w : W₁,
      v₁ w y = exp (-D₁ w) := by
    intro w
    exact probeFiniteExtensionPlaceValuation_eq_exp_neg_order
      K L w y hy0
  have hv₁const : ∀ (w : W₁) (c : K),
      v₁ w (algebraMap K L c) ≤ 1 := by
    intro w c
    exact probeFiniteExtensionPlaceValuation_constant_le_one K L w c
  have hv₁inj : Function.Injective v₁ := by
    change Function.Injective
      (probeFiniteExtensionPlaceValuation K L)
    exact probeFiniteExtensionPlaceValuation_injective K L
  intro source secondAlgebra finiteDimension separable tower hpolyX
  have hdegreeCompare (w : W₁) (q : FiniteExtensionFinitePlace K L)
      (hqval : q.valuation L = v₁ w) :
      finiteExtensionPlaceDegree K L (.inl q) = degree₁ w := by
    let : Finite q.asIdeal.ResidueField :=
      finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
    rw [probe_finiteExtensionPlaceDegree_inl_eq_finrank_residue K L q]
    exact (hdegree₁ w q hqval).symm
  have hsource_le :
      (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤ finiteExtensionPositiveDegree K L y :=
    positiveDegree_le_of_valuation_transport K L divisor₁ degree₁ v₁ y hy0 hpolyX
      hv₁surj hv₁y hv₁const hv₁inj hdegreeCompare
  change (∑ w ∈ S₁, (D₁ w).toNat * degree₁ w) ≤ _
  exact hsource_le



end

noncomputable section

section PlaneBoundaryProbe


variable {K₀ : Type*} [Field K₀] [Fintype K₀] [DecidableEq K₀]
  [DecidableEq (RatFunc K₀)]

theorem finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
    {f : MvPolynomial (Fin 2) K₀} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : FiniteDimensional (RatFunc K₀) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K₀) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionPositiveDegree K₀ (PlaneCurveFunctionField f)
        (planeCurveFunction f 1) ≤ MvPolynomial.degreeOf 0 f := by
  intro domain hxTrans firstAlg finiteDimension separable
  classical
  let L₀ := PlaneCurveFunctionField f
  let x : L₀ := planeCurveFunction f 0
  let y : L₀ := planeCurveFunction f 1
  have hyTrans : Transcendental K₀ y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  let : IsScalarTower K₀ (RatFunc K₀) L₀ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap K₀ L₀ c =
      ratFuncSpecialization x hxTrans (RatFunc.C c)
    have h := DFunLike.congr_fun
      (ratFuncSpecialization_comp_polynomial_algebraMap x hxTrans)
      (Polynomial.C c)
    simpa using h.symm
  let secondHom : RatFunc K₀ →+* L₀ := ratFuncSpecialization y hyTrans
  let sourceDegree := finiteExtensionPositiveDegree K₀ L₀ y
  have hcompare := positiveDegree_le_in_secondModel K₀ L₀ secondHom y hy0
  let : Algebra (RatFunc K₀) L₀ := secondHom.toAlgebra
  let : FiniteDimensional (RatFunc K₀) L₀ :=
    finiteDimensional_planeCurveFunctionField_over_secondRatFunc
      hf hpartialFirst
  let : Algebra.IsSeparable (RatFunc K₀) L₀ :=
    separable_planeCurveFunctionField_over_secondRatFunc hf hpartialFirst
  let : IsScalarTower K₀ (RatFunc K₀) L₀ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap K₀ L₀ c =
      ratFuncSpecialization y hyTrans (RatFunc.C c)
    have h := DFunLike.congr_fun
      (ratFuncSpecialization_comp_polynomial_algebraMap y hyTrans)
      (Polynomial.C c)
    simpa using h.symm
  let : Algebra K₀[X] L₀ :=
    RingHom.toAlgebra ((algebraMap (RatFunc K₀) L₀).comp
      (algebraMap K₀[X] (RatFunc K₀)))
  have hpolyX : algebraMap K₀[X] L₀ Polynomial.X = y := by
    change ratFuncSpecialization y hyTrans RatFunc.X = y
    simp [ratFuncSpecialization, RatFunc.algEquivOfTranscendental_X]
  have hsource_le : sourceDegree ≤ finiteExtensionPositiveDegree K₀ L₀ y :=
    hcompare inferInstance inferInstance inferInstance hpolyX
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
  exact hsource_le.trans_eq hySecondDegree

/-- The zero/pole boundary of positive powers of the two plane-curve
coordinates has degree at most twice the sum of the two coordinate degrees. -/
theorem planeCurve_propositionTwoExceptionalPlaces_weightedDegree_le
    {f : MvPolynomial (Fin 2) K₀} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    let := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∑ w ∈ propositionTwoExceptionalPlaces K₀ (PlaneCurveFunctionField f)
        ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
        finiteExtensionPlaceDegree K₀ (PlaneCurveFunctionField f) w ≤
      2 * (MvPolynomial.degreeOf 0 f + MvPolynomial.degreeOf 1 f) := by
  intro domain hxTrans ratFuncAlgebra finiteDimension separable
  classical
  let L₀ := PlaneCurveFunctionField f
  let x : L₀ := planeCurveFunction f 0
  let y : L₀ := planeCurveFunction f 1
  have hyTrans : Transcendental K₀ y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro h
    apply hxTrans
    change IsAlgebraic K₀ x
    rw [h]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
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
  let _ : DecidableEq (FiniteExtensionPlace K₀ L₀) := fun a b => instDecidableEqSum a b
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
  dsimp only [propositionTwoExceptionalPlaces]
  change (∑ w ∈
      (finiteExtensionPrincipalDivisor K₀ L₀ (x ^ m)).support ∪
        (finiteExtensionPrincipalDivisor K₀ L₀ (y ^ n)).support,
      finiteExtensionPlaceDegree K₀ L₀ w) ≤
    2 * (MvPolynomial.degreeOf 0 f + MvPolynomial.degreeOf 1 f)
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
