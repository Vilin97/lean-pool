/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStrictLevels
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLeadingTermCancellation
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationOrder
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionResidueSurjectivity
import Mathlib.FieldTheory.Finiteness

/-!
# Leading coefficients at a single place

Compare residue-field degrees and lift constant residues through the local rings of finite and
infinite places.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

private noncomputable def residueFieldAlgEquivOfIdealEqOver
    {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[C] J.ResidueField := by
  subst J
  exact AlgEquiv.refl

private theorem constantResidue_surjective_of_ideal_eq
    {C A : Type*} [CommRing C] [CommRing A] [Algebra C A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J)
    (hJ : Function.Surjective (algebraMap C J.ResidueField)) :
    Function.Surjective (algebraMap C I.ResidueField) := by
  let e := residueFieldAlgEquivOfIdealEqOver (C := C) h
  intro z
  obtain ⟨c, hc⟩ := hJ (e z)
  refine ⟨c, e.injective ?_⟩
  simpa [e] using hc

@[reducible] private noncomputable def canonicalFractionRingAlgebra
    (A : Type*) [CommRing A] [IsDomain A] :
    Algebra A (FractionRing A) := inferInstance

section LocalizationResidue

variable {C R S : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [Algebra C R]
  [CommRing S] [Algebra R S]
  [Algebra C S] [IsScalarTower C R S]

/-- Surjectivity of constants onto a height-one residue field is preserved
when the Dedekind domain is localized at that place. -/
theorem localizationAtPrime_constantResidue_surjective
    (q : HeightOneSpectrum R) [IsLocalization q.asIdeal.primeCompl S]
    [IsLocalRing S]
    (hresidue : Function.Surjective
      (algebraMap C q.asIdeal.ResidueField)) :
    Function.Surjective
      (algebraMap C
        (IsLocalRing.maximalIdeal S).ResidueField) := by
  intro z
  let m := IsLocalRing.maximalIdeal S
  let : q.asIdeal.IsMaximal := q.isMaximal
  let : m.IsMaximal := by
    simpa [m] using (IsLocalRing.maximalIdeal.isMaximal S)
  obtain ⟨s, hs⟩ := m.algebraMap_residueField_surjective z
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal S
  let rbar : R ⧸ q.asIdeal := e.symm (Ideal.Quotient.mk m s)
  obtain ⟨c, hc⟩ := hresidue
    (algebraMap (R ⧸ q.asIdeal) q.asIdeal.ResidueField rbar)
  refine ⟨c, ?_⟩
  change algebraMap C m.ResidueField c = z
  rw [← hs]
  rw [IsScalarTower.algebraMap_apply C S m.ResidueField]
  simp only [IsScalarTower.algebraMap_apply S (S ⧸ m) m.ResidueField]
  congr 1
  have hq : algebraMap R (R ⧸ q.asIdeal) (algebraMap C R c) = rbar := by
    apply q.asIdeal.injective_algebraMap_quotient_residueField
    simpa only [IsScalarTower.algebraMap_apply C R
      q.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply R (R ⧸ q.asIdeal)
        q.asIdeal.ResidueField] using hc
  calc
    algebraMap S (S ⧸ m) (algebraMap C S c) =
        e (algebraMap R (R ⧸ q.asIdeal) (algebraMap C R c)) := by
      rw [IsScalarTower.algebraMap_apply C R S]
      change Ideal.Quotient.mk m
          (algebraMap R S (algebraMap C R c)) =
        e (Ideal.Quotient.mk q.asIdeal (algebraMap C R c))
      simpa [e, m] using
        (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk
          q.asIdeal S (algebraMap C R c)).symm
    _ = e rbar := by rw [hq]
    _ = algebraMap S (S ⧸ m) s := by simp [rbar, m]

end LocalizationResidue

section DegreeOneResidue

attribute [local instance high] Module.Free.of_divisionRing

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) onePointPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance onePointPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance onePointFiniteConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance onePointFiniteConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance onePointInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance onePointInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance onePointInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance onePointInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def onePointResidueFieldAlgEquivOfIdealEq
    {I J : Ideal K[X]} [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[K] J.ResidueField := by
  subst J
  exact AlgEquiv.refl

omit [Fintype K] [DecidableEq (RatFunc K)] in
/-- The degree of a rational-function finite place is the dimension of its
residue field over the constant field. -/
theorem ratFuncFinitePlaceDegree_eq_finrank_residueField
    (p : HeightOneSpectrum K[X]) :
    ratFuncFinitePlaceDegree p =
      Module.finrank K p.asIdeal.ResidueField := by
  let r := finitePlaceNormalizedPrime p
  have hp : normalizedPrimeFinitePlace (K := K) r = p :=
    normalizedPrimeFinitePlace_finitePlaceNormalizedPrime p
  have hpIdeal : p.asIdeal = Ideal.span {(r : K[X])} := by
    rw [← show (normalizedPrimeFinitePlace (K := K) r).asIdeal =
      p.asIdeal by exact congrArg HeightOneSpectrum.asIdeal hp]
    rfl
  let : (Ideal.span {(r : K[X])}).IsPrime :=
    (normalizedPrimeFinitePlace (K := K) r).isPrime
  let : (Ideal.span {(r : K[X])}).IsMaximal :=
    (inferInstance : (Ideal.span {(r : K[X])}).IsPrime).isMaximal (by
      simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
        r.property.1.ne_zero)
  let ep := onePointResidueFieldAlgEquivOfIdealEq (K := K) hpIdeal
  let e : (K[X] ⧸ Ideal.span {(r : K[X])}) ≃ₐ[K]
      (Ideal.span {(r : K[X])}).ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K
        (K[X] ⧸ Ideal.span {(r : K[X])})
        (Ideal.span {(r : K[X])}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  symm
  calc
    Module.finrank K p.asIdeal.ResidueField =
        Module.finrank K (Ideal.span {(r : K[X])}).ResidueField :=
      ep.toLinearEquiv.finrank_eq
    _ =
        Module.finrank K (K[X] ⧸ Ideal.span {(r : K[X])}) :=
      e.toLinearEquiv.finrank_eq.symm
    _ = (r : K[X]).natDegree :=
      (AdjoinRoot.powerBasis r.property.1.ne_zero).finrank
    _ = ratFuncFinitePlaceDegree p := by
      rw [ratFuncFinitePlaceDegree]

omit [Fintype K] in
/-- At a finite extension place, the exhaustive place degree is exactly the
constant-field dimension of the residue field. -/
theorem finiteExtensionFinitePlace_degree_eq_finrank_residueField
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
  rw [ratFuncFinitePlaceDegree_eq_finrank_residueField K p]
  rw [mul_comm, Module.finrank_mul_finrank]

omit [Fintype K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- At an infinity extension place, the exhaustive place degree is exactly
the constant-field dimension of the residue field. -/
theorem finiteExtensionInfinityPlace_degree_eq_finrank_residueField
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
  have hbase : Module.finrank K p.ResidueField = 1 := by
    simpa [p] using
      (ratFuncInfinityPlaceResidueEquiv K).toLinearEquiv.finrank_eq
  calc
    Module.finrank p.ResidueField P.1.ResidueField =
        1 * Module.finrank p.ResidueField P.1.ResidueField := by simp
    _ = Module.finrank K p.ResidueField *
        Module.finrank p.ResidueField P.1.ResidueField := by rw [hbase]
    _ = Module.finrank K P.1.ResidueField :=
      Module.finrank_mul_finrank K p.ResidueField P.1.ResidueField

omit [Fintype K] in
/-- Degree one forces constants to fill the residue field at a finite
extension place. -/
theorem finiteExtensionFinitePlace_constantResidue_surjective_of_degree_one
    (q : FiniteExtensionFinitePlace K L)
    (hq : finiteExtensionPlaceDegree K L (.inl q) = 1) :
    Function.Surjective (algebraMap K q.asIdeal.ResidueField) := by
  have hfinrank : Module.finrank K q.asIdeal.ResidueField = 1 := by
    rw [← finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q]
    exact hq
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank).2

omit [Fintype K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Degree one forces constants to fill the residue field at an infinity
extension place. -/
theorem finiteExtensionInfinityPlace_constantResidue_surjective_of_degree_one
    (P : FiniteExtensionInfinityPlace K L)
    (hP : finiteExtensionPlaceDegree K L (.inr P) = 1) :
    Function.Surjective (algebraMap K P.1.ResidueField) := by
  have hfinrank : Module.finrank K P.1.ResidueField = 1 := by
    rw [← finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P]
    exact hP
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank).2

end DegreeOneResidue

section GlobalDedekindCancellation

variable {C R L : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [Field L] [Algebra C R] [Algebra R L] [Algebra C L]
  [IsScalarTower C R L] [IsFractionRing R L]

/-- Global height-one cancellation obtained by applying the DVR theorem after
localizing at the chosen Dedekind place. -/
theorem exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt_of_residue
    (q : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C q.asIdeal.ResidueField))
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : finitePlaceOrder q x = finitePlaceOrder q y) :
    ∃ c : C,
      x - algebraMap C L c * y = 0 ∨
        finitePlaceOrder q x <
          finitePlaceOrder q (x - algebraMap C L c * y) := by
  let S := Localization.AtPrime q.asIdeal
  let : Algebra C S :=
    Algebra.ofModule smul_mul_assoc mul_smul_comm
  let : IsScalarTower C R S := inferInstance
  let toField : S →+* L :=
    IsLocalization.lift
      (S := S) (M := q.asIdeal.primeCompl)
      (g := algebraMap R L) fun d =>
        IsLocalization.map_units L
          ⟨d.1, q.asIdeal.primeCompl_le_nonZeroDivisors d.2⟩
  let : Algebra S L := toField.toAlgebra
  let : IsScalarTower R S L := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  let : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      q.asIdeal.primeCompl S L
  let : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R q.ne_bot S
  let : IsScalarTower C S L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    simp only [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply C R L,
      IsScalarTower.algebraMap_apply C R S,
      IsScalarTower.algebraMap_apply R S L]
  let v := IsDiscreteValuationRing.maximalIdeal S
  have hlocalResidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField) := by
    have hvIdeal : v.asIdeal = IsLocalRing.maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal v.isMaximal
    apply constantResidue_surjective_of_ideal_eq hvIdeal
    exact localizationAtPrime_constantResidue_surjective
      (C := C) (R := R) (S := S) q hresidue
  have hlocalOrder : finitePlaceOrder v x = finitePlaceOrder v y := by
    simpa [v, S, localizationAtPrime_finitePlaceOrder_eq q] using horder
  obtain ⟨c, hc⟩ :=
    exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt
      v hlocalResidue x y hx hy hlocalOrder
  refine ⟨c, hc.elim Or.inl (fun hlt => Or.inr ?_)⟩
  simpa [v, S, localizationAtPrime_finitePlaceOrder_eq q] using hlt

end GlobalDedekindCancellation

section FiniteExtensionCancellation


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance onePointCancellationConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance onePointCancellationConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) onePointCancellationPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance onePointCancellationPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance onePointCancellationFiniteConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance onePointCancellationInfinityBaseConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance onePointCancellationInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance onePointCancellationFiniteIsDedekindDomain :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  integralClosure.isDedekindDomain K[X] (RatFunc K) L

local instance onePointCancellationFiniteIsFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) L

local instance onePointCancellationInfinityIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance onePointCancellationInfinityIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) L

local instance onePointCancellationInfinityCanonicalFractionAlgebra :
    Algebra (RatFuncInfinityIntegralClosure K L)
      (FractionRing (RatFuncInfinityIntegralClosure K L)) :=
  canonicalFractionRingAlgebra (RatFuncInfinityIntegralClosure K L)

local instance onePointCancellationInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance onePointCancellationInfinityIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance onePointCancellationFiniteConstantTowerToField :
    IsScalarTower K (RatFuncFiniteIntegralClosure K L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
  rfl

local instance onePointCancellationInfinityConstantTowerToField :
    IsScalarTower K (RatFuncInfinityIntegralClosure K L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
  rfl

omit [Fintype K] in
private theorem finiteExtensionPrincipalDivisor_inr_eq_finitePlaceOrder
    (x : L) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inr P) =
      finitePlaceOrder
        (primeOverHeightOne (ratFuncInfinityPlace K) P) x := by
  rw [finiteExtensionPrincipalDivisor_inr]
  symm
  simpa [ratFuncInfinityIntegralClosureFractionRingEquiv] using
    fractionRingAlgEquiv_finitePlaceOrder_eq
      (R := RatFuncInfinityIntegralClosure K L) (L := L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P)
      ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)

omit [Fintype K] in
/-- At a degree-one exhaustive place, equal-order nonzero functions admit a
strict constant leading-term cancellation. -/
theorem exists_constant_finiteExtensionPlaceOrder_sub_mul_eq_zero_or_lt
    (P : FiniteExtensionPlace K L)
    (hP : finiteExtensionPlaceDegree K L P = 1)
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : finiteExtensionPrincipalDivisor K L x P =
      finiteExtensionPrincipalDivisor K L y P) :
    ∃ c : K,
      x - algebraMap K L c * y = 0 ∨
        finiteExtensionPrincipalDivisor K L x P <
          finiteExtensionPrincipalDivisor K L
            (x - algebraMap K L c * y) P := by
  cases P with
  | inl q =>
      have hresidue :=
        finiteExtensionFinitePlace_constantResidue_surjective_of_degree_one
          K L q hP
      have horder' : finitePlaceOrder q x = finitePlaceOrder q y := by
        simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
          using horder
      obtain ⟨c, hc⟩ :=
        exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt_of_residue
          (C := K) (R := RatFuncFiniteIntegralClosure K L) (L := L)
          q hresidue x y hx hy horder'
      refine ⟨c, hc.imp id ?_⟩
      intro hlt
      simpa only [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
        using hlt
  | inr P =>
      let q := primeOverHeightOne
        (R := RatFuncInfinityIntegers K)
        (S := RatFuncInfinityIntegralClosure K L)
        (ratFuncInfinityPlace K) P
      have hresidue : Function.Surjective
          (algebraMap K q.asIdeal.ResidueField) := by
        change Function.Surjective (algebraMap K P.1.ResidueField)
        exact
          finiteExtensionInfinityPlace_constantResidue_surjective_of_degree_one
            K L P hP
      have horder' : finitePlaceOrder q x = finitePlaceOrder q y := by
        simpa only [q,
          finiteExtensionPrincipalDivisor_inr_eq_finitePlaceOrder]
          using horder
      obtain ⟨c, hc⟩ :=
        exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt_of_residue
          (C := K) (R := RatFuncInfinityIntegralClosure K L) (L := L)
          q hresidue x y hx hy horder'
      refine ⟨c, hc.imp id ?_⟩
      intro hlt
      simpa only [q,
        finiteExtensionPrincipalDivisor_inr_eq_finitePlaceOrder]
        using hlt

/-- At a degree-one place, cancelling the common leading coefficient of two
nonzero sections with exact pole order `n` either gives zero or lowers the
allowed pole order by one. -/
theorem exists_constant_sub_mul_mem_onePointRiemannSpace_pred
    (P : FiniteExtensionPlace K L)
    (hP : finiteExtensionPlaceDegree K L P = 1)
    {n : ℕ} (hn : 0 < n) {x y : L}
    (hx : x ∈ finiteExtensionOnePointRiemannSpace K L P n)
    (hy : y ∈ finiteExtensionOnePointRiemannSpace K L P n)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxOrder : finiteExtensionPrincipalDivisor K L x P = -(n : ℤ))
    (hyOrder : finiteExtensionPrincipalDivisor K L y P = -(n : ℤ)) :
    ∃ c : K,
      x - algebraMap K L c * y = 0 ∨
        x - algebraMap K L c * y ∈
          finiteExtensionOnePointRiemannSpace K L P (n - 1) := by
  have hxyOrder : finiteExtensionPrincipalDivisor K L x P =
      finiteExtensionPrincipalDivisor K L y P :=
    hxOrder.trans hyOrder.symm
  obtain ⟨c, hc⟩ :=
    exists_constant_finiteExtensionPlaceOrder_sub_mul_eq_zero_or_lt
      K L P hP x y hx0 hy0 hxyOrder
  refine ⟨c, hc.elim Or.inl (fun hlt => ?_)⟩
  let z := x - algebraMap K L c * y
  by_cases hz0 : z = 0
  · exact Or.inl (by simpa [z] using hz0)
  · refine Or.inr ?_
    rw [mem_finiteExtensionOnePointRiemannSpace_iff]
    refine Or.inr ⟨hz0, ?_, ?_⟩
    · change -((n - 1 : ℕ) : ℤ) ≤
        finiteExtensionPrincipalDivisor K L z P
      have hzOrder : -(n : ℤ) <
          finiteExtensionPrincipalDivisor K L z P := by
        simpa [z, hxOrder] using hlt
      omega
    · have hcy : algebraMap K L c * y ∈
          finiteExtensionOnePointRiemannSpace K L P n := by
        have hsmul :=
          (finiteExtensionOnePointRiemannSpace K L P n).smul_mem c hy
        simpa only [Algebra.smul_def] using hsmul
      have hzMem : z ∈ finiteExtensionOnePointRiemannSpace K L P n := by
        exact (finiteExtensionOnePointRiemannSpace K L P n).sub_mem hx hcy
      rcases
          (mem_finiteExtensionOnePointRiemannSpace_iff K L P n z).mp hzMem with
        hz | ⟨_, _, hAway⟩
      · exact (hz0 hz).elim
      · exact hAway

/-- If the degree-one one-point filtration grows at level `n + 1`, one new
section is a pivot for the whole quotient.  Its pole order is exactly
`-(n + 1)`, and every section of the larger space becomes a scalar multiple
of it modulo the preceding space. -/
theorem exists_onePointRiemannSpace_pivot_of_lt
    (P : FiniteExtensionPlace K L)
    (hP : finiteExtensionPlaceDegree K L P = 1) (n : ℕ)
    (hstrict : finiteExtensionOnePointRiemannSpace K L P n <
      finiteExtensionOnePointRiemannSpace K L P (n + 1)) :
    ∃ y : L,
      y ∈ finiteExtensionOnePointRiemannSpace K L P (n + 1) ∧
      finiteExtensionPrincipalDivisor K L y P = -((n + 1 : ℕ) : ℤ) ∧
      ∀ x : L,
        x ∈ finiteExtensionOnePointRiemannSpace K L P (n + 1) →
          ∃ c : K,
            x - c • y ∈ finiteExtensionOnePointRiemannSpace K L P n := by
  have hnotle : ¬ finiteExtensionOnePointRiemannSpace K L P (n + 1) ≤
      finiteExtensionOnePointRiemannSpace K L P n :=
    not_le_of_gt hstrict
  have hexists : ∃ y : L,
      y ∈ finiteExtensionOnePointRiemannSpace K L P (n + 1) ∧
      y ∉ finiteExtensionOnePointRiemannSpace K L P n := by
    by_contra h
    apply hnotle
    intro y hy
    by_contra hyNot
    exact h ⟨y, hy, hyNot⟩
  obtain ⟨y, hySucc, hyNot⟩ := hexists
  obtain ⟨hy0, hyOrder⟩ :=
    BGS.HasseWeil.onePointRiemannSpace_order_eq_neg_succ_of_mem_not_mem
      K L P n hySucc hyNot
  refine ⟨y, hySucc, hyOrder, ?_⟩
  intro x hxSucc
  by_cases hxMem : x ∈ finiteExtensionOnePointRiemannSpace K L P n
  · refine ⟨0, ?_⟩
    simpa using hxMem
  · obtain ⟨hx0, hxOrder⟩ :=
      BGS.HasseWeil.onePointRiemannSpace_order_eq_neg_succ_of_mem_not_mem
        K L P n hxSucc hxMem
    obtain ⟨c, hc⟩ :=
      exists_constant_sub_mul_mem_onePointRiemannSpace_pred
        K L P hP (Nat.zero_lt_succ n) hxSucc hySucc hx0 hy0 hxOrder hyOrder
    refine ⟨c, ?_⟩
    rcases hc with hzero | hmem
    · have hzero' : x - c • y = 0 := by
        simpa only [Algebra.smul_def] using hzero
      rw [hzero']
      exact Submodule.zero_mem _
    · simpa only [Algebra.smul_def, Nat.succ_sub_one] using hmem

end FiniteExtensionCancellation

end

end BGS.CorvajaZannier
