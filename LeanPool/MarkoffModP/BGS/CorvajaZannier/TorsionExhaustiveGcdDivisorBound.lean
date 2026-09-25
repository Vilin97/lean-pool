/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionGcdDivisorBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveRatFuncModel
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalizationOrder
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Torsion points and the exhaustive gcd divisor

The affine normalization used in `TorsionGcdDivisorBound` need not be finite
over the polynomial ring defining the selected `K(X)`-model.  This file
bridges that mismatch without assuming an algebra map between the two
normalizations.  A valuation subring dominating the affine local ring of a
torsion point determines a height-one prime in the finite integral closure of
`K[X]`.  Distinct affine points determine distinct valuation subrings, hence
distinct finite places.  Both powered coordinate functions have positive
order there.

Consequently rational torsion points inject into the finite part of the
exhaustive place type.  Each selected place contributes at least one to the
degree-weighted positive gcd divisor used by the global Wronskian argument.
-/

@[expose] public section

open IsDedekindDomain
open Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

section DominatingValuationSubring

variable {A L : Type*} [CommRing A] [IsDomain A] [Field L]
  [Algebra A L] [IsFractionRing A L]

/-- The fraction-field embedding, with codomain restricted to its range. -/
noncomputable def fractionEmbeddingRangeEquiv :
    A ≃+* (algebraMap A L).range :=
  RingEquiv.ofBijective (algebraMap A L).rangeRestrict
    ⟨fun x y hxy => IsFractionRing.injective A L (congrArg Subtype.val hxy),
      fun y => by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The image of a maximal ideal inside the embedded copy of `A` in `L`. -/
noncomputable def maximalIdealInFractionEmbeddingRange
    (m : MaximalSpectrum A) : Ideal (algebraMap A L).range :=
  m.asIdeal.map (fractionEmbeddingRangeEquiv (A := A) (L := L)).toRingHom

private theorem maximalIdealInFractionEmbeddingRange_ne_top
    (m : MaximalSpectrum A) :
    maximalIdealInFractionEmbeddingRange (A := A) (L := L) m ≠ ⊤ := by
  rw [maximalIdealInFractionEmbeddingRange]
  intro htop
  apply m.isMaximal.ne_top
  let e := fractionEmbeddingRangeEquiv (A := A) (L := L)
  calc
    m.asIdeal = Ideal.comap e.toRingHom
        (Ideal.map e.toRingHom m.asIdeal) := by
      symm
      calc
        Ideal.comap e.toRingHom (Ideal.map e.toRingHom m.asIdeal) =
            m.asIdeal ⊔ Ideal.comap e.toRingHom ⊥ :=
          Ideal.comap_map_of_surjective e.toRingHom e.surjective m.asIdeal
        _ = m.asIdeal := by
          have hker : Ideal.comap e.toRingHom ⊥ = ⊥ :=
            (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
          rw [hker, sup_eq_left]
          exact bot_le
    _ = Ideal.comap e.toRingHom ⊤ := by rw [htop]
    _ = ⊤ := Ideal.comap_top

/-- A valuation subring of the fraction field dominating the affine local
ring at `m`. -/
noncomputable def dominatingValuationSubring (m : MaximalSpectrum A) :
    ValuationSubring L :=
  Classical.choose (Ideal.image_subset_nonunits_valuationSubring
    (maximalIdealInFractionEmbeddingRange (A := A) (L := L) m)
    (by exact maximalIdealInFractionEmbeddingRange_ne_top m))

theorem range_le_dominatingValuationSubring (m : MaximalSpectrum A) :
    (algebraMap A L).range ≤
      (dominatingValuationSubring (A := A) (L := L) m).toSubring :=
  (Classical.choose_spec (Ideal.image_subset_nonunits_valuationSubring
    (maximalIdealInFractionEmbeddingRange (A := A) (L := L) m)
    (by exact maximalIdealInFractionEmbeddingRange_ne_top m))).1

theorem algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
    (m : MaximalSpectrum A) (r : A) (hr : r ∈ m.asIdeal) :
    algebraMap A L r ∈
      (dominatingValuationSubring (A := A) (L := L) m).nonunits := by
  let e := fractionEmbeddingRangeEquiv (A := A) (L := L)
  have himage : e r ∈
      maximalIdealInFractionEmbeddingRange (A := A) (L := L) m := by
    exact Ideal.mem_map_of_mem e.toRingHom hr
  have hnonunits :=
    (Classical.choose_spec (Ideal.image_subset_nonunits_valuationSubring
      (maximalIdealInFractionEmbeddingRange (A := A) (L := L) m)
      (by exact maximalIdealInFractionEmbeddingRange_ne_top m))).2
  apply hnonunits
  refine ⟨e r, himage, ?_⟩
  rfl

/-- The affine ring map into its dominating valuation subring. -/
noncomputable def coordinateRingToDominatingValuationSubring
    (m : MaximalSpectrum A) :
    A →+* dominatingValuationSubring (A := A) (L := L) m :=
  (Subring.inclusion (range_le_dominatingValuationSubring m)).comp
    (algebraMap A L).rangeRestrict

theorem pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
    (m : MaximalSpectrum A) :
    m.asIdeal = Ideal.comap (coordinateRingToDominatingValuationSubring m)
      (IsLocalRing.maximalIdeal
        (dominatingValuationSubring (A := A) (L := L) m)) := by
  apply m.isMaximal.eq_of_le
  · intro htop
    have hmaxTop : IsLocalRing.maximalIdeal
        (dominatingValuationSubring (A := A) (L := L) m) = ⊤ :=
      Ideal.comap_eq_top_iff.mp htop
    exact (IsLocalRing.maximalIdeal.isMaximal
      (dominatingValuationSubring (A := A) (L := L) m)).ne_top hmaxTop
  · intro r hr
    have hnonunits :=
      algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
        (A := A) (L := L) m r hr
    exact ValuationSubring.coe_mem_nonunits_iff.mp hnonunits

/-- Equality of the chosen dominating valuation subrings forces equality of
the affine centers. -/
theorem pointIdeal_eq_of_dominatingValuationSubring_eq
    {m n : MaximalSpectrum A}
    (h : dominatingValuationSubring (A := A) (L := L) m =
      dominatingValuationSubring (A := A) (L := L) n) :
    m.asIdeal = n.asIdeal := by
  apply le_antisymm
  · intro r hr
    rw [pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
      (A := A) (L := L) n]
    have hnonunits :=
      algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
        (A := A) (L := L) m r hr
    rw [h] at hnonunits
    exact ValuationSubring.coe_mem_nonunits_iff.mp hnonunits
  · intro r hr
    rw [pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
      (A := A) (L := L) m]
    have hnonunits :=
      algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
        (A := A) (L := L) n r hr
    rw [← h] at hnonunits
    exact ValuationSubring.coe_mem_nonunits_iff.mp hnonunits

section IntegralClosure

variable {P : Type*} [CommRing P] [Algebra P L]

theorem integralClosure_le_dominatingValuationSubring
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range) :
    (integralClosure P L).toSubring ≤
      (dominatingValuationSubring (A := A) (L := L) m).toSubring := by
  let V := dominatingValuationSubring (A := A) (L := L) m
  let : IsIntegrallyClosedIn V.toSubring L :=
    inferInstanceAs (IsIntegrallyClosedIn V L)
  rw [Subring.integralClosure_le_iff]
  intro p
  exact range_le_dominatingValuationSubring m (hbase p)

/-- The finite integral closure maps into the valuation subring because the
selected polynomial base is already contained in the affine ring. -/
noncomputable def integralClosureToDominatingValuationSubring
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range) :
    integralClosure P L →+*
      dominatingValuationSubring (A := A) (L := L) m :=
  Subring.inclusion (integralClosure_le_dominatingValuationSubring m hbase)

/-- The center of the dominating valuation on the finite integral closure. -/
noncomputable def dominatingIntegralClosurePrime
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range) :
    Ideal (integralClosure P L) :=
  Ideal.comap (integralClosureToDominatingValuationSubring m hbase)
    (IsLocalRing.maximalIdeal
      (dominatingValuationSubring (A := A) (L := L) m))

theorem dominatingIntegralClosurePrime_isPrime
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range) :
    (dominatingIntegralClosurePrime m hbase).IsPrime := by
  exact Ideal.comap_isPrime _ _

variable [IsDedekindDomain (integralClosure P L)]
  [IsFractionRing (integralClosure P L) L]

/-- A nonzero center in the finite integral closure, regarded as a finite
place. -/
noncomputable def dominatingIntegralClosurePlace
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (hne : dominatingIntegralClosurePrime m hbase ≠ ⊥) :
    HeightOneSpectrum (integralClosure P L) :=
  ⟨dominatingIntegralClosurePrime m hbase,
    dominatingIntegralClosurePrime_isPrime m hbase, hne⟩

theorem valuationSubringAt_dominatingIntegralClosurePlace_le
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (hne : dominatingIntegralClosurePrime m hbase ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L
      (dominatingIntegralClosurePlace m hbase hne) ≤
        dominatingValuationSubring (A := A) (L := L) m := by
  let V := dominatingValuationSubring (A := A) (L := L) m
  let q := dominatingIntegralClosurePlace m hbase hne
  let φ : integralClosure P L →+* V :=
    integralClosureToDominatingValuationSubring m hbase
  rintro x ⟨a, s, hs, rfl⟩
  have hsNotMem : s ∉ q.asIdeal := hs
  have hsUnit : IsUnit (φ s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact hsNotMem
  obtain ⟨u, hu⟩ := hsUnit
  let t : V := φ a * ↑(u⁻¹)
  have ht : algebraMap (integralClosure P L) L a *
      (algebraMap (integralClosure P L) L s)⁻¹ = (t : L) := by
    dsimp only [t]
    have hφa : ((φ a : V) : L) =
        algebraMap (integralClosure P L) L a := rfl
    have hφs : ((φ s : V) : L) =
        algebraMap (integralClosure P L) L s := rfl
    rw [← hφa, ← hφs, ← hu]
    change ((φ a : V) : L) * ((((u : V) : L))⁻¹) =
      ((φ a : V) : L) * (((↑(u⁻¹) : V) : L))
    congr 1
    exact (map_units_inv V.toSubring.subtype u).symm
  rw [ht]
  exact t.property

theorem valuationSubringAt_dominatingIntegralClosurePlace_eq
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (hne : dominatingIntegralClosurePrime m hbase ≠ ⊥)
    (hV : dominatingValuationSubring (A := A) (L := L) m ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L
      (dominatingIntegralClosurePlace m hbase hne) =
        dominatingValuationSubring (A := A) (L := L) m := by
  exact ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAt_dominatingIntegralClosurePlace_le m hbase hne) hV

theorem dominatingIntegralClosurePlace_valuation_isEquiv
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (hne : dominatingIntegralClosurePrime m hbase ≠ ⊥)
    (hV : dominatingValuationSubring (A := A) (L := L) m ≠ ⊤) :
    ((dominatingIntegralClosurePlace m hbase hne).valuation L).IsEquiv
      (dominatingValuationSubring (A := A) (L := L) m).valuation := by
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ValuationSubring.valuationSubring_valuation]
  exact valuationSubringAt_dominatingIntegralClosurePlace_eq m hbase hne hV

theorem finitePlaceOrder_dominatingIntegralClosurePlace_pos_of_mem
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (hne : dominatingIntegralClosurePrime m hbase ≠ ⊥)
    (hV : dominatingValuationSubring (A := A) (L := L) m ≠ ⊤)
    (r : A) (hr : r ∈ m.asIdeal) (hr0 : algebraMap A L r ≠ 0) :
    0 < finitePlaceOrder (dominatingIntegralClosurePlace m hbase hne)
      (algebraMap A L r) := by
  have hnonunits :=
    algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
      (A := A) (L := L) m r hr
  have hVlt :
      (dominatingValuationSubring (A := A) (L := L) m).valuation
        (algebraMap A L r) < 1 := hnonunits
  have hequiv := dominatingIntegralClosurePlace_valuation_isEquiv
    m hbase hne hV
  have hqlt :
      (dominatingIntegralClosurePlace m hbase hne).valuation L
        (algebraMap A L r) < 1 := hequiv.lt_one_iff_lt_one.mpr hVlt
  have horder := valuation_eq_exp_neg_finitePlaceOrder
    (dominatingIntegralClosurePlace m hbase hne) (algebraMap A L r) hr0
  rw [horder, ← exp_zero, exp_lt_exp] at hqlt
  omega

/-- A nonzero integral element at a maximal ideal gives a centered finite place
where both prescribed elements have positive order. -/
theorem exists_integralClosurePlace_orders_positive
    (m : MaximalSpectrum A)
    (hbase : ∀ p : P, algebraMap P L p ∈ (algebraMap A L).range)
    (r s : A) (hr : r ∈ m.asIdeal) (hs : s ∈ m.asIdeal)
    (hr0 : algebraMap A L r ≠ 0) (hs0 : algebraMap A L s ≠ 0)
    (b : integralClosure P L) (hb : algebraMap (integralClosure P L) L b =
      algebraMap A L r) :
    ∃ q : HeightOneSpectrum (integralClosure P L),
      HeightOneSpectrum.valuationSubringAtPrime L q =
        dominatingValuationSubring (A := A) (L := L) m ∧
      0 < finitePlaceOrder q (algebraMap A L r) ∧
      0 < finitePlaceOrder q (algebraMap A L s) := by
  let V := dominatingValuationSubring (A := A) (L := L) m
  have hnonunits : algebraMap A L r ∈ V.nonunits :=
    algebraMap_mem_dominatingValuationSubring_nonunits_of_mem m r hr
  have hV : V ≠ ⊤ := by
    intro htop
    exact ((ValuationSubring.eq_top_iff V).mp htop)
      ((Valuation.isNontrivial_iff_exists_lt_one V.valuation).2 ⟨_, hr0, hnonunits⟩)
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hr0
    rw [← hb, hzero, map_zero]
  have hbMem : b ∈ dominatingIntegralClosurePrime m hbase := by
    change integralClosureToDominatingValuationSubring m hbase b ∈ IsLocalRing.maximalIdeal V
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    change algebraMap (integralClosure P L) L b ∈ V.nonunits
    rwa [hb]
  have hqne : dominatingIntegralClosurePrime m hbase ≠ ⊥ := by
    intro hbot
    apply hb0
    simpa only [hbot, Ideal.mem_bot] using hbMem
  exact ⟨dominatingIntegralClosurePlace m hbase hqne,
    valuationSubringAt_dominatingIntegralClosurePlace_eq m hbase hqne hV,
    finitePlaceOrder_dominatingIntegralClosurePlace_pos_of_mem m hbase hqne hV r hr hr0,
    finitePlaceOrder_dominatingIntegralClosurePlace_pos_of_mem m hbase hqne hV s hs hs0⟩

end IntegralClosure

end DominatingValuationSubring

section FiniteExtensionGcdDivisor

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) exhaustiveGcdPolynomialAlgebra :
    Algebra (Polynomial K) L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap (Polynomial K) (RatFunc K)))

local instance exhaustiveGcdPolynomialScalarTower :
    IsScalarTower (Polynomial K) (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance exhaustiveGcdFiniteIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  integralClosure.isDedekindDomain (Polynomial K) (RatFunc K) L

local instance exhaustiveGcdFiniteIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) L

local instance exhaustiveGcdFiniteIntegralClosureModuleFinite :
    Module.Finite (Polynomial K) (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite (Polynomial K)
    (RatFuncFiniteIntegralClosure K L)

/-- Common finite support of the two principal divisors on the exhaustive
place type. -/
noncomputable def finiteExtensionGcdSupport (x y : L) :
    Finset (FiniteExtensionPlace K L) := by
  classical
  exact (finiteExtensionPrincipalDivisor K L x).support ∪
    (finiteExtensionPrincipalDivisor K L y).support

/-- Positive local gcd multiplicity of two nonzero rational functions. -/
def finiteExtensionGcdMultiplicity (x y : L)
    (v : FiniteExtensionPlace K L) : ℕ :=
  Int.toNat (min
    (finiteExtensionPrincipalDivisor K L x v)
    (finiteExtensionPrincipalDivisor K L y v))

/-- Degree of the positive gcd divisor on the exhaustive place type. -/
def finiteExtensionGcdWeightedDegree (x y : L) : ℕ :=
  ∑ v ∈ finiteExtensionGcdSupport K L x y,
    finiteExtensionGcdMultiplicity K L x y v *
      finiteExtensionPlaceDegree K L v

/-- On a finite place, the exhaustive principal-divisor coefficient is the
normalized order computed directly in `L`. -/
theorem finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder
    (x : L) (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inl q) =
      finitePlaceOrder q x := by
  rw [finiteExtensionPrincipalDivisor_inl]
  have h := fractionRingAlgEquiv_finitePlaceOrder_eq
    (L := L) q ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)
  simpa [ratFuncFiniteIntegralClosureFractionRingEquiv] using h.symm

theorem finiteExtensionPlaceDegree_inl_pos
    (q : FiniteExtensionFinitePlace K L) :
    0 < finiteExtensionPlaceDegree K L (.inl q) := by
  rw [finiteExtensionPlaceDegree]
  apply Nat.mul_pos
  · exact Ideal.inertiaDeg_pos q.asIdeal (Polynomial K)
  · exact (finitePlaceNormalizedPrime
      (HeightOneSpectrum.under (Polynomial K) q)).property.1.irreducible.natDegree_pos

theorem inl_mem_finiteExtensionGcdSupport_of_orders_positive
    (x y : L) (q : FiniteExtensionFinitePlace K L)
    (hxpos : 0 < finitePlaceOrder q x) :
    (.inl q : FiniteExtensionPlace K L) ∈
      finiteExtensionGcdSupport K L x y := by
  classical
  rw [finiteExtensionGcdSupport]
  apply Finset.mem_union_left
  rw [Finsupp.mem_support_iff,
    finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder K L x q]
  omega

theorem one_le_finiteExtensionGcdMultiplicity_mul_degree_inl_of_orders_positive
    (x y : L) (q : FiniteExtensionFinitePlace K L)
    (hxpos : 0 < finitePlaceOrder q x)
    (hypos : 0 < finitePlaceOrder q y) :
    1 ≤ finiteExtensionGcdMultiplicity K L x y (.inl q) *
      finiteExtensionPlaceDegree K L (.inl q) := by
  have hxD : 0 < finiteExtensionPrincipalDivisor K L x (.inl q) := by
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder K L x q]
    exact hxpos
  have hyD : 0 < finiteExtensionPrincipalDivisor K L y (.inl q) := by
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder K L y q]
    exact hypos
  have hmult : 0 < finiteExtensionGcdMultiplicity K L x y (.inl q) := by
    unfold finiteExtensionGcdMultiplicity
    omega
  exact Nat.mul_pos hmult (finiteExtensionPlaceDegree_inl_pos K L q)

end FiniteExtensionGcdDivisor

section PlaneCurveExhaustiveFinitePlaces

variable {K : Type*} [Field K]
variable {f : MvPolynomial (Fin 2) K}

/-- The selected polynomial parameter belongs to the affine coordinate ring
inside the curve's function field. -/
theorem polynomial_algebraMap_mem_planeCurveCoordinateRing_range
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (P : Polynomial K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    algebraMap (Polynomial K) (PlaneCurveFunctionField f) P ∈
      (algebraMap (PlaneCurveCoordinateRing f)
        (PlaneCurveFunctionField f)).range := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  refine ⟨planeCurveQuotientMap f (polynomialInFirstCoordinate P), ?_⟩
  change algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
      (planeCurveQuotientMap f (polynomialInFirstCoordinate P)) =
    algebraMap (Polynomial K) (PlaneCurveFunctionField f) P
  rw [show algebraMap (Polynomial K) (PlaneCurveFunctionField f) P =
      algebraMap (RatFunc K) (PlaneCurveFunctionField f)
        (algebraMap (Polynomial K) (RatFunc K) P) by rfl]
  change ((algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)).comp (planeCurveQuotientMap f))
      (polynomialInFirstCoordinate P) = _
  rw [← eval₂_planeCurveFunction f]
  have hcoordinates : planeCurveFunction f =
      ![planeCurveFunction f 0, planeCurveFunction f 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoordinates]
  change MvPolynomial.eval₂ (algebraMap K (PlaneCurveFunctionField f))
      ![planeCurveFunction f 0, planeCurveFunction f 1]
      (polynomialInFirstCoordinate P) = _
  rw [eval₂_polynomialInFirstCoordinate]
  have hcomp := congrArg
    (fun h : Polynomial K →+* PlaneCurveFunctionField f => h P)
    (ratFuncSpecialization_comp_polynomial_algebraMap
      (planeCurveFunction f 0) hx)
  exact hcomp.symm

private theorem map_power_sub_one {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (x : R) (y : S) (h : φ x = y) (n : ℕ) :
    φ (x ^ n - 1) = y ^ n - 1 := by
  rw [map_sub, map_pow, map_one, h]

variable [Fintype K] [DecidableEq K]

/-- Every rational torsion point produces an actual finite place of the
`K[X]` integral-closure model at which both powered coordinate functions have
positive order.  The valuation-subring equality records its affine center and
will make the choice injective. -/
theorem exists_torsionPoint_exhaustiveFinitePlace_orders_positive
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : IsDedekindDomain
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)) :=
      integralClosure.isDedekindDomain (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f)
    let : IsFractionRing
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f))
        (PlaneCurveFunctionField f) :=
      integralClosure.isFractionRing_of_finite_extension (RatFunc K)
        (PlaneCurveFunctionField f)
    ∃ q : HeightOneSpectrum
        (integralClosure (Polynomial K) (PlaneCurveFunctionField f)),
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f) q =
        dominatingValuationSubring
          (torsionPointMaximalIdeal f firstOrder secondOrder z) ∧
        0 < finitePlaceOrder q
          (planeCurveFunction f 0 ^ firstOrder - 1) ∧
        0 < finitePlaceOrder q
          (planeCurveFunction f 1 ^ secondOrder - 1) := by
  intro domain hx ratFuncAlgebra polynomialAlgebra scalarTower finiteDimension separable
    dedekind fraction
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  let B := integralClosure (Polynomial K) E
  let m := torsionPointMaximalIdeal f firstOrder secondOrder z
  have hbase : ∀ P : Polynomial K,
      algebraMap (Polynomial K) E P ∈ (algebraMap A E).range :=
    polynomial_algebraMap_mem_planeCurveCoordinateRing_range hf hpartialSecond
  let rfirst : A := planeCurveCoordinate f 0 ^ firstOrder - 1
  let rsecond : A := planeCurveCoordinate f 1 ^ secondOrder - 1
  let Pfirst : Polynomial K := Polynomial.X ^ firstOrder - 1
  let bfirst : B := algebraMap (Polynomial K) B Pfirst
  have hrfirst : rfirst ∈ m.asIdeal :=
    first_torsionFunction_mem_torsionPointMaximalIdeal
      f firstOrder secondOrder z
  have hrsecond : rsecond ∈ m.asIdeal :=
    second_torsionFunction_mem_torsionPointMaximalIdeal
      f firstOrder secondOrder z
  have hrfirstMap : algebraMap A E rfirst =
      planeCurveFunction f 0 ^ firstOrder - 1 := by
    simp only [rfirst, map_sub, map_pow, map_one]
    rfl
  have hrsecondMap : algebraMap A E rsecond =
      planeCurveFunction f 1 ^ secondOrder - 1 := by
    simp only [rsecond, map_sub, map_pow, map_one]
    rfl
  have hPfirstMap : algebraMap (Polynomial K) E Pfirst =
      planeCurveFunction f 0 ^ firstOrder - 1 := by
    exact map_power_sub_one (algebraMap (Polynomial K) E) Polynomial.X
      (planeCurveFunction f 0) (planeCurveFirstCoordinateRatFuncAlgebra_X f hx) firstOrder
  have hbfirstMap : algebraMap B E bfirst =
      planeCurveFunction f 0 ^ firstOrder - 1 := by
    rw [show algebraMap B E bfirst =
      algebraMap (Polynomial K) E Pfirst by
        exact IsScalarTower.algebraMap_apply (Polynomial K) B E Pfirst]
    exact hPfirstMap
  have hrfirstMap0 : algebraMap A E rfirst ≠ 0 := by
    rw [hrfirstMap]
    exact hfirstNonzero
  have hrsecondMap0 : algebraMap A E rsecond ≠ 0 := by
    rw [hrsecondMap]
    exact hsecondNonzero
  obtain ⟨q, hq, hfirst, hsecond⟩ := exists_integralClosurePlace_orders_positive
    m hbase rfirst rsecond hrfirst hrsecond hrfirstMap0 hrsecondMap0 bfirst
    (hbfirstMap.trans hrfirstMap.symm)
  exact ⟨q, hq, hrfirstMap ▸ hfirst, hrsecondMap ▸ hsecond⟩

/-- The finite place in the exhaustive `K[X]`-integral-closure model selected
above a rational torsion point. -/
def torsionPointExhaustiveFinitePlace
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    FiniteExtensionFinitePlace K (PlaneCurveFunctionField f) := by
  exact Classical.choose
    (exists_torsionPoint_exhaustiveFinitePlace_orders_positive
      hf hpartialSecond firstOrder secondOrder
      hfirstNonzero hsecondNonzero z)

/-- The selected exhaustive finite place is centered at the given affine
torsion point, and both powered coordinate functions have positive order
there. -/
theorem torsionPointExhaustiveFinitePlace_spec
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (PlaneCurveFunctionField f)
        (torsionPointExhaustiveFinitePlace hf hpartialSecond
          firstOrder secondOrder hfirstNonzero hsecondNonzero z) =
      dominatingValuationSubring
        (torsionPointMaximalIdeal f firstOrder secondOrder z) ∧
      0 < finitePlaceOrder
        (torsionPointExhaustiveFinitePlace hf hpartialSecond
          firstOrder secondOrder hfirstNonzero hsecondNonzero z)
        (planeCurveFunction f 0 ^ firstOrder - 1) ∧
      0 < finitePlaceOrder
        (torsionPointExhaustiveFinitePlace hf hpartialSecond
          firstOrder secondOrder hfirstNonzero hsecondNonzero z)
        (planeCurveFunction f 1 ^ secondOrder - 1) := by
  exact Classical.choose_spec
    (exists_torsionPoint_exhaustiveFinitePlace_orders_positive
      hf hpartialSecond firstOrder secondOrder
      hfirstNonzero hsecondNonzero z)

/-- Distinct rational torsion points have distinct selected finite places in
the exhaustive `K[X]`-model. -/
theorem torsionPointExhaustiveFinitePlace_injective
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    Function.Injective
      (torsionPointExhaustiveFinitePlace hf hpartialSecond
        firstOrder secondOrder hfirstNonzero hsecondNonzero) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change Function.Injective
    (torsionPointExhaustiveFinitePlace hf hpartialSecond
      firstOrder secondOrder hfirstNonzero hsecondNonzero)
  intro z w hzw
  apply torsionPointMaximalIdeal_injective f firstOrder secondOrder
  apply MaximalSpectrum.ext
  apply pointIdeal_eq_of_dominatingValuationSubring_eq
    (A := PlaneCurveCoordinateRing f)
    (L := PlaneCurveFunctionField f)
  calc
    dominatingValuationSubring
        (torsionPointMaximalIdeal f firstOrder secondOrder z) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (torsionPointExhaustiveFinitePlace hf hpartialSecond
            firstOrder secondOrder hfirstNonzero hsecondNonzero z) :=
      (torsionPointExhaustiveFinitePlace_spec hf hpartialSecond
        firstOrder secondOrder hfirstNonzero hsecondNonzero z).1.symm
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f)
          (torsionPointExhaustiveFinitePlace hf hpartialSecond
            firstOrder secondOrder hfirstNonzero hsecondNonzero w) := by
      rw [hzw]
    _ = dominatingValuationSubring
        (torsionPointMaximalIdeal f firstOrder secondOrder w) :=
      (torsionPointExhaustiveFinitePlace_spec hf hpartialSecond
        firstOrder secondOrder hfirstNonzero hsecondNonzero w).1

/-- Degree of the positive gcd divisor of the two powered coordinate
functions, taken on the exhaustive finite-and-infinite place model attached to
the first coordinate. -/
noncomputable def planeCurveExhaustiveTorsionGcdWeightedDegree
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ) : ℕ := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : DecidableEq (RatFunc K) := Classical.decEq (RatFunc K)
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  exact finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
    (planeCurveFunction f 0 ^ firstOrder - 1)
    (planeCurveFunction f 1 ^ secondOrder - 1)

/-- Rational torsion points inject into the positive gcd divisor on the
exhaustive place model.  The residue-degree weight of every selected place is
positive, so each point contributes at least one to its weighted degree. -/
theorem torsionPoint_card_le_planeCurveExhaustiveTorsionGcdWeightedDegree
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0) :
    Fintype.card (TorusCurveTorsionPoint f firstOrder secondOrder) ≤
      planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond firstOrder secondOrder := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq (RatFunc K)
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (FiniteExtensionPlace K (PlaneCurveFunctionField f)) :=
    Classical.decEq _
  let x : PlaneCurveFunctionField f :=
    planeCurveFunction f 0 ^ firstOrder - 1
  let y : PlaneCurveFunctionField f :=
    planeCurveFunction f 1 ^ secondOrder - 1
  let finitePlace : TorusCurveTorsionPoint f firstOrder secondOrder →
      FiniteExtensionFinitePlace K (PlaneCurveFunctionField f) :=
    torsionPointExhaustiveFinitePlace hf hpartialSecond
      firstOrder secondOrder hfirstNonzero hsecondNonzero
  let place : TorusCurveTorsionPoint f firstOrder secondOrder →
      FiniteExtensionPlace K (PlaneCurveFunctionField f) :=
    fun z => .inl (finitePlace z)
  have hFinitePlaceInjective : Function.Injective finitePlace :=
    torsionPointExhaustiveFinitePlace_injective hf hpartialSecond
      firstOrder secondOrder hfirstNonzero hsecondNonzero
  have hPlaceInjective : Function.Injective place := by
    intro z w hzw
    apply hFinitePlaceInjective
    exact Sum.inl_injective hzw
  have hImageSubset : Finset.univ.image place ⊆
      finiteExtensionGcdSupport K (PlaneCurveFunctionField f) x y := by
    intro v hv
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hv
    have hz := torsionPointExhaustiveFinitePlace_spec hf hpartialSecond
      firstOrder secondOrder hfirstNonzero hsecondNonzero z
    exact inl_mem_finiteExtensionGcdSupport_of_orders_positive
      K (PlaneCurveFunctionField f) x y (finitePlace z) hz.2.1
  calc
    Fintype.card (TorusCurveTorsionPoint f firstOrder secondOrder) =
        (Finset.univ.image place).card := by
      rw [Finset.card_image_of_injective _ hPlaceInjective,
        Finset.card_univ]
    _ = ∑ v ∈ Finset.univ.image place, 1 := by simp
    _ ≤ ∑ v ∈ Finset.univ.image place,
        finiteExtensionGcdMultiplicity K (PlaneCurveFunctionField f) x y v *
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hv
      have hz := torsionPointExhaustiveFinitePlace_spec hf hpartialSecond
        firstOrder secondOrder hfirstNonzero hsecondNonzero z
      exact
        one_le_finiteExtensionGcdMultiplicity_mul_degree_inl_of_orders_positive
          K (PlaneCurveFunctionField f) x y (finitePlace z) hz.2.1 hz.2.2
    _ ≤ ∑ v ∈ finiteExtensionGcdSupport K (PlaneCurveFunctionField f) x y,
        finiteExtensionGcdMultiplicity K (PlaneCurveFunctionField f) x y v *
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hImageSubset (by omega)
    _ = planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond firstOrder secondOrder := by
      rfl

end PlaneCurveExhaustiveFinitePlaces
