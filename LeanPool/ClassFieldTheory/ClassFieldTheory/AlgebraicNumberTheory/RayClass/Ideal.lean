/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Ring.Compact
/-!
# Ideals prime to a ray-class modulus

This file defines the subgroup of fractional ideals prime to a modulus,
connects it with the corresponding finite-idele higher-unit conditions, and
develops the approximation maps used in ray-class ideal constructions.
-/

open scoped NumberField WithZero open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

open scoped Classical in
/-- Fractional ideals having valuation zero at every finite prime in the
support of the modulus. -/
def primeToModulusIdeals (m : Modulus K) :
    Subgroup (FractionalIdealGroup K) where
  carrier := {I | ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0}
  one_mem' v _ := FractionalIdeal.count_one K v
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul,
      FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J),
      hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K v,
      hI v hv, neg_zero]

open scoped Classical in
@[simp]
theorem mem_primeToModulusIdeals_iff
    (m : Modulus K) (I : FractionalIdealGroup K) :
    I ∈ primeToModulusIdeals m ↔
      ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count K v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
  Iff.rfl

open scoped Classical in
/-- A finite prime outside the support of `m`, regarded as an element of
the group of fractional ideals prime to `m`. -/
def primeToModulusIdeal
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    primeToModulusIdeals m :=
  ⟨FractionalIdealGroup.prime v, by
    intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      FractionalIdeal.count K w
          (v.asIdeal :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        0
    exact
      FractionalIdeal.count_maximal_coprime
        K w hwv.symm⟩

open scoped Classical in
/-- Coercing a prime outside the modulus support recovers its prime
fractional ideal. -/
@[simp]
theorem primeToModulusIdeal_coe
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    (primeToModulusIdeal m v hv :
        FractionalIdealGroup K) =
      FractionalIdealGroup.prime v :=
  rfl

open scoped Classical in
/-- Finite ideles satisfying the higher-unit condition at every prime in
the support of the modulus. -/
def finitePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∈ m.finitePart.support →
    a v ∈ localHigherUnitGroup v (m.finitePart v)}
  one_mem' v _ := (localHigherUnitGroup v (m.finitePart v)).one_mem
  mul_mem' ha hb v hv :=
    (localHigherUnitGroup v (m.finitePart v)).mul_mem (ha v hv) (hb v hv)
  inv_mem' ha v hv :=
    (localHigherUnitGroup v (m.finitePart v)).inv_mem (ha v hv)

open scoped Classical in
/-- Ideles satisfying the infinite positivity and finite higher-unit
conditions of a modulus. -/
def idelePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup K) :=
  m.infiniteCongruenceSubgroup.prod
    (finitePrimeToModulusSubgroup m)

open scoped Classical in
theorem localHigherUnitGroup_le_integralUnits
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

open scoped Classical in
theorem fractionalIdeal_mem_primeToModulusIdeals
    (m : Modulus K) (a : IdeleGroup K)
    (ha : a ∈ idelePrimeToModulusSubgroup m) :
    IdeleGroup.fractionalIdeal a ∈ primeToModulusIdeals m := by
  intro v hv
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector a.2) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v (a.2 v)).2
  exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v hv)

open scoped Classical in
/-- The fractional-ideal map restricted to ideles prime to a modulus. -/
def primeToIdealMap (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      primeToModulusIdeals m where
  toFun a :=
    ⟨IdeleGroup.fractionalIdeal a,
      fractionalIdeal_mem_primeToModulusIdeals m a a.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

open scoped Classical in
/-- A finite idele with a prescribed valuation vector away from the
support of a modulus and value one on its support. -/
def valuationVectorSectionPrimeTo
    (m : Modulus K)
  (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  ⟨fun v =>
      if v ∈ m.finitePart.support then 1
      else FiniteIdeleGroup.chosenLocalOrderSection v (e v), by
    filter_upwards
      [m.finitePart.support.eventually_cofinite_notMem,
        e.support.eventually_cofinite_notMem] with v hvm he
    simp only [hvm, ↓reduceIte]
    apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).1
    rw [FiniteIdeleGroup.localOrder_chosenLocalOrderSection,
      Finsupp.notMem_support_iff.mp he]⟩

open scoped Classical in
theorem valuationVector_valuationVectorSectionPrimeTo
    (m : Modulus K)
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, v ∈ m.finitePart.support → e v = 0) :
    FiniteIdeleGroup.valuationVector
        (valuationVectorSectionPrimeTo m e) =
      Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  ext v
  rw [FiniteIdeleGroup.valuationVector_apply]
  by_cases hv : v ∈ m.finitePart.support
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_left hv, map_one]
    exact (he v hv).symm
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_right hv,
      FiniteIdeleGroup.localOrder_chosenLocalOrderSection]

open scoped Classical in
theorem primeToIdealMap_surjective (m : Modulus K) :
    Function.Surjective (primeToIdealMap m) := by
  intro I
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    FractionalIdealGroup.countVector (I : FractionalIdealGroup K)
  have he : ∀ v, v ∈ m.finitePart.support → e v = 0 := by
    intro v hv
    exact I.property v hv
  let a : IdeleGroup K :=
    (1, valuationVectorSectionPrimeTo m e)
  have ha : a ∈ idelePrimeToModulusSubgroup m := by
    constructor
    · exact m.infiniteCongruenceSubgroup.one_mem
    · intro v hv
      change
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v)) ∈
            localHigherUnitGroup v (m.finitePart v)
      rw [ite_eq_left hv]
      exact (localHigherUnitGroup v (m.finitePart v)).one_mem
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  apply FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (valuationVectorSectionPrimeTo m e)) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        ((I : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [valuationVector_valuationVectorSectionPrimeTo m e he,
    FractionalIdealGroup.count_factorization]
  exact FractionalIdealGroup.countVector_apply I v

open scoped Classical in
theorem ideleCongruenceSubgroup_le_primeTo
    (m : Modulus K) :
    m.ideleCongruenceSubgroup ≤
      idelePrimeToModulusSubgroup m := by
  intro a ha
  exact ⟨ha.1, fun v _ => ha.2 v⟩

open scoped Classical in
/-- The congruence subgroup, viewed inside the subgroup of ideles prime
to the modulus. -/
def congruenceSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  m.ideleCongruenceSubgroup.subgroupOf
    (idelePrimeToModulusSubgroup m)

open scoped Classical in
theorem primeToIdealMap_ker (m : Modulus K) :
    (primeToIdealMap m).ker =
      congruenceSubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hintegral :
        (a : IdeleGroup K) ∈
          IdeleGroup.integralAtFinitePlaces (K := K) := by
      rw [← IdeleGroup.fractionalIdeal_ker,
        MonoidHom.mem_ker]
      exact congrArg Subtype.val
        (MonoidHom.mem_ker.mp ha)
    constructor
    · exact a.property.1
    · intro v
      by_cases hv : v ∈ m.finitePart.support
      · exact a.property.2 v hv
      · rw [Finsupp.notMem_support_iff.mp hv,
          localHigherUnitGroup_zero]
        exact hintegral v
  · intro ha
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal (a : IdeleGroup K) = 1
    rw [← MonoidHom.mem_ker,
      IdeleGroup.fractionalIdeal_ker]
    intro v
    exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v)

open scoped Classical in
/-- The quotient of ideles prime to a modulus by the congruence subgroup,
identified with fractional ideals prime to the modulus. -/
def quotientCongruenceEquivPrimeToIdeals (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        congruenceSubgroupInPrimeTo m ≃*
      primeToModulusIdeals m := by
  rw [← primeToIdealMap_ker m]
  exact QuotientGroup.quotientKerEquivOfSurjective
    (primeToIdealMap m) (primeToIdealMap_surjective m)

open scoped Classical in
/-- Principal ideles satisfying the modulus conditions, considered inside
`I_K^(m)`. -/
def principalSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  Subgroup.comap (idelePrimeToModulusSubgroup m).subtype
    (IdeleGroup.principalSubgroup K)

open scoped Classical in
/-- Principal ideals generated by a totally positive element congruent to
one modulo the finite modulus. -/
def principalRayIdealSubgroup (m : Modulus K) :
    Subgroup (primeToModulusIdeals m) :=
  Subgroup.map (primeToIdealMap m)
    (principalSubgroupInPrimeTo m)

open scoped Classical in
theorem mem_principalRayIdealSubgroup_iff
    (m : Modulus K) (I : primeToModulusIdeals m) :
    I ∈ principalRayIdealSubgroup m ↔
      ∃ x : Kˣ,
        ∃ _hx : IdeleGroup.principalIdele K x ∈
          idelePrimeToModulusSubgroup m,
        toPrincipalIdeal (𝓞 K) K x =
          (I : FractionalIdealGroup K) := by
  constructor
  · rintro ⟨a, ha, hmap⟩
    obtain ⟨x, hx⟩ := ha
    refine ⟨x, ?_, ?_⟩
    · rw [hx]
      exact a.property
    · have hval := congrArg Subtype.val hmap
      change IdeleGroup.fractionalIdeal (a : IdeleGroup K) =
        (I : FractionalIdealGroup K) at hval
      rw [← IdeleGroup.fractionalIdeal_principalIdele]
      exact (congrArg (IdeleGroup.fractionalIdeal (K := K)) hx).trans hval
  · rintro ⟨x, hx, hideal⟩
    let a : idelePrimeToModulusSubgroup m :=
      ⟨IdeleGroup.principalIdele K x, hx⟩
    have ha : a ∈ principalSubgroupInPrimeTo m := by
      change IdeleGroup.principalIdele K x ∈
        IdeleGroup.principalSubgroup K
      exact ⟨x, rfl⟩
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal
        (IdeleGroup.principalIdele K x) =
      (I : FractionalIdealGroup K)
    rw [IdeleGroup.fractionalIdeal_principalIdele, hideal]

open scoped Classical in
/-- The ideal-theoretic ray class group `J_K^m / P_K^m`. -/
abbrev IdealRayClassGroup (m : Modulus K) :=
  primeToModulusIdeals m ⧸ principalRayIdealSubgroup m

open scoped Classical in
/-- The canonical projection from ideles prime to the modulus to the
ideal-theoretic ray class group. -/
def idealRayProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdealRayClassGroup m :=
  (QuotientGroup.mk' (principalRayIdealSubgroup m)).comp
    (primeToIdealMap m)

open scoped Classical in
/-- The subgroup generated by congruence ideles and principal ideles
inside the ideles prime to a modulus. -/
def raySubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  congruenceSubgroupInPrimeTo m ⊔
    principalSubgroupInPrimeTo m

open scoped Classical in
theorem idealRayProjection_surjective (m : Modulus K) :
    Function.Surjective (idealRayProjection m) := by
  intro c
  obtain ⟨I, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (principalRayIdealSubgroup m) c
  obtain ⟨a, rfl⟩ := primeToIdealMap_surjective m I
  exact ⟨a, rfl⟩

open scoped Classical in
theorem idealRayProjection_ker (m : Modulus K) :
    (idealRayProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m a) = 1 at ha
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    let n : idelePrimeToModulusSubgroup m := a * p⁻¹
    have hn : n ∈ congruenceSubgroupInPrimeTo m := by
      rw [← primeToIdealMap_ker m, MonoidHom.mem_ker]
      change primeToIdealMap m (a * p⁻¹) = 1
      rw [map_mul, map_inv, hpa]
      simp
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine ⟨n, hn, p, hp, ?_⟩
    dsimp [n]
    group
  · intro ha
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨n, hn, p, hp, rfl⟩ := ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m (n * p)) = 1
    rw [map_mul]
    have hn' : primeToIdealMap m n = 1 :=
      MonoidHom.mem_ker.mp
        ((primeToIdealMap_ker m).symm ▸ hn)
    rw [hn', one_mul]
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨p, hp, rfl⟩

open scoped Classical in
/-- The quotient of ideles prime to the modulus by the full ray subgroup,
identified with the ideal-theoretic ray class group. -/
def quotientRaySubgroupEquivIdealRayClassGroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdealRayClassGroup m :=
  (QuotientGroup.quotientMulEquivOfEq
      (idealRayProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (idealRayProjection m)
      (idealRayProjection_surjective m))

open scoped Classical in
/-- The quotient equivalence induced by the ideal-ray projection evaluates on
the class of a prime-to-modulus idele as the original projection. -/
theorem quotientRaySubgroupEquivIdealRayClassGroup_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdealRayClassGroup m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      idealRayProjection m a := by
  rw [quotientRaySubgroupEquivIdealRayClassGroup,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (idealRayProjection m) a

/-! ### Simultaneous approximation at the places in a modulus -/

open scoped Classical in
/-- The finite primes in `m`, together with all infinite places. -/
abbrev ApproximationPlace (m : Modulus K) :=
  (↥m.finitePart.support) ⊕ InfinitePlace K

open scoped Classical in
/-- The absolute value represented by an approximation place. -/
abbrev approximationAbsoluteValue (m : Modulus K) :
    ApproximationPlace m → AbsoluteValue K ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv K v.1
  | Sum.inr w => w.1

open scoped Classical in
theorem adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv

open scoped Classical in
theorem adicAbv_not_isEquiv_of_ne
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) := by
  intro h
  have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
    intro hvw_le
    have htop_le : (⊤ : Ideal (𝓞 K)) ≤ w.asIdeal := by
      rw [← (v.isCoprime_of_ne w hvw).sup_eq]
      exact sup_le hvw_le le_rfl
    exact w.isPrime.ne_top (top_unique htop_le)
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.mp hnotle
  have hvlt :
      NumberField.HeightOneSpectrum.adicAbv K v
        (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
  have hweq :
      NumberField.HeightOneSpectrum.adicAbv K w
        (algebraMap (𝓞 K) K x) = 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem (K := K) w x).2 hxw
  exact (ne_of_lt hvlt) (h.eq_one_iff.mpr hweq)

open scoped Classical in
theorem adicAbv_not_isEquiv_infinitePlace
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have hle :
      w.1 ((2 : ℕ) : K) ≤ 1 :=
    h.le_one_iff.mp
      (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  have hw :
      w.1 ((2 : ℕ) : K) = (2 : ℝ) :=
    NumberField.InfinitePlace.map_natCast w 2
  have hfalse : (2 : ℝ) ≤ 1 := hw ▸ hle
  norm_num at hfalse

open scoped Classical in
theorem approximationAbsoluteValue_isNontrivial
    (m : Modulus K) :
    ∀ i, (approximationAbsoluteValue m i).IsNontrivial
  | Sum.inl v => by
      change
        (NumberField.HeightOneSpectrum.adicAbv K v.1).IsNontrivial
      exact adicAbv_isNontrivial v.1
  | Sum.inr w => by
      change w.1.IsNontrivial
      exact w.isNontrivial

open scoped Classical in
theorem approximationAbsoluteValue_pairwise
    (m : Modulus K) :
    Pairwise fun i j =>
      ¬ (approximationAbsoluteValue m i).IsEquiv
        (approximationAbsoluteValue m j) := by
  intro i j hij
  cases i with
  | inl v =>
      cases j with
      | inl w =>
          apply adicAbv_not_isEquiv_of_ne
          intro hvw
          apply hij
          exact congrArg Sum.inl (Subtype.ext hvw)
      | inr w =>
          exact adicAbv_not_isEquiv_infinitePlace v.1 w
  | inr v =>
      cases j with
      | inl w =>
          exact fun h =>
            adicAbv_not_isEquiv_infinitePlace w.1 v h.symm
      | inr w =>
          intro h
          apply hij
          congr
          change v.1.IsEquiv w.1 at h
          exact
            (InfinitePlace.eq_iff_isEquiv (K := K)).mpr h

open scoped Classical in
/-- The corresponding product of local completions. -/
abbrev approximationCompletion (m : Modulus K) :
    ApproximationPlace m → Type _
  | Sum.inl v => v.1.adicCompletion K
  | Sum.inr w => w.Completion

open scoped Classical in
noncomputable instance approximationCompletionTopologicalSpace
    (m : Modulus K) (i : ApproximationPlace m) :
    TopologicalSpace (approximationCompletion m i) := by
  cases i <;> simp only [approximationCompletion] <;> infer_instance

open scoped Classical in
/-- Coordinatewise completion of the valued copies of `K`. -/
def approximationCompletionMap (m : Modulus K) :
    ∀ i : ApproximationPlace m,
      WithAbs (approximationAbsoluteValue m i) →
        approximationCompletion m i
  | Sum.inl v =>
      fun x =>
        FinitePlace.embedding v.1
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v.1) x)
  | Sum.inr w => fun x => (x : w.Completion)

open scoped Classical in
theorem denseRange_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    DenseRange
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  have hrange :
      Set.range
          (fun x :
              WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
            FinitePlace.embedding v
              (WithAbs.equiv
                (NumberField.HeightOneSpectrum.adicAbv K v) x)) =
        Set.range (algebraMap K (v.adicCompletion K)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact
        ⟨WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine
        ⟨(WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v)).symm x, ?_⟩
      rfl
  rw [DenseRange, hrange]
  exact v.denseRange_algebraMap K

open scoped Classical in
theorem continuous_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    FinitePlace.norm_embedding]
  rfl

open scoped Classical in
theorem denseRange_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, DenseRange (approximationCompletionMap m i)
  | Sum.inl v => denseRange_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.denseRange_coe w

open scoped Classical in
theorem continuous_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, Continuous (approximationCompletionMap m i)
  | Sum.inl v => continuous_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.continuous_coe w

open scoped Classical in
/-- The diagonal embedding into the finite product of the relevant
completions. -/
def approximationEmbedding (m : Modulus K) :
    K → (i : ApproximationPlace m) → approximationCompletion m i :=
  (Pi.map (approximationCompletionMap m)) ∘
    algebraMap K
      ((i : ApproximationPlace m) →
        WithAbs (approximationAbsoluteValue m i))

open scoped Classical in
@[simp]
theorem approximationEmbedding_finite
    (m : Modulus K) (x : K) (v : ↥m.finitePart.support) :
    approximationEmbedding m x (Sum.inl v) =
      FinitePlace.embedding v.1 x :=
  rfl

open scoped Classical in
@[simp]
theorem approximationEmbedding_infinite
    (m : Modulus K) (x : K) (w : InfinitePlace K) :
    approximationEmbedding m x (Sum.inr w) =
      (x : w.Completion) :=
  rfl

open scoped Classical in
theorem denseRange_approximationEmbedding (m : Modulus K) :
    DenseRange (approximationEmbedding m) := by
  exact
    (DenseRange.piMap
      (denseRange_approximationCompletionMap m)).comp
      (AbsoluteValue.denseRange_algebraMap_pi
        (approximationAbsoluteValue_isNontrivial m)
        (approximationAbsoluteValue_pairwise m))
      (.piMap (continuous_approximationCompletionMap m))

open scoped Classical in
/-- The open set of field elements whose ratio with a fixed unit lies in
a prescribed open unit set. -/
def unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    Set F :=
  Units.val '' (fun y : Fˣ => a * y⁻¹) ⁻¹' (U : Set Fˣ)

open scoped Classical in
/-- The unit-ratio set associated to an open set of units is open. -/
theorem isOpen_unitRatioSet
    {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [ContinuousInv₀ F] [T1Space F]
    (a : Fˣ) (U : Subgroup Fˣ)
    (hU : IsOpen (U : Set Fˣ)) :
    IsOpen (unitRatioSet a U) := by
  apply IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap
  exact hU.preimage (continuous_const.mul continuous_inv)

open scoped Classical in
/-- The value of the distinguished unit belongs to its unit-ratio set. -/
theorem val_mem_unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    (a : F) ∈ unitRatioSet a U := by
  exact ⟨a, by simp, rfl⟩

open scoped Classical in
/-- The open local conditions that make `a / x` prime to `m`. -/
def approximationTarget (m : Modulus K) (a : IdeleGroup K) :
    ∀ i : ApproximationPlace m, Set (approximationCompletion m i)
  | Sum.inl v =>
      unitRatioSet (a.2 v.1)
        (localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w =>
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w)
        (m.localInfiniteCongruenceSubgroup w)

open scoped Classical in
theorem isOpen_approximationTarget
    (m : Modulus K) (a : IdeleGroup K) :
    ∀ i, IsOpen (approximationTarget m a i)
  | Sum.inl v => by
      change IsOpen
        (unitRatioSet (a.2 v.1)
          (localHigherUnitGroup v.1 (m.finitePart v.1)))
      exact isOpen_unitRatioSet _ _
        (isOpen_localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w => by
      change IsOpen
        (unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w))
      apply isOpen_unitRatioSet _ _
      classical
      by_cases hw : w.IsReal
      · by_cases hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_left hmem]
          exact isOpen_infinitePositiveSubgroup w
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_right hmem]
          exact isOpen_univ
      · rw [Modulus.localInfiniteCongruenceSubgroup, dite_eq_right hw]
        exact isOpen_univ

open scoped Classical in
/-- The given idele itself lies in the product of its approximation
neighborhoods. -/
def approximationTargetPoint
    (m : Modulus K) (a : IdeleGroup K) :
    (i : ApproximationPlace m) → approximationCompletion m i
  | Sum.inl v => (a.2 v.1 : v.1.adicCompletion K)
  | Sum.inr w =>
      (ContinuousMulEquiv.piUnits a.1 w : w.Completion)

open scoped Classical in
theorem approximationTargetPoint_mem
    (m : Modulus K) (a : IdeleGroup K) :
    approximationTargetPoint m a ∈
      Set.univ.pi (approximationTarget m a) := by
  intro i _hi
  cases i with
  | inl v =>
      exact val_mem_unitRatioSet _ _
  | inr w =>
      exact val_mem_unitRatioSet _ _

open scoped Classical in
/-- Weak approximation in the precise open local cosets required by the
modulus. -/
theorem exists_principal_quotient_mem_primeTo
    (m : Modulus K) (a : IdeleGroup K) :
    ∃ x : Kˣ,
      a * (IdeleGroup.principalIdele K x)⁻¹ ∈
        idelePrimeToModulusSubgroup m := by
  let U : Set
      ((i : ApproximationPlace m) → approximationCompletion m i) :=
    Set.univ.pi (approximationTarget m a)
  have hUOpen : IsOpen U := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_approximationTarget m a i
  have hUNonempty : U.Nonempty :=
    ⟨approximationTargetPoint m a,
      approximationTargetPoint_mem m a⟩
  obtain ⟨x, hx⟩ :=
    (denseRange_approximationEmbedding m).exists_mem_open
      hUOpen hUNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w₀)
        (m.localInfiniteCongruenceSubgroup w₀) at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_⟩
  constructor
  · apply
      (Modulus.mem_infiniteCongruenceSubgroup_iff_local m
        (a * (IdeleGroup.principalIdele K xu)⁻¹).1).2
    intro w
    have hw :=
      hx (Sum.inr w) (Set.mem_univ (Sum.inr w))
    change
      (x : w.Completion) ∈
        unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w) at hw
    obtain ⟨y, hy, hyx⟩ := hw
    have hprincipal :
        ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w =
          y := by
      apply Units.ext
      calc
        ((ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w :
              w.Completionˣ) : w.Completion) =
            (xu : K) :=
          IdeleGroup.infiniteComponent_principalIdele xu w
        _ = (x : K) := rfl
        _ = (y : w.Completion) := hyx.symm
    change
      ContinuousMulEquiv.piUnits a.1 w *
          (ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w)⁻¹ ∈
        m.localInfiniteCongruenceSubgroup w
    rw [hprincipal]
    exact hy
  · intro v hv
    let vm : ↥m.finitePart.support := ⟨v, hv⟩
    have hvx :=
      hx (Sum.inl vm) (Set.mem_univ (Sum.inl vm))
    change
      FinitePlace.embedding v x ∈
        unitRatioSet (a.2 v)
          (localHigherUnitGroup v (m.finitePart v)) at hvx
    obtain ⟨y, hy, hyx⟩ := hvx
    have hprincipal :
        (IdeleGroup.principalIdele K xu).2 v = y := by
      apply Units.ext
      calc
        (((IdeleGroup.principalIdele K xu).2 v :
            (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            (xu : K) :=
          IdeleGroup.finiteComponent_principalIdele xu v
        _ = (x : K) := rfl
        _ = (y : v.adicCompletion K) := hyx.symm
    change
      a.2 v *
          ((IdeleGroup.principalIdele K xu).2 v)⁻¹ ∈
        localHigherUnitGroup v (m.finitePart v)
    rw [hprincipal]
    exact hy

open scoped Classical in
/-- Approximation identifies the idele group as
`I_K = I_K^(m) Kˣ`. -/
theorem idelePrimeToModulusSubgroup_sup_principalSubgroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  intro a _ha
  obtain ⟨x, hx⟩ :=
    exists_principal_quotient_mem_primeTo m a
  rw [Subgroup.mem_sup]
  refine
    ⟨a * (IdeleGroup.principalIdele K x)⁻¹, hx,
      IdeleGroup.principalIdele K x, ⟨x, rfl⟩, ?_⟩
  group

open scoped Classical in
/-- The natural map from the prime-to-`m` ideles to the full idelic
ray-class quotient. -/
def primeToRayClassProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.mk'
    (m.ideleCongruenceSubgroup ⊔
      IdeleGroup.principalSubgroup K)).comp
    (idelePrimeToModulusSubgroup m).subtype

open scoped Classical in
theorem primeToRayClassProjection_ker (m : Modulus K) :
    (primeToRayClassProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hN :
        (a : IdeleGroup K) ∈
          m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K := by
      rw [← QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_ker.mp ha
    rw [Subgroup.mem_sup] at hN
    obtain ⟨c, hc, p, hp, hcp⟩ := hN
    have hcA :
        c ∈ idelePrimeToModulusSubgroup m :=
      ideleCongruenceSubgroup_le_primeTo m hc
    have hpA :
        p ∈ idelePrimeToModulusSubgroup m := by
      have haA :
          (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        a.property
      have hmul :
          c⁻¹ * (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        (idelePrimeToModulusSubgroup m).mul_mem
          ((idelePrimeToModulusSubgroup m).inv_mem hcA) haA
      rw [← hcp] at hmul
      simpa using hmul
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine
      ⟨⟨c, hcA⟩, ?_, ⟨p, hpA⟩, ?_, ?_⟩
    · exact hc
    · exact hp
    · apply Subtype.ext
      exact hcp
  · intro ha
    apply MonoidHom.mem_ker.mpr
    change
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K) =
        1
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨c, hc, p, hp, rfl⟩ := ha
    apply
      (m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K).mul_mem
    · exact
        (show m.ideleCongruenceSubgroup ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_left) hc
    · exact
      (show IdeleGroup.principalSubgroup K ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_right) hp

open scoped Classical in
theorem primeToRayClassProjection_surjective (m : Modulus K) :
    Function.Surjective (primeToRayClassProjection m) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈ idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K := by
    rw [idelePrimeToModulusSubgroup_sup_principalSubgroup m]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨a, ha, p, hp, hap⟩ := hg
  refine ⟨⟨a, ha⟩, ?_⟩
  change
    QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a =
      QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) g
  rw [← hap, map_mul]
  have hpN :
      p ∈ m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K :=
    (show IdeleGroup.principalSubgroup K ≤
        m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K from le_sup_right) hp
  have hmkp :
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K) p =
        1 := by
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hpN
  rw [hmkp]
  exact
    (mul_one
      (QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a)).symm

open scoped Classical in
/-- Restricting the full idelic ray-class quotient to prime-to-`m`
ideles is an equivalence. -/
def quotientRaySubgroupEquivIdeleRayQuotient
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (primeToRayClassProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (primeToRayClassProjection m)
      (primeToRayClassProjection_surjective m))

open scoped Classical in
/-- The quotient equivalence induced by the idelic ray projection evaluates
on a prime-to-modulus idele class as the original projection. -/
theorem quotientRaySubgroupEquivIdeleRayQuotient_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdeleRayQuotient m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      primeToRayClassProjection m a := by
  rw [quotientRaySubgroupEquivIdeleRayQuotient,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (primeToRayClassProjection m) a

open scoped Classical in
/-- The idelic and ideal-theoretic ray class
groups are canonically multiplicatively equivalent. -/
def rayClassGroupEquivIdealRayClassGroup
    (m : Modulus K) :
    RayClassGroup m ≃* IdealRayClassGroup m :=
  (rayClassGroupEquivIdeleQuotient m).trans
    ((quotientRaySubgroupEquivIdeleRayQuotient m).symm.trans
      (quotientRaySubgroupEquivIdealRayClassGroup m))

end RayClass
