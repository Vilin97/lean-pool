/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertSplitting
/-!
# Prime splitting for a maximal everywhere-unramified cyclic norm quotient

Suppose a cyclic extension is unramified at every finite and infinite
place and its degree is the ordinary class number.  Its actual
idèle-class norm quotient is then the small-Hilbert reciprocity quotient.
This file transports prime Frobenius classes across that identification
and proves that trivial Frobenius is equivalent to principality of the
prime ideal.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
private theorem hilbertPrimeSplittingClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] hilbertPrimeSplittingClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramifiedAtInfinitePlaces K L]

/-- The prime Frobenius class in the big-Hilbert reciprocity quotient. -/
def bigHilbertFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      bigHilbertClassFieldNormSubgroup (K := K) :=
  (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm
    (QuotientGroup.mk'
      (RayClass.narrowDenominator (K := K))
      (finitePrimeIdele v))

private theorem mulEquiv_symm_apply_eq_one_iff
    {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (x : H) :
    e.symm x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply e.symm.injective
    exact hx.trans (map_one e.symm).symm
  · intro hx
    calc
      e.symm x = e.symm 1 := congrArg e.symm hx
      _ = 1 := map_one e.symm

private theorem mulEquiv_apply_trans_symm
    {G H I : Type} [Group G] [Group H] [Group I]
    (e : G ≃* H) (f : H ≃* I) (x : I) :
    e ((e.trans f).symm x) = f.symm x :=
  e.apply_symm_apply (f.symm x)

private theorem quotientMulEquivOfEq_trans_apply_mk
    {G I : Type} [Group G] [Group I]
    (M N : Subgroup G) [M.Normal] [N.Normal]
    (h : M = N) (e : G ⧸ N ≃* I) (x : G) :
    ((QuotientGroup.quotientMulEquivOfEq h).trans e)
        (QuotientGroup.mk' M x) =
      e (QuotientGroup.mk' N x) := by
  exact
    congrArg e
      (QuotientGroup.quotientMulEquivOfEq_mk h x)

private def primeHasTotallyPositiveGenerator
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ x : Kˣ,
    IdeleGroup.principalIdele K x ∈
      RayClass.idelePrimeToModulusSubgroup
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K)) ∧
    toPrincipalIdeal (𝓞 K) K x =
      FractionalIdealGroup.prime v

private theorem
    finitePrimeIdele_mem_narrowDenominator_imp_primeHasTotallyPositiveGenerator
    (v : HeightOneSpectrum (𝓞 K))
    (hv : finitePrimeIdele v ∈
      RayClass.narrowDenominator (K := K)) :
    primeHasTotallyPositiveGenerator v := by
  have hvSup :
      finitePrimeIdele v ∈
        (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K := by
    simpa only [RayClass.narrowDenominator] using hv
  obtain ⟨c, hc, p, hp, hcp⟩ := (Subgroup.mem_sup).1 hvSup
  obtain ⟨x, rfl⟩ := hp
  refine ⟨x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hproduct :
          c.1 * (IdeleGroup.principalIdele K x).1 = 1 := by
        calc
          c.1 * (IdeleGroup.principalIdele K x).1 =
              (c * IdeleGroup.principalIdele K x).1 :=
            rfl
          _ = (finitePrimeIdele v).1 :=
            congrArg Prod.fst hcp
          _ = 1 := rfl
      have hinfinite :
          (IdeleGroup.principalIdele K x).1 = c.1⁻¹ :=
        eq_inv_of_mul_eq_one_right hproduct
      rw [hinfinite]
      change
        c.1⁻¹ ∈
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).infiniteCongruenceSubgroup
      exact
        ((RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K)).infiniteCongruenceSubgroup).inv_mem
          hc.1
    · intro w hw
      exact ((Finsupp.mem_support_iff.mp hw) rfl).elim
  · have hcIdeal :
        IdeleGroup.fractionalIdeal c = 1 := by
      rw [← MonoidHom.mem_ker,
        IdeleGroup.fractionalIdeal_ker]
      exact
        RayClass.narrowIdeleCongruenceSubgroup_zero_le_integral hc
    calc
      toPrincipalIdeal (𝓞 K) K x =
          IdeleGroup.fractionalIdeal
            (IdeleGroup.principalIdele K x) :=
        (IdeleGroup.fractionalIdeal_principalIdele x).symm
      _ =
          IdeleGroup.fractionalIdeal c *
            IdeleGroup.fractionalIdeal
              (IdeleGroup.principalIdele K x) := by
        rw [hcIdeal, one_mul]
      _ =
          IdeleGroup.fractionalIdeal
            (c * IdeleGroup.principalIdele K x) := by
        rw [map_mul]
      _ = IdeleGroup.fractionalIdeal (finitePrimeIdele v) :=
        congrArg (IdeleGroup.fractionalIdeal (K := K)) hcp
      _ = FractionalIdealGroup.prime v :=
        fractionalIdeal_finitePrimeIdele v

private theorem
    primeHasTotallyPositiveGenerator_imp_finitePrimeIdele_mem_narrowDenominator
    (v : HeightOneSpectrum (𝓞 K))
    (hgenerator : primeHasTotallyPositiveGenerator v) :
    finitePrimeIdele v ∈
      RayClass.narrowDenominator (K := K) := by
  obtain ⟨x, hxPositive, hxIdeal⟩ := hgenerator
  let c : IdeleGroup K :=
    finitePrimeIdele v *
      (IdeleGroup.principalIdele K x)⁻¹
  have hcIdeal :
      IdeleGroup.fractionalIdeal c = 1 := by
    dsimp [c]
    rw [map_mul, map_inv,
      fractionalIdeal_finitePrimeIdele,
      IdeleGroup.fractionalIdeal_principalIdele,
      hxIdeal, mul_inv_cancel]
  have hcIntegral :
      c ∈ IdeleGroup.integralAtFinitePlaces (K := K) := by
    rw [← IdeleGroup.fractionalIdeal_ker,
      MonoidHom.mem_ker]
    exact hcIdeal
  have hcCongruence :
      c ∈
        RayClass.Modulus.ideleCongruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)) := by
    refine ⟨?_, ?_⟩
    · change
        (finitePrimeIdele v).1 *
            ((IdeleGroup.principalIdele K x).1)⁻¹ ∈
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).infiniteCongruenceSubgroup
      change
        1 * ((IdeleGroup.principalIdele K x).1)⁻¹ ∈
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).infiniteCongruenceSubgroup
      simpa only [one_mul] using
        ((RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K)).infiniteCongruenceSubgroup).inv_mem
          hxPositive.1
    · rw [RayClass.Modulus.finitePart_narrowOfFinite,
        RayClass.finiteCongruenceSubgroup_zero]
      exact hcIntegral
  have hvSup :
      finitePrimeIdele v ∈
        (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K := by
    apply (Subgroup.mem_sup).2
    refine
      ⟨c, hcCongruence,
        IdeleGroup.principalIdele K x,
        ⟨x, rfl⟩, ?_⟩
    dsimp [c]
    group
  simpa only [RayClass.narrowDenominator] using hvSup

private theorem
    finitePrimeIdele_mem_narrowDenominator_iff_primeHasTotallyPositiveGenerator
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePrimeIdele v ∈
        RayClass.narrowDenominator (K := K) ↔
      primeHasTotallyPositiveGenerator v :=
  ⟨finitePrimeIdele_mem_narrowDenominator_imp_primeHasTotallyPositiveGenerator v,
    primeHasTotallyPositiveGenerator_imp_finitePrimeIdele_mem_narrowDenominator v⟩

/-- The big-Hilbert Frobenius class is trivial exactly when the prime
has a generator whose principal idèle is positive at every real
infinite place. -/
theorem
    bigHilbertFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator
    (v : HeightOneSpectrum (𝓞 K)) :
    bigHilbertFrobeniusClass v = 1 ↔
      ∃ x : Kˣ,
        IdeleGroup.principalIdele K x ∈
          RayClass.idelePrimeToModulusSubgroup
            (RayClass.Modulus.narrowOfFinite
              (0 : RayClass.FiniteModulus K)) ∧
        toPrincipalIdeal (𝓞 K) K x =
          FractionalIdealGroup.prime v := by
  exact
    (mulEquiv_symm_apply_eq_one_iff
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K))
      (QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K))
        (finitePrimeIdele v))).trans
      ((QuotientGroup.eq_one_iff (finitePrimeIdele v)).trans
        (finitePrimeIdele_mem_narrowDenominator_iff_primeHasTotallyPositiveGenerator
          v))

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- The prime Frobenius class in the actual norm quotient of a maximal
finite-unramified cyclic extension. -/
def maximalFiniteUnramifiedCyclicFrobeniusClass
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      (_root_.ideleClassNorm K L).range :=
  (maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
      (K := K) (L := L) hunramified hdegree).symm
    (QuotientGroup.mk'
      (RayClass.narrowDenominator (K := K))
      (finitePrimeIdele v))

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- The maximal finite-unramified norm-quotient Frobenius class is
represented by the one-place prime idèle class. -/
theorem
    maximalFiniteUnramifiedCyclicFrobeniusClass_eq_finitePrimeIdeleClass
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalFiniteUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramified hdegree v =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v)) := by
  apply
    (maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
      (K := K) (L := L) hunramified hdegree).injective
  calc
    _ = QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K))
          (finitePrimeIdele v) :=
      (maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
        (K := K) (L := L) hunramified hdegree).apply_symm_apply _
    _ = bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)
          (QuotientGroup.mk'
            (bigHilbertClassFieldNormSubgroup (K := K))
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (finitePrimeIdele v))) :=
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
        (K := K) (finitePrimeIdele v)).symm
    _ = maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
          (K := K) (L := L) hunramified hdegree
          (QuotientGroup.mk'
            ((_root_.ideleClassNorm K L).range)
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (finitePrimeIdele v))) :=
      (quotientMulEquivOfEq_trans_apply_mk
        ((_root_.ideleClassNorm K L).range)
        (bigHilbertClassFieldNormSubgroup (K := K))
        ((ideleClassNorm_range_eq_bigHilbertClassFieldNormSubgroup_iff_finrank_eq_narrowClassGroup_card
          (K := K) (L := L) hunramified).2 hdegree)
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K))
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v))).symm

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- The order of the actual maximal finite-unramified Frobenius class
is the order of its narrow ideal class. -/
theorem orderOf_maximalFiniteUnramifiedCyclicFrobeniusClass
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (maximalFiniteUnramifiedCyclicFrobeniusClass
          (K := K) (L := L) hunramified hdegree v) =
      orderOf
        (QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K))
          (finitePrimeIdele v)) := by
  exact
    (maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
      (K := K) (L := L) hunramified hdegree).symm.orderOf_eq
      (QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K))
        (finitePrimeIdele v))

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- The Frobenius class in the actual maximal finite-unramified norm
quotient is trivial exactly when the prime has a totally positive
generator. -/
theorem
    maximalFiniteUnramifiedCyclicFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalFiniteUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramified hdegree v = 1 ↔
      ∃ x : Kˣ,
        IdeleGroup.principalIdele K x ∈
          RayClass.idelePrimeToModulusSubgroup
            (RayClass.Modulus.narrowOfFinite
              (0 : RayClass.FiniteModulus K)) ∧
        toPrincipalIdeal (𝓞 K) K x =
          FractionalIdealGroup.prime v := by
  exact
    (mulEquiv_symm_apply_eq_one_iff
      (maximalFiniteUnramifiedCyclicNormQuotientEquivNarrowClassGroup
        (K := K) (L := L) hunramified hdegree)
      (QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K))
        (finitePrimeIdele v))).trans
      ((QuotientGroup.eq_one_iff (finitePrimeIdele v)).trans
        (finitePrimeIdele_mem_narrowDenominator_iff_primeHasTotallyPositiveGenerator
          v))

omit [IsCyclic (L ≃ₐ[K] L)] [IsUnramifiedAtInfinitePlaces K L] in
private theorem finitePrimeIdeleClass_eq_one_of_splitsCompletely
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  change
    IdeleGroup.finitePlaceIdeleClass v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) ∈
      (_root_.ideleClassNorm K L).range
  apply
    finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely
      (K := K) (L := L) v hsplit
  exact
    ⟨FiniteIdeleGroup.chosenLocalOrderSection v 1, rfl⟩

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- Actual complete splitting in a maximal finite-unramified cyclic
extension forces triviality of the corresponding norm-quotient
Frobenius class. -/
theorem
    finitePlaceSplitsCompletely_imp_maximalFiniteUnramifiedCyclicFrobeniusClass_eq_one
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    maximalFiniteUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramified hdegree v = 1 := by
  exact
    (maximalFiniteUnramifiedCyclicFrobeniusClass_eq_finitePrimeIdeleClass
      (K := K) (L := L) hunramified hdegree v).trans
      (finitePrimeIdeleClass_eq_one_of_splitsCompletely
        (K := K) (L := L) v hsplit)

omit [IsUnramifiedAtInfinitePlaces K L] in
/-- Every prime which actually splits completely in a maximal
finite-unramified cyclic extension has a totally positive generator. -/
theorem
    finitePlaceSplitsCompletely_imp_exists_totallyPositiveGenerator_of_maximalFiniteUnramifiedCyclic
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        Nat.card (RayClass.NarrowClassGroup K))
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    ∃ x : Kˣ,
      IdeleGroup.principalIdele K x ∈
        RayClass.idelePrimeToModulusSubgroup
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)) ∧
      toPrincipalIdeal (𝓞 K) K x =
        FractionalIdealGroup.prime v :=
  (maximalFiniteUnramifiedCyclicFrobeniusClass_eq_one_iff_exists_totallyPositiveGenerator
    (K := K) (L := L) hunramified hdegree v).1
    (finitePlaceSplitsCompletely_imp_maximalFiniteUnramifiedCyclicFrobeniusClass_eq_one
      (K := K) (L := L) hunramified hdegree v hsplit)

/-- At maximal everywhere-unramified cyclic degree, the actual norm
quotient is canonically the small-Hilbert reciprocity quotient. -/
def maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) :=
  QuotientGroup.quotientMulEquivOfEq
    ((ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
      (K := K) (L := L) hunramifiedFinite).2 hdegree)

/-- The prime Frobenius class in the actual norm quotient of a maximal
everywhere-unramified cyclic extension. -/
def maximalEverywhereUnramifiedCyclicFrobeniusClass
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      (_root_.ideleClassNorm K L).range :=
  (maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
      (K := K) (L := L) hunramifiedFinite hdegree).symm
    (ClassGroup.mk K (FractionalIdealGroup.prime v))

/-- The actual maximal norm-quotient Frobenius class corresponds to the
small-Hilbert Frobenius class. -/
theorem
    maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient_frobeniusClass
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient
        (K := K) (L := L) hunramifiedFinite hdegree
        (maximalEverywhereUnramifiedCyclicFrobeniusClass
          (K := K) (L := L) hunramifiedFinite hdegree v) =
      IdealClassFieldTheory.smallHilbertFrobeniusClass v := by
  exact
    mulEquiv_apply_trans_symm
      (maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient
        (K := K) (L := L) hunramifiedFinite hdegree)
      (smallHilbertClassFieldQuotientEquivClassGroup (K := K))
      (ClassGroup.mk K (FractionalIdealGroup.prime v))

/-- The maximal norm-quotient Frobenius class is represented by the
one-place prime idèle class. -/
theorem
    maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_finitePrimeIdeleClass
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalEverywhereUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramifiedFinite hdegree v =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v)) := by
  apply
    (maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
      (K := K) (L := L) hunramifiedFinite hdegree).injective
  calc
    _ = ClassGroup.mk K (FractionalIdealGroup.prime v) :=
      (maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
        (K := K) (L := L) hunramifiedFinite hdegree).apply_symm_apply _
    _ = IdeleGroup.idealClass (finitePrimeIdele v) :=
      (IdeleGroup.idealClass_finitePrimeIdele v).symm
    _ = smallHilbertClassFieldQuotientEquivClassGroup
          (K := K)
          (QuotientGroup.mk'
            (smallHilbertClassFieldNormSubgroup (K := K))
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (finitePrimeIdele v))) :=
      (smallHilbertClassFieldQuotientEquivClassGroup_mk
        (K := K) (finitePrimeIdele v)).symm
    _ = maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
          (K := K) (L := L) hunramifiedFinite hdegree
          (QuotientGroup.mk'
            ((_root_.ideleClassNorm K L).range)
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (finitePrimeIdele v))) :=
      (quotientMulEquivOfEq_trans_apply_mk
        ((_root_.ideleClassNorm K L).range)
        (smallHilbertClassFieldNormSubgroup (K := K))
        ((ideleClassNorm_range_eq_smallHilbertClassFieldNormSubgroup_iff_finrank_eq_classNumber
          (K := K) (L := L) hunramifiedFinite).2 hdegree)
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := K))
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (finitePrimeIdele v))).symm

/-- The order of the actual norm-quotient Frobenius class is the order
of the corresponding ordinary ideal class. -/
theorem orderOf_maximalEverywhereUnramifiedCyclicFrobeniusClass
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    orderOf
        (maximalEverywhereUnramifiedCyclicFrobeniusClass
          (K := K) (L := L) hunramifiedFinite hdegree v) =
      orderOf
        (ClassGroup.mk K (FractionalIdealGroup.prime v)) := by
  exact
    (maximalEverywhereUnramifiedCyclicNormQuotientEquivClassGroup
      (K := K) (L := L) hunramifiedFinite hdegree).symm.orderOf_eq
      (ClassGroup.mk K (FractionalIdealGroup.prime v))

/-- Under the canonical quotient identification, complete splitting in
the small Hilbert class field is equivalent to triviality of the
corresponding Frobenius class in the actual maximal norm quotient. -/
theorem
    maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_smallHilbertClassFieldSplitsCompletely
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalEverywhereUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramifiedFinite hdegree v = 1 ↔
      IdealClassFieldTheory.SplitsCompletelyInSmallHilbertClassField v := by
  let e :=
    maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient
      (K := K) (L := L) hunramifiedFinite hdegree
  constructor
  · intro hv
    calc
      IdealClassFieldTheory.smallHilbertFrobeniusClass v =
          e (maximalEverywhereUnramifiedCyclicFrobeniusClass
            (K := K) (L := L) hunramifiedFinite hdegree v) :=
        (maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient_frobeniusClass
          (K := K) (L := L) hunramifiedFinite hdegree v).symm
      _ = e 1 := congrArg e hv
      _ = 1 := map_one e
  · intro hv
    apply e.injective
    calc
      e (maximalEverywhereUnramifiedCyclicFrobeniusClass
          (K := K) (L := L) hunramifiedFinite hdegree v) =
          IdealClassFieldTheory.smallHilbertFrobeniusClass v :=
        maximalEverywhereUnramifiedCyclicNormQuotientEquivSmallHilbertQuotient_frobeniusClass
          (K := K) (L := L) hunramifiedFinite hdegree v
      _ = 1 := hv
      _ = e 1 := (map_one e).symm

/-- The Frobenius class in the actual maximal norm quotient is trivial
exactly when the corresponding prime ideal is principal. -/
theorem
    maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_principal
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalEverywhereUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramifiedFinite hdegree v = 1 ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  exact
    (maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_smallHilbertClassFieldSplitsCompletely
      (K := K) (L := L) hunramifiedFinite hdegree v).trans
      (IdealClassFieldTheory.splitsCompletelyInSmallHilbertClassField_iff_principal
        v)

/-- Existential generator form of the trivial-Frobenius criterion in
the actual maximal norm quotient. -/
theorem
    maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_exists_generator
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K)) :
    maximalEverywhereUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramifiedFinite hdegree v = 1 ↔
      ∃ x : Kˣ,
        toPrincipalIdeal (𝓞 K) K x =
          FractionalIdealGroup.prime v := by
  exact
    (maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_principal
      (K := K) (L := L) hunramifiedFinite hdegree v).trans Iff.rfl

/-- If a finite prime actually splits completely in the maximal
everywhere-unramified cyclic extension, then its norm-quotient
Frobenius class is trivial. -/
theorem
    finitePlaceSplitsCompletely_imp_maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    maximalEverywhereUnramifiedCyclicFrobeniusClass
        (K := K) (L := L) hunramifiedFinite hdegree v = 1 := by
  exact
    (maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_finitePrimeIdeleClass
      (K := K) (L := L) hunramifiedFinite hdegree v).trans
      (finitePrimeIdeleClass_eq_one_of_splitsCompletely
        (K := K) (L := L) v hsplit)

/-- In a maximal everywhere-unramified cyclic extension, every prime
which actually splits completely is principal. -/
theorem
    finitePlaceSplitsCompletely_imp_prime_principal_of_maximalEverywhereUnramifiedCyclic
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    FractionalIdealGroup.prime v ∈
      (toPrincipalIdeal (𝓞 K) K).range :=
  (maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one_iff_principal
    (K := K) (L := L) hunramifiedFinite hdegree v).1
    (finitePlaceSplitsCompletely_imp_maximalEverywhereUnramifiedCyclicFrobeniusClass_eq_one
      (K := K) (L := L) hunramifiedFinite hdegree v hsplit)

/-- A nonprincipal prime cannot split completely in a maximal
everywhere-unramified cyclic extension. -/
theorem
    not_finitePlaceSplitsCompletely_of_prime_not_principal_of_maximalEverywhereUnramifiedCyclic
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (hdegree :
      Module.finrank K L =
        NumberField.classNumber K)
    (v : HeightOneSpectrum (𝓞 K))
    (hprincipal :
      FractionalIdealGroup.prime v ∉
        (toPrincipalIdeal (𝓞 K) K).range) :
    ¬ _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  intro hsplit
  exact
    hprincipal
      (finitePlaceSplitsCompletely_imp_prime_principal_of_maximalEverywhereUnramifiedCyclic
        (K := K) (L := L) hunramifiedFinite hdegree v hsplit)

end GlobalClassFields
end GlobalClassFieldTheory
