/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentDivisor
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceTower

/-!
# Finiteness of the branch locus

For a finite separable extension of Dedekind domains, a height-one prime is
ramified exactly when it divides the different.  The different is nonzero and
has finite prime support, so both the ramification locus upstairs and its image
in the base are finite.  This is the algebraic branch-locus finiteness used for
finite separable morphisms of curves.

The final theorems attach to every exhaustive closed place its residue-degree
weight over the constant field.  The branch support is finite, and the
degree-weighted sum over any selected part of it is at most the full branch
sum.  Passing from this closed-place bound to a uniform count of geometric
branch points after constant-field extension still requires an explicit
closed-place/geometric-point comparison.
-/

open scoped BigOperators
open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

section Dedekind

variable (A B : Type*) [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- The height-one primes upstairs at which a finite separable Dedekind
extension is ramified. -/
def dedekindRamificationLocus : Set (HeightOneSpectrum B) :=
  {Q | ¬ Algebra.IsUnramifiedAt A Q.asIdeal}

/-- The ramification locus is contained in the finite support of the
different, and is therefore finite. -/
theorem dedekindRamificationLocus_finite :
    (dedekindRamificationLocus A B).Finite := by
  let hDifferent : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  let D := BGS.CorvajaZannier.differentMultiplicityDivisor A B hDifferent
  refine D.support.finite_toSet.subset ?_
  intro Q hQ
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  have hdiv : Q.asIdeal ∣ differentIdeal A B :=
    dvd_differentIdeal_iff.mpr hQ
  simpa [D, BGS.CorvajaZannier.differentMultiplicityDivisor_apply] using
    (multiplicity_pos_of_dvd hdiv (FiniteMultiplicity.of_prime_left Q.prime hDifferent)).ne'

/-- The branch locus downstairs is the image of the ramification locus under
contraction of height-one primes. -/
def dedekindBranchLocus : Set (HeightOneSpectrum A) :=
  HeightOneSpectrum.under A '' dedekindRamificationLocus A B

/-- The branch locus of a finite separable Dedekind extension is finite. -/
theorem dedekindBranchLocus_finite :
    (dedekindBranchLocus A B).Finite := by
  exact (dedekindRamificationLocus_finite A B).image
    (HeightOneSpectrum.under A)

/-- Any distinguished subset of the closed-place branch locus has cardinality
at most the full closed-place branch locus. -/
theorem dedekindBranchLocus_selected_ncard_le
    (isSelected : HeightOneSpectrum A → Prop) :
    (dedekindBranchLocus A B ∩ {P | isSelected P}).ncard ≤
      (dedekindBranchLocus A B).ncard := by
  exact Set.ncard_le_ncard Set.inter_subset_left
    (dedekindBranchLocus_finite A B)

end Dedekind

section FunctionField

open BGS.CorvajaZannier Polynomial

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L]

local instance (priority := 10) branchPolynomialAlgebraM : Algebra K[X] M :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) M).comp
    (algebraMap K[X] (RatFunc K)))

local instance (priority := 10) branchPolynomialAlgebraL : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance branchPolynomialTowerM : IsScalarTower K[X] (RatFunc K) M :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance branchPolynomialTowerL : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance branchPolynomialFieldTower : IsScalarTower K[X] M L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) x) =
      algebraMap M L
        (algebraMap (RatFunc K) M (algebraMap K[X] (RatFunc K) x))
    exact IsScalarTower.algebraMap_apply (RatFunc K) M L _

local instance branchFiniteClosureAlgebra :
    Algebra (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  (finiteIntegralClosureMap K M L).toAlgebra

local instance branchFiniteIntermediateIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra K[X] M

local instance branchFiniteTopIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance branchFiniteIntermediateModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K M) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K M)

local instance branchFiniteTopModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance branchFiniteIntermediateTorsionFree :
    Module.IsTorsionFree K[X] M :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) M

local instance branchFiniteTopTorsionFree :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance branchFiniteIntermediateClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree K[X] M

local instance branchFiniteTopClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance branchFiniteIntermediateDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) M
    (RatFuncFiniteIntegralClosure K M)

local instance branchFiniteTopDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance branchFiniteClosuresTower :
    IsScalarTower K[X] (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    change algebraMap K[X] L _ = algebraMap M L (algebraMap K[X] M _)
    exact IsScalarTower.algebraMap_apply K[X] M L _

local instance branchFiniteRelativeIntegral :
    Algebra.IsIntegral (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Algebra.IsIntegral.tower_top K[X]

local instance branchFiniteRelativeFaithful :
    FaithfulSMul (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap M L).injective
  exact congrArg Subtype.val hxy

local instance branchFiniteRelativeModuleFinite :
    Module.Finite (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Module.Finite.of_restrictScalars_finite K[X]
    (RatFuncFiniteIntegralClosure K M)
    (RatFuncFiniteIntegralClosure K L)

local instance branchFiniteIntermediateClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M) M L :=
  inferInstance

local instance branchFiniteTopClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def, map_mul]
    rw [show algebraMap (RatFuncFiniteIntegralClosure K L) L
        (algebraMap (RatFuncFiniteIntegralClosure K M)
          (RatFuncFiniteIntegralClosure K L) r) =
        algebraMap (RatFuncFiniteIntegralClosure K M) L r by rfl]
    ring⟩

local instance branchFiniteIntermediateFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) M (RatFuncFiniteIntegralClosure K M)

local instance branchFiniteTopFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

local instance branchFiniteFractionRingSeparable :
    Algebra.IsSeparable
      (FractionRing (RatFuncFiniteIntegralClosure K M))
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  letI : Algebra.IsSeparable M L :=
    Algebra.isSeparable_tower_top_of_isSeparable (RatFunc K) M L
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv (RatFuncFiniteIntegralClosure K M) M).symm.toRingEquiv
    (FractionRing.algEquiv (RatFuncFiniteIntegralClosure K L) L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv (RatFuncFiniteIntegralClosure K M) M).symm
    (FractionRing.algEquiv (RatFuncFiniteIntegralClosure K L) L).symm z

local instance branchInfinityClosureAlgebra :
    Algebra (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  (infinityIntegralClosureMap K M L).toAlgebra

local instance branchInfinityIntermediateIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) M

local instance branchInfinityIntermediateModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) M
    (RatFuncInfinityIntegralClosure K M)

local instance branchInfinityIntermediateDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) M (RatFuncInfinityIntegralClosure K M)

local instance branchInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K M) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K M))

/-- The exhaustive branch locus of the finite separable function-field tower
`L / M / K(t)`.  The finite chart is the contraction of the different support;
the infinity chart records the base infinity places admitting a ramified lift.
-/
def finiteExtensionBranchLocus : Set (FiniteExtensionPlace K M) :=
  Sum.inl '' dedekindBranchLocus
      (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) ∪
    Sum.inr '' {P : FiniteExtensionInfinityPlace K M |
      ∃ Q : FiniteExtensionInfinityPlace K L,
        infinityPlaceUnder K M L Q = P ∧
          ¬ Algebra.IsUnramifiedAt
            (RatFuncInfinityIntegralClosure K M) Q.1}

/-- The exhaustive branch locus of a finite separable function-field
extension is finite. -/
theorem finiteExtensionBranchLocus_finite :
    (finiteExtensionBranchLocus K M L).Finite := by
  apply Set.Finite.union
  · exact (dedekindBranchLocus_finite
      (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L)).image Sum.inl
  · exact (Set.toFinite _).image Sum.inr

section DegreeWeight

variable [DecidableEq K]

/-- The nonnegative weight of an exhaustive closed place is its degree over
the constant field `K`.  On the finite chart this is the relative residue
degree times the degree of the contracted polynomial place; above infinity it
is the relative residue degree, since the base infinity place has degree one.
-/
def finiteExtensionClosedPlaceWeight
    (P : FiniteExtensionPlace K M) : ℕ :=
  finiteExtensionPlaceDegree K M P

omit [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M] in
@[simp]
theorem finiteExtensionClosedPlaceWeight_inl
    (P : FiniteExtensionFinitePlace K M) :
    finiteExtensionClosedPlaceWeight K M (.inl P) =
      P.asIdeal.inertiaDeg K[X] *
        ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] P) := by
  rfl

omit [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M] in
@[simp]
theorem finiteExtensionClosedPlaceWeight_inr
    (P : FiniteExtensionInfinityPlace K M) :
    finiteExtensionClosedPlaceWeight K M (.inr P) =
      P.1.inertiaDeg (RatFuncInfinityIntegers K) := by
  rfl

/-- The finite support on which the branch-locus degree sum is taken. -/
def finiteExtensionBranchLocusSupport :
    Finset (FiniteExtensionPlace K M) :=
  (finiteExtensionBranchLocus_finite K M L).toFinset

omit [DecidableEq K] in
@[simp]
theorem mem_finiteExtensionBranchLocusSupport_iff
    (P : FiniteExtensionPlace K M) :
    P ∈ finiteExtensionBranchLocusSupport K M L ↔
      P ∈ finiteExtensionBranchLocus K M L := by
  simp [finiteExtensionBranchLocusSupport]

/-- The support finset represents exactly the finite branch locus. -/
theorem finiteExtensionBranchLocusSupport_coe :
    (finiteExtensionBranchLocusSupport K M L :
      Set (FiniteExtensionPlace K M)) =
        finiteExtensionBranchLocus K M L := by
  ext P
  simp

/-- In set form, the exact branch support is finite. -/
theorem finiteExtensionBranchLocusSupport_finite :
    ((finiteExtensionBranchLocusSupport K M L :
      Finset (FiniteExtensionPlace K M)) :
        Set (FiniteExtensionPlace K M)).Finite :=
  Finset.finite_toSet _

/-- The total residue-degree weight of the exhaustive branch locus. -/
def finiteExtensionBranchLocusDegreeSum : ℕ :=
  ∑ P ∈ finiteExtensionBranchLocusSupport K M L,
    finiteExtensionClosedPlaceWeight K M P

/-- The finite branch support restricted by an arbitrary predicate. -/
def finiteExtensionBranchLocusSelectedSupport
    (isSelected : FiniteExtensionPlace K M → Prop) :
    Finset (FiniteExtensionPlace K M) := by
  classical
  exact (finiteExtensionBranchLocusSupport K M L).filter isSelected

@[simp]
theorem mem_finiteExtensionBranchLocusSelectedSupport_iff
    (isSelected : FiniteExtensionPlace K M → Prop)
    (P : FiniteExtensionPlace K M) :
    P ∈ finiteExtensionBranchLocusSelectedSupport K M L isSelected ↔
      P ∈ finiteExtensionBranchLocus K M L ∧ isSelected P := by
  classical
  simp [finiteExtensionBranchLocusSelectedSupport]

/-- The residue-degree weight of a selected part of the finite branch
support. -/
def finiteExtensionBranchLocusSelectedDegreeSum
    (isSelected : FiniteExtensionPlace K M → Prop) : ℕ :=
  ∑ P ∈ finiteExtensionBranchLocusSelectedSupport K M L isSelected,
    finiteExtensionClosedPlaceWeight K M P

/-- Every selected part of the branch locus has residue-degree weight at most
the total residue-degree weight of the full finite branch support. -/
theorem finiteExtensionBranchLocus_selected_degreeSum_le
    (isSelected : FiniteExtensionPlace K M → Prop) :
    finiteExtensionBranchLocusSelectedDegreeSum K M L isSelected ≤
        finiteExtensionBranchLocusDegreeSum K M L := by
  classical
  rw [finiteExtensionBranchLocusSelectedDegreeSum,
    finiteExtensionBranchLocusDegreeSum,
    finiteExtensionBranchLocusSelectedSupport]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end DegreeWeight

/-- Any distinguished subset of the exhaustive closed-place branch locus has
cardinality at most the full closed-place branch locus. -/
theorem finiteExtensionBranchLocus_selected_ncard_le
    (isSelected : FiniteExtensionPlace K M → Prop) :
    (finiteExtensionBranchLocus K M L ∩ {P | isSelected P}).ncard ≤
      (finiteExtensionBranchLocus K M L).ncard := by
  exact Set.ncard_le_ncard Set.inter_subset_left
    (finiteExtensionBranchLocus_finite K M L)

end FunctionField

end

end BGS.HasseWeil
