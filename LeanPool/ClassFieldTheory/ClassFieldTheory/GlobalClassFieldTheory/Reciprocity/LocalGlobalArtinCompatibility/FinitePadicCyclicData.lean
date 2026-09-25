/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.SeparableClosurePadicLift
/-!
# Finite p-adic cyclic data for local-global Artin compatibility

This module packages the simultaneous finite-quotient and cyclotomic
coordinates and the corresponding abstract auxiliary subextension.
-/

@[expose] public section

open scoped IsMulCommutative NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

local instance numberFieldTowerExtensionNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

local instance finitePadicTowerExtensionQuotientFinite :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L

noncomputable local instance numberFieldTowerExtensionQuotientIsMulCommutative :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L/K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L/K))).is_comm.comm
                (e x) (e y)⟩ }

local instance numberFieldTowerBaseSubgroupCompactSpace :
    CompactSpace
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
  isCompact_iff_compactSpace.mp
    (numberFieldTowerBaseSubgroup K L).isClosed'.isCompact

/-- Inclusion of a subgroup equipped with its subtype topology. -/
private def continuousSubgroupSubtype
    {A : Type*} [Group A] [TopologicalSpace A]
    (H : Subgroup A) : H →ₜ* A where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

/-- The finite quotient coordinate on the compatible embedded copy of
the absolute Galois group of `K`. -/
noncomputable def numberFieldTowerFiniteQuotientCoordinate :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let N :=
    extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    { toMonoidHom := QuotientGroup.mk' N
      continuous_toFun := QuotientGroup.continuous_mk }

/-- The genuine `p`-adic cyclotomic degree on the rational absolute
Galois group. -/
noncomputable def rationalSeparableClosurePadicCyclotomicDegree
    (p : Nat.Primes) :
    Gal(SeparableClosure ℚ/ℚ) →ₜ*
      Multiplicative ℤ_[p.1] :=
  (rationalCyclotomicPadicCoordinate p).comp
    rationalAbsoluteGaloisRestrictionToCyclotomicZHat

/-- The kernel of the absolute `p`-adic cyclotomic degree is exactly
the fixing subgroup of the actual `p`-primary cyclotomic field in the
rational separable closure. -/
theorem rationalSeparableClosurePadicCyclotomicDegree_ker
    (p : Nat.Primes) :
    (rationalSeparableClosurePadicCyclotomicDegree
        p).toMonoidHom.ker =
      (rationalCyclotomicPadicField p).fixingSubgroup := by
  let : Algebra ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField.algebra'
  let : @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' :=
    rationalCyclotomicZHatField_normal
  let E :=
    rationalCyclotomicPadicFieldWithinZHat p
  ext σ
  change
    rationalCyclotomicPadicCoordinate p
        (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) =
      1 ↔
    σ ∈ (IntermediateField.lift E).fixingSubgroup
  constructor
  · intro hσ
    have hr :
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ ∈
          E.fixingSubgroup := by
      rw [
        rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup]
      exact hσ
    refine (IntermediateField.mem_fixingSubgroup_iff
      (IntermediateField.lift E) σ).2 ?_
    intro x hx
    let xC : rationalCyclotomicZHatField :=
      ⟨x, IntermediateField.lift_le E hx⟩
    have hxE : xC ∈ E :=
      (IntermediateField.mem_lift xC).1 hx
    have hfix :
        (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) xC =
          xC :=
      (IntermediateField.mem_fixingSubgroup_iff
        E
          (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ)).1 hr xC hxE
    calc
      σ x =
          algebraMap rationalCyclotomicZHatField (SeparableClosure ℚ)
            ((rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) xC) := by
              exact
                (AlgEquiv.restrictNormal_commutes
                  σ rationalCyclotomicZHatField xC).symm
      _ = algebraMap rationalCyclotomicZHatField
            (SeparableClosure ℚ) xC := by
            rw [hfix]
      _ = x := rfl
  · intro hσ
    have hr :
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ ∈
          E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have hfix :
          σ x.1 = x.1 :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IntermediateField.lift E) σ).1 hσ x.1
            ((IntermediateField.mem_lift x).2 hx)
      exact
        (AlgEquiv.restrictNormal_commutes
          σ rationalCyclotomicZHatField x).trans hfix
    rw [
      rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup]
      at hr
    exact hr

/-- The genuine rational cyclotomic `p`-adic degree restricted to the
compatible embedded copy of the absolute Galois group of `K`. -/
noncomputable def numberFieldTowerBaseSubgroupPadicCyclotomicDegree
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      Multiplicative ℤ_[p.1] :=
  (rationalSeparableClosurePadicCyclotomicDegree p).comp
    (continuousSubgroupSubtype
      (numberFieldTowerBaseSubgroup K L).toSubgroup)

/-- The simultaneous finite-extension and cyclotomic `p`-adic
coordinate on the compatible absolute Galois group of `K`. -/
noncomputable def numberFieldTowerFinitePadicCoordinate
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      (((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ×
        Multiplicative ℤ_[p.1]) := by
  let finiteCoordinate :=
    numberFieldTowerFiniteQuotientCoordinate
      (K := K) (L := L)
  let padicDegree :=
    numberFieldTowerBaseSubgroupPadicCyclotomicDegree
      (K := K) (L := L) p
  exact
    { toFun := fun τ =>
        (finiteCoordinate τ, padicDegree τ)
      map_one' := by
        simp only [map_one]
        rfl
      map_mul' := by
        intro σ τ
        simp only [map_mul, Prod.mul_def]
      continuous_toFun :=
        finiteCoordinate.continuous_toFun.prodMk
          padicDegree.continuous_toFun }

/-- The actual image of the simultaneous finite and `p`-adic
cyclotomic coordinate, as a closed subgroup of the product. -/
noncomputable def numberFieldTowerFinitePadicImage
    (p : Nat.Primes) :
    ClosedSubgroup
      (((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ×
        Multiplicative ℤ_[p.1]) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  letI extensionSubgroupClosed : IsClosed (N : Set H.toSubgroup) :=
    extensionSubgroup_isClosed
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  refine
    { toSubgroup := coordinate.toMonoidHom.range
      isClosed' := ?_ }
  change IsClosed (Set.range coordinate)
  exact
    (isCompact_range coordinate.continuous_toFun).isClosed

/-- The `p`-adic degree on the actual simultaneous-coordinate image is
its second projection. -/
noncomputable def numberFieldTowerFinitePadicImageDegree
    (p : Nat.Primes) :
    (numberFieldTowerFinitePadicImage
        (K := K) (L := L) p).toSubgroup →ₜ*
      Multiplicative ℤ_[p.1] := by
  exact
    { toFun := fun z => z.1.2
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        continuous_snd.comp continuous_subtype_val }

/-- The kernel of the `p`-adic degree on the simultaneous-coordinate
image is finite: its first projection injects it into the finite
Galois quotient. -/
theorem numberFieldTowerFinitePadicImageDegree_ker_finite
    (p : Nat.Primes) :
    Finite
      (numberFieldTowerFinitePadicImageDegree
        (K := K) (L := L) p).toMonoidHom.ker := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let first :
      degree.toMonoidHom.ker → Q :=
    fun z => z.1.1.1
  apply Finite.of_injective first
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · have hx : x.1.1.2 = 1 := x.2
    have hy : y.1.1.2 = 1 := y.2
    exact hx.trans hy.symm

/-- The simultaneous coordinate with codomain restricted to its actual
closed image. -/
noncomputable def numberFieldTowerFinitePadicRangeRestriction
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      (numberFieldTowerFinitePadicImage
        (K := K) (L := L) p).toSubgroup := by
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  exact
    { toMonoidHom := coordinate.toMonoidHom.rangeRestrict
      continuous_toFun :=
        coordinate.continuous_toFun.subtype_mk
          (fun τ => ⟨τ, rfl⟩) }

/-- The degree projection of the restricted simultaneous coordinate is the
original cyclotomic degree.  Keeping this pointwise boundary avoids unfolding
the closed-image package in downstream proofs. -/
theorem numberFieldTowerFinitePadicImageDegree_rangeRestriction_apply
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    numberFieldTowerFinitePadicImageDegree
        (K := K) (L := L) p
        (numberFieldTowerFinitePadicRangeRestriction
          (K := K) (L := L) p τ) =
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
        (K := K) (L := L) p τ :=
  rfl

/-- Restriction to the actual simultaneous-coordinate image is
surjective. -/
theorem numberFieldTowerFinitePadicRangeRestriction_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (numberFieldTowerFinitePadicRangeRestriction
        (K := K) (L := L) p) := by
  exact
    (numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p).toMonoidHom.rangeRestrict_surjective

/-- The inverse image in the compatible absolute Galois group of the
closed cyclic subgroup generated by one simultaneous finite/`p`-adic
coordinate. -/
noncomputable def numberFieldTowerFinitePadicCyclicPreimage
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ClosedSubgroup
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  exact
    { toSubgroup :=
        Γ.toSubgroup.comap
          rangeRestriction.toMonoidHom
      isClosed' :=
        Γ.isClosed'.preimage
          rangeRestriction.continuous_toFun }

/-- The simultaneous finite/cyclotomic coordinate has abelian image,
so the inverse image of the closed cyclic subgroup generated by one
coordinate is normal in the compatible absolute Galois group of `K`.

Consequently, the auxiliary fixed field constructed below is Galois
over the embedded copy of `K`, as in the field diagram of the
finite-place reduction. -/
theorem numberFieldTowerFinitePadicCyclicPreimage_normal
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ).toSubgroup.Normal := by
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  change
    (Γ.toSubgroup.comap
      rangeRestriction.toMonoidHom).Normal
  exact
    Γ.toSubgroup.normal_of_isMulCommutative.comap
      rangeRestriction.toMonoidHom

/-- A lift with nontrivial `p`-adic degree generates an open cyclic
preimage in the compatible absolute Galois group. -/
theorem numberFieldTowerFinitePadicCyclicPreimage_isOpen
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    IsOpen
      ((numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ :
        ClosedSubgroup
          (numberFieldTowerBaseSubgroup K L).toSubgroup) :
        Set (numberFieldTowerBaseSubgroup K L).toSubgroup) := by
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let : CompactSpace P.toSubgroup :=
    isCompact_iff_compactSpace.mp P.isClosed'.isCompact
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let finiteDegreeKernel : Finite degree.toMonoidHom.ker :=
    numberFieldTowerFinitePadicImageDegree_ker_finite
      (K := K) (L := L) p
  have hγ : degree γ ≠ 1 := by
    simpa only [degree, γ, rangeRestriction,
      numberFieldTowerFinitePadicImageDegree_rangeRestriction_apply] using hτ
  have hΓ :
      IsOpen
        ((ClassFormation.padicCyclicClosure γ :
            Subgroup P.toSubgroup) :
          Set P.toSubgroup) :=
    ClassFormation.padicCyclicClosure_isOpen_of_degree_ne_one
      p.1 degree γ hγ
  exact
    hΓ.preimage rangeRestriction.continuous_toFun

/-- For a lift whose finite coordinate is `p`-primary and whose
cyclotomic degree is a positive integer, the `p`-adic degree is
injective on its actual closed cyclic image. -/
theorem numberFieldTowerFinitePadicCyclicImageDegree_injective
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    let P :=
      numberFieldTowerFinitePadicImage
        (K := K) (L := L) p
    let γ : P.toSubgroup :=
      numberFieldTowerFinitePadicRangeRestriction
        (K := K) (L := L) p τ
    Function.Injective
      (((numberFieldTowerFinitePadicImageDegree
          (K := K) (L := L) p).comp
        (continuousSubgroupSubtype
          (ClassFormation.padicCyclicClosure γ).toSubgroup)) :
        ClassFormation.padicCyclicClosure γ →
          Multiplicative ℤ_[p.1]) := by
  dsimp only
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p τ
  let finiteProjection :
      P.toSubgroup →ₜ* Q :=
    { toFun := fun z => z.1.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        continuous_fst.comp continuous_subtype_val }
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let extensionSubgroupClosed : IsClosed (N : Set H.toSubgroup) :=
    extensionSubgroup_isClosed H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let extensionSubgroupFiniteIndex : N.FiniteIndex :=
    N.finiteIndex_of_finite_quotient
  let quotientDiscreteTopology : DiscreteTopology Q :=
    QuotientGroup.discreteTopology
      (N.isOpen_of_isClosed_of_finiteIndex
        extensionSubgroupClosed)
  obtain ⟨m, hm⟩ := hprimary
  apply
    ClassFormation.padicCyclicClosure_degree_injective_of_primePower_finiteCoordinate
        p.1 finiteProjection degree
        (γ := γ) (m := m) (n := n)
  · intro x y hxy
    apply Subtype.ext
    exact hxy
  · exact hn
  · exact hm
  · exact hdegree

/-- On a positive-degree lift with `p`-primary finite coordinate, the
intersection of its cyclic preimage with the cyclotomic `p`-adic
kernel already fixes `L`. -/
theorem
    numberFieldTowerFinitePadicCyclicPreimage_inf_padicKernel_le_extensionSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ⊓
        (numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p).toMonoidHom.ker ≤
      extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  have hinjective :=
    numberFieldTowerFinitePadicCyclicImageDegree_injective
      (K := K) (L := L) p τ n hn hdegree hprimary
  intro u hu
  let z : Γ.toSubgroup :=
    ⟨rangeRestriction u, hu.1⟩
  have hz : z = 1 := by
    apply hinjective
    change
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p u =
        1
    exact hu.2
  have hfinite :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) u =
        1 := by
    have hzfinite :=
      congrArg (fun w : Γ.toSubgroup => w.1.1.1) hz
    exact hzfinite
  exact
    (QuotientGroup.eq_one_iff (N := N) u).mp hfinite

/-- The cyclic preimage, embedded back into the rational absolute
Galois group.  Its fixed field is the concrete auxiliary number field
used in the finite-place reduction. -/
noncomputable def numberFieldTowerFinitePadicCyclicFixedSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ClosedSubgroup (Gal(SeparableClosure ℚ/ℚ)) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  exact
    { toSubgroup :=
        U.toSubgroup.map H.toSubgroup.subtype
      isClosed' := by
        change
          IsClosed
            (Subtype.val ''
              (U : Set H.toSubgroup))
        exact
          H.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap
            (U : Set H.toSubgroup) U.isClosed' }

/-- The distinguished simultaneous finite/cyclotomic lift itself lies
in the auxiliary subgroup whose fixed field is used for descent. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_generator_mem
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (τ : Gal(SeparableClosure ℚ/ℚ)) ∈
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  change
    (τ : Gal(SeparableClosure ℚ/ℚ)) ∈
      U.toSubgroup.map H.toSubgroup.subtype
  refine ⟨τ, ?_, rfl⟩
  change rangeRestriction τ ∈ Γ.toSubgroup
  exact
    (ClassFormation.padicCyclicClosureGenerator γ).2

/-- The auxiliary cyclic fixed subgroup lies in the subgroup fixing
the compatible embedded copy of `K`. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ≤
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  rintro _ ⟨u, _, rfl⟩
  exact u.2

/-- The auxiliary fixed field is Galois over the compatible embedded
copy of `K`.  On subgroup coordinates this is normality of the
embedded cyclic-preimage subgroup inside the base fixing subgroup. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
        (K := K) (L := L) p τ)).Normal := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let hSH :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  have hU : U.toSubgroup.Normal :=
    numberFieldTowerFinitePadicCyclicPreimage_normal
      (K := K) (L := L) p τ
  have hext :
      extensionSubgroup H S hSH =
        U.toSubgroup := by
    ext u
    rw [mem_extensionSubgroup_iff]
    change
      u.1 ∈ U.toSubgroup.map H.toSubgroup.subtype ↔
        u ∈ U.toSubgroup
    constructor
    · rintro ⟨z, hz, hzu⟩
      have hzu' : z = u :=
        Subtype.ext hzu
      exact hzu' ▸ hz
    · intro hu
      exact ⟨u, hu, rfl⟩
  exact hext.symm ▸ hU

/-- The relative subgroup defined by the ambient auxiliary fixed
subgroup is exactly the original cyclic preimage inside the compatible
absolute Galois group of `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extensionSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
          (K := K) (L := L) p τ) =
      (numberFieldTowerFinitePadicCyclicPreimage
        (K := K) (L := L) p τ).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  ext u
  rw [mem_extensionSubgroup_iff]
  change
    u.1 ∈ U.toSubgroup.map H.toSubgroup.subtype ↔
      u ∈ U.toSubgroup
  constructor
  · rintro ⟨z, hz, hzu⟩
    have hzu' : z = u :=
      Subtype.ext hzu
    exact hzu' ▸ hz
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- Ambient form of the kernel-intersection statement. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ⊓
        (rationalSeparableClosurePadicCyclotomicDegree
          p).toMonoidHom.ker ≤
      (numberFieldTowerTopSubgroup L).toSubgroup := by
  let T :=
    numberFieldTowerTopSubgroup L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  have hrelative :=
    numberFieldTowerFinitePadicCyclicPreimage_inf_padicKernel_le_extensionSubgroup
      (K := K) (L := L) p τ n hn hdegree hprimary
  intro σ hσ
  obtain ⟨u, huU, huσ⟩ := hσ.1
  have huDegree :
      u ∈
        (numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p).toMonoidHom.ker := by
    change
      rationalSeparableClosurePadicCyclotomicDegree
          p u.1 =
        1
    calc
      rationalSeparableClosurePadicCyclotomicDegree p u.1 =
          rationalSeparableClosurePadicCyclotomicDegree p σ :=
        congrArg
          (rationalSeparableClosurePadicCyclotomicDegree p) huσ
      _ = 1 := hσ.2
  have huN :=
    hrelative ⟨huU, huDegree⟩
  change σ ∈ T.toSubgroup
  exact huσ ▸ huN

/-- A nonzero-degree cyclic lift cuts out an open subgroup of the
rational absolute Galois group. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_isOpen
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    IsOpen
      ((numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ :
        ClosedSubgroup
          (Gal(SeparableClosure ℚ/ℚ))) :
        Set (Gal(SeparableClosure ℚ/ℚ))) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  change
    IsOpen
      (Subtype.val '' (U : Set H.toSubgroup))
  exact
    (numberFieldTowerBaseSubgroup_isOpen K L).isOpenMap_subtype_val
      (U : Set H.toSubgroup)
      (numberFieldTowerFinitePadicCyclicPreimage_isOpen
        (K := K) (L := L) p τ hτ)

/-- The auxiliary cyclic fixed subgroup as a genuine finite Galois
subextension of the compatible abstract field attached to `K`. -/
noncomputable def
    numberFieldTowerFinitePadicCyclicGaloisSubextension
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteGaloisSubextension
      (numberFieldTowerBaseSubgroup K L) where
  field :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  below :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  normal :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
      (K := K) (L := L) p τ
  finite := by
    rw [
      numberFieldTowerFinitePadicCyclicFixedSubgroup_extensionSubgroup
        (K := K) (L := L) p τ]
    exact
      Subgroup.quotient_finite_of_isOpen
        (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup
        (numberFieldTowerFinitePadicCyclicPreimage_isOpen
          (K := K) (L := L) p τ hτ)

/-- The auxiliary fixed subgroup, with its absolute finite-index
witness, as the finite abstract field used by fixed-field global
reciprocity. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryAbstractField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ((numberFieldTowerFinitePadicCyclicGaloisSubextension
      (K := K) (L := L) p τ hτ).toFiniteAbstractFieldExtension
    (K := numberFieldTowerFiniteAbstractField K L)).field

/-- Base change of `L / K` to the auxiliary cyclic fixed field.  Its
top subgroup is the intersection of the auxiliary fixing subgroup
with the subgroup fixing `L`, hence its concrete top field is the
auxiliary compositum with `L`. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    FiniteAbelianSubextension
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ) :=
  (numberFieldTowerFiniteAbelianSubextension K L).baseChange
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ)
    (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ)

/-- The auxiliary compositum is unramified for the genuine
cyclotomic degree datum.  The proof is the key `p`-primary
intersection: full cyclotomic inertia lies in every `p`-adic
cyclotomic kernel, and the latter intersection already fixes `L`. -/
theorem
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension_isUnramified
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).toFiniteGaloisExtension.IsUnramified
      rationalCyclotomicDegreeData := by
  let : Algebra ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField.algebra'
  let : @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' :=
    rationalCyclotomicZHatField_normal
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  apply
    (P.toFiniteGaloisExtension.isUnramified_iff_inertia_le
      rationalCyclotomicDegreeData).2
  intro σ hσ
  change σ ∈ S.toSubgroup ⊓ T.toSubgroup
  refine ⟨hσ.1, ?_⟩
  apply
    numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
      (K := K) (L := L) p τ n hn hdegree hprimary
  refine ⟨hσ.1, ?_⟩
  change
    rationalSeparableClosurePadicCyclotomicDegree p σ =
      1
  have hdegreeOne :
      rationalCyclotomicZHatFieldGalEquivZHat
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicZHatField σ) =
        1 := by
    exact hσ.2
  apply Multiplicative.toAdd.injective
  change
    zHatToPadicInt p
        (Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (AlgEquiv.restrictNormalHom
              rationalCyclotomicZHatField σ))) =
      (0 : ℤ_[p.1])
  have hdegreeAdd :=
    congrArg Multiplicative.toAdd hdegreeOne
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicZHatField σ)) =
      0 at hdegreeAdd
  rw [hdegreeAdd]
  exact map_zero (zHatToPadicInt p)

end Reciprocity
end GlobalClassFieldTheory
