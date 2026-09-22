/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.Augmentation
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.Transfer
/-!
# Transfer and relative augmentation quotients

This file constructs the transfer on abelianizations and the concrete
relative augmentation quotient

`(I_H + I_G I_H) / I_G I_H`.

The two vertical augmentation maps in the transfer square are developed
from the integral group rings themselves.
-/

open scoped Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace RelativeAugmentation

open GroupTheory.Augmentation
open Subgroup

variable {G : Type*} [Group G]

/-- Transfer from `G` to the abelianization of a finite-index subgroup. -/
noncomputable def transferToAbelianization
    (H : Subgroup G) [H.FiniteIndex] :
    G →* Abelianization H :=
  MonoidHom.transfer (Abelianization.of : H →* Abelianization H)

/-- The transfer factors through the abelianization of `G`. -/
noncomputable def abelianizedTransfer
    (H : Subgroup G) [H.FiniteIndex] :
    Abelianization G →* Abelianization H :=
  Abelianization.lift (transferToAbelianization H)

@[simp]
theorem abelianizedTransfer_of
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    abelianizedTransfer H (Abelianization.of g) =
      transferToAbelianization H g :=
  rfl

/-- The explicit transversal formula for the top horizontal map in
the relative augmentation construction. -/
theorem abelianizedTransfer_of_eq_diff
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    abelianizedTransfer H (Abelianization.of g) =
      Subgroup.leftTransversals.diff
        (Abelianization.of : H →* Abelianization H)
        T (g • T) := by
  exact MonoidHom.transfer_def
    (Abelianization.of : H →* Abelianization H) T g

/-- The inclusion of the subgroup ring `ℤ[H]` into `ℤ[G]`. -/
def subgroupRingMap (H : Subgroup G) :
    IntegralGroupRing H →+* IntegralGroupRing G :=
  MonoidAlgebra.mapDomainRingHom ℤ H.subtype

@[simp]
theorem subgroupRingMap_single
    (H : Subgroup G) (h : H) (n : ℤ) :
    subgroupRingMap H (MonoidAlgebra.single h n) =
      MonoidAlgebra.single (h : G) n := by
  simp [subgroupRingMap]

theorem subgroupRingMap_injective
    (H : Subgroup G) :
    Function.Injective (subgroupRingMap H) :=
  MonoidAlgebra.mapDomain_injective H.subtype_injective

/-- The additive embedding `I_H → ℤ[G]`. -/
def subgroupIdealEmbedding (H : Subgroup G) :
    ideal H →+ IntegralGroupRing G where
  toFun x := subgroupRingMap H (x : IntegralGroupRing H)
  map_zero' := (subgroupRingMap H).map_zero
  map_add' x y := (subgroupRingMap H).map_add x y

theorem subgroupIdealEmbedding_injective
    (H : Subgroup G) :
    Function.Injective (subgroupIdealEmbedding H) := by
  intro x y hxy
  apply Subtype.ext
  exact subgroupRingMap_injective H hxy

/-- Evaluation of the subgroup-ideal embedding in the ambient group ring. -/
@[simp]
theorem subgroupIdealEmbedding_apply
    (H : Subgroup G) (x : ideal H) :
    subgroupIdealEmbedding H x =
      subgroupRingMap H (x : IntegralGroupRing H) :=
  rfl

/-- The embedded copy of `I_H` in `ℤ[G]`. -/
def embeddedSubgroupIdeal (H : Subgroup G) :
    AddSubgroup (IntegralGroupRing G) :=
  (subgroupIdealEmbedding H).range

/-- The additive product `I_G I_H` occurring in the relative augmentation construction. -/
def mixedAugmentationProduct (H : Subgroup G) :
    AddSubgroup (IntegralGroupRing G) :=
  AddSubgroup.closure
    {z | ∃ x ∈ ideal G, ∃ y ∈ embeddedSubgroupIdeal H,
      z = x * y}

/-- The numerator `I_H + I_G I_H`. -/
def relativeAugmentationNumerator (H : Subgroup G) :
    AddSubgroup (IntegralGroupRing G) :=
  embeddedSubgroupIdeal H ⊔ mixedAugmentationProduct H

/-- The denominator, viewed inside the numerator. -/
def mixedProductInNumerator (H : Subgroup G) :
    AddSubgroup (relativeAugmentationNumerator H) where
  carrier :=
    {x | (x : IntegralGroupRing G) ∈ mixedAugmentationProduct H}
  zero_mem' := (mixedAugmentationProduct H).zero_mem
  add_mem' := (mixedAugmentationProduct H).add_mem
  neg_mem' := (mixedAugmentationProduct H).neg_mem

/-- Membership in the mixed product after forgetting the relative-numerator
subtype. -/
@[simp]
theorem mem_mixedProductInNumerator_iff
    (H : Subgroup G) (x : relativeAugmentationNumerator H) :
    x ∈ mixedProductInNumerator H ↔
      (x : IntegralGroupRing G) ∈ mixedAugmentationProduct H :=
  Iff.rfl

/-- The lower-right group in the diagram of the relative augmentation construction. -/
abbrev RelativeAugmentationQuotient (H : Subgroup G) :=
  relativeAugmentationNumerator H ⧸ mixedProductInNumerator H

/-- The element `h - 1`, embedded from `ℤ[H]` into `ℤ[G]`. -/
def embeddedDelta (H : Subgroup G) (h : H) :
    IntegralGroupRing G :=
  subgroupRingMap H (deltaElement H h : IntegralGroupRing H)

@[simp]
theorem embeddedDelta_eq (H : Subgroup G) (h : H) :
    embeddedDelta H h =
      (deltaElement G (h : G) : IntegralGroupRing G) := by
  simp [embeddedDelta, deltaElement]

theorem embeddedDelta_mem_ideal
    (H : Subgroup G) (h : H) :
    embeddedDelta H h ∈ ideal G := by
  rw [embeddedDelta_eq]
  exact (deltaElement G (h : G)).property

theorem embeddedDelta_mem_embeddedSubgroupIdeal
    (H : Subgroup G) (h : H) :
    embeddedDelta H h ∈ embeddedSubgroupIdeal H :=
  ⟨deltaElement H h, rfl⟩

/-- The relative augmentation element in the numerator. -/
def relativeDeltaElement (H : Subgroup G) (h : H) :
    relativeAugmentationNumerator H :=
  ⟨embeddedDelta H h,
    AddSubgroup.mem_sup_left
      (embeddedDelta_mem_embeddedSubgroupIdeal H h)⟩

/-- The class of `h - 1` in
`(I_H + I_G I_H) / I_G I_H`. -/
def relativeDeltaClass (H : Subgroup G) (h : H) :
    RelativeAugmentationQuotient H :=
  QuotientAddGroup.mk' (mixedProductInNumerator H)
    (relativeDeltaElement H h)

@[simp]
theorem relativeDeltaClass_one (H : Subgroup G) :
    relativeDeltaClass H 1 = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  rw [mem_mixedProductInNumerator_iff]
  change embeddedDelta H 1 ∈ mixedAugmentationProduct H
  rw [embeddedDelta_eq]
  simp

/-- The relative identity `δ(hk)=δh+δk` modulo `I_G I_H`. -/
theorem relativeDeltaClass_mul
    (H : Subgroup G) (h k : H) :
    relativeDeltaClass H (h * k) =
      relativeDeltaClass H h + relativeDeltaClass H k := by
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  rw [mem_mixedProductInNumerator_iff]
  change
    embeddedDelta H (h * k) -
        (embeddedDelta H h + embeddedDelta H k) ∈
      mixedAugmentationProduct H
  have hprod :
      embeddedDelta H h * embeddedDelta H k ∈
        mixedAugmentationProduct H :=
    AddSubgroup.subset_closure
      ⟨embeddedDelta H h,
        embeddedDelta_mem_ideal H h,
        embeddedDelta H k,
        embeddedDelta_mem_embeddedSubgroupIdeal H k,
        rfl⟩
  convert hprod using 1
  simp only [embeddedDelta_eq, deltaElement_val]
  have hsingle :
      MonoidAlgebra.single ((h * k : H) : G) (1 : ℤ) =
        MonoidAlgebra.single (h : G) 1 *
          MonoidAlgebra.single (k : G) 1 := by
    simp
  rw [hsingle, ← MonoidAlgebra.one_def]
  noncomm_ring

/-- Multiplicative form of the relative augmentation map. -/
def relativeDeltaMonoidHom (H : Subgroup G) :
    H →* Multiplicative (RelativeAugmentationQuotient H) where
  toFun h := Multiplicative.ofAdd (relativeDeltaClass H h)
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact relativeDeltaClass_one H
  map_mul' h k := by
    apply Multiplicative.toAdd.injective
    exact relativeDeltaClass_mul H h k

/-- The right vertical augmentation map in the relative augmentation construction. -/
def relativeDeltaAbelianization (H : Subgroup G) :
    Abelianization H →*
      Multiplicative (RelativeAugmentationQuotient H) :=
  Abelianization.lift (relativeDeltaMonoidHom H)

@[simp]
theorem relativeDeltaAbelianization_of
    (H : Subgroup G) (h : H) :
    relativeDeltaAbelianization H (Abelianization.of h) =
      Multiplicative.ofAdd (relativeDeltaClass H h) :=
  rfl

/-- The `H`-component of `g` with respect to a left transversal. -/
def transversalComponent
    (H : Subgroup G) (T : H.LeftTransversal) (g : G) : H :=
  ⟨((T.2.toLeftFun g : G)⁻¹ * g),
    T.2.inv_toLeftFun_mul_mem g⟩

theorem transversalComponent_mul_right
    (H : Subgroup G) (T : H.LeftTransversal)
    (g : G) (h : H) :
    transversalComponent H T (g * (h : G)) =
      transversalComponent H T g * h := by
  have hcoset :
      (QuotientGroup.mk (g * (h : G)) : G ⧸ H) =
        QuotientGroup.mk g := by
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    simp [mul_assoc, H.inv_mem h.property]
  have hrep :
      T.2.toLeftFun (g * (h : G)) =
        T.2.toLeftFun g := by
    exact congrArg T.2.leftQuotientEquiv hcoset
  apply Subtype.ext
  change
    (T.2.toLeftFun (g * (h : G)) : G)⁻¹ *
        (g * (h : G)) =
      ((T.2.toLeftFun g : G)⁻¹ * g) * (h : G)
  rw [hrep]
  exact
    (mul_assoc ((T.2.toLeftFun g : G)⁻¹) g (h : G)).symm

/-- A coefficient at `g` records its transversal `H`-component in
`Hᵃᵇ`. -/
def transversalCoefficientToAbelianization
    (H : Subgroup G) (T : H.LeftTransversal) (g : G) :
    ℤ →+ Additive (Abelianization H) where
  toFun n :=
    n • Additive.ofMul
      (Abelianization.of (transversalComponent H T g))
  map_zero' := zero_zsmul _
  map_add' _ _ := add_zsmul _ _ _

/-- Transversal linearization of `ℤ[G]` in `Hᵃᵇ`. -/
def transversalLinearization
    (H : Subgroup G) (T : H.LeftTransversal) :
    IntegralGroupRing G →+ Additive (Abelianization H) :=
  ((Finsupp.liftAddHom
      (α := G) (M := ℤ)
      (N := Additive (Abelianization H)))
      (transversalCoefficientToAbelianization H T)).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp]
theorem transversalLinearization_single
    (H : Subgroup G) (T : H.LeftTransversal)
    (g : G) (n : ℤ) :
    transversalLinearization H T
        (MonoidAlgebra.single g n) =
      n • Additive.ofMul
        (Abelianization.of (transversalComponent H T g)) := by
  simp [transversalLinearization,
    transversalCoefficientToAbelianization]

/-- On the embedded subgroup ideal, transversal linearization is the
ordinary abelianization linearization. -/
theorem transversalLinearization_embeddedDelta
    (H : Subgroup G) (T : H.LeftTransversal) (h : H) :
    transversalLinearization H T (embeddedDelta H h) =
      Additive.ofMul (Abelianization.of h) := by
  have hc :=
    transversalComponent_mul_right H T (1 : G) h
  rw [embeddedDelta_eq]
  simp only [deltaElement_val, map_sub,
    transversalLinearization_single, one_zsmul]
  rw [show transversalComponent H T (h : G) =
      transversalComponent H T 1 * h by simpa using hc]
  simp

/-- A basic generator of `I_G I_H` is killed by transversal
linearization. -/
theorem transversalLinearization_delta_mul_embeddedDelta
    (H : Subgroup G) (T : H.LeftTransversal)
    (g : G) (h : H) :
    transversalLinearization H T
        ((deltaElement G g : IntegralGroupRing G) *
          embeddedDelta H h) =
      0 := by
  have hcg :=
    transversalComponent_mul_right H T g h
  have hc1 :=
    transversalComponent_mul_right H T (1 : G) h
  rw [embeddedDelta_eq]
  simp only [deltaElement_val, mul_sub, sub_mul, map_sub,
    MonoidAlgebra.single_mul_single,
    transversalLinearization_single, one_mul, one_zsmul]
  rw [show transversalComponent H T (g * (h : G)) =
      transversalComponent H T g * h by
        simpa using hcg]
  rw [show transversalComponent H T (h : G) =
      transversalComponent H T 1 * h by
        simpa using hc1]
  simp

/-- Transversal linearization kills a product of an augmentation-zero
element of `ℤ[G]` with an embedded augmentation-zero element of
`ℤ[H]`. -/
theorem transversalLinearization_mul_eq_zero
    (H : Subgroup G) (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G)
    (y : IntegralGroupRing G) (hy : y ∈ embeddedSubgroupIdeal H) :
    transversalLinearization H T (x * y) = 0 := by
  rcases hy with ⟨yH, rfl⟩
  rw [← deltaCombination_eq_of_mem_ideal G x hx]
  have hycomb :=
    deltaCombination_eq_of_mem_ideal H
      (yH : IntegralGroupRing H) yH.property
  rw [subgroupIdealEmbedding_apply, ← hycomb]
  simp only [deltaCombination, map_sum, map_zsmul]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro g hg
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro h hh
  change
    transversalLinearization H T
        ((x.coeff g •
            (deltaElement G g : IntegralGroupRing G)) *
          (yH.1.coeff h • embeddedDelta H h)) =
      0
  rw [smul_mul_smul_comm, map_zsmul,
    transversalLinearization_delta_mul_embeddedDelta, smul_zero]

/-- Transversal linearization vanishes on `I_G I_H`. -/
theorem transversalLinearization_eq_zero_of_mem_mixed
    (H : Subgroup G) (T : H.LeftTransversal)
    (z : IntegralGroupRing G)
    (hz : z ∈ mixedAugmentationProduct H) :
    transversalLinearization H T z = 0 := by
  rw [mixedAugmentationProduct] at hz
  refine AddSubgroup.closure_induction
    (p := fun z _ => transversalLinearization H T z = 0)
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨x, hx, y, hy, rfl⟩
    exact transversalLinearization_mul_eq_zero
      H T x hx y hy
  · exact map_zero (transversalLinearization H T)
  · intro x y hx hy hlinx hliny
    rw [map_add, hlinx, hliny, add_zero]
  · intro x hx hlin
    rw [map_neg, hlin, neg_zero]

/-- Transversal linearization restricted to
`I_H + I_G I_H`. -/
def relativeLinearizationOnNumerator
    (H : Subgroup G) (T : H.LeftTransversal) :
    relativeAugmentationNumerator H →+
      Additive (Abelianization H) where
  toFun x :=
    transversalLinearization H T
      (x : IntegralGroupRing G)
  map_zero' := (transversalLinearization H T).map_zero
  map_add' x y := (transversalLinearization H T).map_add x y

/-- The inverse linearization on the relative augmentation quotient. -/
def relativeQuotientLinearization
    (H : Subgroup G) (T : H.LeftTransversal) :
    RelativeAugmentationQuotient H →+
      Additive (Abelianization H) :=
  QuotientAddGroup.lift
    (mixedProductInNumerator H)
    (relativeLinearizationOnNumerator H T) (by
      intro x hx
      apply AddMonoidHom.mem_ker.2
      exact transversalLinearization_eq_zero_of_mem_mixed
        H T x hx)

@[simp]
theorem relativeQuotientLinearization_deltaClass
    (H : Subgroup G) (T : H.LeftTransversal) (h : H) :
    relativeQuotientLinearization H T
        (relativeDeltaClass H h) =
      Additive.ofMul (Abelianization.of h) := by
  exact transversalLinearization_embeddedDelta H T h

/-- Multiplicative form of inverse relative linearization. -/
def relativeQuotientLinearizationMonoidHom
    (H : Subgroup G) (T : H.LeftTransversal) :
    Multiplicative (RelativeAugmentationQuotient H) →*
      Abelianization H :=
  (relativeQuotientLinearization H T).toMultiplicativeLeft

@[simp]
theorem relativeQuotientLinearizationMonoidHom_deltaClass
    (H : Subgroup G) (T : H.LeftTransversal) (h : H) :
    relativeQuotientLinearizationMonoidHom H T
        (Multiplicative.ofAdd (relativeDeltaClass H h)) =
      Abelianization.of h := by
  exact congrArg Additive.toMul
    (relativeQuotientLinearization_deltaClass H T h)

theorem relativeQuotientLinearizationMonoidHom_deltaAbelianization
    (H : Subgroup G) (T : H.LeftTransversal)
    (a : Abelianization H) :
    relativeQuotientLinearizationMonoidHom H T
        (relativeDeltaAbelianization H a) =
      a := by
  refine QuotientGroup.induction_on a ?_
  intro h
  exact
    relativeQuotientLinearizationMonoidHom_deltaClass
      H T h

/-- The right vertical augmentation map is injective. -/
theorem relativeDeltaAbelianization_injective
    (H : Subgroup G) :
    Function.Injective (relativeDeltaAbelianization H) := by
  let T : H.LeftTransversal := default
  intro a b hab
  have h :=
    congrArg
      (relativeQuotientLinearizationMonoidHom H T) hab
  rw [
    relativeQuotientLinearizationMonoidHom_deltaAbelianization
      H T a,
    relativeQuotientLinearizationMonoidHom_deltaAbelianization
      H T b] at h
  exact h

/-- An embedded augmentation-ideal element, intrinsically valued in the
relative numerator. -/
def embeddedIdealElement
    (H : Subgroup G) (x : IntegralGroupRing H)
    (hx : x ∈ ideal H) :
    relativeAugmentationNumerator H :=
  ⟨subgroupRingMap H x,
    AddSubgroup.mem_sup_left
      (show subgroupRingMap H x ∈ embeddedSubgroupIdeal H from
        ⟨⟨x, hx⟩, rfl⟩)⟩

/-- The coefficient expression supplies a preimage for every embedded
augmentation-ideal element. -/
theorem relativeDeltaAbelianization_deltaPreimage
    (H : Subgroup G) (x : IntegralGroupRing H)
    (hx : x ∈ ideal H) :
    relativeDeltaAbelianization H (deltaPreimage H x) =
      Multiplicative.ofAdd
        (QuotientAddGroup.mk' (mixedProductInNumerator H)
          (embeddedIdealElement H x hx)) := by
  apply Multiplicative.toAdd.injective
  change
    Multiplicative.toAdd
        (relativeDeltaAbelianization H (deltaPreimage H x)) =
      QuotientAddGroup.mk' (mixedProductInNumerator H)
        (embeddedIdealElement H x hx)
  rw [deltaPreimage, map_prod]
  simp_rw [map_zpow, relativeDeltaAbelianization_of]
  change
    ∑ h ∈ x.coeff.support,
        x.coeff h • relativeDeltaClass H h =
      QuotientAddGroup.mk' (mixedProductInNumerator H)
        (embeddedIdealElement H x hx)
  change
    ∑ h ∈ x.coeff.support,
        x.coeff h •
          QuotientAddGroup.mk' (mixedProductInNumerator H)
            (relativeDeltaElement H h) =
      QuotientAddGroup.mk' (mixedProductInNumerator H)
        (embeddedIdealElement H x hx)
  simp_rw [← map_zsmul]
  rw [← map_sum]
  apply congrArg
    (QuotientAddGroup.mk' (mixedProductInNumerator H))
  apply Subtype.ext
  calc
    (↑(∑ h ∈ x.coeff.support,
          x.coeff h • relativeDeltaElement H h) :
        IntegralGroupRing G) =
        ∑ h ∈ x.coeff.support,
          x.coeff h • embeddedDelta H h := by
            simp [relativeDeltaElement]
    _ = subgroupRingMap H (deltaCombination H x) := by
      simp [deltaCombination, embeddedDelta]
    _ = subgroupRingMap H x := by
      rw [deltaCombination_eq_of_mem_ideal H x hx]
    _ = (embeddedIdealElement H x hx :
        IntegralGroupRing G) :=
      rfl

/-- The right vertical augmentation map is surjective. -/
theorem relativeDeltaAbelianization_surjective
    (H : Subgroup G) :
    Function.Surjective (relativeDeltaAbelianization H) := by
  intro q
  change
    ∃ a : Abelianization H,
      relativeDeltaAbelianization H a =
        Multiplicative.ofAdd (Multiplicative.toAdd q)
  refine
    QuotientAddGroup.induction_on
      (Multiplicative.toAdd q) ?_
  intro z
  rcases (AddSubgroup.mem_sup.mp z.property) with
    ⟨e, he, m, hm, hem⟩
  rcases he with ⟨yH, rfl⟩
  refine
    ⟨deltaPreimage H (yH : IntegralGroupRing H), ?_⟩
  rw [relativeDeltaAbelianization_deltaPreimage
    H (yH : IntegralGroupRing H) yH.property]
  apply Multiplicative.toAdd.injective
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  rw [mem_mixedProductInNumerator_iff]
  change
    subgroupRingMap H (yH : IntegralGroupRing H) -
        (z : IntegralGroupRing G) ∈
      mixedAugmentationProduct H
  have hem' :
      subgroupRingMap H (yH : IntegralGroupRing H) + m =
        (z : IntegralGroupRing G) := by
    exact hem
  rw [← hem']
  simpa using (mixedAugmentationProduct H).neg_mem hm

/-- The right vertical isomorphism in the diagram of the relative augmentation construction. -/
noncomputable def relativeDeltaAbelianizationEquiv
    (H : Subgroup G) :
    Abelianization H ≃*
      Multiplicative (RelativeAugmentationQuotient H) :=
  MulEquiv.ofBijective (relativeDeltaAbelianization H)
    ⟨relativeDeltaAbelianization_injective H,
      relativeDeltaAbelianization_surjective H⟩

@[simp]
theorem relativeDeltaAbelianizationEquiv_apply
    (H : Subgroup G) (a : Abelianization H) :
    relativeDeltaAbelianizationEquiv H a =
      relativeDeltaAbelianization H a :=
  rfl

@[simp]
theorem relativeDeltaAbelianizationEquiv_of
    (H : Subgroup G) (h : H) :
    relativeDeltaAbelianizationEquiv H
        (Abelianization.of h) =
      Multiplicative.ofAdd (relativeDeltaClass H h) :=
  rfl

/-- The lower horizontal map in the relative augmentation construction, obtained from transfer
through
the two canonical augmentation isomorphisms. -/
noncomputable def augmentationTransfer
    (H : Subgroup G) [H.FiniteIndex] :
    Multiplicative (Quotient G) →*
      Multiplicative (RelativeAugmentationQuotient H) :=
  (relativeDeltaAbelianization H).comp
    ((abelianizedTransfer H).comp
      (deltaAbelianizationEquiv G).symm.toMonoidHom)

/-- Evaluation of the lower transfer map before using the augmentation
isomorphism. -/
@[simp]
theorem augmentationTransfer_apply
    (H : Subgroup G) [H.FiniteIndex]
    (q : Multiplicative (Quotient G)) :
    augmentationTransfer H q =
      relativeDeltaAbelianization H
        (abelianizedTransfer H
          ((deltaAbelianizationEquiv G).symm q)) :=
  rfl

/-- Commutativity of the transfer/augmentation square. -/
theorem augmentationTransfer_deltaAbelianization
    (H : Subgroup G) [H.FiniteIndex]
    (a : Abelianization G) :
    augmentationTransfer H (deltaAbelianization G a) =
      relativeDeltaAbelianization H
        (abelianizedTransfer H a) := by
  rw [augmentationTransfer_apply,
    ← deltaAbelianizationEquiv_apply G a,
    MulEquiv.symm_apply_apply]

theorem augmentationTransfer_deltaClass
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    augmentationTransfer H
        (Multiplicative.ofAdd (deltaClass G g)) =
      relativeDeltaAbelianization H
        (transferToAbelianization H g) := by
  rw [← deltaAbelianization_of]
  exact augmentationTransfer_deltaAbelianization H
    (Abelianization.of g)

/-- The representative of a left coset selected by `T`. -/
def leftRepresentative
    (H : Subgroup G) (T : H.LeftTransversal)
    (q : G ⧸ H) : G :=
  T.2.leftQuotientEquiv q

/-- The `H`-factor comparing `T` with its translate by `g`. -/
def transferComponent
    (H : Subgroup G) (T : H.LeftTransversal)
    (g : G) (q : G ⧸ H) : H :=
  ⟨(leftRepresentative H T q)⁻¹ *
      leftRepresentative H (g • T) q,
    QuotientGroup.leftRel_apply.mp <|
      Quotient.exact' <|
        (T.2.leftQuotientEquiv.symm_apply_apply q).trans
          ((g • T).2.leftQuotientEquiv.symm_apply_apply q).symm⟩

theorem leftRepresentative_mul_transferComponent
    (H : Subgroup G) (T : H.LeftTransversal)
    (g : G) (q : G ⧸ H) :
    leftRepresentative H T q *
        (transferComponent H T g q : G) =
      leftRepresentative H (g • T) q := by
  simp [transferComponent, leftRepresentative]

/-- The transfer is the product of the transversal components. -/
theorem abelianizedTransfer_of_eq_prod_transferComponent
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    abelianizedTransfer H (Abelianization.of g) =
      letI := H.fintypeQuotientOfFiniteIndex
      ∏ q : G ⧸ H,
        Abelianization.of (transferComponent H T g q) := by
  let := H.fintypeQuotientOfFiniteIndex
  rw [abelianizedTransfer_of_eq_diff H T g]
  rfl

/-- The group-ring norm element attached to a left transversal. -/
def transversalNormElement
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) :
    IntegralGroupRing G :=
  letI := H.fintypeQuotientOfFiniteIndex
  ∑ q : G ⧸ H,
    MonoidAlgebra.single (leftRepresentative H T q) 1

/-- Translating a transversal translates its group-ring sum. -/
theorem sum_shifted_leftRepresentatives
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    ∑ q : G ⧸ H,
        MonoidAlgebra.single
          (leftRepresentative H (g • T) q) (1 : ℤ) =
      MonoidAlgebra.single g 1 *
        transversalNormElement H T := by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    ∑ q : G ⧸ H,
        MonoidAlgebra.single
          (leftRepresentative H (g • T) q) (1 : ℤ) =
        ∑ q : G ⧸ H,
          MonoidAlgebra.single
            (leftRepresentative H (g • T) (g • q)) 1 := by
              exact
                (Equiv.sum_comp (MulAction.toPerm g)
                  (fun q : G ⧸ H =>
                    MonoidAlgebra.single
                      (leftRepresentative H (g • T) q)
                      (1 : ℤ))).symm
    _ = ∑ q : G ⧸ H,
          MonoidAlgebra.single
            (g * leftRepresentative H T q) 1 := by
              apply Finset.sum_congr rfl
              intro q _
              congr 2
              exact
                (Subgroup.smul_leftQuotientEquiv
                  g T q).symm
    _ = MonoidAlgebra.single g 1 *
        transversalNormElement H T := by
          simp [transversalNormElement,
            Finset.mul_sum]

/-- Multiplying an embedded augmentation difference by a transversal
representative stays in `I_H + I_G I_H`. -/
theorem single_mul_embeddedDelta_mem_numerator
    (H : Subgroup G) (r : G) (h : H) :
    MonoidAlgebra.single r 1 * embeddedDelta H h ∈
      relativeAugmentationNumerator H := by
  have hmixed :
      (deltaElement G r : IntegralGroupRing G) *
          embeddedDelta H h ∈
        mixedAugmentationProduct H :=
    AddSubgroup.subset_closure
      ⟨(deltaElement G r : IntegralGroupRing G),
        (deltaElement G r).property,
        embeddedDelta H h,
        embeddedDelta_mem_embeddedSubgroupIdeal H h,
        rfl⟩
  have hsum :
      embeddedDelta H h +
          (deltaElement G r : IntegralGroupRing G) *
            embeddedDelta H h ∈
        relativeAugmentationNumerator H :=
    (relativeAugmentationNumerator H).add_mem
      (AddSubgroup.mem_sup_left
        (embeddedDelta_mem_embeddedSubgroupIdeal H h))
      (AddSubgroup.mem_sup_right hmixed)
  convert hsum using 1
  simp only [deltaElement_val]
  rw [← MonoidAlgebra.one_def]
  noncomm_ring

/-- The group-ring element `δg · ∑ρ` belongs to the relative
augmentation numerator. -/
theorem delta_mul_transversalNormElement_mem_numerator
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    (deltaElement G g : IntegralGroupRing G) *
        transversalNormElement H T ∈
      relativeAugmentationNumerator H := by
  let := H.fintypeQuotientOfFiniteIndex
  have hsum :
      ∑ q : G ⧸ H,
          MonoidAlgebra.single
              (leftRepresentative H T q) 1 *
            embeddedDelta H (transferComponent H T g q) ∈
        relativeAugmentationNumerator H := by
    apply AddSubgroup.sum_mem
    intro q _
    exact single_mul_embeddedDelta_mem_numerator H
      (leftRepresentative H T q)
      (transferComponent H T g q)
  convert hsum using 1
  simp only [embeddedDelta_eq, deltaElement_val]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [MonoidAlgebra.single_mul_single]
  simp only [mul_one]
  simp_rw [leftRepresentative_mul_transferComponent H T g]
  rw [sum_shifted_leftRepresentatives H T g]
  simp [transversalNormElement, sub_mul, Finset.mul_sum]

/-- The group-ring identity underlying the norm-element formula. -/
theorem delta_mul_transversalNormElement_eq_sum
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    (deltaElement G g : IntegralGroupRing G) *
        transversalNormElement H T =
      ∑ q : G ⧸ H,
        MonoidAlgebra.single
            (leftRepresentative H T q) 1 *
          embeddedDelta H (transferComponent H T g q) := by
  let := H.fintypeQuotientOfFiniteIndex
  simp only [embeddedDelta_eq, deltaElement_val]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [MonoidAlgebra.single_mul_single]
  simp only [mul_one]
  simp_rw [leftRepresentative_mul_transferComponent H T g]
  rw [sum_shifted_leftRepresentatives H T g]
  simp [transversalNormElement, sub_mul, Finset.mul_sum]

/-- A single summand in the norm formula, intrinsically valued in the
relative numerator. -/
def singleMulEmbeddedDeltaElement
    (H : Subgroup G) (r : G) (h : H) :
    relativeAugmentationNumerator H :=
  ⟨MonoidAlgebra.single r 1 * embeddedDelta H h,
    single_mul_embeddedDelta_mem_numerator H r h⟩

/-- Multiplying by a representative does not change an embedded
augmentation class modulo `I_G I_H`. -/
theorem mk_singleMulEmbeddedDeltaElement_eq_relativeDeltaClass
    (H : Subgroup G) (r : G) (h : H) :
    QuotientAddGroup.mk' (mixedProductInNumerator H)
        (singleMulEmbeddedDeltaElement H r h) =
      relativeDeltaClass H h := by
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  rw [mem_mixedProductInNumerator_iff]
  change
    MonoidAlgebra.single r 1 * embeddedDelta H h -
        embeddedDelta H h ∈
      mixedAugmentationProduct H
  have hmixed :
      (deltaElement G r : IntegralGroupRing G) *
          embeddedDelta H h ∈
        mixedAugmentationProduct H :=
    AddSubgroup.subset_closure
      ⟨(deltaElement G r : IntegralGroupRing G),
        (deltaElement G r).property,
        embeddedDelta H h,
        embeddedDelta_mem_embeddedSubgroupIdeal H h,
        rfl⟩
  convert hmixed using 1
  simp only [deltaElement_val]
  rw [← MonoidAlgebra.one_def]
  noncomm_ring

/-- The element `δg · ∑ρ`, intrinsically in the relative numerator. -/
def deltaNormElement
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    relativeAugmentationNumerator H :=
  ⟨(deltaElement G g : IntegralGroupRing G) *
      transversalNormElement H T,
    delta_mul_transversalNormElement_mem_numerator H T g⟩

/-- Its class in the lower-right quotient. -/
def deltaNormClass
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    RelativeAugmentationQuotient H :=
  QuotientAddGroup.mk' (mixedProductInNumerator H)
    (deltaNormElement H T g)

/-- Evaluation of vanishing for the norm class in the concrete mixed
augmentation product. -/
theorem deltaNormClass_eq_zero_iff
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    deltaNormClass H T g = 0 ↔
      (deltaElement G g : IntegralGroupRing G) *
          transversalNormElement H T ∈
        mixedAugmentationProduct H :=
  QuotientAddGroup.eq_zero_iff _

/-- The sum of transfer-component augmentation classes is the class of
`δg · ∑ρ`. -/
theorem sum_relativeDeltaClass_transferComponent_eq_deltaNormClass
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    ∑ q : G ⧸ H,
        relativeDeltaClass H (transferComponent H T g q) =
      deltaNormClass H T g := by
  let := H.fintypeQuotientOfFiniteIndex
  calc
    ∑ q : G ⧸ H,
        relativeDeltaClass H (transferComponent H T g q) =
        ∑ q : G ⧸ H,
          QuotientAddGroup.mk' (mixedProductInNumerator H)
            (singleMulEmbeddedDeltaElement H
              (leftRepresentative H T q)
              (transferComponent H T g q)) := by
                apply Finset.sum_congr rfl
                intro q _
                exact
                  (mk_singleMulEmbeddedDeltaElement_eq_relativeDeltaClass
                    H (leftRepresentative H T q)
                    (transferComponent H T g q)).symm
    _ = QuotientAddGroup.mk' (mixedProductInNumerator H)
          (∑ q : G ⧸ H,
            singleMulEmbeddedDeltaElement H
              (leftRepresentative H T q)
              (transferComponent H T g q)) := by
            rw [map_sum]
    _ = deltaNormClass H T g := by
      apply congrArg
        (QuotientAddGroup.mk' (mixedProductInNumerator H))
      apply Subtype.ext
      simpa [singleMulEmbeddedDeltaElement,
        deltaNormElement] using
          (delta_mul_transversalNormElement_eq_sum
            H T g).symm

/-- **The norm-element formula.**
On the class of `g-1`, the lower horizontal map is multiplication by
the sum of a left transversal. -/
theorem augmentationTransfer_deltaClass_eq_deltaNorm
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal) (g : G) :
    augmentationTransfer H
        (Multiplicative.ofAdd (deltaClass G g)) =
      Multiplicative.ofAdd (deltaNormClass H T g) := by
  rw [augmentationTransfer_deltaClass]
  rw [← abelianizedTransfer_of H g,
    abelianizedTransfer_of_eq_prod_transferComponent H T g,
    map_prod]
  let := H.fintypeQuotientOfFiniteIndex
  exact congrArg Multiplicative.ofAdd
    (sum_relativeDeltaClass_transferComponent_eq_deltaNormClass H T g)

/-- Multiplication of an arbitrary augmentation-zero group-ring element
by the transversal norm stays in the relative numerator. -/
theorem ideal_mul_transversalNormElement_mem_numerator
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G) :
    x * transversalNormElement H T ∈
      relativeAugmentationNumerator H := by
  rw [← deltaCombination_eq_of_mem_ideal G x hx]
  unfold deltaCombination
  rw [Finset.sum_mul]
  apply AddSubgroup.sum_mem
  intro g hg
  rw [smul_mul_assoc]
  exact
    (relativeAugmentationNumerator H).zsmul_mem
      (delta_mul_transversalNormElement_mem_numerator
        H T g) (x.coeff g)

/-- The group-ring norm multiple of `x`, intrinsically in the relative
numerator. -/
def idealNormElement
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G) :
    relativeAugmentationNumerator H :=
  ⟨x * transversalNormElement H T,
    ideal_mul_transversalNormElement_mem_numerator
      H T x hx⟩

/-- The class of `x · ∑ρ` in the relative augmentation quotient. -/
def idealNormClass
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G) :
    RelativeAugmentationQuotient H :=
  QuotientAddGroup.mk' (mixedProductInNumerator H)
    (idealNormElement H T x hx)

/-- The coefficient decomposition of the general norm-element class. -/
theorem sum_deltaNormClass_eq_idealNormClass
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G) :
    ∑ g ∈ x.coeff.support,
        x.coeff g • deltaNormClass H T g =
      idealNormClass H T x hx := by
  calc
    ∑ g ∈ x.coeff.support,
        x.coeff g • deltaNormClass H T g =
        QuotientAddGroup.mk' (mixedProductInNumerator H)
          (∑ g ∈ x.coeff.support,
            x.coeff g • deltaNormElement H T g) := by
              simp_rw [deltaNormClass, ← map_zsmul]
              rw [← map_sum]
    _ = idealNormClass H T x hx := by
      apply congrArg
        (QuotientAddGroup.mk' (mixedProductInNumerator H))
      apply Subtype.ext
      calc
        (↑(∑ g ∈ x.coeff.support,
              x.coeff g • deltaNormElement H T g) :
            IntegralGroupRing G) =
            ∑ g ∈ x.coeff.support,
              x.coeff g •
                ((deltaElement G g : IntegralGroupRing G) *
                  transversalNormElement H T) := by
                    simp [deltaNormElement]
        _ = deltaCombination G x *
              transversalNormElement H T := by
                simp_rw [← smul_mul_assoc]
                rw [← Finset.sum_mul]
                rfl
        _ = x * transversalNormElement H T := by
          rw [deltaCombination_eq_of_mem_ideal G x hx]
        _ = (idealNormElement H T x hx :
            IntegralGroupRing G) :=
          rfl

/-- **The full transfer/augmentation formula.**
For every `x ∈ I_G`,

`S(x mod I_G²) = x · (∑ρ) mod I_G I_H`.
-/
theorem augmentationTransfer_apply_quotientMk
    (H : Subgroup G) [H.FiniteIndex]
    (T : H.LeftTransversal)
    (x : IntegralGroupRing G) (hx : x ∈ ideal G) :
    augmentationTransfer H
        (Multiplicative.ofAdd
          (QuotientAddGroup.mk' (squareInIdeal G) ⟨x, hx⟩)) =
      Multiplicative.ofAdd (idealNormClass H T x hx) := by
  rw [← deltaAbelianization_deltaPreimage G x hx]
  unfold deltaPreimage
  rw [map_prod, map_prod]
  simp_rw [map_zpow, deltaAbelianization_of]
  simp_rw [
    augmentationTransfer_deltaClass_eq_deltaNorm H T]
  apply Multiplicative.toAdd.injective
  exact sum_deltaNormClass_eq_idealNormClass
    H T x hx

end RelativeAugmentation
end Transfer
end GroupTheory
