/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdeal
import LeanPool.Stafford38.Stafford38.Weyl.AssociatedGraded

/-!
# Differential-order filtration on a right-ideal quotient

This file constructs the filtration induced on the actual additive quotient by
a right ideal and identifies each associated graded piece with homogeneous
symbols modulo the principal components of the filtered ideal.  Thus the
degreewise object is derived from `A / I`; it is not the cyclic
`SymbolRing / orderInitialIdeal` model.

The remaining global step is to assemble these degreewise equivalences into a
graded `SymbolRing`-module equivalence and identify its annihilator/support
with `orderInitialIdeal`.
-/

namespace Stafford38.CharacteristicFilteredQuotient

open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylLeadingSymbol

noncomputable section


universe u

variable (k : Type u) [Field k]

/-!
`PresentedWeyl` is a `RingQuot`, whose `AddCommMonoid` and `Ring` instances
are declared independently.  The two induced `AddCommMonoid` structures on a
submodule of it are definitionally equal but not syntactically identical, and
since Lean 4.33 instance arguments are matched only up to instance
transparency.  Mathlib's `Submodule.hasQuotient` expects the group-derived
shape, so without the two alignments below no quotient `↥p ⧸ q` of a
differential-order piece elaborates.  Both are `rfl`, so nothing about the
`k`-module structure changes.
-/

local instance (priority := 10000) pieceAddCommMonoid {n : ℕ}
    (p : Submodule k (PresentedWeyl k n)) : AddCommMonoid p :=
  AddCommGroup.toAddCommMonoid

local instance (priority := 10000) pieceModule {n : ℕ}
    (p : Submodule k (PresentedWeyl k n)) : Module k p :=
  Submodule.module p

/-- A right ideal, regarded only as a `k`-linear subspace.  Its carrier is
literally unchanged. -/
def rightIdealKSubmodule {A : Type*} [Ring A] [Algebra k A]
    (I : RightIdeal A) : Submodule k A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c a ha := by
    have h := I.smul_mem (MulOpposite.op (algebraMap k A c)) ha
    rw [Algebra.smul_def, Algebra.commutes]
    exact h

@[simp] theorem mem_rightIdealKSubmodule {A : Type*} [Ring A] [Algebra k A]
    (I : RightIdeal A) (a : A) :
    a ∈ rightIdealKSubmodule k I ↔ a ∈ I :=
  Iff.rfl

theorem rightIdealKSubmodule_eq_restrictScalars
    {A : Type*} [Ring A] [Algebra k A] (I : RightIdeal A) :
    rightIdealKSubmodule k I = I.restrictScalars k := by
  ext a
  rfl

/-- The `k`-linear quotient used for the filtration is canonically the same
underlying quotient as the regular right-module quotient. -/
def filteredRightQuotientEquivRightQuotient
    {A : Type*} [Ring A] [Algebra k A] (I : RightIdeal A) :
    (A ⧸ rightIdealKSubmodule k I) ≃ₗ[k] RightQuotient I :=
  Submodule.quotEquivOfEq _ _ (rightIdealKSubmodule_eq_restrictScalars k I) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv k I

variable {n : ℕ}

/-- The additive quotient by the underlying `k`-subspace of a right ideal. -/
abbrev FilteredRightQuotient (I : RightIdeal (PresentedWeyl k n)) :=
  PresentedWeyl k n ⧸ rightIdealKSubmodule k I

/-- Global alignment for the actual filtered quotient.  Lean 4.33 matches
instance arguments only up to instance transparency, and the default
`Submodule.Quotient.addCommMonoid` is not the additive monoid derived from the
quotient's `AddCommGroup`.  Without this alignment the direct sum of the
pieces below inherits an additive monoid that `Submodule.hasQuotient` cannot
match, and `FilteredQuotientSpecialFibre` cannot state its quotient.  This is
the same repair already made below for `QuotientOrderGradedPiece`. -/
instance (priority := 10000) filteredRightQuotientAddCommMonoid
    (I : RightIdeal (PresentedWeyl k n)) :
    AddCommMonoid (FilteredRightQuotient k I) :=
  AddCommGroup.toAddCommMonoid

instance (priority := 10000) filteredRightQuotientModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module k (FilteredRightQuotient k I) :=
  Submodule.Quotient.module _

/-- The image of the differential-order piece in the actual quotient. -/
def quotientOrderPiece (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Submodule k (FilteredRightQuotient k I) :=
  (presentedWeightPiece k (@orderWeight n) N).map
    (rightIdealKSubmodule k I).mkQ

/-- The image of the strict lower differential-order piece in the actual
quotient. -/
def quotientOrderStrictLowerPiece (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Submodule k (FilteredRightQuotient k I) :=
  (presentedStrictLowerPiece k orderWeight N).map
    (rightIdealKSubmodule k I).mkQ

theorem quotientOrderStrictLowerPiece_le
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    quotientOrderStrictLowerPiece k I N ≤ quotientOrderPiece k I N :=
  Submodule.map_mono (presentedStrictLowerPiece_le k orderWeight)

/-- The degree-`N` associated graded piece of the filtration induced on the
actual quotient `A / I`. -/
abbrev QuotientOrderGradedPiece
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :=
  quotientOrderPiece k I N ⧸
    (quotientOrderStrictLowerPiece k I N).comap
      (quotientOrderPiece k I N).subtype

/-- The same global alignment for the actual graded pieces: they are the
components of `QuotientOrderAssociatedGraded`, whose `AddCommGroup` instance
needs the group-derived additive monoid on each component. -/
instance (priority := 10000) quotientOrderGradedPieceAddCommMonoid
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    AddCommMonoid (QuotientOrderGradedPiece k I N) :=
  AddCommGroup.toAddCommMonoid

instance (priority := 10000) quotientOrderGradedPieceModule
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Module k (QuotientOrderGradedPiece k I N) :=
  Submodule.Quotient.module _

/-- Relations in the degree-`N` filtered algebra piece: an element is zero in
the quotient graded piece exactly when it lies in `I + F_{<N} A`. -/
def orderQuotientRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Submodule k (presentedWeightPiece k (@orderWeight n) N) :=
  ((rightIdealKSubmodule k I) ⊔
      presentedStrictLowerPiece k (@orderWeight n) N).comap
    (presentedWeightPiece k (@orderWeight n) N).subtype

/-- The canonical map from a filtered algebra piece to the corresponding
filtered piece of the actual quotient. -/
def orderPieceToQuotientPiece
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    presentedWeightPiece k (@orderWeight n) N →ₗ[k] quotientOrderPiece k I N :=
  ((rightIdealKSubmodule k I).mkQ.comp
    (presentedWeightPiece k (@orderWeight n) N).subtype).codRestrict
      (quotientOrderPiece k I N) (fun z => ⟨z, z.property, rfl⟩)

/-- The canonical map from a filtered algebra piece to the corresponding
graded piece of the actual quotient. -/
def orderPieceToQuotientGraded
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    presentedWeightPiece k (@orderWeight n) N →ₗ[k] QuotientOrderGradedPiece k I N :=
  ((quotientOrderStrictLowerPiece k I N).comap
      (quotientOrderPiece k I N).subtype).mkQ.comp
    (orderPieceToQuotientPiece k I N)

theorem orderPieceToQuotientGraded_surjective
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Function.Surjective (orderPieceToQuotientGraded k I N) := by
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  rintro ⟨q, hq⟩
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Exact kernel computation for the filtered quotient map. -/
theorem ker_orderPieceToQuotientGraded
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    LinearMap.ker (orderPieceToQuotientGraded k I N) =
      orderQuotientRelation k I N := by
  ext z
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk
      (⟨(rightIdealKSubmodule k I).mkQ z,
        ⟨z, z.property, rfl⟩⟩ : quotientOrderPiece k I N) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change (rightIdealKSubmodule k I).mkQ z ∈
      quotientOrderStrictLowerPiece k I N ↔ _
  change (z : PresentedWeyl k n) ∈
    (quotientOrderStrictLowerPiece k I N).comap
      (rightIdealKSubmodule k I).mkQ ↔ _
  rw [quotientOrderStrictLowerPiece, Submodule.comap_map_mkQ]
  rfl

/-- The actual quotient graded piece is the filtered algebra piece modulo
`I + F_{<N} A`. -/
def quotientOrderGradedPieceEquivRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    (presentedWeightPiece k (@orderWeight n) N ⧸
      orderQuotientRelation k I N) ≃ₗ[k]
      QuotientOrderGradedPiece k I N := by
  let hEq := ker_orderPieceToQuotientGraded k I N
  let g : (presentedWeightPiece k (@orderWeight n) N ⧸
      orderQuotientRelation k I N) →ₗ[k]
      QuotientOrderGradedPiece k I N :=
    (orderQuotientRelation k I N).liftQ
      (orderPieceToQuotientGraded k I N) (le_of_eq hEq.symm)
  apply LinearEquiv.ofBijective g
  constructor
  · intro q₁ q₂ h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    apply (Submodule.Quotient.eq _).2
    have hzw : orderPieceToQuotientGraded k I N z =
        orderPieceToQuotientGraded k I N w := by
      simpa [g] using h
    have hzwdiff : z - w ∈
        LinearMap.ker (orderPieceToQuotientGraded k I N) := by
      have e := LinearMap.map_sub (orderPieceToQuotientGraded k I N) z w
      rw [LinearMap.mem_ker, e, hzw, sub_self]
    rw [ker_orderPieceToQuotientGraded k I N] at hzwdiff
    exact hzwdiff
  · intro q
    obtain ⟨z, hz⟩ := orderPieceToQuotientGraded_surjective k I N q
    exact ⟨Submodule.Quotient.mk z, by simpa [g] using hz⟩

/-- Homogeneous symbol relations arising from `I + F_{<N} A`.  The strict
lower summand maps to zero, so these are precisely the degree-`N` principal
components contributed by filtered elements of `I`. -/
def orderSymbolRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Submodule k
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N) :=
  (orderQuotientRelation k I N).map
    (principalComponentOnPiece k (@orderWeight n) N)

/-- Align the additive monoid structure on a degree-`N` symbol quotient with
its additive group structure.  `Submodule.Quotient` declares the two
independently, so `DirectSum`'s `AddCommGroup` instance, and hence
`Submodule.liftQ` into the graded relation module, does not apply without
this `rfl` alignment.  Unlike the alignments above this one is global,
because `OrderSymbolRelationGraded` is assembled from these quotients in a
later module. -/
instance (priority := 10000) orderSymbolQuotientAddCommMonoid
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    AddCommMonoid
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N ⧸
        orderSymbolRelation k I N) :=
  AddCommGroup.toAddCommMonoid

instance (priority := 10000) orderSymbolQuotientModule
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Module k
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N ⧸
        orderSymbolRelation k I N) :=
  Submodule.Quotient.module _

/-- Principal component, descended to the quotient by the exact source and
target relation submodules. -/
def quotientPrincipalComponentMap
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    (presentedWeightPiece k (@orderWeight n) N ⧸
      orderQuotientRelation k I N) →ₗ[k]
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N ⧸
        orderSymbolRelation k I N) :=
  let f : presentedWeightPiece k (@orderWeight n) N →ₗ[k]
      MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N :=
    principalComponentOnPiece k (@orderWeight n) N
  let h : orderQuotientRelation k I N ≤
      (orderSymbolRelation k I N).comap f := by
    intro z hz
    change f z ∈ orderSymbolRelation k I N
    exact ⟨z, hz, rfl⟩
  Submodule.mapQ (p := orderQuotientRelation k I N)
    (q := orderSymbolRelation k I N) f h

theorem quotientPrincipalComponentMap_surjective
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Function.Surjective (quotientPrincipalComponentMap k I N) := by
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro P
  obtain ⟨z, rfl⟩ :=
    principalComponentOnPiece_surjective k (@orderWeight n) P
  let z' : presentedWeightPiece k (@orderWeight n) N := ⟨z, z.property⟩
  refine ⟨Submodule.Quotient.mk z', ?_⟩
  rw [quotientPrincipalComponentMap, Submodule.mapQ_apply]

theorem quotientPrincipalComponentMap_injective
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Function.Injective (quotientPrincipalComponentMap k I N) := by
  intro q₁ q₂
  revert q₂
  refine Submodule.Quotient.induction_on _ q₁ ?_
  intro z q₂
  refine Submodule.Quotient.induction_on _ q₂ ?_
  intro w h
  rw [quotientPrincipalComponentMap, Submodule.mapQ_apply,
    Submodule.mapQ_apply] at h
  apply (Submodule.Quotient.eq _).2
  have hpc :
      principalComponentOnPiece k (@orderWeight n) N z -
          principalComponentOnPiece k (@orderWeight n) N w ∈
        orderSymbolRelation k I N :=
    (Submodule.Quotient.eq _).mp h
  obtain ⟨r, hr, hpr⟩ := hpc
  have hdiffLower :
      (((z - w) - r : presentedWeightPiece k (@orderWeight n) N) : PresentedWeyl k n) ∈
        presentedStrictLowerPiece k orderWeight N := by
    apply (mem_ker_principalComponentOnPiece_iff k (@orderWeight n)
      ((z - w) - r)).mp
    have e₁ := LinearMap.map_sub
      (principalComponentOnPiece k (@orderWeight n) N) (z - w) r
    have e₂ := LinearMap.map_sub
      (principalComponentOnPiece k (@orderWeight n) N) z w
    rw [LinearMap.mem_ker, e₁, e₂, hpr, sub_self]
  have hdiffRelation : (z - w) - r ∈ orderQuotientRelation k I N := by
    change ((((z - w) - r : presentedWeightPiece k (@orderWeight n) N) : PresentedWeyl k n)) ∈
      (rightIdealKSubmodule k I) ⊔
        presentedStrictLowerPiece k orderWeight N
    exact Submodule.mem_sup_right hdiffLower
  have hsum := (orderQuotientRelation k I N).add_mem hr hdiffRelation
  have hrw : r + ((z - w) - r) = z - w := by abel
  rwa [hrw] at hsum

/-- Degreewise filtered-quotient bridge: the actual associated graded piece
of `A / I` is canonically equivalent to homogeneous symbols modulo the
principal components of `I + F_{<N} A`. -/
def quotientOrderGradedPieceEquivSymbols
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    QuotientOrderGradedPiece k I N ≃ₗ[k]
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N ⧸
        orderSymbolRelation k I N) :=
  (quotientOrderGradedPieceEquivRelation k I N).symm ≪≫ₗ
    LinearEquiv.ofBijective (quotientPrincipalComponentMap k I N)
      ⟨quotientPrincipalComponentMap_injective k I N,
        quotientPrincipalComponentMap_surjective k I N⟩

/-- Every filtered element of the right ideal contributes its principal
component to the exact symbol relation in the actual quotient graded piece. -/
theorem principalComponent_mem_orderSymbolRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) (z : PresentedWeyl k n)
    (hzN : z ∈ presentedWeightPiece k (@orderWeight n) N) (hzI : z ∈ I) :
    principalComponentOnPiece k (@orderWeight n) N ⟨z, hzN⟩ ∈
      orderSymbolRelation k I N := by
  refine ⟨⟨z, hzN⟩, ?_, rfl⟩
  change z ∈ (rightIdealKSubmodule k I) ⊔
    presentedStrictLowerPiece k orderWeight N
  exact Submodule.mem_sup_left hzI

/-- Exact description of the degree-`N` symbol relations: they are precisely
the principal components of elements of `I` lying in `F_N A`. -/
theorem mem_orderSymbolRelation_iff
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (P : MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N) :
    P ∈ orderSymbolRelation k I N ↔
      ∃ (z : PresentedWeyl k n)
        (hzN : z ∈ presentedWeightPiece k (@orderWeight n) N),
        z ∈ I ∧ P = principalComponentOnPiece k (@orderWeight n) N ⟨z, hzN⟩ := by
  constructor
  · rintro ⟨r, hr, hPr⟩
    change (r : PresentedWeyl k n) ∈
      (rightIdealKSubmodule k I) ⊔
        presentedStrictLowerPiece k orderWeight N at hr
    obtain ⟨i, hi, l, hl, hil⟩ := Submodule.mem_sup.mp hr
    have hlN : l ∈ presentedWeightPiece k (@orderWeight n) N :=
      presentedStrictLowerPiece_le k (@orderWeight n) hl
    have hiN : i ∈ presentedWeightPiece k (@orderWeight n) N := by
      have hieq : i = (r : PresentedWeyl k n) - l := by
        rw [← hil]
        simp
      rw [hieq]
      exact Submodule.sub_mem _ r.property hlN
    refine ⟨i, hiN, hi, ?_⟩
    let ii : presentedWeightPiece k (@orderWeight n) N := ⟨i, hiN⟩
    let ll : presentedWeightPiece k (@orderWeight n) N := ⟨l, hlN⟩
    have hrl : r = ii + ll := by
      apply Subtype.ext
      exact hil.symm
    have hpl :
        principalComponentOnPiece k (@orderWeight n) N ll = 0 := by
      apply Subtype.ext
      exact (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
        k (@orderWeight n) ll ll.property).mpr hl
    rw [← hPr, hrl, map_add]
    calc
      principalComponentOnPiece k (@orderWeight n) N ii +
          principalComponentOnPiece k (@orderWeight n) N ll =
          principalComponentOnPiece k (@orderWeight n) N ii + 0 :=
        congrArg (fun Q =>
          principalComponentOnPiece k (@orderWeight n) N ii + Q) hpl
      _ = principalComponentOnPiece k (@orderWeight n) N ii := add_zero _
      _ = principalComponentOnPiece k (@orderWeight n) N ⟨i, hiN⟩ := by
        congr 1
  · rintro ⟨z, hzN, hzI, rfl⟩
    exact principalComponent_mem_orderSymbolRelation k I N z hzN hzI

/-- Every exact degree-`N` relation of the actual quotient is one of the
generators used by the existing order initial ideal. -/
theorem coe_mem_orderInitialGeneratorSet_of_mem_orderSymbolRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (P : MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N)
    (hP : P ∈ orderSymbolRelation k I N) :
    (P : SymbolRing k n) ∈ orderInitialGeneratorSet k I := by
  obtain ⟨z, hzN, hzI, hPz⟩ :=
    (mem_orderSymbolRelation_iff k I N P).mp hP
  refine ⟨N, z, hzN, hzI, ?_⟩
  rw [hPz]
  rfl

theorem coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (P : MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N)
    (hP : P ∈ orderSymbolRelation k I N) :
    (P : SymbolRing k n) ∈ orderInitialIdeal k I :=
  Ideal.subset_span
    (coe_mem_orderInitialGeneratorSet_of_mem_orderSymbolRelation k I N P hP)


end

end Stafford38.CharacteristicFilteredQuotient
