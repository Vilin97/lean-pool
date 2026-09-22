/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.GaloisCohomology
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.NormKernelVanishing
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.NormImage
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic

/-! # Cohomology Bridge -/
namespace LocalClassFieldTheory

open CyclicCohomology

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The norm in the actual unit representation is the multiplicative Herbrand
norm after passing from `Additive Lˣ` back to `Lˣ`. -/
theorem unitsNormLinearMap_toMul_eq_tateNorm
    [Fintype (Gal(L/K))] (x : Lˣ) :
    Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) =
      tateNorm (Gal(L/K)) Lˣ x := by
  have hnorm :
      unitsNormLinearMap K L (Additive.ofMul x) =
        ∑ σ : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) := by
    exact LinearMap.sum_apply Finset.univ
      (fun σ : Gal(L/K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ)
      (Additive.ofMul x : Additive Lˣ)
  rw [hnorm]
  calc
    (Additive.toMul
        ((∑ σ : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x)) :
          Additive Lˣ) : Lˣ) =
        ∏ σ : Gal(L/K),
          (Additive.toMul
            ((Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) : Additive Lˣ) : Lˣ) := by
      simpa only using additive_toMul_finset_sum_units L Finset.univ
        (fun σ : Gal(L/K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x))
    _ = tateNorm (Gal(L/K)) Lˣ x := by
      rfl

/-- Multiplicative fixed units and the invariant submodule of the actual unit
representation are the same additive group. -/
def additiveFixedUnitsEquivInvariants :
    Additive (fixedSubgroup (Gal(L/K)) Lˣ) ≃+
      unitsInvariantSubmodule K L where
  toFun x := ⟨Additive.ofMul ((Additive.toMul x : fixedSubgroup (Gal(L/K)) Lˣ) : Lˣ), by
    intro σ
    exact congrArg Additive.ofMul ((Additive.toMul x).property σ)⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    intro σ
    exact Additive.ofMul.injective (x.property σ)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- Compose an additive equivalence with a submodule quotient map.

Keeping this construction polymorphic prevents typeclass search from unfolding
the concrete Galois representation while it looks for the quotient's additive
structure. -/
private def additiveEquivToQuotientHom
    {A M : Type} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom

/-- Multiplicative form of an additive homomorphism, kept polymorphic for the
same elaboration reason as `additiveEquivToQuotientHom`. -/
private def additiveHomToMultiplicativeHom
    {G B : Type} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B :=
  AddMonoidHom.toMultiplicativeRight f

/-- The multiplicative group structure on an additive submodule quotient.
This is passed explicitly at concrete call sites to avoid rediscovering it by
unfolding the coefficient representation. -/
@[implicit_reducible]
private def multiplicativeQuotientGroup
    {M : Type} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N)) :=
  Multiplicative.group

/-- Kernel of a homomorphism into a multiplicative additive quotient, with the
codomain structure supplied directly. -/
private def kernelOfAdditiveQuotientHom
    {G M : Type} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G :=
  @MonoidHom.ker G inferInstance (Multiplicative (M ⧸ N))
    (multiplicativeQuotientGroup N).toMulOneClass f

/-- First-isomorphism-theorem comparison for a surjection onto a
multiplicative additive quotient. -/
private def quotientMulEquivOfSurjectiveAdditiveQuotient
    {G M : Type} [CommGroup G] [AddCommGroup M]
    (N : Submodule ℤ M) (S : Subgroup G)
    (f : G →* Multiplicative (M ⧸ N))
    (hker : kernelOfAdditiveQuotientHom N f = S)
    (hsurj : Function.Surjective f) :
    G ⧸ S ≃* Multiplicative (M ⧸ N) := by
  letI : Group (Multiplicative (M ⧸ N)) := multiplicativeQuotientGroup N
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

/-- Forget the type tags in an equivalence whose codomain is the
multiplicative form of an additive group. -/
private def mulEquivMultiplicativeToEquiv
    {G B : Type} [Group G] [AddCommGroup B]
    (e : G ≃* Multiplicative B) : G ≃ B where
  toFun q := Multiplicative.toAdd (e q)
  invFun q := e.symm (Multiplicative.ofAdd q)
  left_inv q := e.left_inv q
  right_inv q := e.right_inv (Multiplicative.ofAdd q)

/-- Additive quotient map from fixed units to invariant units modulo norms. -/
def additiveFixedUnitToInvariantsNormQuotientHom
    [Fintype (Gal(L/K))] :
    Additive (fixedSubgroup (Gal(L/K)) Lˣ) →+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveEquivToQuotientHom (additiveFixedUnitsEquivInvariants K L)
    (unitsTateH0NormSubmodule K L)

/-- Send a fixed unit to its invariant-unit class modulo norms. -/
def fixedUnitToInvariantsNormQuotientMonoidHom
    [Fintype (Gal(L/K))] :
    fixedSubgroup (Gal(L/K)) Lˣ →*
      Multiplicative
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveHomToMultiplicativeHom
    (additiveFixedUnitToInvariantsNormQuotientHom K L)

/-- A fixed unit maps to its canonical invariant-unit class modulo norms. -/
@[simp]
theorem fixedUnitToInvariantsNormQuotientMonoidHom_apply
    [Fintype (Gal(L/K))] (x : fixedSubgroup (Gal(L/K)) Lˣ) :
    Multiplicative.toAdd
        (fixedUnitToInvariantsNormQuotientMonoidHom K L x) =
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) :=
  rfl

/-- The kernel of the fixed-unit quotient map is exactly
the Herbrand norm subgroup inside the fixed subgroup. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_ker
    [Fintype (Gal(L/K))] :
    kernelOfAdditiveQuotientHom (unitsTateH0NormSubmodule K L)
        (fixedUnitToInvariantsNormQuotientMonoidHom K L) =
      (tateNormSubgroup (Gal(L/K)) Lˣ).subgroupOf
        (fixedSubgroup (Gal(L/K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0 at hx0
    have hxmem :
        additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
          unitsTateH0NormSubmodule K L :=
      (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).1 hx0
    rcases hxmem with ⟨y, hy⟩
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L/K)) Lˣ
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : unitsInvariantSubmodule K L =>
        Additive.toMul (z : Additive Lˣ)) hy
    change Additive.toMul (unitsNormLinearMap K L y) = (x : Lˣ) at hy'
    rw [tateNormHom_apply,
      ← unitsNormLinearMap_toMul_eq_tateNorm K L (Additive.toMul y)]
    simpa using hy'
  · intro hx
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L/K)) Lˣ at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0
    apply (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).2
    change additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
      LinearMap.range (unitsNormToInvariantsLinearMap K L)
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul y)) = (x : Lˣ)
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L y]
    exact hy

/-- Every invariant-unit class modulo norms has a multiplicatively fixed representative. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_surjective
    [Fintype (Gal(L/K))] :
    Function.Surjective (fixedUnitToInvariantsNormQuotientMonoidHom K L) := by
  intro q
  rcases Submodule.mkQ_surjective (unitsTateH0NormSubmodule K L)
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L/K)) Lˣ :=
    Additive.toMul ((additiveFixedUnitsEquivInvariants K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  change
    (unitsTateH0NormSubmodule K L).mkQ
      (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) =
        Multiplicative.toAdd q
  calc
    _ = (unitsTateH0NormSubmodule K L).mkQ z := by
      apply congrArg (unitsTateH0NormSubmodule K L).mkQ
      change additiveFixedUnitsEquivInvariants K L
        ((additiveFixedUnitsEquivInvariants K L).symm z) = z
      exact (additiveFixedUnitsEquivInvariants K L).apply_symm_apply z
    _ = Multiplicative.toAdd q := hz

/-- The multiplicative Herbrand quotient is the invariant-unit quotient by norms. -/
def herbrandH0MulEquivInvariantsNormQuotient
    [Fintype (Gal(L/K))] :=
  quotientMulEquivOfSurjectiveAdditiveQuotient
    (unitsTateH0NormSubmodule K L)
    ((tateNormSubgroup (Gal(L/K)) Lˣ).subgroupOf
      (fixedSubgroup (Gal(L/K)) Lˣ))
    (fixedUnitToInvariantsNormQuotientMonoidHom K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_ker K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_surjective K L)

/-- The multiplicative Herbrand quotient of field units is mathlib's
degree-zero Tate cohomology. -/
def herbrandH0EquivTateCohomologyZero [Fintype (Gal(L/K))] :
    HerbrandH0 (Gal(L/K)) Lˣ ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  (mulEquivMultiplicativeToEquiv
      (herbrandH0MulEquivInvariantsNormQuotient K L)).trans
    (tateUnitsH0IsoInvariantsQuotient K L).symm.toLinearEquiv.toEquiv

/-- Cardinality transport from the concrete Herbrand quotient to mathlib's
degree-zero Tate cohomology. -/
theorem cardinalMk_herbrandH0_fieldUnits_eq_tateCohomology_zero
    [Fintype (Gal(L/K))] :
    Cardinal.mk (HerbrandH0 (Gal(L/K)) Lˣ) =
      Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  Cardinal.mk_congr (herbrandH0EquivTateCohomologyZero K L)

/-- Subtraction by the identity in the actual unit representation is the
multiplicative coboundary `x ↦ g•x/x`. -/
theorem unitsRhoSub_toMul_eq_sigmaMinusOne
    (g : Gal(L/K)) (x : Lˣ) :
    (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul x)) : Lˣ) * x⁻¹ =
      sigmaMinusOne (Gal(L/K)) Lˣ g x := by
  rfl

/-- Multiplicative norm-one units and the kernel of the norm on the actual
unit representation are the same additive group. -/
def additiveNormKernelEquivUnitsNormKer [Fintype (Gal(L/K))] :
    Additive (normKernelSubgroup (Gal(L/K)) Lˣ) ≃+
      LinearMap.ker (unitsNormLinearMap K L) where
  toFun x := ⟨Additive.ofMul
      ((Additive.toMul x : normKernelSubgroup (Gal(L/K)) Lˣ) : Lˣ), by
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul
        ((Additive.toMul x : normKernelSubgroup (Gal(L/K)) Lˣ) : Lˣ))) = 1
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L
      ((Additive.toMul x : normKernelSubgroup (Gal(L/K)) Lˣ) : Lˣ)]
    exact (Additive.toMul x).property⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    change tateNorm (Gal(L/K)) Lˣ (Additive.toMul (x : Additive Lˣ)) = 1
    rw [← unitsNormLinearMap_toMul_eq_tateNorm K L
      (Additive.toMul (x : Additive Lˣ))]
    have hx := congrArg Additive.toMul x.property
    exact hx⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- The actual additive differential `ρ(g)-1`, with codomain restricted to
the kernel of the norm. -/
def unitsRhoSubToNormKerLinearMap [Fintype (Gal(L/K))]
    (g : Gal(L/K)) :
    Additive Lˣ →ₗ[ℤ] LinearMap.ker (unitsNormLinearMap K L) :=
  ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id).codRestrict
    (LinearMap.ker (unitsNormLinearMap K L)) (by
      intro x
      change unitsNormLinearMap K L
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      change (Rep.ofAlgebraAutOnUnits K L).norm.hom
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      change Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x) =
          Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ x
      exact Representation.norm_self_apply (Rep.ofAlgebraAutOnUnits K L).ρ g x)

/-- Additive quotient map from the multiplicative norm kernel to the
standard boundary presentation of degree-minus-one Tate cohomology. -/
def additiveNormKernelToUnitsBoundaryQuotientHom
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    Additive (normKernelSubgroup (Gal(L/K)) Lˣ) →+
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  additiveEquivToQuotientHom
    (additiveNormKernelEquivUnitsNormKer K L)
    (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))

/-- Multiplicative form of the standard boundary quotient map. -/
def normKernelToUnitsBoundaryQuotientMonoidHom
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    normKernelSubgroup (Gal(L/K)) Lˣ →*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  additiveHomToMultiplicativeHom
    (additiveNormKernelToUnitsBoundaryQuotientHom K L g)

/-- The kernel of the standard boundary quotient map is the augmentation
subgroup generated by `ρ(g)-1`. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_ker
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    kernelOfAdditiveQuotientHom
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
        (normKernelToUnitsBoundaryQuotientMonoidHom K L g) =
      (augmentationSubgroup (Gal(L/K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L/K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0 at hx0
    have hxmem :
        additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x) ∈
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).1 hx0
    rcases hxmem with ⟨y, hy⟩
    change (x : Lˣ) ∈ augmentationSubgroup (Gal(L/K)) Lˣ g
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : LinearMap.ker (unitsNormLinearMap K L) =>
        Additive.toMul (z : Additive Lˣ)) hy
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer] at hy'
    change
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g y) : Lˣ) *
        (Additive.toMul y)⁻¹ = (x : Lˣ) at hy'
    rw [sigmaMinusOneHom_apply,
      ← unitsRhoSub_toMul_eq_sigmaMinusOne K L g (Additive.toMul y)]
    exact hy'
  · intro hx
    change (x : Lˣ) ∈ augmentationSubgroup (Gal(L/K)) Lˣ g at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).2
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer]
    change
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul y)) : Lˣ) * y⁻¹ =
        (x : Lˣ)
    rw [unitsRhoSub_toMul_eq_sigmaMinusOne K L g y]
    exact hy

/-- Every class of the standard boundary quotient has a representative in
the multiplicative norm kernel. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_surjective
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    Function.Surjective
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g) := by
  intro q
  rcases Submodule.mkQ_surjective
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x : normKernelSubgroup (Gal(L/K)) Lˣ :=
    Additive.toMul ((additiveNormKernelEquivUnitsNormKer K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  change
    (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
        (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        Multiplicative.toAdd q
  calc
    _ = (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ z := by
      apply congrArg
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
      change additiveNormKernelEquivUnitsNormKer K L
        ((additiveNormKernelEquivUnitsNormKer K L).symm z) = z
      exact (additiveNormKernelEquivUnitsNormKer K L).apply_symm_apply z
    _ = Multiplicative.toAdd q := hz

/-- The multiplicative Herbrand quotient is the standard additive boundary
quotient used by mathlib's finite-cyclic Tate complex. -/
def herbrandHminusOneMulEquivUnitsBoundaryQuotient
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    HerbrandHMinusOne (Gal(L/K)) Lˣ g ≃*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  (HerbrandHMinusOne.equiv (G := Gal(L/K)) (A := Lˣ) g).trans
    (quotientMulEquivOfSurjectiveAdditiveQuotient
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      ((augmentationSubgroup (Gal(L/K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L/K)) Lˣ))
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_ker K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_surjective K L g))

/-- Type-level comparison with the standard boundary quotient. -/
def herbrandHminusOneEquivUnitsBoundaryQuotient
    [Fintype (Gal(L/K))] (g : Gal(L/K)) :
    HerbrandHMinusOne (Gal(L/K)) Lˣ g ≃
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  mulEquivMultiplicativeToEquiv
    (herbrandHminusOneMulEquivUnitsBoundaryQuotient K L g)

/-- Mathlib's degree-minus-one Tate object is its standard finite-cyclic
boundary quotient `ker N / im(ρ(g)-1)`. -/
noncomputable def unitsTateHminusOneIsoBoundaryQuotient
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) := by
  letI : IsCyclic (Gal(L/K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  letI : CommGroup (Gal(L/K)) := IsCyclic.commGroup
  let T :=
    Rep.FiniteCyclicGroup.subCompNormHom (Rep.ofAlgebraAutOnUnits K L) g
  have hmap :
      T.moduleCatToCycles =
          unitsRhoSubToNormKerLinearMap K L g := by
    ext x
    rfl
  have e := T.moduleCatHomologyIso
  change
    T.homology ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range
            T.moduleCatToCycles) at e
  rw [hmap] at e
  exact TateCohomology.isoFiniteCyclicNegOne (Rep.ofAlgebraAutOnUnits K L) g hg ≪≫
    e

/-- Genuine comparison of the multiplicative `H⁻¹` quotient
for field units with Mathlib's actual Tate `H⁻¹` object. -/
noncomputable def herbrandHminusOneEquivUnitsTateHminusOne
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) :
    HerbrandHMinusOne (Gal(L/K)) Lˣ g ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  (herbrandHminusOneEquivUnitsBoundaryQuotient K L g).trans
    (unitsTateHminusOneIsoBoundaryQuotient K L g hg).symm.toLinearEquiv.toEquiv

/-- Cardinality transport from the concrete Herbrand `H⁻¹` quotient to
the actual Tate `H⁻¹` object.  The statement is valid without introducing an
extraneous finiteness hypothesis. -/
theorem cardinalMk_herbrandHminusOne_fieldUnits_eq_unitsTateHminusOne
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) :
    Cardinal.mk (HerbrandHMinusOne (Gal(L/K)) Lˣ g) =
      Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
  Cardinal.mk_congr (herbrandHminusOneEquivUnitsTateHminusOne K L g hg)

end
end LocalClassFieldTheory
