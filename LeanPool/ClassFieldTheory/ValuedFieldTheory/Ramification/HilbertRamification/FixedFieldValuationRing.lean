/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
/-!
# Restricted valuation rings on actual fixed fields

For a normal subgroup of a finite Galois group, this file uses the literal
fixed field and the restriction of the chosen top valuation ring.  Unique
extension identifies that restricted ring with the integral closure of the
base valuation ring.  It is consequently a DVR, without a completeness or
Henselian assumption.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The actual fixed field of a subgroup. -/
abbrev fixedFieldDVF (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

/-- Restriction of the chosen top valuation ring to the actual fixed field. -/
def fixedFieldValuationSubringDVF (H : Subgroup Gal(L/K)) :
    ValuationSubring (fixedFieldDVF (K := K) H) :=
  target.valuation.valuationSubring.comap
    (algebraMap (fixedFieldDVF (K := K) H) L)

/-- States the theorem `mem_fixedFieldValuationSubringDVF_iff`. -/
@[simp] theorem mem_fixedFieldValuationSubringDVF_iff
    (H : Subgroup Gal(L/K)) (a : fixedFieldDVF (K := K) H) :
    a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H ↔
      algebraMap (fixedFieldDVF (K := K) H) L a ∈
        target.valuation.valuationSubring :=
  Iff.rfl

/-- Inclusion of the restricted fixed-field valuation ring into the top
valuation ring. -/
def fixedFieldValuationSubringDVFToTarget
    (H : Subgroup Gal(L/K)) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H →+*
      target.valuationSubring :=
  (algebraMap (fixedFieldDVF (K := K) H) L).restrict
    (fixedFieldValuationSubringDVF (K := K) (target := target) H)
    target.valuation.valuationSubring (fun _ ha => ha)

/-- States the theorem `fixedFieldValuationSubringDVFToTarget_apply_coe`. -/
@[simp] theorem fixedFieldValuationSubringDVFToTarget_apply_coe
    (H : Subgroup Gal(L/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    ((fixedFieldValuationSubringDVFToTarget
      (K := K) (target := target) H a : target.valuationSubring) : L) =
      algebraMap (fixedFieldDVF (K := K) H) L (a : fixedFieldDVF (K := K) H) :=
  rfl

/-- States the theorem `fixedFieldValuationSubringDVFToTarget_injective`. -/
theorem fixedFieldValuationSubringDVFToTarget_injective
    (H : Subgroup Gal(L/K)) :
    Function.Injective
      (fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H) := by
  intro a b hab
  apply Subtype.ext
  apply (algebraMap (fixedFieldDVF (K := K) H) L).injective
  exact congrArg (fun z : target.valuationSubring => (z : L)) hab

/-- The base valuation-ring map into the restricted valuation ring of the
fixed field. -/
def baseToFixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    base.valuationSubring →+*
      fixedFieldValuationSubringDVF (K := K) (target := target) H :=
  (algebraMap K (fixedFieldDVF (K := K) H)).restrict
    base.valuation.valuationSubring
    (fixedFieldValuationSubringDVF (K := K) (target := target) H)
    (fun a _ha => by
      change target.valuation (algebraMap K L (a : K)) ≤ 1
      exact (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) (a : K)).2 _ha)

/-- Provides the instance `instAlgebraBaseFixedFieldValuationSubringDVF`. -/
noncomputable instance instAlgebraBaseFixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    Algebra base.valuationSubring
      (fixedFieldValuationSubringDVF (K := K) (target := target) H) :=
  (baseToFixedFieldValuationSubringDVF
    (base := base) (target := target) H).toAlgebra

/-- The restricted valuation on the fixed field extends the base valuation. -/
theorem base_hasExtension_fixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    base.valuation.HasExtension
      (fixedFieldValuationSubringDVF
        (K := K) (target := target) H).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp [ValuationSubring.integer_valuation, _root_.Valuation.mem_integer_iff]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := base.valuation) (vA := target.valuation) a

/-- Provides the instance `instBaseHasExtensionFixedFieldValuationSubringDVF`. -/
instance instBaseHasExtensionFixedFieldValuationSubringDVF
    (H : Subgroup Gal(L/K)) :
    base.valuation.HasExtension
      (fixedFieldValuationSubringDVF
        (K := K) (target := target) H).valuation :=
  base_hasExtension_fixedFieldValuationSubringDVF
    (base := base) (target := target) H

/-- The inclusion of valuation rings, as an algebra homomorphism over the
base valuation ring. -/
def fixedFieldValuationSubringDVFToTargetAlgHom
    (H : Subgroup Gal(L/K)) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H →ₐ[
      base.valuationSubring] target.valuationSubring where
  toRingHom := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  commutes' a := by
    apply Subtype.ext
    rfl

/-- States the theorem `fixedFieldValuationSubringDVFToTargetAlgHom_injective`. -/
theorem fixedFieldValuationSubringDVFToTargetAlgHom_injective
    (H : Subgroup Gal(L/K)) :
    Function.Injective
      (fixedFieldValuationSubringDVFToTargetAlgHom
        (K := K) (base := base) (target := target) H) :=
  fixedFieldValuationSubringDVFToTarget_injective
    (K := K) (target := target) H

variable [FiniteDimensional K L]
variable [IsGalois K L]

/-- The restricted fixed-field valuation ring is integral over the base
valuation ring. -/
theorem fixedFieldValuationSubringDVF_isIntegral
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) :
    Algebra.IsIntegral base.valuationSubring
      (fixedFieldValuationSubringDVF (K := K) (target := target) H) := by
  let : Algebra.IsIntegral base.valuationSubring target.valuationSubring :=
    target_valuationSubring_isIntegral_of_uniqueExtension
      (base := base) (target := target) huniq
  exact Algebra.IsIntegral.of_injective
    (fixedFieldValuationSubringDVFToTargetAlgHom
      (K := K) (base := base) (target := target) H)
    (fixedFieldValuationSubringDVFToTargetAlgHom_injective
      (K := K) (base := base) (target := target) H)

/-- The restricted fixed-field valuation ring is the actual integral closure
of the base valuation ring in the fixed field. -/
theorem fixedFieldValuationSubringDVF_isIntegralClosure
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) :
    IsIntegralClosure
      (fixedFieldValuationSubringDVF (K := K) (target := target) H)
      base.valuationSubring (fixedFieldDVF (K := K) H) := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let M := fixedFieldDVF (K := K) H
  let : Algebra.IsIntegral base.valuationSubring B :=
    fixedFieldValuationSubringDVF_isIntegral
      (base := base) (target := target) huniq H
  let hTarget : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_uniqueExtension
      (base := base) (target := target) huniq
  let : IsScalarTower base.valuationSubring M L := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let : IsScalarTower base.valuationSubring B M := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
  · exact Subtype.coe_injective
  · intro z
    constructor
    · intro hz
      have hzTop : IsIntegral base.valuationSubring
          (algebraMap M L z) :=
        hz.map (IsScalarTower.toAlgHom base.valuationSubring M L)
      rcases hTarget.isIntegral_iff.mp hzTop with ⟨y, hy⟩
      refine ⟨⟨z, ?_⟩, rfl⟩
      change algebraMap M L z ∈ target.valuation.valuationSubring
      rw [← hy]
      exact y.property
    · rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := base.valuationSubring) y).map
        (IsScalarTower.toAlgHom base.valuationSubring B M)

/-- Module finiteness of the restricted integral closure. -/
theorem fixedFieldValuationSubringDVF_moduleFinite
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) :
    Module.Finite base.valuationSubring
      (fixedFieldValuationSubringDVF (K := K) (target := target) H) := by
  let : IsNoetherianRing base.valuationSubring :=
    base.valuationSubring_isNoetherianRing
  let : IsIntegralClosure
      (fixedFieldValuationSubringDVF (K := K) (target := target) H)
      base.valuationSubring (fixedFieldDVF (K := K) H) :=
    fixedFieldValuationSubringDVF_isIntegralClosure
      (base := base) (target := target) huniq H
  let : IsFractionRing base.valuationSubring K :=
    base.valuationSubring_isFractionRing
  let : IsScalarTower base.valuationSubring
      (fixedFieldValuationSubringDVF (K := K) (target := target) H)
      (fixedFieldDVF (K := K) H) := by
    apply IsScalarTower.of_algebraMap_eq; intro; rfl
  exact IsIntegralClosure.finite base.valuationSubring K (fixedFieldDVF (K := K) H) _

/-- The restricted valuation ring on a nontrivial finite fixed field is a
DVR.  This is an algebraic consequence of module finiteness and does not use
completeness. -/
theorem fixedFieldValuationSubringDVF_isDiscreteValuationRing
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    IsDiscreteValuationRing
      (fixedFieldValuationSubringDVF (K := K) (target := target) H) := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let : Module.Finite base.valuationSubring B :=
    fixedFieldValuationSubringDVF_moduleFinite
      (base := base) (target := target) huniq H
  let : IsNoetherianRing base.valuationSubring :=
    base.valuationSubring_isNoetherianRing
  let : IsNoetherianRing B :=
    IsNoetherianRing.of_finite base.valuationSubring B
  let : Algebra.IsIntegral base.valuationSubring B :=
    fixedFieldValuationSubringDVF_isIntegral
      (base := base) (target := target) huniq H
  have hinj : Function.Injective (algebraMap base.valuationSubring B) := by
    intro a b hab
    apply Subtype.ext
    apply (algebraMap K (fixedFieldDVF (K := K) H)).injective
    exact congrArg (fun z : B => (z : fixedFieldDVF (K := K) H)) hab
  have hnotField : ¬ IsField B := by
    intro hB
    exact IsDiscreteValuationRing.not_isField base.valuationSubring
      (isField_of_isIntegral_of_isField hinj hB)
  exact ((IsDiscreteValuationRing.TFAE B hnotField).out 2 1).mp
    (inferInstance : ValuationRing B)

/-- The quotient automorphism on the fixed field commutes with inclusion into
the top field. -/
theorem algebraMap_normalAutEquivQuotient_apply_dvf
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) (a : fixedFieldDVF (K := K) H) :
    algebraMap (fixedFieldDVF (K := K) H) L
        (IsGalois.normalAutEquivQuotient H sigma a) =
      sigma (algebraMap (fixedFieldDVF (K := K) H) L a) := by
  rw [IsGalois.normalAutEquivQuotient_apply]
  exact AlgEquiv.restrictNormal_commutes sigma
    (fixedFieldDVF (K := K) H) a

/-- Restriction of the quotient automorphism to the actual fixed-field
valuation ring. -/
def fixedFieldValuationSubringLiftedAutDVF
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H ≃+*
      fixedFieldValuationSubringDVF (K := K) (target := target) H where
  toFun a :=
    ⟨IsGalois.normalAutEquivQuotient H sigma (a : fixedFieldDVF (K := K) H), by
      rw [mem_fixedFieldValuationSubringDVF_iff,
        algebraMap_normalAutEquivQuotient_apply_dvf
          (K := K) H sigma]
      exact
        (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq sigma _).1 a.property⟩
  invFun a :=
    ⟨(IsGalois.normalAutEquivQuotient H sigma).symm
        (a : fixedFieldDVF (K := K) H), by
      rw [mem_fixedFieldValuationSubringDVF_iff]
      have hEq :
          algebraMap (fixedFieldDVF (K := K) H) L
              ((IsGalois.normalAutEquivQuotient H sigma).symm
                (a : fixedFieldDVF (K := K) H)) =
            sigma⁻¹ (algebraMap (fixedFieldDVF (K := K) H) L a) := by
        simpa using algebraMap_normalAutEquivQuotient_apply_dvf
          (K := K) H (sigma⁻¹) (a : fixedFieldDVF (K := K) H)
      rw [hEq]
      exact
        (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq (sigma⁻¹) _).1 a.property⟩
  left_inv a := by
    ext
    simp
  right_inv a := by
    ext
    simp
  map_mul' a b := by
    ext
    simp
  map_add' a b := by
    ext
    simp

/-- States the theorem `fixedFieldValuationSubringDVFToTarget_aut_apply`. -/
@[simp] theorem fixedFieldValuationSubringDVFToTarget_aut_apply
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H
        (fixedFieldValuationSubringLiftedAutDVF
          (base := base) (target := target) huniq H sigma a) =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma
        (fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H a) := by
  apply Subtype.ext
  exact algebraMap_normalAutEquivQuotient_apply_dvf
    (K := K) H sigma (a : fixedFieldDVF (K := K) H)

/-- Every automorphism of the fixed field preserves its restricted
valuation ring.  Surjectivity in the finite Galois correspondence is used
only to prove preservation; the automorphism appearing in the statement is
an automorphism of `L ^ H` itself. -/
theorem fixedFieldDVF_aut_mem_valuationSubring_iff
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (q : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldDVF (K := K) H) :
    a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H ↔
      q a ∈ fixedFieldValuationSubringDVF (K := K) (target := target) H := by
  let qbar : Gal(L/K) ⧸ H :=
    (IsGalois.normalAutEquivQuotient H).symm q
  obtain ⟨sigma, hsigma⟩ := QuotientGroup.mk'_surjective H qbar
  have hq : IsGalois.normalAutEquivQuotient H sigma = q := by
    change (IsGalois.normalAutEquivQuotient H)
      ((QuotientGroup.mk' H) sigma) = q
    rw [hsigma]
    exact (IsGalois.normalAutEquivQuotient H).apply_symm_apply q
  rw [mem_fixedFieldValuationSubringDVF_iff,
    mem_fixedFieldValuationSubringDVF_iff]
  rw [← hq, algebraMap_normalAutEquivQuotient_apply_dvf]
  exact
    mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
      (base := base) (target := target) huniq sigma _

/-- The canonical action of the fixed-field Galois group on its restricted
valuation ring. -/
def fixedFieldValuationSubringAutDVF
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (q : Gal((fixedFieldDVF (K := K) H)/K)) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H ≃+*
      fixedFieldValuationSubringDVF (K := K) (target := target) H where
  toFun a := ⟨q (a : fixedFieldDVF (K := K) H),
    (fixedFieldDVF_aut_mem_valuationSubring_iff
      (base := base) (target := target) huniq H q _).1 a.property⟩
  invFun a := ⟨q⁻¹ (a : fixedFieldDVF (K := K) H),
    (fixedFieldDVF_aut_mem_valuationSubring_iff
      (base := base) (target := target) huniq H q⁻¹ _).1 a.property⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp
  map_mul' a b := by ext; simp
  map_add' a b := by ext; simp

/-- States the theorem `fixedFieldValuationSubringAutDVF_apply_coe`. -/
@[simp] theorem fixedFieldValuationSubringAutDVF_apply_coe
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (q : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    ((fixedFieldValuationSubringAutDVF
      (base := base) (target := target) huniq H q a :
        fixedFieldValuationSubringDVF (K := K) (target := target) H) :
      fixedFieldDVF (K := K) H) = q (a : fixedFieldDVF (K := K) H) :=
  rfl

/-- States the theorem `fixedFieldValuationSubringAutDVF_mul_apply`. -/
@[simp] theorem fixedFieldValuationSubringAutDVF_mul_apply
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (q r : Gal((fixedFieldDVF (K := K) H)/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    fixedFieldValuationSubringAutDVF
        (base := base) (target := target) huniq H (q * r) a =
      fixedFieldValuationSubringAutDVF
        (base := base) (target := target) huniq H q
        (fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H r a) := by
  ext
  rfl

/-- The fixed-field action agrees with the lifted action obtained from any
chosen lift in the top Galois group. -/
theorem fixedFieldValuationSubringAutDVF_normalAutEquivQuotient
    (huniq :
      HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    fixedFieldValuationSubringAutDVF
        (base := base) (target := target) huniq H
        (IsGalois.normalAutEquivQuotient H sigma) a =
      fixedFieldValuationSubringLiftedAutDVF
        (base := base) (target := target) huniq H sigma a := by
  ext
  rfl

end Higher
end RamificationTheory.HilbertRamification
