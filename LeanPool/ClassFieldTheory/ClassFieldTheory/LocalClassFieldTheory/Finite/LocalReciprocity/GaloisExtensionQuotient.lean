/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation

/-! # Galois Extension Quotient -/
namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology

open ClassFormation

/-!
# Finite local reciprocity: abstract extension quotients and actual Galois groups

For a Galois ambient extension `Ω/K`, the abstract class-formation model represents `K` by the
closed fixing subgroup of the bottom intermediate field and an intermediate
normal extension `E/K` by the closed subgroup fixing `E`.  This file proves
that the resulting abstract class-formation quotient is canonically the actual group
`Gal(E/K)`.
-/

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The subgroup fixing the bottom intermediate field is the distinguished
base field of the class formation. -/
theorem closedFixingSubgroup_bot_eq_baseField :
    closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω) =
      baseField (Gal(Ω/K)) := by
  ext σ
  change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup ↔
    σ ∈ (⊤ : Subgroup (Gal(Ω/K)))
  rw [IntermediateField.fixingSubgroup_bot]

/-- The fixing subgroup of an intermediate field lies in the fixing subgroup
of the base field. -/
theorem fixingSubgroupLeBase
    (E : IntermediateField K Ω) :
    (closedFixingSubgroup K Ω E).toSubgroup ≤
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup :=
  IntermediateField.fixingSubgroup_le bot_le

/-- In the base fixing group, the abstract class-formation extension subgroup is exactly
the subgroup obtained from the ambient fixing subgroup by `subgroupOf`. -/
theorem extensionSubgroup_base_eq_subgroupOf
    (E : IntermediateField K Ω) :
    extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) =
      (closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup := by
  rfl

/-- The fixing subgroup of a Galois intermediate extension is normal in the
ambient Galois group. -/
instance closedFixingSubgroup_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω E).toSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois E).2 inferInstance

/-- Normality of a Galois intermediate extension, in the exact subgroup
presentation used by the abstract class-formation framework. -/
instance extensionSubgroupBase_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).Normal := by
  rw [extensionSubgroup_base_eq_subgroupOf]
  infer_instance

/-- The quotient map from the abstract class-formation base fixing group to the ordinary
ambient quotient by `Gal(Ω/E)`. -/
def baseFixingToAmbientQuotient
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup →*
      Gal(Ω/K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup).comp
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup.subtype

/-- The kernel of the preceding map is the exact `extensionSubgroup` used in
the abstract theory. -/
theorem baseFixingToAmbientQuotient_ker
    (E : IntermediateField K Ω) [IsGalois K E] :
    (baseFixingToAmbientQuotient K Ω E).ker =
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) := by
  rw [extensionSubgroup_base_eq_subgroupOf]
  ext x
  change
    (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup x.1 = 1) ↔
      x.1 ∈ (closedFixingSubgroup K Ω E).toSubgroup
  exact QuotientGroup.eq_one_iff x.1

/-- The base fixing group is the whole ambient Galois group, hence its map to
the ambient quotient is onto. -/
theorem baseFixingToAmbientQuotient_surjective
    (E : IntermediateField K Ω) [IsGalois K E] :
    Function.Surjective (baseFixingToAmbientQuotient K Ω E) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro σ
  have hσ :
      σ ∈ (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  exact ⟨⟨σ, hσ⟩, rfl⟩

/-- The abstract class-formation quotient for `E/K` is the ordinary quotient of the
ambient Galois group by the subgroup fixing `E`. -/
def baseFixingExtensionQuotientEquivAmbient
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(Ω/K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (baseFixingToAmbientQuotient_ker K Ω E).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (baseFixingToAmbientQuotient K Ω E)
      (baseFixingToAmbientQuotient_surjective K Ω E))

/-- States the theorem `baseFixingExtensionQuotientEquivAmbient_mk`. -/
@[simp]
theorem baseFixingExtensionQuotientEquivAmbient_mk
    (E : IntermediateField K Ω) [IsGalois K E]
    (σ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingExtensionQuotientEquivAmbient K Ω E (QuotientGroup.mk σ) =
      QuotientGroup.mk σ.1 :=
  rfl

/-- The exact quotient group appearing in the abstract class-formation framework for the normal
intermediate extension `E/K` is canonically the actual `Gal(E/K)`. -/
def baseFixingExtensionQuotientEquivGaloisGroup
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(E/K) := by
  let H : ClosedSubgroup (Gal(Ω/K)) := closedFixingSubgroup K Ω E
  letI : H.toSubgroup.Normal := closedFixingSubgroup_normal K Ω E
  exact (baseFixingExtensionQuotientEquivAmbient K Ω E).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup E))))

end
end LocalClassFieldTheory
