/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
/-!
# Absolute data for finite local existence

This file isolates the common abstract Galois-theoretic realization of the absolute Galois
group, its unit representation, and the ground-field fixing subgroup.  Both
the characteristic-zero and equal-characteristic existence arguments use
these definitions.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

/-- An open finite-index subgroup of the ordinary topological group `Kˣ`.

This is a genuine public object rather than a transparent subtype alias: its
topological and finite-index contracts remain available without exposing a
particular nested-pair representation. -/
structure OpenFiniteIndexSubgroup
    (K : Type) [Field K] [TopologicalSpace K] where
  /-- The underlying subgroup of field units. -/
  subgroup : Subgroup Kˣ
  /-- The underlying subgroup is open in the unit-group topology. -/
  isOpen : IsOpen (subgroup : Set Kˣ)
  /-- The underlying subgroup has finite index. -/
  finiteIndex : subgroup.FiniteIndex

namespace OpenFiniteIndexSubgroup

variable {K : Type} [Field K] [TopologicalSpace K]

/-- Provides this instance. -/
instance : Coe (OpenFiniteIndexSubgroup K) (Subgroup Kˣ) :=
  ⟨OpenFiniteIndexSubgroup.subgroup⟩

/-- States the theorem `ext`. -/
@[ext]
theorem ext {H H' : OpenFiniteIndexSubgroup K}
    (h : H.subgroup = H'.subgroup) : H = H' := by
  cases H
  cases H'
  cases h
  rfl

/-- Provides this instance. -/
instance : PartialOrder (OpenFiniteIndexSubgroup K) :=
  PartialOrder.lift OpenFiniteIndexSubgroup.subgroup
    (fun _ _ h ↦ OpenFiniteIndexSubgroup.ext h)

end OpenFiniteIndexSubgroup

/-- Normality over the abstract base fixing group makes the represented
fixed field Galois over the concrete local base field. -/
theorem abstractFixedField_isGalois_of_base_normal
    (K : Type) [Field K]
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H
        (le_baseField H)).Normal) :
    IsGalois K (abstractFixedField K (SeparableClosure K) H) := by
  let B := baseField (Gal(SeparableClosure K / K))
  have hsub :
      extensionSubgroup B H (le_baseField H) =
        H.toSubgroup.subgroupOf B.toSubgroup := by
    ext sigma
    rw [mem_extensionSubgroup_iff]
  have hrelative :
      (H.toSubgroup.subgroupOf B.toSubgroup).Normal := by
    rw [← hsub]
    exact hnormal
  have hconj :
      ∀ h g : Gal(SeparableClosure K / K),
        h ∈ H.toSubgroup → g ∈ B.toSubgroup →
          g * h * g⁻¹ ∈ H.toSubgroup :=
    (Subgroup.normal_subgroupOf_iff (le_baseField H)).1 hrelative
  let : H.toSubgroup.Normal :=
    { conj_mem := fun h hh g => hconj h g hh (by simp [B, baseField]) }
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractFixedField K (SeparableClosure K) H)).1
  have hfix :
      (abstractFixedField K (SeparableClosure K) H).fixingSubgroup =
        H.toSubgroup := by
    have hclosed := closedFixingSubgroup_abstractFixedField_eq
      K (SeparableClosure K) H
    exact congrArg ClosedSubgroup.toSubgroup hclosed
  rw [hfix]
  infer_instance

variable (K : Type) [Field K]

/-- The closed fixing group of the ground field is absolutely finite in the
abstract Galois-theoretic sense (indeed, it is the full absolute Galois group). -/
noncomputable instance intrinsicAbstractBase_index_finite :
    Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K))
        (intrinsicAbstractBase K) (le_baseField (intrinsicAbstractBase K))) := by
  exact (intrinsicFiniteAbstractBase K).finite

end LocalClassFieldTheory

end
