/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.IsSepClosed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
/-!
# Intrinsic absolute Galois data

This module packages the absolute Galois group of a field, its integral unit
representation, and its distinguished abstract base field using the chosen
separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

/-- The absolute Galois group of a field, formed using its chosen separable closure. -/
abbrev intrinsicAbsoluteGalois
    (F : Type) [Field F] :=
  Gal(SeparableClosure F / F)

/-- The integral representation of the intrinsic absolute Galois group on the
units of the chosen separable closure. -/
abbrev intrinsicAbsoluteUnits
    (F : Type) [Field F] :
    Rep ℤ (intrinsicAbsoluteGalois F) :=
  galoisAmbientUnitsRep F (SeparableClosure F)

/-- The closed base subgroup of the intrinsic absolute Galois group, expressed
as the fixing subgroup of the bottom intermediate field. -/
abbrev intrinsicAbstractBase
    (F : Type) [Field F] :
    ClosedSubgroup (intrinsicAbsoluteGalois F) :=
  closedFixingSubgroup F (SeparableClosure F)
    (⊥ : IntermediateField F (SeparableClosure F))

/-- The canonical equivalence from the intrinsic abstract base subgroup to the
full absolute Galois group. -/
noncomputable def intrinsicAbstractBaseEquivAbsolute
    (F : Type) [Field F] :
    (intrinsicAbstractBase F).toSubgroup ≃*
      intrinsicAbsoluteGalois F :=
  (MulEquiv.subgroupCongr (by
    rw [intrinsicAbstractBase,
      closedFixingSubgroup_bot_eq_baseField,
      baseField_toSubgroup])).trans Subgroup.topEquiv

/-- The inverse intrinsic-base equivalence has underlying automorphism equal to
the supplied absolute Galois automorphism. -/
@[simp]
theorem intrinsicAbstractBaseEquivAbsolute_symm_apply_val
    (F : Type) [Field F] (σ : intrinsicAbsoluteGalois F) :
    ((intrinsicAbstractBaseEquivAbsolute F).symm σ).1 = σ := by
  simp [intrinsicAbstractBaseEquivAbsolute]

/-- The intrinsic abstract base packaged as a finite abstract field; its
defining quotient is the trivial finite quotient. -/
@[reducible]
noncomputable def intrinsicFiniteAbstractBase
    (F : Type) [Field F] :
    FiniteAbstractField (intrinsicAbsoluteGalois F) where
  field := intrinsicAbstractBase F
  finite := by
    rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField]
    exact (FiniteAbstractField.base (intrinsicAbsoluteGalois F)).finite

/-- The finite intrinsic base is the distinguished finite base of the
abstract class formation. -/
@[simp]
theorem intrinsicFiniteAbstractBase_eq_base
    (F : Type) [Field F] :
    intrinsicFiniteAbstractBase F =
      FiniteAbstractField.base (intrinsicAbsoluteGalois F) := by
  have h := closedFixingSubgroup_bot_eq_baseField F (SeparableClosure F)
  change intrinsicAbstractBase F =
    baseField (intrinsicAbsoluteGalois F) at h
  exact FiniteAbstractField.eq_of_field_eq _ _ h
