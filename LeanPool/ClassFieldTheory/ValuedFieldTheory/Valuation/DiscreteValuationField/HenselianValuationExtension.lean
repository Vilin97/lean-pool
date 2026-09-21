/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Mathlib.RingTheory.Valuation.Extension

/-! # Henselian Valuation Extension -/
namespace ValuationTheory

/-!
# Valuation-extension API for Henselian discretely valued fields

This file keeps the valuation-extension uniqueness interface separate from the
lightweight Henselian-DVF core.  The core file is used by Hensel lifting and
does not need to import mathlib's full `Valuation.HasExtension` API.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace HenselianDVF

variable {K : Type u} [Field K]
variable {L : Type w} [Field L] [Algebra K L]

/-- A Henselian-DVF uniqueness predicate for extensions of the base valuation.
This is the non-complete analogue of the complete-DVF predicate used by
`ValuedExtension.HasUniqueValuationExtension`. -/
def HasUniqueValuationExtension (base : HenselianDVF.{u, v} K)
    (target : HenselianDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
      target.toDVF.valuation.IsEquiv v'

omit [Algebra K L] in
/-- A Henselian-DVF valuation is equivalent to another valuation as soon as
their valuation subrings are equal. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.toDVF.valuation.valuationSubring = v'.valuationSubring) :
    target.toDVF.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v').2 hsub

omit [Algebra K L] in
/-- Equivalent valuations have the same valuation subring. -/
theorem valuationSubring_eq_of_valuation_isEquiv
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    {v' : _root_.Valuation L Gamma'}
    (h : target.toDVF.valuation.IsEquiv v') :
    target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v').1 h

omit [Algebra K L] in
/-- Valuation equivalence is exactly equality of valuation subrings. -/
theorem valuation_isEquiv_iff_valuationSubring_eq
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.toDVF.valuation.IsEquiv v' ↔
      target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
  _root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v'

omit [Algebra K L] in
/-- Equality of valuation subrings is exactly pointwise equality of membership
in those subrings. -/
theorem valuationSubring_eq_iff_mem_valuationSubring
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.toDVF.valuation.valuationSubring = v'.valuationSubring ↔
      ∀ z : L, z ∈ target.toDVF.valuation.valuationSubring ↔
        z ∈ v'.valuationSubring := by
  constructor
  · intro h z
    rw [h]
  · intro h
    exact SetLike.ext (fun z => h z)

omit [Algebra K L] in
/-- Valuation equivalence can be checked by pointwise equality of membership
in valuation subrings. -/
theorem valuation_isEquiv_iff_mem_valuationSubring
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') :
    target.toDVF.valuation.IsEquiv v' ↔
      ∀ z : L, z ∈ target.toDVF.valuation.valuationSubring ↔
        z ∈ v'.valuationSubring := by
  rw [valuation_isEquiv_iff_valuationSubring_eq base target v',
    valuationSubring_eq_iff_mem_valuationSubring base target v']

/-- Equality of valuation subrings for all extensions proves Henselian-DVF
uniqueness up to mathlib's valuation equivalence. -/
theorem hasUniqueValuationExtension_of_forall_valuationSubring_eq
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    (h :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          target.toDVF.valuation.valuationSubring = v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  intro Gamma' _ v' _
  exact valuation_isEquiv_of_valuationSubring_eq base target v' (@h Gamma' _ v' _)

/-- Henselian-DVF unique extension implies valuation-subring equality for every
extension valuation. -/
theorem valuationSubring_eq_of_hasUniqueValuationExtension
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    (huniq : HasUniqueValuationExtension.{u, v, w, x, y} base target)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'] :
    target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
  valuationSubring_eq_of_valuation_isEquiv base target (@huniq Gamma' _ v' _)

/-- Henselian-DVF unique extension is equivalent to equality of the chosen
target valuation subring with every extension valuation subring. -/
theorem hasUniqueValuationExtension_iff_forall_valuationSubring_eq
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L) :
    HasUniqueValuationExtension.{u, v, w, x, y} base target ↔
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          target.toDVF.valuation.valuationSubring = v'.valuationSubring := by
  constructor
  · intro huniq Gamma' _ v' _
    exact valuationSubring_eq_of_hasUniqueValuationExtension base target huniq v'
  · intro h
    exact hasUniqueValuationExtension_of_forall_valuationSubring_eq base target h

/-- Henselian-DVF unique extension can be checked pointwise on membership in
valuation subrings. -/
theorem hasUniqueValuationExtension_iff_forall_mem_valuationSubring
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L) :
    HasUniqueValuationExtension.{u, v, w, x, y} base target ↔
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          ∀ z : L, z ∈ target.toDVF.valuation.valuationSubring ↔
            z ∈ v'.valuationSubring := by
  constructor
  · intro huniq Gamma' _ v' _ z
    rw [valuationSubring_eq_of_hasUniqueValuationExtension base target huniq v']
  · intro h
    rw [hasUniqueValuationExtension_iff_forall_valuationSubring_eq]
    intro Gamma' _ v' _
    exact (valuationSubring_eq_iff_mem_valuationSubring base target v').2
      (@h Gamma' _ v' _)

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
