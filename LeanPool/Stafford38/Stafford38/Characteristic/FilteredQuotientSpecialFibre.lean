/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientReesExact

/-!
# Additive special fibre of the filtered quotient direct sum

The exact successor-shift sequence identifies the quotient by the shift range
with the actual associated graded module. This is a `k`-linear equivalence
only. The right order-Rees action and its parameter compatibility are separate.
-/

namespace Stafford38.CharacteristicFilteredQuotientSpecialFibre

open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicFilteredQuotientRees
open Stafford38.CharacteristicFilteredQuotientReesExact
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The additive quotient by the successor-shift range is the actual
associated graded quotient. -/
def quotientOrderShiftQuotientLinearEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    (QuotientOrderReesModule k I ⧸
        LinearMap.range (quotientOrderReesShift k I)) ≃ₗ[k]
      QuotientOrderAssociatedGraded k I :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (quotientOrderReesShift k I))
      (LinearMap.ker (quotientOrderReesToAssociatedGraded k I))
      (quotientOrderReesToAssociatedGraded_ker_eq_range_shift k I).symm).trans
    ((quotientOrderReesToAssociatedGraded k I).quotKerEquivOfSurjective
      (quotientOrderReesToAssociatedGraded_surjective k I))

@[simp]
theorem quotientOrderShiftQuotientLinearEquiv_mk
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) :
    quotientOrderShiftQuotientLinearEquiv k I
        (Submodule.Quotient.mk x) =
      quotientOrderReesToAssociatedGraded k I x := by
  rfl


end

end Stafford38.CharacteristicFilteredQuotientSpecialFibre
