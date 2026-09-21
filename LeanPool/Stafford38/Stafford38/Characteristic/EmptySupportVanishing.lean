/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientSupport
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredVanishing

/-!
# Empty order-characteristic support forces quotient vanishing

The global additive equivalence between the cyclic symbol quotient and the
external direct sum of the actual filtered quotient pieces is enough for
vanishing.  No action of the symbol ring on that direct sum is transported or
used here.
-/

namespace Stafford38.CharacteristicEmptySupportVanishing

open Stafford38.Characteristic
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicFilteredQuotientSupport
open Stafford38.CharacteristicFilteredVanishing
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- Empty order-characteristic support makes every actual associated-graded
piece of the induced quotient filtration subsingleton.  The argument uses
only the global additive equivalence with the cyclic symbol quotient. -/
theorem all_graded_subsingleton_of_orderCharacteristicSupport_eq_empty
    (I : RightIdeal (PresentedWeyl k n))
    (hsupport : orderCharacteristicSupport k I = ∅) :
    ∀ N, Subsingleton (QuotientOrderGradedPiece k I N) := by
  have htop : orderInitialIdeal k I = ⊤ :=
    (orderCharacteristicSupport_eq_empty_iff k I).mp hsupport
  letI : Subsingleton (OrderCharacteristicModule k I) := by
    rw [Submodule.Quotient.subsingleton_iff]
    exact htop
  letI : Subsingleton (QuotientOrderAssociatedGraded k I) :=
    (quotientOrderAssociatedGradedAddEquivCharacteristic k I).toEquiv.subsingleton
  intro N
  exact ⟨fun q r => DirectSum.of_injective N (Subsingleton.elim
    (DirectSum.of (fun M => QuotientOrderGradedPiece k I M) N q)
    (DirectSum.of (fun M => QuotientOrderGradedPiece k I M) N r))⟩

/-- Empty order-characteristic support reflects through the actual associated
graded pieces to vanishing of the original right-module quotient. -/
theorem rightQuotient_subsingleton_of_orderCharacteristicSupport_eq_empty
    (I : RightIdeal (PresentedWeyl k n))
    (hsupport : orderCharacteristicSupport k I = ∅) :
    Subsingleton (RightQuotient I) :=
  rightQuotient_subsingleton_of_all_graded_subsingleton k I
    (all_graded_subsingleton_of_orderCharacteristicSupport_eq_empty k I hsupport)

/-- Vanishing of the actual quotient also forces every filtered graded piece
to vanish. -/
theorem all_graded_subsingleton_of_rightQuotient_subsingleton
    (I : RightIdeal (PresentedWeyl k n))
    (hquotient : Subsingleton (RightQuotient I)) :
    ∀ N, Subsingleton (QuotientOrderGradedPiece k I N) := by
  letI : Subsingleton (RightQuotient I) := hquotient
  letI : Subsingleton (FilteredRightQuotient k I) :=
    (filteredRightQuotientEquivRightQuotient k I).toEquiv.subsingleton
  intro N
  constructor
  intro q r
  refine Submodule.Quotient.induction_on _ q ?_
  intro a
  refine Submodule.Quotient.induction_on _ r ?_
  intro b
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (Subsingleton.elim a.1 b.1))

/-- For the concrete order filtration, the initial ideal is the unit ideal
exactly when the original right-module quotient vanishes. -/
theorem orderInitialIdeal_eq_top_iff_rightQuotient_subsingleton
    (I : RightIdeal (PresentedWeyl k n)) :
    orderInitialIdeal k I = ⊤ ↔ Subsingleton (RightQuotient I) := by
  constructor
  · intro htop
    apply rightQuotient_subsingleton_of_orderCharacteristicSupport_eq_empty k I
    exact (orderCharacteristicSupport_eq_empty_iff k I).mpr htop
  · intro hquotient
    letI : ∀ N, Subsingleton (QuotientOrderGradedPiece k I N) :=
      all_graded_subsingleton_of_rightQuotient_subsingleton k I hquotient
    letI : Subsingleton (QuotientOrderAssociatedGraded k I) := by
      infer_instance
    letI : Subsingleton (OrderCharacteristicModule k I) :=
      (Equiv.subsingleton_congr
        (quotientOrderAssociatedGradedAddEquivCharacteristic k I).toEquiv).mp
          (by infer_instance)
    exact (Submodule.Quotient.subsingleton_iff).mp (by infer_instance)

/-- Clean support formulation of the same vanishing criterion. -/
theorem orderCharacteristicSupport_eq_empty_iff_rightQuotient_subsingleton
    (I : RightIdeal (PresentedWeyl k n)) :
    orderCharacteristicSupport k I = ∅ ↔ Subsingleton (RightQuotient I) := by
  rw [orderCharacteristicSupport_eq_empty_iff,
    orderInitialIdeal_eq_top_iff_rightQuotient_subsingleton]


end

end Stafford38.CharacteristicEmptySupportVanishing
