/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotient

/-!
# Vanishing reflected by an exhaustive filtered quotient

For the actual quotient `A / I` with its induced differential-order
filtration, vanishing of every associated graded piece forces the quotient
itself to vanish.  The proof is internal to the filtration: degree zero uses
that its strict-lower piece is zero, and the successor step lowers the degree
by one.  Exhaustivity of the PBW order filtration then reaches every quotient
class.
-/

namespace Stafford38.CharacteristicFilteredVanishing

open Stafford38.CharacteristicFilteredQuotient
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- If every associated graded piece of the induced order filtration is
subsingleton, then every filtration piece is zero.  The induction explicitly
separates the degree-zero and successor cases. -/
theorem quotientOrderPiece_eq_bot_of_all_graded_subsingleton
    (I : RightIdeal (PresentedWeyl k n))
    (hgraded : ∀ N, Subsingleton (QuotientOrderGradedPiece k I N)) :
    ∀ N, quotientOrderPiece k I N = ⊥ := by
  intro N
  induction N with
  | zero =>
      apply le_antisymm
      · intro q hq
        let qN : quotientOrderPiece k I 0 := ⟨q, hq⟩
        have hmk :
            (Submodule.Quotient.mk qN : QuotientOrderGradedPiece k I 0) = 0 :=
          Subsingleton.elim _ _
        have hlower : qN ∈
            (quotientOrderStrictLowerPiece k I 0).comap
              (quotientOrderPiece k I 0).subtype :=
          (Submodule.Quotient.mk_eq_zero _).mp hmk
        change q ∈ quotientOrderStrictLowerPiece k I 0 at hlower
        simpa [quotientOrderStrictLowerPiece, presentedStrictLowerPiece] using hlower
      · exact bot_le
  | succ N ih =>
      apply le_antisymm
      · intro q hq
        let qN : quotientOrderPiece k I (N + 1) := ⟨q, hq⟩
        have hmk :
            (Submodule.Quotient.mk qN :
              QuotientOrderGradedPiece k I (N + 1)) = 0 :=
          Subsingleton.elim _ _
        have hlower : qN ∈
            (quotientOrderStrictLowerPiece k I (N + 1)).comap
              (quotientOrderPiece k I (N + 1)).subtype :=
          (Submodule.Quotient.mk_eq_zero _).mp hmk
        change q ∈ quotientOrderStrictLowerPiece k I (N + 1) at hlower
        have hqN : q ∈ quotientOrderPiece k I N := by
          simpa [quotientOrderStrictLowerPiece, presentedStrictLowerPiece,
            quotientOrderPiece] using hlower
        rw [ih] at hqN
        exact hqN
      · exact bot_le

/-- Vanishing of every actual associated graded piece reflects to the actual
filtered quotient because the induced order filtration is exhaustive. -/
theorem filteredRightQuotient_subsingleton_of_all_graded_subsingleton
    (I : RightIdeal (PresentedWeyl k n))
    (hgraded : ∀ N, Subsingleton (QuotientOrderGradedPiece k I N)) :
    Subsingleton (FilteredRightQuotient k I) := by
  have hzero : ∀ q : FilteredRightQuotient k I, q = 0 := by
    intro q
    refine Submodule.Quotient.induction_on _ q ?_
    intro a
    obtain ⟨N, hN⟩ := exists_mem_orderPiece k a
    have hpiece :
        (rightIdealKSubmodule k I).mkQ a ∈ quotientOrderPiece k I N :=
      ⟨a, hN, rfl⟩
    rw [quotientOrderPiece_eq_bot_of_all_graded_subsingleton k I hgraded] at hpiece
    exact hpiece
  exact ⟨fun q r => (hzero q).trans (hzero r).symm⟩

/-- Consequently the existing regular-right-module quotient is zero as well,
via its canonical linear equivalence with the filtered quotient. -/
theorem rightQuotient_subsingleton_of_all_graded_subsingleton
    (I : RightIdeal (PresentedWeyl k n))
    (hgraded : ∀ N, Subsingleton (QuotientOrderGradedPiece k I N)) :
    Subsingleton (RightQuotient I) := by
  let : Subsingleton (FilteredRightQuotient k I) :=
    filteredRightQuotient_subsingleton_of_all_graded_subsingleton k I hgraded
  constructor
  intro q r
  apply (filteredRightQuotientEquivRightQuotient k I).symm.injective
  exact Subsingleton.elim _ _


end

end Stafford38.CharacteristicFilteredVanishing
