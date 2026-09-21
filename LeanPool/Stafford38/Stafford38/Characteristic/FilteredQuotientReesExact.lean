/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientRees

/-!
# Exact specialization of the filtered quotient Rees direct sum

This file completes the additive exactness statement for the concrete direct
sum constructed in `FilteredQuotientRees`.  The filtration inclusions make the
degree shift injective, and the kernel of the componentwise associated-graded
quotient is exactly its range.

Only `k`-linear maps are used here.  In particular, this file introduces no
Rees-ring action and asserts no special-fibre ring or module equivalence.
-/

namespace Stafford38.CharacteristicFilteredQuotientReesExact

open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicFilteredQuotientRees
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

private theorem quotientOrderReesShift_apply_succ
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) (N : ℕ) :
    (quotientOrderReesShift k I x) (N + 1) =
      quotientOrderPieceSucc k I N (x N) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of M q =>
      rw [quotientOrderReesShift_of]
      simp only [DirectSum.of_apply]
      by_cases h : M = N
      · subst M
        simp
      · have hs : M + 1 ≠ N + 1 := by omega
        simp [h, hs]
  | add x y hx hy =>
      simpa using congrArg₂ (· + ·) hx hy

private theorem quotientOrderReesToAssociatedGraded_apply
    (I : RightIdeal (PresentedWeyl k n))
    (x : QuotientOrderReesModule k I) (N : ℕ) :
    (quotientOrderReesToAssociatedGraded k I x) N =
      quotientOrderPieceToGraded k I N (x N) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of M q =>
      rw [quotientOrderReesToAssociatedGraded_of]
      simp only [DirectSum.of_apply]
      by_cases h : M = N
      · subst M
        simp
      · simp [h]
  | add x y hx hy =>
      simpa using congrArg₂ (· + ·) hx hy

/-- The degree-raising filtration shift on the concrete quotient Rees direct
sum is injective. -/
theorem quotientOrderReesShift_injective
    (I : RightIdeal (PresentedWeyl k n)) :
    Function.Injective (quotientOrderReesShift k I) := by
  intro x y hxy
  apply DFinsupp.ext
  intro N
  have hcomponent := congrArg (fun z => z (N + 1)) hxy
  change (quotientOrderReesShift k I x) (N + 1) =
    (quotientOrderReesShift k I y) (N + 1) at hcomponent
  rw [quotientOrderReesShift_apply_succ,
    quotientOrderReesShift_apply_succ] at hcomponent
  have hval :
      ((quotientOrderPieceSucc k I N (x N) :
        quotientOrderPiece k I (N + 1)) : FilteredRightQuotient k I) =
      ((quotientOrderPieceSucc k I N (y N) :
        quotientOrderPiece k I (N + 1)) : FilteredRightQuotient k I) :=
    congrArg
      (fun z : quotientOrderPiece k I (N + 1) =>
        (z : FilteredRightQuotient k I)) hcomponent
  apply Subtype.ext
  exact hval

private theorem homogeneous_mem_range_of_specialization_eq_zero
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (q : quotientOrderPiece k I N)
    (hq : quotientOrderPieceToGraded k I N q = 0) :
    DirectSum.of (fun M => quotientOrderPiece k I M) N q ∈
      LinearMap.range (quotientOrderReesShift k I) := by
  cases N with
  | zero =>
      have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
      have hqzero : q = 0 := by
        apply Subtype.ext
        change (q : FilteredRightQuotient k I) = 0
        simpa [quotientOrderStrictLowerPiece,
          Stafford38.WeylAssociatedGraded.presentedStrictLowerPiece] using hmem
      subst q
      rw [map_zero]
      exact (LinearMap.range (quotientOrderReesShift k I)).zero_mem
  | succ N =>
      have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
      have hprev : (q : FilteredRightQuotient k I) ∈
          quotientOrderPiece k I N := by
        simpa [quotientOrderStrictLowerPiece_succ_eq] using hmem
      let qprev : quotientOrderPiece k I N := ⟨q, hprev⟩
      refine ⟨DirectSum.of (fun M => quotientOrderPiece k I M) N qprev, ?_⟩
      rw [quotientOrderReesShift_of]
      congr 1

/-- Exactness of specialization for the concrete filtered quotient direct sum:
the elements killed by passage to the associated graded object are precisely
the images of the degree-raising filtration shift. -/
theorem quotientOrderReesToAssociatedGraded_ker_eq_range_shift
    (I : RightIdeal (PresentedWeyl k n)) :
    LinearMap.ker (quotientOrderReesToAssociatedGraded k I) =
      LinearMap.range (quotientOrderReesShift k I) := by
  classical
  apply le_antisymm
  · intro x hx
    have hmap : quotientOrderReesToAssociatedGraded k I x = 0 :=
      LinearMap.mem_ker.mp hx
    rw [← DirectSum.sum_support_of x]
    apply Submodule.sum_mem
    intro N hN
    apply homogeneous_mem_range_of_specialization_eq_zero k I N
    have hcomponent := congrArg (fun z => z N) hmap
    simpa [quotientOrderReesToAssociatedGraded_apply] using hcomponent
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply LinearMap.mem_ker.mpr
    have hcomp := LinearMap.congr_fun
      (quotientOrderReesToAssociatedGraded_comp_shift k I) y
    simpa using hcomp


end

end Stafford38.CharacteristicFilteredQuotientReesExact
