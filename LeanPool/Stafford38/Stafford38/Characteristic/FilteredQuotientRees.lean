/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
import LeanPool.Stafford38.Stafford38.Weyl.OrderRees
import Mathlib.Algebra.DirectSum.Module

/-!
# The filtered quotient direct sum and associated-graded map

The filtered quotient pieces assemble into a direct sum with a successor
shift. Quotienting each degree by the preceding piece gives the already
constructed associated graded module; here we define the global map, prove
that it kills the shift, and prove surjectivity. This file does not construct
the required right action of the order-Rees ring. Kernel equality and that
action are deliberately left as subsequent theorems.
-/

namespace Stafford38.CharacteristicFilteredQuotientRees

open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

theorem quotientOrderPiece_mono
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ} (hNM : N ≤ M) :
    quotientOrderPiece k I N ≤ quotientOrderPiece k I M := by
  exact Submodule.map_mono (presentedWeightPiece_mono k orderWeight hNM)

theorem quotientOrderStrictLowerPiece_succ_eq
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    quotientOrderStrictLowerPiece k I (N + 1) =
      quotientOrderPiece k I N := by
  rfl

/-- The filtered direct sum underlying the intended right Rees module. -/
abbrev QuotientOrderReesModule
    (I : RightIdeal (PresentedWeyl k n)) :=
  DirectSum ℕ (fun N => quotientOrderPiece k I N)

/-- Inclusion of one quotient filtration piece into the next. -/
def quotientOrderPieceSucc
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    quotientOrderPiece k I N →ₗ[k] quotientOrderPiece k I (N + 1) :=
  Submodule.inclusion (quotientOrderPiece_mono k I (Nat.le_succ N))

/-- The successor inclusion shift on the filtered quotient direct sum. -/
def quotientOrderReesShift
    (I : RightIdeal (PresentedWeyl k n)) :
    QuotientOrderReesModule k I →ₗ[k] QuotientOrderReesModule k I :=
  DirectSum.toModule k ℕ (QuotientOrderReesModule k I) fun N =>
    (DirectSum.lof k ℕ (fun M => quotientOrderPiece k I M) (N + 1)).comp
      (quotientOrderPieceSucc k I N)

@[simp]
theorem quotientOrderReesShift_of
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (q : quotientOrderPiece k I N) :
    quotientOrderReesShift k I
        (DirectSum.of (fun M => quotientOrderPiece k I M) N q) =
      DirectSum.of (fun M => quotientOrderPiece k I M) (N + 1)
        (quotientOrderPieceSucc k I N q) := by
  change (DirectSum.toModule k ℕ (QuotientOrderReesModule k I) fun N =>
      (DirectSum.lof k ℕ (fun M => quotientOrderPiece k I M) (N + 1)).comp
        (quotientOrderPieceSucc k I N))
      (DirectSum.lof k ℕ (fun M => quotientOrderPiece k I M) N q) = _
  rw [DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.lof_eq_of]

/-- The quotient map from one filtered piece to its associated graded piece. -/
def quotientOrderPieceToGraded
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    quotientOrderPiece k I N →ₗ[k] QuotientOrderGradedPiece k I N :=
  ((quotientOrderStrictLowerPiece k I N).comap
    (quotientOrderPiece k I N).subtype).mkQ

/-- Global specialization of the filtered quotient direct sum to the actual
associated graded quotient. -/
def quotientOrderReesToAssociatedGraded
    (I : RightIdeal (PresentedWeyl k n)) :
    QuotientOrderReesModule k I →ₗ[k] QuotientOrderAssociatedGraded k I :=
  DirectSum.toModule k ℕ (QuotientOrderAssociatedGraded k I) fun N =>
    (DirectSum.lof k ℕ (fun M => QuotientOrderGradedPiece k I M) N).comp
      (quotientOrderPieceToGraded k I N)

@[simp]
theorem quotientOrderReesToAssociatedGraded_of
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (q : quotientOrderPiece k I N) :
    quotientOrderReesToAssociatedGraded k I
        (DirectSum.of (fun M => quotientOrderPiece k I M) N q) =
      DirectSum.of (fun M => QuotientOrderGradedPiece k I M) N
        (quotientOrderPieceToGraded k I N q) := by
  change (DirectSum.toModule k ℕ (QuotientOrderAssociatedGraded k I) fun N =>
      (DirectSum.lof k ℕ (fun M => QuotientOrderGradedPiece k I M) N).comp
        (quotientOrderPieceToGraded k I N))
      (DirectSum.lof k ℕ (fun M => quotientOrderPiece k I M) N q) = _
  rw [DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.lof_eq_of]

theorem quotientOrderPieceToGraded_succ_inclusion_eq_zero
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (q : quotientOrderPiece k I N) :
    quotientOrderPieceToGraded k I (N + 1)
        (quotientOrderPieceSucc k I N q) = 0 := by
  change Submodule.Quotient.mk (quotientOrderPieceSucc k I N q) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (q : FilteredRightQuotient k I) ∈
    quotientOrderStrictLowerPiece k I (N + 1)
  rw [quotientOrderStrictLowerPiece_succ_eq]
  exact q.property

/-- Specialization kills the successor shift. -/
theorem quotientOrderReesToAssociatedGraded_comp_shift
    (I : RightIdeal (PresentedWeyl k n)) :
    (quotientOrderReesToAssociatedGraded k I).comp
        (quotientOrderReesShift k I) = 0 := by
  apply DirectSum.linearMap_ext
  intro N
  apply LinearMap.ext
  intro q
  change quotientOrderReesToAssociatedGraded k I
      (quotientOrderReesShift k I
        (DirectSum.of (fun M => quotientOrderPiece k I M) N q)) = 0
  rw [quotientOrderReesShift_of, quotientOrderReesToAssociatedGraded_of,
    quotientOrderPieceToGraded_succ_inclusion_eq_zero]
  exact map_zero _

/-- Every associated-graded class has a filtered Rees representative. -/
theorem quotientOrderReesToAssociatedGraded_surjective
    (I : RightIdeal (PresentedWeyl k n)) :
    Function.Surjective (quotientOrderReesToAssociatedGraded k I) := by
  intro g
  induction g using DirectSum.induction_on with
  | zero =>
      exact ⟨0, map_zero _⟩
  | of N q =>
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective
        ((quotientOrderStrictLowerPiece k I N).comap
          (quotientOrderPiece k I N).subtype) q
      exact ⟨DirectSum.of (fun M => quotientOrderPiece k I M) N p,
        quotientOrderReesToAssociatedGraded_of k I N p⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      calc
        quotientOrderReesToAssociatedGraded k I (a + b) =
            quotientOrderReesToAssociatedGraded k I a +
              quotientOrderReesToAssociatedGraded k I b := map_add _ _ _
        _ = x + y := congrArg₂ (· + ·) ha hb


end

end Stafford38.CharacteristicFilteredQuotientRees
