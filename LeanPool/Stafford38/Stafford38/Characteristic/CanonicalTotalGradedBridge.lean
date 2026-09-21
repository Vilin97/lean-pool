/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalFilteredGradedBridge
import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalPages

/-!
Equivalences between total two-term pages and the canonical associated graded modules.
-/

namespace Stafford38.Characteristic.CanonicalTotalGradedBridge

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.Characteristic.CanonicalFilteredGradedBridge
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

universe u

variable (k : Type u) [Field k]

section ReindexNonpositive

variable {A : ℤ → Type u} {B : ℕ → Type u}
variable [∀ p, AddCommMonoid (A p)] [∀ p, Module k (A p)]
variable [∀ m, AddCommMonoid (B m)] [∀ m, Module k (B m)]

/-- The nonpositive integer index corresponding to a natural filtration degree. -/
def negIndex : ℕ → ℤ
  | 0 => 0
  | n + 1 => Int.negSucc n

theorem negIndex_eq (m : ℕ) : negIndex m = -(m : ℤ) := by
  cases m <;> simp [negIndex, Int.negSucc_eq]

private noncomputable def nonpositiveDirectSumToNat
    (e : ∀ m : ℕ, A (negIndex m) ≃ₗ[k] B m) :
    DirectSum ℤ A →ₗ[k] DirectSum ℕ B :=
  DirectSum.toModule k ℤ (DirectSum ℕ B) (fun p =>
    match p with
    | Int.ofNat 0 => (DirectSum.lof k ℕ B 0).comp (e 0).toLinearMap
    | Int.ofNat (_n + 1) => 0
    | Int.negSucc n =>
        (DirectSum.lof k ℕ B (n + 1)).comp (e (n + 1)).toLinearMap)

private noncomputable def natDirectSumToNonpositive
    (e : ∀ m : ℕ, A (negIndex m) ≃ₗ[k] B m) :
    DirectSum ℕ B →ₗ[k] DirectSum ℤ A :=
  DirectSum.toModule k ℕ (DirectSum ℤ A) (fun m =>
    (DirectSum.lof k ℤ A (negIndex m)).comp (e m).symm.toLinearMap)

@[simp]
private theorem natDirectSumToNonpositive_lof
    (e : ∀ m : ℕ, A (negIndex m) ≃ₗ[k] B m) (m : ℕ) (x : B m) :
    natDirectSumToNonpositive k e (DirectSum.lof k ℕ B m x) =
      DirectSum.lof k ℤ A (negIndex m) ((e m).symm x) := by
  rw [natDirectSumToNonpositive, DirectSum.toModule_lof]
  rfl

private noncomputable def nonpositiveDirectSumLinearEquiv
    (e : ∀ m : ℕ, A (negIndex m) ≃ₗ[k] B m)
    (hpos : ∀ p, 0 < p → Subsingleton (A p)) :
    DirectSum ℤ A ≃ₗ[k] DirectSum ℕ B := by
  refine LinearEquiv.ofLinearMap (nonpositiveDirectSumToNat k e)
    (natDirectSumToNonpositive k e) ?_ ?_
  · apply DirectSum.linearMap_ext k
    intro m
    apply LinearMap.ext
    intro x
    change nonpositiveDirectSumToNat k e
        (natDirectSumToNonpositive k e (DirectSum.lof k ℕ B m x)) =
      DirectSum.lof k ℕ B m x
    rw [natDirectSumToNonpositive_lof]
    cases m with
    | zero =>
        rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
        change DirectSum.lof k ℕ B 0 (e 0 ((e 0).symm x)) = _
        rw [(e 0).apply_symm_apply]
    | succ m =>
        rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
        change DirectSum.lof k ℕ B (m + 1)
            (e (m + 1) ((e (m + 1)).symm x)) = _
        rw [(e (m + 1)).apply_symm_apply]
  · apply DirectSum.linearMap_ext k
    intro p
    apply LinearMap.ext
    intro x
    change natDirectSumToNonpositive k e
        (nonpositiveDirectSumToNat k e (DirectSum.lof k ℤ A p x)) =
      DirectSum.lof k ℤ A p x
    cases p with
    | ofNat n =>
        cases n with
        | zero =>
            rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
            change natDirectSumToNonpositive k e
                (DirectSum.lof k ℕ B 0 (e 0 x)) = DirectSum.lof k ℤ A 0 x
            rw [natDirectSumToNonpositive_lof]
            congr 1
            exact (e 0).symm_apply_apply (show A (negIndex 0) from x)
        | succ n =>
            have := hpos (Int.ofNat (n + 1)) (by simp)
            simp [nonpositiveDirectSumToNat, Subsingleton.elim x 0]
    | negSucc n =>
        rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
        change natDirectSumToNonpositive k e
            (DirectSum.lof k ℕ B (n + 1) (e (n + 1) x)) =
          DirectSum.lof k ℤ A (Int.negSucc n) x
        rw [natDirectSumToNonpositive_lof]
        congr 1
        exact (e (n + 1)).symm_apply_apply
          (show A (negIndex (n + 1)) from x)

@[simp]
private theorem nonpositiveDirectSumLinearEquiv_lof
    (e : ∀ m : ℕ, A (negIndex m) ≃ₗ[k] B m)
    (hpos : ∀ p, 0 < p → Subsingleton (A p)) (m : ℕ) (x : A (negIndex m)) :
    nonpositiveDirectSumLinearEquiv k e hpos
        (DirectSum.lof k ℤ A (negIndex m) x) =
      DirectSum.lof k ℕ B m (e m x) := by
  cases m with
  | zero =>
      change nonpositiveDirectSumToNat k e
          (DirectSum.lof k ℤ A (negIndex 0) x) = _
      rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
      rfl
  | succ m =>
      change nonpositiveDirectSumToNat k e
          (DirectSum.lof k ℤ A (negIndex (m + 1)) x) = _
      rw [nonpositiveDirectSumToNat, DirectSum.toModule_lof]
      rfl

end ReindexNonpositive

private abbrev CI (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

private abbrev K (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  canonicalFilteredTwoTerm k n N d

/-- The source total module on page zero of the canonical filtered two-term complex. -/
abbrev SourceTotal0 (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  (K k n N d).SourceTotal 0

/-- The target total module on page zero of the canonical filtered two-term complex. -/
abbrev TargetTotal0 (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  (K k n N d).TargetTotal 0

theorem sourceComponentType_eq
    (n N m : ℕ) (d : PresentedWeyl k (n + 1)) :
    (K k n N d).SourcePage 0 (-(m : ℤ)) =
      QuotientOrderGradedPiece k (CI k n N d) m :=
  zeroPage_source_is_actual_graded_piece k n N m d

theorem targetComponentType_eq
    (n N m : ℕ) (d : PresentedWeyl k (n + 1)) :
    (K k n N d).TargetPage 0 (-(m : ℤ)) =
      QuotientOrderGradedPiece k (CI k n N d) m :=
  zeroPage_target_is_actual_graded_piece k n N m d

/-- The total degree-zero source page is the actual order-associated graded module. -/
noncomputable def sourceTotal0LinearEquivOrderAssociatedGraded
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    SourceTotal0 k n N d ≃ₗ[k]
      OrderAssociatedGradedModule k (CI k n N d) :=
  nonpositiveDirectSumLinearEquiv k
    (fun m =>
      (LinearEquiv.cast (M := fun p : ℤ => (K k n N d).SourcePage 0 p)
        (negIndex_eq m)) ≪≫ₗ
      zeroPageSourceLinearEquivOrderGradedPiece k n N m d)
    (zeroPage_source_subsingleton_of_pos k n N · d)

/-- The total degree-zero target page is the actual order-associated graded module. -/
noncomputable def targetTotal0LinearEquivOrderAssociatedGraded
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    TargetTotal0 k n N d ≃ₗ[k]
      OrderAssociatedGradedModule k (CI k n N d) :=
  nonpositiveDirectSumLinearEquiv k
    (fun m =>
      (LinearEquiv.cast (M := fun p : ℤ => (K k n N d).TargetPage 0 p)
        (negIndex_eq m)) ≪≫ₗ
      zeroPageTargetLinearEquivOrderGradedPiece k n N m d)
    (zeroPage_target_subsingleton_of_pos k n N · d)

@[simp]
theorem sourceTotal0LinearEquiv_lof_negIndex
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (x : (K k n N d).SourcePage 0 (negIndex m)) :
    sourceTotal0LinearEquivOrderAssociatedGraded k n N d
        (DirectSum.lof k ℤ (fun p => (K k n N d).SourcePage 0 p)
          (negIndex m) x) =
      orderAssociatedGradedOf k (CI k n N d) m
        (((LinearEquiv.cast
          (M := fun p : ℤ => (K k n N d).SourcePage 0 p) (negIndex_eq m)) ≪≫ₗ
            zeroPageSourceLinearEquivOrderGradedPiece k n N m d) x) := by
  exact nonpositiveDirectSumLinearEquiv_lof k _ _ m x

@[simp]
theorem targetTotal0LinearEquiv_lof_negIndex
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (x : (K k n N d).TargetPage 0 (negIndex m)) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d
        (DirectSum.lof k ℤ (fun p => (K k n N d).TargetPage 0 p)
          (negIndex m) x) =
      orderAssociatedGradedOf k (CI k n N d) m
        (((LinearEquiv.cast
          (M := fun p : ℤ => (K k n N d).TargetPage 0 p) (negIndex_eq m)) ≪≫ₗ
            zeroPageTargetLinearEquivOrderGradedPiece k n N m d) x) := by
  exact nonpositiveDirectSumLinearEquiv_lof k _ _ m x


end
end Stafford38.Characteristic.CanonicalTotalGradedBridge
