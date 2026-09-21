/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalFilteredTwoTerm
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientRees

/-!
# The degree-zero page of the canonical filtered quotient

This file records the first genuine page-level bridge: at `p = -m`, the
zero-page source and target are the actual order-`m` quotient graded piece.
-/

namespace Stafford38.Characteristic.CanonicalFilteredGradedBridge

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicFilteredQuotientRees
open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CI (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

private abbrev K (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :=
  canonicalFilteredTwoTerm k n N d hd

theorem G_at_neg
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).G (-(m : ℤ)) =
      quotientOrderPiece k (CI k n N d) m := by
  change (if -(m : ℤ) ≤ 0 then
      quotientOrderPiece k (CI k n N d) (- - (m : ℤ)).toNat else ⊥) = _
  rw [if_pos (by omega)]
  have hidx : (- - (m : ℤ)).toNat = m := by omega
  rw [hidx]

theorem G_succ_neg
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).G (-(m : ℤ) + 1) =
      quotientOrderStrictLowerPiece k (CI k n N d) m := by
  by_cases hm : m = 0
  · subst m
    norm_num
    change (if (1 : ℤ) ≤ 0 then
      quotientOrderPiece k (CI k n N d) 1 else
      (⊥ : Submodule k (CanonicalQuotient k n N d))) = _
    rw [if_neg (by norm_num)]
    rw [quotientOrderStrictLowerPiece]
    change (⊥ : Submodule k (CanonicalQuotient k n N d)) =
      (presentedStrictLowerPiece k orderWeight 0).map _
    rw [show presentedStrictLowerPiece k orderWeight 0 = ⊥ by rfl]
    simp
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [show (-(↑(m' + 1) : ℤ) + 1) = -(m' : ℤ) by omega,
      G_at_neg]
    rw [quotientOrderStrictLowerPiece_succ_eq]

theorem zeroPage_source_cycles_eq_orderPiece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).cycles 0 (-(m : ℤ)) =
      quotientOrderPiece k (CI k n N d) m := by
  rw [FilteredTwoTerm.cycles, G_at_neg k n N m d hd]
  apply inf_eq_left.mpr
  intro z hz
  have hzK : z ∈ (K k n N d hd).G (-(m : ℤ)) := by
    rw [G_at_neg k n N m d hd]
    exact hz
  change (K k n N d hd).f z ∈ (K k n N d hd).G (-(m : ℤ) + 0)
  norm_num
  apply (K k n N d hd).map_le (-(m : ℤ))
  exact ⟨z, hzK, rfl⟩

theorem zeroPage_target_boundaries_eq_orderStrictLowerPiece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).boundaries 0 (-(m : ℤ)) =
      quotientOrderStrictLowerPiece k (CI k n N d) m := by
  rw [FilteredTwoTerm.boundaries, G_succ_neg k n N m d hd,
    G_at_neg k n N m d hd]
  norm_num
  apply le_trans inf_le_right
  rw [← G_succ_neg k n N m d hd]
  exact (K k n N d hd).map_le (-(m : ℤ) + 1)

theorem zeroPage_source_is_actual_graded_piece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).SourcePage 0 (-(m : ℤ)) =
      QuotientOrderGradedPiece k (CI k n N d) m := by
  change ((K k n N d hd).cycles 0 (-(m : ℤ)) ⧸ _) = _
  rw [zeroPage_source_cycles_eq_orderPiece k n N m d hd]
  rw [G_succ_neg k n N m d hd]

theorem zeroPage_target_is_actual_graded_piece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).TargetPage 0 (-(m : ℤ)) =
      QuotientOrderGradedPiece k (CI k n N d) m := by
  change ((K k n N d hd).G (-(m : ℤ)) ⧸ _) = _
  rw [G_at_neg k n N m d hd,
    zeroPage_target_boundaries_eq_orderStrictLowerPiece k n N m d hd]

/-- The source component identification, with its actual `k`-linear structure. -/
def zeroPageSourceLinearEquivOrderGradedPiece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).SourcePage 0 (-(m : ℤ)) ≃ₗ[k]
      QuotientOrderGradedPiece k (CI k n N d) m := by
  let hC := zeroPage_source_cycles_eq_orderPiece k n N m d hd
  let hL := G_succ_neg k n N m d hd
  let e := LinearEquiv.ofEq _ _ hC
  exact Submodule.Quotient.equiv _ _ e (by
    ext x
    simp [e, hL])

/-- The target component identification, with its actual `k`-linear structure. -/
def zeroPageTargetLinearEquivOrderGradedPiece
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (K k n N d hd).TargetPage 0 (-(m : ℤ)) ≃ₗ[k]
      QuotientOrderGradedPiece k (CI k n N d) m := by
  let hG := G_at_neg k n N m d hd
  let hB := zeroPage_target_boundaries_eq_orderStrictLowerPiece k n N m d hd
  let e := LinearEquiv.ofEq _ _ hG
  exact Submodule.Quotient.equiv _ _ e (by
    ext x
    simp [e, hB])

theorem zeroPage_source_subsingleton_of_pos
    (n N : ℕ) (p : ℤ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) (hp : 0 < p) :
    Subsingleton ((K k n N d hd).SourcePage 0 p) := by
  have hG : (K k n N d hd).G p = ⊥ :=
    canonicalOrderFiltration_eq_bot_of_pos k _ hp
  have hcycles : (K k n N d hd).cycles 0 p = ⊥ := by
    apply le_antisymm
    · exact le_trans inf_le_left (le_of_eq hG)
    · exact bot_le
  rw [show (K k n N d hd).SourcePage 0 p =
      ((K k n N d hd).cycles 0 p ⧸
        ((K k n N d hd).G (p + 1)).comap
          ((K k n N d hd).cycles 0 p).subtype) by rfl, hcycles]
  infer_instance

theorem zeroPage_target_subsingleton_of_pos
    (n N : ℕ) (p : ℤ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) (hp : 0 < p) :
    Subsingleton ((K k n N d hd).TargetPage 0 p) := by
  have hG : (K k n N d hd).G p = ⊥ :=
    canonicalOrderFiltration_eq_bot_of_pos k _ hp
  rw [show (K k n N d hd).TargetPage 0 p =
      ((K k n N d hd).G p ⧸
        ((K k n N d hd).boundaries 0 p).comap
          ((K k n N d hd).G p).subtype) by rfl, hG]
  infer_instance

theorem zeroPage_drop_representative
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (x : (K k n N d hd).cycles 0 (-(m : ℤ))) :
    (K k n N d hd).drop 0 (-(m : ℤ))
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨(K k n N d hd).f (x : CanonicalQuotient k n N d),
          x.property.2⟩ : (K k n N d hd).G (-(m : ℤ) + 0)) := by
  rw [(K k n N d hd).drop_mk]
  rfl

end
end Stafford38.Characteristic.CanonicalFilteredGradedBridge
