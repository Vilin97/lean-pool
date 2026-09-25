/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RepFlag
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddFlip

/-!
# The edge-sign sector

Flipping the odd colouring converts the diagonal cap pairing's
per-edge signs into the Definition 5 orientation signs, up to the
count of edges whose representative is incoming.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

open Classical in
/-- The participating edges whose representative flag is
incoming. -/
noncomputable def inRepCount (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) : ℕ :=
  (Finset.univ.filter (fun i : Fin (edgeCount W) =>
    (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈
      F.flags ∧
    o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i)) = false)).card

/-- Representative slots are their own edge representatives. -/
theorem repFlag_symm_castAdd (W : ClosedFragment)
    (i : Fin (edgeCount W)) :
    repFlag W ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i)) =
    (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) := by
  refine repFlag_low W _ ?_
  rw [_root_.Equiv.apply_symm_apply]
  exact i.isLt

open Classical in
/-- **The edge-sign sector**: the flipped diagonal signs are the
orientation signs times the incoming-representative parity. -/
theorem edge_sign_sector (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (φ : F.OddColouring ℓ) :
    (∏ i : Fin (edgeCount W),
      (if h : (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        -((oddPartnerSign ℓ
          ((EdgeSubset.OddColouring.flip F (outRepSet W F o)
              (outRepSet_pairing_mem W F o) φ).val
            ⟨(starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i), h⟩) : ℤ) : ℂ)
      else 1)) =
    (-1 : ℂ) ^ inRepCount W F o *
      ∏ i : Fin (edgeCount W),
        (if h : (starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i) ∈ F.flags then
          ((oddPartnerSign ℓ (φ.val
            ⟨(starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i), h⟩) : ℤ) : ℂ)
        else 1) := by
  have hterm : ∀ i : Fin (edgeCount W),
      (if h : (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        -((oddPartnerSign ℓ
          ((EdgeSubset.OddColouring.flip F (outRepSet W F o)
              (outRepSet_pairing_mem W F o) φ).val
            ⟨(starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i), h⟩) : ℤ) : ℂ)
      else 1) =
      (if ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i) ∈ F.flags ∧
          o.isOut ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i)) = false)
        then (-1 : ℂ) else 1) *
      (if h : (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        ((oddPartnerSign ℓ (φ.val
          ⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i), h⟩) : ℤ) : ℂ)
      else 1) := by
    intro i
    set g := (starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i) with hg
    by_cases h : g ∈ F.flags
    · rw [dite_eq_left h, dite_eq_left h]
      by_cases hout : o.isOut g = true
      · have hT : g ∈ outRepSet W F o :=
          (mem_outRepSet_iff W F o g h).mpr (by
            rw [repFlag_symm_castAdd]
            exact hout)
        rw [EdgeSubset.OddColouring.flip_val_mem F _ _ φ
          ⟨g, h⟩ hT, oddPartnerSign_oddPartner]
        rw [ite_eq_right (by
          rintro ⟨-, hfalse⟩
          rw [hout] at hfalse
          exact Bool.noConfusion hfalse)]
        push_cast
        ring
      · have hof : o.isOut g = false := by
          cases hb : o.isOut g
          · rfl
          · exact absurd hb hout
        have hT : g ∉ outRepSet W F o := fun hmem => by
          have h2 := (mem_outRepSet_iff W F o g h).mp hmem
          rw [repFlag_symm_castAdd, hof] at h2
          exact Bool.noConfusion h2
        rw [EdgeSubset.OddColouring.flip_val_not_mem F _ _ φ
          ⟨g, h⟩ hT]
        rw [ite_eq_left ⟨h, hof⟩]
        ring
    · rw [dite_eq_right h, dite_eq_right h,
        ite_eq_right (fun hmem => h hmem.1), one_mul]
  rw [Finset.prod_congr rfl (fun i _ => hterm i),
    Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter]
  rw [Finset.prod_const]
  rfl

end RS
