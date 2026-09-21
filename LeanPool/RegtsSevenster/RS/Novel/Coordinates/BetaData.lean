/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij

/-!
# The `β`-diagonal's colour data

The colour-form entries at a partner slot, the colouring of a sum
index on either side, and the `β`-diagonal these produce.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ}

/-- The colour form entry at an odd colour and its partner equals
minus the partner sign. -/
theorem colourFormEntry_inr_partner (u : Fin (2 * ℓ)) :
    colourFormEntry k ℓ (Sum.inr u) (Sum.inr (oddPartner ℓ u)) =
      -(oddPartnerSign ℓ u : ℂ) := by
  have hu := u.isLt
  unfold oddPartner oddPartnerSign
  by_cases h : u.val < ℓ
  · rw [dif_pos h, if_pos h]
    show (if u.val + ℓ = u.val + ℓ then (1 : ℂ)
      else if (u.val + ℓ) + ℓ = u.val then -1 else 0) =
      -((-1 : ℤ) : ℂ)
    rw [if_pos rfl]
    simp
  · rw [dif_neg h, if_neg h]
    show (if u.val + ℓ = u.val - ℓ then (1 : ℂ)
      else if (u.val - ℓ) + ℓ = u.val then -1 else 0) =
      -((1 : ℤ) : ℂ)
    have h1 : ¬ (u.val + ℓ = u.val - ℓ) := by omega
    rw [if_neg h1, if_pos (by omega)]
    simp

/-- The data colouring at a castAdd slot gives the representative
colour (even or odd). -/
theorem colouringOf_castAdd (W : ClosedFragment) (F : EdgeSubset W)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ) (i : Fin (edgeCount W)) :
    colouringOf W F ψ φ (Fin.castAdd (edgeCount W) i) =
      (if h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        Sum.inr (φ.val ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i), h⟩)
      else Sum.inl
        (ψ.val ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i), h⟩)) := by
  have key : ∀ (slot : Fin (edgeCount W + edgeCount W))
    (hslot : slot.val < edgeCount W),
    colouringOf W F ψ φ slot =
      (if h : (starFlagEnum W).symm slot ∈ F.flags then
        Sum.inr (φ.val ⟨(starFlagEnum W).symm slot, h⟩)
      else Sum.inl (ψ.val ⟨(starFlagEnum W).symm slot, h⟩)) := by
    intro slot hslot
    rw [colouringOf]
    by_cases h : (starFlagEnum W).symm slot ∈ F.flags
    · rw [dif_pos h, dif_pos h, if_pos hslot]
    · rw [dif_neg h, dif_neg h]
  exact key (Fin.castAdd (edgeCount W) i) i.isLt

/-- The data colouring at a natAdd slot gives the partner colour
(even repeat or odd partner). -/
theorem colouringOf_natAdd (W : ClosedFragment) (F : EdgeSubset W)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ) (i : Fin (edgeCount W)) :
    colouringOf W F ψ φ (Fin.natAdd (edgeCount W) i) =
      (if h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        Sum.inr (oddPartner ℓ (φ.val ⟨(starFlagEnum W).symm (Fin.castAdd
          (edgeCount W) i), h⟩))
      else Sum.inl
        (ψ.val ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i), h⟩)) := by
  have hpair : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) =
      W.pairing ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)) :=
    (pairing_starFlagEnum_symm W i).symm
  have key : ∀ (slot : Fin (edgeCount W + edgeCount W))
    (hslot : ¬ slot.val < edgeCount W),
    colouringOf W F ψ φ slot =
      (if h : (starFlagEnum W).symm slot ∈ F.flags then
        Sum.inr (oddPartner ℓ (φ.val ⟨(starFlagEnum W).symm slot, h⟩))
      else Sum.inl (ψ.val ⟨(starFlagEnum W).symm slot, h⟩)) := by
    intro slot hslot
    rw [colouringOf]
    by_cases h : (starFlagEnum W).symm slot ∈ F.flags
    · rw [dif_pos h, dif_pos h, if_neg hslot]
    · rw [dif_neg h, dif_neg h]
  rw [key (Fin.natAdd (edgeCount W) i)
    (show ¬ (Fin.natAdd (edgeCount W) i).val < edgeCount W from by
      show ¬ (edgeCount W + i.val < edgeCount W); omega)]
  by_cases h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags
  · have h' : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) ∈ F.flags := by
      rw [hpair]; exact F.pairing_mem _ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have harg : (⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i), h'⟩ :
        {f : W.Flag // f ∈ F.flags}) =
      ⟨W.pairing ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)),
        F.pairing_mem _ h⟩ := Subtype.ext hpair
    exact Eq.trans (congrArg (fun x => oddPartner ℓ (φ.val x)) harg)
      (congrArg (oddPartner ℓ) (φ.property ⟨_, h⟩))
  · have h' : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) ∉ F.flags := by
      rw [hpair]; intro hmem
      exact h (by
        have := F.pairing_mem _ hmem
        rw [W.pairing_invol] at this
        exact this)
    rw [dif_neg h', dif_neg h]
    congr 1
    have harg : (⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i), h'⟩ :
        {f : W.Flag // f ∉ F.flags}) =
      ⟨W.pairing ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)),
        F.pairing_not_mem h⟩ := Subtype.ext hpair
    exact Eq.trans (congrArg ψ.val harg) (ψ.property ⟨_, h⟩)

open Classical in
-- Raised budget: the diagonal pairing is expanded position by
-- position over `Fin (edgeCount W)`, each with its membership
-- dichotomy.
/-- **The diagonal cap pairing on the data colouring**: the Koszul
sign times the product of per-position form entries, each evaluated
on the diagonal partner. -/
theorem betaDiag_colouringOf (W : ClosedFragment) (F : EdgeSubset W)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ) :
    betaDiag (edgeCount W) (colouringOf W F ψ φ) =
      (-1 : ℂ) ^ (Finset.univ.filter
          (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
            p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧ p.2 ∈ edgeIndexSet W F)).card *
        ∏ i : Fin (edgeCount W),
          (if h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags
            then
            -(oddPartnerSign ℓ (φ.val ⟨(starFlagEnum W).symm (Fin.castAdd
              (edgeCount W) i), h⟩) : ℂ)
          else 1) := by
  rw [betaDiag_eq_betaColour (edgeCount W) (colouringOf W F ψ φ)]
  unfold betaColour
  -- Rewrite the crossing count
  rw [koszulCrossings_colouringOf W F ψ φ]
  congr 1
  -- Show the products agree entry-by-entry
  refine Finset.prod_congr rfl (fun i _ => ?_)
  -- Convert firstHalf/secondHalf to castAdd/natAdd
  show colourFormEntry k ℓ
    (colouringOf W F ψ φ (Fin.castAdd (edgeCount W) i))
    (colouringOf W F ψ φ (Fin.natAdd (edgeCount W) i)) = _
  rw [colouringOf_castAdd, colouringOf_natAdd]
  by_cases h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags
  · rw [dif_pos h, dif_pos h, dif_pos h]
    exact colourFormEntry_inr_partner _
  · rw [dif_neg h, dif_neg h, dif_neg h]
    show (if (ψ.val ⟨_, h⟩) = (ψ.val ⟨_, h⟩) then (1 : ℂ) else 0) = 1
    rw [if_pos rfl]

end RS
