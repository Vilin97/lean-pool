/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockData
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddListMultiset

/-!
# Tau-sign counting lemmas

Combinatorial lemmas connecting the tau-sign product over vertices
to the number of outgoing flags, via the incoming/outgoing partition.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ} (W : ClosedFragment) (F : EdgeSubset W)
  {κ : F.TransitionSystem} (o : κ.Orientation) (φ : F.OddColouring ℓ)

/-! ### Incoming and outgoing flags are equinumerous -/

/-- The match bijection gives equal cardinalities of incoming
and outgoing flags. -/
theorem card_in_eq_card_out :
    (F.flags.filter (fun f => o.isOut f = false)).card =
    (F.flags.filter (fun f => o.isOut f = true)).card := by
  apply Finset.card_bij (fun f hf => κ.match_ f)
  -- maps into target
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨κ.match_mem f hf.1,
      by rw [o.match_flip f hf.1, hf.2]; rfl⟩
  -- injective
  · intro f₁ hf₁ f₂ hf₂ heq
    have h1 := κ.match_invol f₁ (Finset.mem_filter.mp hf₁).1
    have h2 := κ.match_invol f₂ (Finset.mem_filter.mp hf₂).1
    calc f₁ = κ.match_ (κ.match_ f₁) := h1.symm
      _ = κ.match_ (κ.match_ f₂) := by rw [heq]
      _ = f₂ := h2
  -- surjective
  · intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨κ.match_ g, ?_, κ.match_invol g hg.1⟩
    rw [Finset.mem_filter]
    exact ⟨κ.match_mem g hg.1,
      by rw [o.match_flip g hg.1, hg.2]; rfl⟩

/-! ### The out-count as a `Fintype.card` -/

/-- The outgoing-flag filter cardinality equals the Fintype.card
of the corresponding subtype. -/
theorem card_out_eq_fintype :
    (F.flags.filter (fun f => o.isOut f = true)).card =
    Fintype.card {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true} := by
  rw [Fintype.card_subtype]
  -- RHS is #(univ.filter (fun f : {g // g ∈ F.flags} => o.isOut f.val = true))
  -- We build a bijection between the two finsets.
  apply Finset.card_bij
    (fun f (hf : f ∈ F.flags.filter (fun f => o.isOut f = true)) =>
      (⟨f, (Finset.mem_filter.mp hf).1⟩ : {g : W.Flag // g ∈ F.flags}))
  -- maps into
  · intro f hf
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2⟩
  -- injective
  · intro f₁ _ f₂ _ h
    exact congrArg Subtype.val h
  -- surjective
  · intro ⟨g, hg⟩ hb
    rw [Finset.mem_filter] at hb
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, hb.2⟩, rfl⟩

end RS
