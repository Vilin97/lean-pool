/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourWord
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapVal

/-!
# Block restrictions of colourings

Restricting a colouring of a concatenated total to its blocks
through the block enumeration, with the enumeration's value laws
at a cons: the vocabulary in which the assembled star vector's
coordinates factor over the vertices.
-/

@[expose] public section

namespace RS

/-- The head-block values of the enumeration. -/
theorem blockSigmaEquiv_cons_zero_val (d : ℕ) (ds : List ℕ)
    (j : Fin d) :
    ((blockSigmaEquiv (d :: ds))
      ⟨⟨0, by simp⟩, j⟩).val = j.val := rfl

/-- The tail-block values of the enumeration. -/
theorem blockSigmaEquiv_cons_succ_val (d : ℕ) (ds : List ℕ)
    (v : Fin ds.length) (j : Fin (ds.get v)) :
    ((blockSigmaEquiv (d :: ds)) ⟨v.succ, j⟩).val =
      d + ((blockSigmaEquiv ds) ⟨v, j⟩).val := rfl

variable {k ℓ : ℕ}

/-- The block restriction of a colouring. -/
noncomputable def blockRestrict (ds : List ℕ)
    (c : MixedColouring k ℓ ds.sum) (v : Fin ds.length) :
    MixedColouring k ℓ (ds.get v) := fun j =>
  c (blockSigmaEquiv ds ⟨v, j⟩)

/-- The sigma position is strictly monotone in the block
offset. -/
theorem blockSigmaEquiv_strictMono :
    ∀ (ds : List ℕ) (v : Fin ds.length),
      StrictMono (fun j : Fin (ds.get v) =>
        blockSigmaEquiv ds ⟨v, j⟩)
  | [], v => v.elim0
  | d :: ds, v => by
    match v with
    | ⟨0, hv⟩ =>
      intro j₁ j₂ hj
      change blockSigmaEquiv (d :: ds) ⟨⟨0, hv⟩, j₁⟩ <
        blockSigmaEquiv (d :: ds) ⟨⟨0, hv⟩, j₂⟩
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds)
          ⟨⟨0, hv⟩, j₁⟩).val = j₁.val := rfl
      have h2 : (blockSigmaEquiv (d :: ds)
          ⟨⟨0, hv⟩, j₂⟩).val = j₂.val := rfl
      rw [h1, h2]
      exact hj
    | ⟨w + 1, hv⟩ =>
      intro j₁ j₂ hj
      have hw : w < ds.length := by
        have h := hv
        simp only [List.length_cons] at h
        omega
      have hrec := blockSigmaEquiv_strictMono ds ⟨w, hw⟩ hj
      change blockSigmaEquiv (d :: ds) ⟨⟨w + 1, hv⟩, j₁⟩ <
        blockSigmaEquiv (d :: ds) ⟨⟨w + 1, hv⟩, j₂⟩
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds)
          ⟨⟨w + 1, hv⟩, j₁⟩).val =
          d + ((blockSigmaEquiv ds) ⟨⟨w, hw⟩, j₁⟩).val := rfl
      have h2 : (blockSigmaEquiv (d :: ds)
          ⟨⟨w + 1, hv⟩, j₂⟩).val =
          d + ((blockSigmaEquiv ds) ⟨⟨w, hw⟩, j₂⟩).val := rfl
      have hrec' : blockSigmaEquiv ds ⟨⟨w, hw⟩, j₁⟩ <
          blockSigmaEquiv ds ⟨⟨w, hw⟩, j₂⟩ := hrec
      rw [h1, h2]
      rw [Fin.lt_def] at hrec'
      omega

end RS
