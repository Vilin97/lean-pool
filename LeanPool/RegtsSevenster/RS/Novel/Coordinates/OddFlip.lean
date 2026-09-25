/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# Flipping an odd colouring

Reversing the odd colouring at a chosen edge is an involution of the
colourings, so summing a value over the colourings is invariant
under it — the reindexing the circuit-sign computation uses.
-/

@[expose] public section

namespace RS

open Finset

variable {α : Type} {W : Fragment α} (F : EdgeSubset W) {ℓ : ℕ}

open Classical in
/-- Flip an odd colouring on a pairing-closed set of flags: apply `oddPartner`
to every colour indexed by a flag in `T`, leave the rest unchanged. -/
noncomputable def EdgeSubset.OddColouring.flip
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T)
    (φ : F.OddColouring ℓ) : F.OddColouring ℓ :=
  ⟨fun f => if f.val ∈ T then oddPartner ℓ (φ.val f) else φ.val f,
   fun f => by
    by_cases h : f.val ∈ T
    · have hpair : W.pairing f.val ∈ T := hT f.val h
      simp only [hpair, h, ite_true]
      exact congrArg (oddPartner ℓ) (φ.prop f)
    · have hpair : W.pairing f.val ∉ T := by
        intro hmem
        have := hT _ hmem
        rw [W.pairing_invol] at this
        exact h this
      simp only [hpair, h, ite_false]
      exact φ.prop f⟩

open Classical in
/-- Flipping twice is the identity. -/
theorem EdgeSubset.OddColouring.flip_flip
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T)
    (φ : F.OddColouring ℓ) :
    EdgeSubset.OddColouring.flip F T hT (EdgeSubset.OddColouring.flip F T hT φ)
      = φ := by
  apply Subtype.ext
  funext f
  simp only [EdgeSubset.OddColouring.flip]
  by_cases h : f.val ∈ T
  · simp only [h, ite_true, oddPartner_invol]
  · simp only [h, ite_false]

open Classical in
/-- The flip as a self-equivalence on odd colourings. -/
noncomputable def EdgeSubset.OddColouring.flipEquiv
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T) :
    F.OddColouring ℓ ≃ F.OddColouring ℓ where
  toFun := EdgeSubset.OddColouring.flip F T hT
  invFun := EdgeSubset.OddColouring.flip F T hT
  left_inv := EdgeSubset.OddColouring.flip_flip F T hT
  right_inv := EdgeSubset.OddColouring.flip_flip F T hT

open Classical in
/-- Summing over flipped colourings equals summing over the originals. -/
theorem EdgeSubset.OddColouring.sum_flip
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T)
    (g : F.OddColouring ℓ → ℂ) :
    (∑ φ : F.OddColouring ℓ, g (EdgeSubset.OddColouring.flip F T hT φ)) =
      ∑ φ : F.OddColouring ℓ, g φ :=
  Equiv.sum_comp (EdgeSubset.OddColouring.flipEquiv F T hT) g

open Classical in
/-- The value of `flip` at a flag in `T`. -/
theorem EdgeSubset.OddColouring.flip_val_mem
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T)
    (φ : F.OddColouring ℓ) (f : {f : W.Flag // f ∈ F.flags})
    (h : f.val ∈ T) :
    (EdgeSubset.OddColouring.flip F T hT φ).val f = oddPartner ℓ (φ.val f) := by
  change (if f.val ∈ T then oddPartner ℓ (φ.val f) else φ.val f) = _
  exact ite_eq_left h

open Classical in
/-- The value of `flip` at a flag not in `T`. -/
theorem EdgeSubset.OddColouring.flip_val_not_mem
    (T : Finset W.Flag) (hT : ∀ g ∈ T, W.pairing g ∈ T)
    (φ : F.OddColouring ℓ) (f : {f : W.Flag // f ∈ F.flags})
    (h : f.val ∉ T) :
    (EdgeSubset.OddColouring.flip F T hT φ).val f = φ.val f := by
  change (if f.val ∈ T then oddPartner ℓ (φ.val f) else φ.val f) = _
  exact ite_eq_right h

end RS
