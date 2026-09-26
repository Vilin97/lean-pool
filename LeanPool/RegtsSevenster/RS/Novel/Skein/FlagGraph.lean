/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# The strand, and the two branches of a glue

The flag model itself — fragments, relabelling, disjoint union, and
the single-pair gluing primitive — is defined in
`RS/Definitions.lean`.  This module carries the strand (the identity
2-fragment), the two branch equations of `gluePair`, and the sanity
checks that closing the strand onto itself yields one free circle
and no flags.
-/

@[expose] public section

namespace RS

namespace Fragment

variable {α β : Type}

/-! ### The strand -/

/-- The strand: a single edge with two boundary flags and no internal
vertices.  The identity 2-fragment. -/
def strand : Fragment (Fin 2) where
  Flag := Fin 2
  Vertex := Empty
  attach := fun f => Sum.inr f
  pairing := fun f => ⟨1 - f.val, by omega⟩
  pairing_invol := fun f => by ext; simp; omega
  pairing_ne := fun f => by
    intro h
    have := congr_arg Fin.val h
    simp at this
    omega
  boundaryFlag := id
  attach_boundaryFlag := fun ℓ => rfl
  eq_boundaryFlag := fun ℓ f h => Sum.inr.inj h
  circles := 0

/-! ### The two branches of a glue -/

/-- The closed branch of `gluePair`. -/
theorem gluePair_eq_closed {W : Fragment α} {i j : α} (hij : i ≠ j)
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    W.gluePair i j hij = W.gluePairClosed i j hclosed :=
  dite_eq_left hclosed

/-- The open branch of `gluePair`. -/
theorem gluePair_eq_open {W : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    W.gluePair i j hij = W.gluePairOpen i j hij hopen :=
  dite_eq_right hopen

/-! ### Sanity checks -/

/-- Closing the strand onto itself yields one free circle. -/
example :
    (strand.gluePair 0 1 (by decide)).circles = 1 := by
  rw [gluePair, dite_eq_left (by decide)]
  rfl

/-- Closing the strand onto itself leaves no flags. -/
example : (strand.gluePair 0 1 (by decide)).Flag → False := by
  decide

end Fragment

end RS
