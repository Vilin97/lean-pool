/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.Defs

import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data

namespace Distributed2Coloring.LowerBound

namespace N1000000AvailFrom

open Distributed2Coloring.LowerBound.N1000000Data

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n

/-- Symbols `≥ s` inside `Fin n`. -/
def AvailFrom (s : Nat) : Type :=
  { x : SymN // s ≤ x.1 }

noncomputable instance (s : Nat) : Fintype (AvailFrom (s := s)) := by
  dsimp [AvailFrom]
  infer_instance

theorem card_availFrom (s : Nat) : Fintype.card (AvailFrom (s := s)) = n - s := by
  classical
  let e : Fin (n - s) ≃ AvailFrom (s := s) :=
    { toFun := fun i =>
        let xVal : Nat := s + i.1
        have hx : xVal < n := by
          have hi : i.1 < n - s := i.2
          simpa [xVal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Nat.add_lt_of_lt_sub hi)
        ⟨⟨xVal, hx⟩, Nat.le_add_right _ _⟩
      invFun := fun x =>
        ⟨x.1.1 - s, by
          have hxlt : x.1.1 < n := x.1.2
          have : x.1.1 - s < n - s := Nat.sub_lt_sub_right x.2 hxlt
          simpa using this⟩
      left_inv := by
        intro i
        apply Fin.ext
        dsimp
        exact Nat.add_sub_cancel_left s i.1
      right_inv := by
        intro x
        apply Subtype.ext
        apply Fin.ext
        dsimp
        exact Nat.add_sub_of_le x.2 }
  simpa using (Fintype.card_congr e).symm

end N1000000AvailFrom

end Distributed2Coloring.LowerBound
