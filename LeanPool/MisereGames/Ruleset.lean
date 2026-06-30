/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.GameForm
public import LeanPool.MisereGames.Form.Classes

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

public section

open Form

/-- A playable ruleset whose positions map to `GameForm`s. -/
class Ruleset (R : Type u) where
  /-- The game form represented by a ruleset position. -/
  toGameForm : R → GameForm.{u}
  moves_toGameForm (p : Player) (r : R) :
      ∀ g' ∈ Form.moves p (toGameForm r), ∃ r', toGameForm r' = g'

/--
Set of `GameForm`s created by the positions in ruleset `R`.
-/
def Ruleset.Forms (R : Type u) [Ruleset R] (g : GameForm.{u}) : Prop
  := ∃ (r : R), g = Ruleset.toGameForm r

theorem Ruleset.Forms.exists {R : Type u} [Ruleset R] {g : GameForm.{u}}
    (h_g : Ruleset.Forms R g) : ∃ (r : R), g = Ruleset.toGameForm r := by
  unfold Forms at h_g
  exact h_g

theorem Ruleset.Forms.position_mem {R : Type u} [Ruleset R] (r : R) :
    Ruleset.Forms R (Ruleset.toGameForm r) := by
  unfold Forms
  use r

instance {R : Type u} [Ruleset R] : Hereditary (Ruleset.Forms R) where
  has_option h_g h_g' := by
    simp only [isOption_iff_mem_moves] at h_g'
    obtain ⟨p, h_g'⟩ := h_g'
    obtain ⟨r, h_r⟩ := Ruleset.Forms.exists h_g
    subst h_r
    have ⟨r', h_r'⟩ := Ruleset.moves_toGameForm p r _ h_g'
    subst h_r'
    exact Ruleset.Forms.position_mem r'

end

end MisereGames
