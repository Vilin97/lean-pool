/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

/-!
# Neighbours

This file defines neighbouring lists.
-/


variable {T : Type}

/--
Lists which differ by the inclusion or modification of an element.

This is SampCert's private property. 
-/
inductive Neighbour (l₁ l₂ : List T) : Prop where
  | Addition : l₁ = a ++ b → l₂ = a ++ [n] ++ b → Neighbour l₁ l₂
  | Deletion : l₁ = a ++ [n] ++ b → l₂ = a ++ b → Neighbour l₁ l₂
  | Update : l₁ = a ++ [n] ++ b → l₂ = a ++ [m] ++ b -> Neighbour l₁ l₂


/--
Neighbour relation is symmetric.
-/
def Neighbour_symm (l₁ l₂ : List T) (H : Neighbour l₁ l₂) : Neighbour l₂ l₁ := by
  cases H
  · rename_i _ _ _ Hl1 Hl2
    exact Neighbour.Deletion Hl2 Hl1
  · rename_i _ _ _ Hl1 Hl2
    exact Neighbour.Addition Hl2 Hl1
  · rename_i _ _ _ _ Hl1 Hl2
    exact Neighbour.Update Hl2 Hl1
