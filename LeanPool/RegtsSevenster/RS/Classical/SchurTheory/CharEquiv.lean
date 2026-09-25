/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeTable

/-!
# Character invariance under representation equivalence

The character of a representation is invariant under equivalence:
two equivalent representations have the same character at every
group element.  The corollary specialises this to the native
submodule representations `rhoS`.
-/

@[expose] public section

namespace RS

open Finset LinearMap

variable {G : Type*}

/-- Equivalent representations have the same character. -/
theorem character_of_equiv [Group G]
    {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (g : G) :
    ρ.character g = σ.character g :=
  congr_fun (Representation.char_iso e) g

/-- Equivalent native representations have the same native
character. -/
theorem nChar_of_equiv [Group G] [Finite G]
    {S T : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)}
    (e : (rhoS S).Equiv (rhoS T)) (g : G) :
    nChar S g = nChar T g := by
  classical
  let := Fintype.ofFinite G
  unfold nChar
  exact character_of_equiv e g

end RS
