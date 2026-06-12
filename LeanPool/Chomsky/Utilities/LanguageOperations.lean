/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import Mathlib.Computability.Language

/-!
# LanguageOperations

Operations on formal languages used throughout the development.
-/

namespace Chomsky

variable {T : Type}

/-- The image of a language under a bijection on the alphabet. -/
def Language.bijemap {T' : Type} (L : Language T) (π : Equiv T T') : Language T' :=
  (·.map π.invFun ∈ L)

/-- The image of a language under a permutation of the alphabet. -/
def Language.permute (L : Language T) (π : Equiv.Perm T) : Language T :=
  Language.bijemap L π

end Chomsky
