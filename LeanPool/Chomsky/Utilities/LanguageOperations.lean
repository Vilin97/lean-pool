/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import Mathlib.Computability.Language

variable {T : Type}

def Language.bijemap {T' : Type} (L : Language T) (π : Equiv T T') : Language T' :=
  (·.map π.invFun ∈ L)

def Language.permute (L : Language T) (π : Equiv.Perm T) : Language T :=
  L.bijemap π
