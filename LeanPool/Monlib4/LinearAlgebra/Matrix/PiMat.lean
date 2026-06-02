/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Data.Matrix.Basic

/-!
# LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat`.
-/

/-- Square matrices over `R` indexed by `n`. -/
abbrev Mat (R n : Type*) := Matrix n n R

/-- Families of square matrices whose index type can vary with the family index. -/
abbrev PiMat (R k : Type*) (s : k → Type*) :=
Π i, (fun j => Mat R (s j)) i

@[ext]
theorem PiMat.ext {R k : Type*} {s : k → Type*} {x y : PiMat R k s}
    (h : ∀ i, x i = y i) : x = y :=
  funext h
