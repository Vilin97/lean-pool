/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Linear combinations of intertwining endomorphisms

An intertwining relation is preserved by addition and scalar
multiplication in a linear category.
-/

namespace RS

open CategoryTheory

/-- Intertwining endomorphisms are closed under addition. -/
theorem intertwine_add {A : Type*} [Category A] [Preadditive A]
    {P Q : A} {a b : P ⟶ P} {a' b' : Q ⟶ Q} {T : P ⟶ Q}
    (ha : a ≫ T = T ≫ a') (hb : b ≫ T = T ≫ b') :
    (a + b) ≫ T = T ≫ (a' + b') := by
  rw [Preadditive.add_comp, Preadditive.comp_add, ha, hb]

/-- Intertwining endomorphisms are closed under scalar multiplication. -/
theorem intertwine_smul {A : Type*} [Category A] [Preadditive A]
    [Linear ℂ A] {P Q : A} {a : P ⟶ P} {a' : Q ⟶ Q}
    {T : P ⟶ Q} (r : ℂ) (h : a ≫ T = T ≫ a') :
    (r • a) ≫ T = T ≫ (r • a') := by
  rw [Linear.smul_comp, Linear.comp_smul, h]

end RS
