/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Module.Equiv.Basic
/-!
# Additive recoding of multiplicative equivalences

Turns a multiplicative group equivalence into the corresponding equivalence
between the additive recodings of its source and target.
-/

@[expose] public section
namespace LocalFieldTheory

noncomputable section

universe u

/-- Transport a multiplicative equivalence to an additive equivalence. -/
def additiveEquivOfMulEquiv {A B : Type u} [Group A] [Group B] (e : A ≃* B) :
    Additive A ≃+ Additive B where
  toFun := fun a => Additive.ofMul (e (Additive.toMul a))
  invFun := fun b => Additive.ofMul (e.symm (Additive.toMul b))
  left_inv := by
    intro a
    simp
  right_inv := by
    intro b
    simp
  map_add' := by
    intro a b
    ext
    exact e.map_mul _ _

end
end LocalFieldTheory
