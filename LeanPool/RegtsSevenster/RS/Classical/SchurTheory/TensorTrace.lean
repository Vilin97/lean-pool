/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PermModule

/-!
# The tensor-space permutation representation and its character

The symmetric group `Equiv.Perm (Fin n)` acts on the full function
space `Fin n → Fin m` by precomposition with the inverse.  This is
the tensor space `(ℂ^m)^{⊗n}` in its basis-indexed form.  The
character of the induced representation equals the completed
cycle-type product at the constant sequence `fun _ => (m : ℂ)`.
-/

namespace RS

open Finset Equiv MonoidAlgebra



/-! ## The permutation action on the full function space -/

/-- The symmetric group acts on `Fin n → Fin m` by precomposition
with the inverse permutation. -/
instance tensorAction (n m : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (Fin n → Fin m) where
  smul π g := g ∘ ⇑π⁻¹
  one_smul g := by
    change g ∘ ⇑(1 : Equiv.Perm (Fin n))⁻¹ = g
    simp
  mul_smul π ρ g := by
    change g ∘ ⇑(π * ρ)⁻¹ = (g ∘ ⇑ρ⁻¹) ∘ ⇑π⁻¹
    rw [mul_inv_rev]
    rfl

/-! ## cycleProd at the constant sequence -/

/-- `cycleProd (fun _ => (m : ℂ)) π` equals `(m : ℂ) ^ #orbits`. -/
private theorem cycleProd_const (n m : ℕ) (π : Equiv.Perm (Fin n)) :
    cycleProd (fun _ => (m : ℂ)) π =
      (m : ℂ) ^ Fintype.card (OrbitSpace π) := by
  rw [cycleProd]
  rw [Multiset.map_const', Multiset.prod_replicate]
  rw [← pow_add, card_orbitSpace]

end RS
