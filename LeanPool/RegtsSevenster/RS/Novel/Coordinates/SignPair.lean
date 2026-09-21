/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.IndexPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexValue

/-!
# The sign pairing

For two duplicate-free same-membership lists, the product of
their mapped sorting signs is the reindexing permutation's sign:
the transport plus a square.
-/

namespace RS

open Classical

/-- **The sign pairing**: mapped sorting signs of two
enumerations multiply to the reindexing sign. -/
theorem sortSign_key_pair {γ : Type*} [DecidableEq γ]
    {β : Type} [LinearOrder β] (g : γ → β)
    (hg : Function.Injective g) (l₁ l₂ : List γ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hlen : l₁.length = l₂.length) :
    (sortSign (l₁.map g) : ℂ) * (sortSign (l₂.map g) : ℂ) =
      ((Equiv.Perm.sign
        (listIndexPerm l₁ l₂ h₁ h₂ hmem hlen) : ℤ) : ℂ) := by
  have htrans := sortSign_map_listIndexPerm l₁ l₂ h₁ h₂
    hmem hlen g (List.Nodup.map hg h₁)
  have hsq : (sortSign (l₁.map g) : ℂ) *
      (sortSign (l₁.map g) : ℂ) = 1 := sortSign_sq _
  calc (sortSign (l₁.map g) : ℂ) *
      (sortSign (l₂.map g) : ℂ)
      = (sortSign (l₁.map g) : ℂ) *
        (((Equiv.Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem
            hlen) : ℤ) : ℂ) *
          (sortSign (l₁.map g) : ℂ)) := by
        rw [show ((sortSign (l₂.map g) : ℤ) : ℂ) =
          ((Equiv.Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem
              hlen) : ℤ) : ℂ) *
            ((sortSign (l₁.map g) : ℤ) : ℂ) from by
          rw [htrans]
          push_cast
          ring]
    _ = ((sortSign (l₁.map g) : ℂ) *
          (sortSign (l₁.map g) : ℂ)) *
        ((Equiv.Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem
          hlen) : ℤ) : ℂ) := by ring
    _ = ((Equiv.Perm.sign (listIndexPerm l₁ l₂ h₁ h₂ hmem
          hlen) : ℤ) : ℂ) := by
        rw [hsq, one_mul]

end RS
