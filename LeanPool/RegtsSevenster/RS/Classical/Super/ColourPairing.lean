/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPower

/-!
# The tensor-power pairing in colouring coordinates

The accompanying paper's pinned pairing (§5.1):

    β_d(v₁⊗⋯⊗v_d, w₁⊗⋯⊗w_d)
      = (−1)^{Σ_{i<j} |v_j||w_i|} ∏ᵢ b(vᵢ, wᵢ).

On colouring basis vectors this is a sign times a product of
single-position form entries: `1` on matching even colours, the
symplectic entry on odd colours, `0` on mixed positions.
-/

namespace RS

/-- The single-position form entry: Kronecker on even colours,
the symplectic matrix on odd colours, zero on mixed. -/
def colourFormEntry (k ℓ : ℕ) :
    (Fin k ⊕ Fin (2 * ℓ)) → (Fin k ⊕ Fin (2 * ℓ)) → ℂ
  | Sum.inl i, Sum.inl j => if i = j then 1 else 0
  | Sum.inr a, Sum.inr b =>
      if a.val + ℓ = b.val then 1
      else if b.val + ℓ = a.val then -1 else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- The Koszul crossing count of a colouring pair: pairs of
positions `i < j` with the second argument odd at `i` and the
first odd at `j`. -/
def koszulCrossings {k ℓ d : ℕ}
    (c c' : MixedColouring k ℓ d) : ℕ :=
  (Finset.univ.filter (fun p : Fin d × Fin d =>
    p.1 < p.2 ∧ (c p.2).isRight ∧ (c' p.1).isRight)).card

/-- **The pinned tensor-power pairing** on colouring basis
vectors. -/
noncomputable def betaColour {k ℓ d : ℕ}
    (c c' : MixedColouring k ℓ d) : ℂ :=
  (-1 : ℂ) ^ koszulCrossings c c' *
    ∏ i : Fin d, colourFormEntry k ℓ (c i) (c' i)

/-- Mixed positions kill the pairing. -/
theorem betaColour_eq_zero_of_mixed {k ℓ d : ℕ}
    {c c' : MixedColouring k ℓ d} (i : Fin d)
    (h : (c i).isRight ≠ (c' i).isRight) :
    betaColour c c' = 0 := by
  unfold betaColour
  rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
  rcases hc : c i with a | a <;> rcases hc' : c' i with b | b <;>
    simp [colourFormEntry] <;>
    simp [hc, hc'] at h

end RS
