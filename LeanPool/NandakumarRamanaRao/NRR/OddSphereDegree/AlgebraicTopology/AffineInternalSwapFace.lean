/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineInternalSwapLemmas

/-!
# Internal face equality for affine barycentric subdivision

This file closes the affine part of the internal-face cancellation used in the
boundary computation for barycentric subdivision.

The key observation is that an internal face of the subdivided simplex is
obtained by restricting the affine map to the hyperface where the deleted
barycentric-coordinate is zero. On that hyperface, changing the permutation by
swapping the adjacent positions `i` and `i+1` changes only the deleted prefix
barycenter; all remaining prefix barycenters are equal by
`prefixBarycenter_internal_swap_eq`.

No chain-level boundary statement is asserted here. This is only the affine
face identity needed before the sign-cancellation proof.
-/

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- If two affine subdivision maps have the same prefix barycenters away from a
coordinate `i`, then they agree on the hyperface where the `i`-th barycentric
coordinate of the input is zero.

This is the generic linear-algebra lemma behind the internal adjacent-swap face
identity. -/
theorem affineSubdivMap_eq_of_zero_coord_and_prefixBarycenter_eq {m : ℕ}
    (π π' : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)) (x : Delta m)
    (hx : x i = 0)
    (hprefix : ∀ k : Fin (m + 1), k ≠ i →
      prefixBarycenter m π k = prefixBarycenter m π' k) :
    affineSubdivMap m π x = affineSubdivMap m π' x := by
  apply SphereOddDegree.FiniteSimplex.ext
  funext j
  rw [affineSubdivMap_apply, affineSubdivMap_apply]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [hx]
  · rw [hprefix k hki]

/-- Internal adjacent-swap affine face identity.

Let `τ` be the adjacent transposition swapping the `i`-th and `(i+1)`-st
positions in `Fin (n+2)`. The two affine subdivision maps associated to `π`
and `τ.trans π` agree on the hyperface where the deleted internal coordinate
`Fin.castSucc i` is zero.

In particular, after precomposition with the ordinary coface map
`δ_i : Δ^n → Δ^(n+1)` whose image is this hyperface, this gives the usual
identity

`a_π ∘ δ_i = a_(τ.trans π) ∘ δ_i`.

The coface map itself is intentionally not mentioned in the statement, so the
lemma is independent of the library's exact face-map API. -/
theorem affineSubdiv_face_internal_swap {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) (x : Delta (n + 1))
    (hx : x (Fin.castSucc i) = 0) :
    affineSubdivMap (n + 1) π x =
      affineSubdivMap (n + 1)
        ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) x := by
  exact affineSubdivMap_eq_of_zero_coord_and_prefixBarycenter_eq
    π ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π)
    (Fin.castSucc i) x hx
    (fun k hk => prefixBarycenter_internal_swap_eq π i k hk)

end AffineBarycentricSubdivision
end SphereOddDegree
