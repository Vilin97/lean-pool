/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite cancellation kernels for barycentric subdivision

This file collects the purely finite, abstract algebraic cancellation and
reindexing lemmas used in the boundary computation for barycentric subdivision.

They are stated for arbitrary finite index types and abelian groups, so they are
independent of any singular-chain or face-map API:

* `finite_sum_cancel_of_fixedPointFree_involution`: a fixed-point-free involution
 pairing terms with opposite signs makes the total sum vanish;
* `internal_faces_cancel_for_index` / `internal_faces_double_sum_cancel`: the
 specializations used to cancel internal boundary faces;
* `last_faces_reindex_of_equiv`: a finite reindexing principle for the last
 faces.

No chain-level boundary statement is asserted here.
-/

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/--
A fixed-point-free involution cancellation principle for finite sums.

In the barycentric subdivision proof, `α` is `Equiv.Perm (Fin (n+2))`,
`ι π = (swap i i+1).trans π`, and `f π` is the corresponding internal face term.
-/
theorem finite_sum_cancel_of_fixedPointFree_involution
    {α M : Type} [Fintype α]  [AddCommGroup M]
    (ι : α → α) (hιι : Function.Involutive ι) (hneq : ∀ a, ι a ≠ a)
    (f : α → M) (hpair : ∀ a, f (ι a) = - f a) :
    (∑ a : α, f a) = 0 := by
  classical
  -- Mathlib's non-dependent involution cancellation lemma.
  -- Its result is phrased as a sum over membership in a finset; with `univ`
  -- this is exactly the ordinary Fintype sum.
  have hmain : (∑ a ∈ (Finset.univ : Finset α), f a) = 0 := by
    simpa using
      (Finset.sum_ninvolution
        (s := (Finset.univ : Finset α))
        (f := f)
        (g := ι)
        (hg₁ := by
          intro a
          rw [hpair a]
          exact add_neg_cancel (f a))
        (hg₂ := by
          intro a _ha
          exact hneq a)
        (g_mem := by
          intro a
          simp)
        (hg₃ := by
          intro a
          exact hιι a))
  simpa using hmain

/-- Internal barycentric boundary faces cancel for each fixed internal face index. -/
theorem internal_faces_cancel_for_index
    {α M : Type} [Fintype α] [AddCommGroup M]
    (ι : α → α) (hιι : Function.Involutive ι) (hneq : ∀ a, ι a ≠ a)
    (T : α → M) (hT : ∀ a, T (ι a) = - T a) :
    (∑ a : α, T a) = 0 :=
  finite_sum_cancel_of_fixedPointFree_involution ι hιι hneq T hT

/-- Double internal-face cancellation after summing over all internal face indices. -/
theorem internal_faces_double_sum_cancel
    {ιx α M : Type} [Fintype ιx] [Fintype α] [DecidableEq α] [AddCommGroup M]
    (swapFor : ιx → α → α)
    (hswap_invol : ∀ i, Function.Involutive (swapFor i))
    (hswap_ne : ∀ i a, swapFor i a ≠ a)
    (T : α → ιx → M)
    (hpair : ∀ i a, T (swapFor i a) i = - T a i) :
    (∑ a : α, ∑ i : ιx, T a i) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  exact internal_faces_cancel_for_index
    (swapFor i) (hswap_invol i) (hswap_ne i) (fun a => T a i) (hpair i)

/--
A finite reindexing principle for the last faces.

In the barycentric subdivision proof, `α` is the set of permutations of
`Fin (n+2)` and `β` is the sigma type of a deleted boundary vertex and a
permutation of the remaining vertices. The equivalence is intended to be
`π ↦ (π last, lastFacePermutation π)`.
-/
theorem last_faces_reindex_of_equiv
    {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M]
    (e : α ≃ β) (L : α → M) (Rhs : β → M)
    (h : ∀ a, L a = Rhs (e a)) :
    (∑ a : α, L a) = ∑ b : β, Rhs b := by
  classical
  calc
    (∑ a : α, L a) = ∑ a : α, Rhs (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact h a
    _ = ∑ b : β, Rhs b := by
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end AffineBarycentricSubdivision
end SphereOddDegree
