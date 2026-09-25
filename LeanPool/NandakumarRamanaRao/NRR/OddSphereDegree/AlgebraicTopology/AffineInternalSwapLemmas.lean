/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineBarycentricSubdivision

/-!
# Internal-swap barycenter lemmas for barycentric subdivision

This file supplies the three local lemmas needed before proving the internal
face-cancellation part of the barycentric-subdivision boundary identity.

The main theorem is `prefixBarycenter_internal_swap_eq`: if `τ` is the adjacent
swap of the `i`-th and `(i+1)`-st ambient vertices, then every prefix
barycenter except the deleted `i`-th one is unchanged after replacing `π` by
`τ.trans π`.

The proof is deliberately stated in terms of reindexing of the prefix domain;
this is the right form for the later face-map proof.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

section BarycenterReindex

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-
The barycenter of a standard simplex is invariant under reindexing by an
 equivalence.
-/
theorem stdSimplex_map_barycenter_equiv (e : X ≃ Y) [Nonempty X] [Nonempty Y] :
    SphereOddDegree.FiniteSimplex.map (S := ℝ) (X := X) (Y := Y) e
        (SphereOddDegree.FiniteSimplex.barycenter (X := X) (𝕜 := ℝ))
      = SphereOddDegree.FiniteSimplex.barycenter (X := Y) (𝕜 := ℝ) := by
  classical
  apply SphereOddDegree.FiniteSimplex.ext
  funext y
  -- `SphereOddDegree.FiniteSimplex.map` is `FunOnFinite.linearMap`; for an equivalence each fiber
  -- has exactly one point, namely `e.symm y`.
  convert congr_arg ( fun f => f y ) ( SphereOddDegree.FiniteSimplex.map_coe e
    SphereOddDegree.FiniteSimplex.barycenter ) using 1; simp +decide [
    SphereOddDegree.FiniteSimplex.barycenter ];
  simp +decide [ FunOnFinite.linearMap, Fintype.card_congr e ]

/-- If two maps out of the prefix domain differ only by a permutation of that
 domain, then the corresponding prefix barycenters are equal. -/
theorem prefixBarycenter_eq_of_prefix_reindex {n : ℕ}
    {π π' : Equiv.Perm (Fin (n + 1))} {k : Fin (n + 1)}
    (e : Equiv.Perm (Fin (k.val + 1)))
    (h : ∀ t : Fin (k.val + 1),
      prefixVertex n π k t = prefixVertex n π' k (e t)) :
    prefixBarycenter n π k = prefixBarycenter n π' k := by
  classical
  unfold prefixBarycenter
  calc
    SphereOddDegree.FiniteSimplex.map (S := ℝ) (prefixVertex n π k)
        (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ))
        = SphereOddDegree.FiniteSimplex.map (S := ℝ) ((prefixVertex n π' k) ∘ e)
          (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ)) := by
            congr 1
            funext t
            exact h t
    _ = SphereOddDegree.FiniteSimplex.map (S := ℝ) (prefixVertex n π' k)
          (SphereOddDegree.FiniteSimplex.map (S := ℝ) e
            (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ))) := by
            rw [SphereOddDegree.FiniteSimplex.map_comp_apply]
    _ = SphereOddDegree.FiniteSimplex.map (S := ℝ) (prefixVertex n π' k)
          (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ)) := by
            rw [stdSimplex_map_barycenter_equiv e]

end BarycenterReindex

/-! ## Internal adjacent swap on prefix barycenters -/

/-- The domain permutation used when a prefix already contains both adjacent
 indices `i` and `i+1`: swap their representatives in the smaller prefix
 domain. -/
noncomputable def prefixDomainAdjacentSwap {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 2)) (hik : i.val + 1 ≤ k.val) :
    Equiv.Perm (Fin (k.val + 1)) :=
  Equiv.swap
    ⟨i.val, by omega⟩
    ⟨i.val + 1, by omega⟩

/-
Reindexing identity for the internal adjacent swap. This is the raw
 vertex-level fact behind `prefixBarycenter_internal_swap_eq`.

Here `τ` swaps the ambient vertices `i` and `i+1`. If `k ≠ i`, then the
 `k`-prefix for `π` is the same finite set as the `k`-prefix for `τ.trans π`,
 up to a permutation of the prefix domain.
-/
theorem prefixVertex_internal_swap_reindex {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.castSucc i) :
    ∃ e : Equiv.Perm (Fin (k.val + 1)),
      ∀ t : Fin (k.val + 1),
        prefixVertex (n + 1) π k t =
          prefixVertex (n + 1)
            ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) k (e t) := by
  classical
  rcases lt_trichotomy k.val i.val with ( hk_lt | hk_eq | hk_gt ) <;> simp_all +decide only
      [ne_eq, prefixVertex, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq];
  · refine ⟨ Equiv.refl (Fin (k.val + 1)), ?_ ⟩; simp +decide [ Equiv.swap_apply_def ];
    grind;
  · exact False.elim <| hk <| Fin.ext hk_eq;
  · use Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩;
    intro t; by_cases h : t.val = i.val <;> by_cases h' : t.val = i.val + 1 <;> simp_all +decide
      [ Fin.ext_iff, Equiv.swap_apply_def ];

/-- Prefix barycenters are unchanged by the internal adjacent swap, except at
 the deleted prefix index itself.

This is the main local affine fact needed for the internal-face cancellation in
 the proof that barycentric subdivision commutes with the singular boundary. -/
theorem prefixBarycenter_internal_swap_eq {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.castSucc i) :
    prefixBarycenter (n + 1) π k =
      prefixBarycenter (n + 1)
        ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) k := by
  classical
  rcases prefixVertex_internal_swap_reindex π i k hk with ⟨e, he⟩
  exact prefixBarycenter_eq_of_prefix_reindex e he

end AffineBarycentricSubdivision
end SphereOddDegree
