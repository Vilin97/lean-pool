/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — Module D2 : assembling the per-round matchings

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

The nibble builds its final matching as the union of the matchings produced in each round. Because
each round works on the residual hypergraph (vertices not yet covered), the round matchings have
pairwise-disjoint *supports*. This module proves the deterministic assembly facts:

* `biUnion_isMatching` — a family of matchings of `H` with pairwise-disjoint supports unions to a
  single matching of `H`.
* `biUnion_card` — if additionally all edges are nonempty (true for `r ≥ 1`), the union's size is
  the sum of the per-round sizes.

Definitions (`IsMatching`, `support`) come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` / `LeanPool.AsymptoticTrianglePacking.Internal.Greedy`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V] {ι : Type*} [DecidableEq ι]

/-- An edge of a family is contained in the family's support. -/
theorem subset_support {M : Finset (Finset V)} {e : Finset V} (he : e ∈ M) :
    e ⊆ support M := by
  intro x hx
  rw [support, Finset.mem_biUnion]
  exact ⟨e, he, hx⟩

/-- **D2a — union of disjoint-support matchings is a matching.** -/
theorem biUnion_isMatching {H : Finset (Finset V)} (T : Finset ι) (M : ι → Finset (Finset V))
    (hM : ∀ i ∈ T, IsMatching H (M i))
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support (M i)) (support (M j))) :
    IsMatching H (T.biUnion M) where
  subset := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨i, hi, hei⟩ := he
    exact (hM i hi).subset hei
  disjoint := by
    intro e he f hf hef
    rw [Finset.mem_biUnion] at he hf
    obtain ⟨i, hi, hei⟩ := he
    obtain ⟨j, hj, hfj⟩ := hf
    by_cases hij : i = j
    · subst hij
      exact (hM i hi).disjoint e hei f hfj hef
    · exact Finset.disjoint_left.mpr fun x hxe hxf =>
        (Finset.disjoint_left.mp (hdisj i hi j hj hij) (subset_support hei hxe))
          (subset_support hfj hxf)

omit [DecidableEq ι] in
/-- **D2b — the union's size is the sum of the per-round sizes** (edges nonempty, e.g. `r ≥ 1`). -/
theorem biUnion_card {H : Finset (Finset V)} (T : Finset ι) (M : ι → Finset (Finset V))
    (hM : ∀ i ∈ T, IsMatching H (M i)) (hne : ∀ e ∈ H, e.Nonempty)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support (M i)) (support (M j))) :
    (T.biUnion M).card = ∑ i ∈ T, (M i).card := by
  rw [Finset.card_biUnion]
  intro i hi j hj hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro e hei hej
  obtain ⟨x, hx⟩ := hne e ((hM i hi).subset hei)
  exact (Finset.disjoint_left.mp (hdisj i hi j hj hij)
    (subset_support hei hx)) (subset_support hej hx)

end Hypergraph
