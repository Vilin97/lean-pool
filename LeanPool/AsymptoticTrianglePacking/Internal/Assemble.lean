/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Iteration
import LeanPool.AsymptoticTrianglePacking.Internal.Assembly

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — D3 assembly : the accumulated matching is a matching

Standalone, Mathlib-only. The accumulated matching after `k` nibble rounds (`nibbleMatching`, D1) is
a genuine matching of `H`. The key is a cross-round invariant: the residual hypergraph after `k`
rounds is disjoint from the support of the accumulated matching (each round only matches edges that
avoid all previously covered vertices). Hence the round matchings have pairwise-disjoint supports
and their union is a matching — the assembly step of T3.

Definitions from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` /
`LeanPool.AsymptoticTrianglePacking.Internal.Greedy` /
`LeanPool.AsymptoticTrianglePacking.Internal.Round` /
`LeanPool.AsymptoticTrianglePacking.Internal.Iteration`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- Support of a union is the union of supports. -/
theorem support_union (M₁ M₂ : Finset (Finset V)) :
    support (M₁ ∪ M₂) = support M₁ ∪ support M₂ := by
  ext x
  simp only [support, Finset.mem_biUnion, id_eq, Finset.mem_union]
  constructor
  · rintro ⟨a, (ha | ha), hx⟩
    · exact Or.inl ⟨a, ha, hx⟩
    · exact Or.inr ⟨a, ha, hx⟩
  · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
    · exact ⟨a, Or.inl ha, hx⟩
    · exact ⟨a, Or.inr ha, hx⟩

/-- **D3a — accumulated matching stays inside `H`.** -/
theorem nibbleMatching_subset {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    nibbleMatching R H k ⊆ H := by
  induction k with
  | zero => exact Finset.empty_subset H
  | succ k ih =>
      change (nibbleIter R H k).1 ∪ roundMatching (R (nibbleIter R H k).2) ⊆ H
      refine Finset.union_subset ih ?_
      exact (roundMatching_subset _).trans
        ((hR _).trans (nibbleResidual_subset R H k))

/-- **D3b — cross-round invariant.** Every edge of the residual after `k` rounds is disjoint from
the support of the accumulated matching. -/
theorem nibbleResidual_disjoint_support {R : Finset (Finset V) → Finset (Finset V)}
    (H : Finset (Finset V)) (k : ℕ) :
    ∀ e ∈ nibbleResidual R H k, Disjoint e (support (nibbleMatching R H k)) := by
  induction k with
  | zero =>
      intro e _
      change Disjoint e (support (∅ : Finset (Finset V)))
      rw [support, Finset.biUnion_empty]
      exact Finset.disjoint_empty_right e
  | succ k ih =>
      intro e he
      change Disjoint e (support ((nibbleIter R H k).1 ∪ roundMatching (R (nibbleIter R H k).2)))
      rw [support_union, Finset.disjoint_union_right]
      have he' : e ∈ nibbleResidual R H k :=
        residual_subset (nibbleResidual R H k) (R (nibbleResidual R H k)) he
      refine ⟨ih e he', ?_⟩
      -- e ∈ residual_{k+1} avoids covered = support of the new round matching
      have := residual_disjoint_covered
        (H := nibbleResidual R H k) (R := R (nibbleResidual R H k)) (e := e) he
      rwa [covered] at this

/-- **D3 — the accumulated matching is a matching of `H`.** -/
theorem nibbleMatching_isMatching {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    IsMatching H (nibbleMatching R H k) where
  subset := nibbleMatching_subset hR H k
  disjoint := by
    induction k with
    | zero =>
        intro e he
        rw [show nibbleMatching R H 0 = (∅ : Finset (Finset V)) from rfl] at he
        exact absurd he (Finset.notMem_empty e)
    | succ k ih =>
        change ∀ e ∈ (nibbleIter R H k).1 ∪ roundMatching (R (nibbleIter R H k).2),
          ∀ f ∈ (nibbleIter R H k).1 ∪ roundMatching (R (nibbleIter R H k).2), e ≠ f → Disjoint e f
        intro e he f hf hef
        have hM : IsMatching (nibbleResidual R H k) (roundMatching (R (nibbleResidual R H k))) :=
          roundMatching_isMatching (hR _)
        have hinv := nibbleResidual_disjoint_support (R := R) H k
        rcases Finset.mem_union.mp he with heM | heR <;>
          rcases Finset.mem_union.mp hf with hfM | hfR
        · exact ih e heM f hfM hef
        · -- e ∈ acc, f ∈ new round: f ⊆ residual (disjoint from acc support), e ⊆ acc support
          have hfres : f ∈ nibbleResidual R H k := (hR _) (roundMatching_subset _ hfR)
          exact Finset.disjoint_left.mpr fun x hxe hxf =>
            (Finset.disjoint_left.mp (hinv f hfres) hxf) (subset_support heM hxe)
        · have heres : e ∈ nibbleResidual R H k := (hR _) (roundMatching_subset _ heR)
          exact Finset.disjoint_left.mpr fun x hxe hxf =>
            (Finset.disjoint_left.mp (hinv e heres) hxe) (subset_support hfM hxf)
        · exact hM.disjoint e heR f hfR hef

end Hypergraph
