/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Iteration
import LeanPool.AsymptoticTrianglePacking.Internal.Assemble

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — round-dependent iteration of nibble rounds

Standalone, Mathlib-only. `LeanPool.AsymptoticTrianglePacking.Internal.Iteration` iterates ONE fixed
retention strategy `R`. The
obstruction `LeanPool.AsymptoticTrianglePacking.Internal.total_gain_le` shows that a fixed strategy
— in particular a fixed retention
probability `p` — can never cover more than a `(1-μ)d/(rΔ) ≤ 1/r` fraction of the vertex set, no
matter how many rounds are run: with `p` fixed, the residual degree decays like `(1-rΔp)^k` and so
does the per-round covering fraction, whose total is a convergent geometric series.

The nibble therefore has to re-tune its retention probability from round to round
(`p_k ≈ x / (r·d_k)`, tracking the shrinking residual degree `d_k`).  This file provides the
corresponding deterministic scaffolding: iteration along a *sequence* `R : ℕ → strategy` of
retention strategies, with all the round-to-round invariants of
`LeanPool.AsymptoticTrianglePacking.Internal.Iteration` and
`LeanPool.AsymptoticTrianglePacking.Internal.Assemble` re-established.

* `nibbleIterSeq`, `nibbleResidualSeq`, `nibbleMatchingSeq` — the sequence-indexed iteration.
* `nibbleResidualSeq_subset`, `nibbleResidualSeq_uniform` — residual invariants.
* `nibbleResidualSeq_disjoint_support`, `nibbleMatchingSeq_isMatching` — the assembly invariants.
* `nibbleIterSeq_const` — the constant sequence recovers
  `LeanPool.AsymptoticTrianglePacking.Internal.Iteration`.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- Run `k` nibble rounds from `H`, using the strategy `R i` in round `i`; returns
`(accumulated matching, current residual)`. -/
def nibbleIterSeq (R : ℕ → Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) :
    ℕ → Finset (Finset V) × Finset (Finset V)
  | 0 => (∅, H)
  | (k + 1) =>
      ((nibbleIterSeq R H k).1 ∪ roundMatching (R k (nibbleIterSeq R H k).2),
        residual (nibbleIterSeq R H k).2 (R k (nibbleIterSeq R H k).2))

/-- The residual hypergraph after `k` rounds of a strategy sequence. -/
def nibbleResidualSeq (R : ℕ → Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V))
    (k : ℕ) : Finset (Finset V) := (nibbleIterSeq R H k).2

/-- The matching accumulated over `k` rounds of a strategy sequence. -/
def nibbleMatchingSeq (R : ℕ → Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V))
    (k : ℕ) : Finset (Finset V) := (nibbleIterSeq R H k).1

/-- The constant strategy sequence recovers the single-strategy iteration. -/
theorem nibbleIterSeq_const (R : Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) :
    ∀ k, nibbleIterSeq (fun _ => R) H k = nibbleIter R H k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((nibbleIterSeq (fun _ => R) H k).1 ∪
        roundMatching (R (nibbleIterSeq (fun _ => R) H k).2),
        residual (nibbleIterSeq (fun _ => R) H k).2 (R (nibbleIterSeq (fun _ => R) H k).2))
        = ((nibbleIter R H k).1 ∪ roundMatching (R (nibbleIter R H k).2),
        residual (nibbleIter R H k).2 (R (nibbleIter R H k).2))
      rw [ih]

/-- The residual after `k` rounds is a sub-hypergraph of `H`. -/
theorem nibbleResidualSeq_subset (R : ℕ → Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) : nibbleResidualSeq R H k ⊆ H := by
  induction k with
  | zero => exact Finset.Subset.refl H
  | succ k ih =>
      change residual (nibbleIterSeq R H k).2 (R k (nibbleIterSeq R H k).2) ⊆ H
      exact (residual_subset _ _).trans ih

/-- The residual stays `r`-uniform. -/
theorem nibbleResidualSeq_uniform {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    (R : ℕ → Finset (Finset V) → Finset (Finset V)) (k : ℕ) :
    IsUniform (nibbleResidualSeq R H k) r := by
  induction k with
  | zero => exact hr
  | succ k ih =>
      change IsUniform (residual (nibbleIterSeq R H k).2 (R k (nibbleIterSeq R H k).2)) r
      exact residual_uniform ih (R k (nibbleIterSeq R H k).2)

/-- The accumulated matching stays inside `H`. -/
theorem nibbleMatchingSeq_subset {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    nibbleMatchingSeq R H k ⊆ H := by
  induction k with
  | zero => exact Finset.empty_subset H
  | succ k ih =>
      change (nibbleIterSeq R H k).1 ∪ roundMatching (R k (nibbleIterSeq R H k).2) ⊆ H
      refine Finset.union_subset ih ?_
      exact (roundMatching_subset _).trans
        ((hR _ _).trans (nibbleResidualSeq_subset R H k))

/-- Cross-round invariant: every edge of the residual after `k` rounds avoids everything covered so
far. -/
theorem nibbleResidualSeq_disjoint_support {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (H : Finset (Finset V)) (k : ℕ) :
    ∀ e ∈ nibbleResidualSeq R H k, Disjoint e (support (nibbleMatchingSeq R H k)) := by
  induction k with
  | zero =>
      intro e _
      change Disjoint e (support (∅ : Finset (Finset V)))
      rw [support, Finset.biUnion_empty]
      exact Finset.disjoint_empty_right e
  | succ k ih =>
      intro e he
      change Disjoint e
        (support ((nibbleIterSeq R H k).1 ∪ roundMatching (R k (nibbleIterSeq R H k).2)))
      rw [support_union, Finset.disjoint_union_right]
      have he' : e ∈ nibbleResidualSeq R H k :=
        residual_subset (nibbleResidualSeq R H k) (R k (nibbleResidualSeq R H k)) he
      refine ⟨ih e he', ?_⟩
      have hd := residual_disjoint_covered
        (H := nibbleResidualSeq R H k) (R := R k (nibbleResidualSeq R H k)) (e := e) he
      rwa [covered] at hd

/-- The accumulated matching is a matching of `H`. -/
theorem nibbleMatchingSeq_isMatching {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    IsMatching H (nibbleMatchingSeq R H k) where
  subset := nibbleMatchingSeq_subset hR H k
  disjoint := by
    induction k with
    | zero =>
        intro e he
        rw [show nibbleMatchingSeq R H 0 = (∅ : Finset (Finset V)) from rfl] at he
        exact absurd he (Finset.notMem_empty e)
    | succ k ih =>
        change ∀ e ∈ (nibbleIterSeq R H k).1 ∪ roundMatching (R k (nibbleIterSeq R H k).2),
          ∀ f ∈ (nibbleIterSeq R H k).1 ∪ roundMatching (R k (nibbleIterSeq R H k).2),
            e ≠ f → Disjoint e f
        intro e he f hf hef
        have hM : IsMatching (nibbleResidualSeq R H k)
            (roundMatching (R k (nibbleResidualSeq R H k))) :=
          roundMatching_isMatching (hR _ _)
        have hinv := nibbleResidualSeq_disjoint_support (R := R) H k
        rcases Finset.mem_union.mp he with heM | heR <;>
          rcases Finset.mem_union.mp hf with hfM | hfR
        · exact ih e heM f hfM hef
        · have hfres : f ∈ nibbleResidualSeq R H k := (hR _ _) (roundMatching_subset _ hfR)
          exact Finset.disjoint_left.mpr fun x hxe hxf =>
            (Finset.disjoint_left.mp (hinv f hfres) hxf) (subset_support heM hxe)
        · have heres : e ∈ nibbleResidualSeq R H k := (hR _ _) (roundMatching_subset _ heR)
          exact Finset.disjoint_left.mpr fun x hxe hxf =>
            (Finset.disjoint_left.mp (hinv e heres) hxe) (subset_support hfM hxf)
        · exact hM.disjoint e heR f hfR hef

/-- New vertices covered in round `k` add exactly to the accumulated covered count. -/
theorem nibbleMatchingSeq_support_card_succ {R : ℕ → Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ k H', R k H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    (support (nibbleMatchingSeq R H (k + 1))).card
      = (support (nibbleMatchingSeq R H k)).card
        + (support (roundMatching (R k (nibbleResidualSeq R H k)))).card := by
  have hdisj : Disjoint (support (nibbleMatchingSeq R H k))
      (support (roundMatching (R k (nibbleResidualSeq R H k)))) := by
    rw [Finset.disjoint_left]
    intro x hxacc hxround
    rw [support, Finset.mem_biUnion] at hxround
    obtain ⟨e, heround, hxe⟩ := hxround
    have heres : e ∈ nibbleResidualSeq R H k := (hR _ _) (roundMatching_subset _ heround)
    exact (Finset.disjoint_left.mp
      (nibbleResidualSeq_disjoint_support (R := R) H k e heres) hxe) hxacc
  have hunion : nibbleMatchingSeq R H (k + 1)
      = nibbleMatchingSeq R H k ∪ roundMatching (R k (nibbleResidualSeq R H k)) := rfl
  rw [hunion, support_union, Finset.card_union_of_disjoint hdisj]

end Hypergraph
