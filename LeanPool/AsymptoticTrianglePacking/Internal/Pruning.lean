/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — deterministic pruning: restoring a degree ceiling at a bounded cost

One nibble round halves all degrees *in expectation*, but the resulting residual has no deterministic
global degree ceiling: a few vertices may keep an atypically large residual degree.  The nibble
invariant needs such a ceiling (it fixes the retention probability of the next round), and a union
bound over the `|V|` vertices is not available (the degree scale `d` is not tied to `|V|`).

The standard repair is *pruning*: delete every edge that touches a vertex of too-large degree.  This
is completely deterministic, and this file quantifies its cost:

* `degree_pruneHigh_le` — after pruning at level `M`, every degree is `≤ M`;
* `card_prunedEdges_le` — the number of deleted edges is at most the total degree of the (few)
  high-degree vertices;
* `card_pruneDamaged_le` / `card_pruneDamaged_le_of_bounds` — the number of vertices whose degree
  drops by more than `t` is at most `r · (#high-degree vertices) · Δ / t`.

So if the high-degree vertices are a `b`-fraction of `V` and the degrees are `≤ Δ`, pruning damages
at most an `rbΔ/t`-fraction, which the round invariant absorbs into its exceptional set.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.InvariantDegree
import Mathlib.Analysis.RCLike.Basic

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- Prune a hypergraph at level `M`: delete every edge containing a vertex of degree `> M`. -/
noncomputable def pruneHigh (G : Finset (Finset V)) (M : ℝ) : Finset (Finset V) :=
  G.filter (fun e => ∀ v ∈ e, (degree G v : ℝ) ≤ M)

open scoped Classical in
/-- The vertices of degree above `M`. -/
noncomputable def highDeg (G : Finset (Finset V)) (M : ℝ) : Finset V :=
  Finset.univ.filter (fun v => M < (degree G v : ℝ))

open scoped Classical in
/-- The vertices whose degree drops by more than `t` when pruning at level `M`. -/
noncomputable def pruneDamaged (G : Finset (Finset V)) (M t : ℝ) : Finset V :=
  Finset.univ.filter (fun v => (degree (pruneHigh G M) v : ℝ) + t < (degree G v : ℝ))

theorem pruneHigh_subset (G : Finset (Finset V)) (M : ℝ) : pruneHigh G M ⊆ G := by
  classical
  exact Finset.filter_subset _ _

/-- **Pruning restores the ceiling.** -/
theorem degree_pruneHigh_le (G : Finset (Finset V)) {M : ℝ} (hM : 0 ≤ M) (v : V) :
    (degree (pruneHigh G M) v : ℝ) ≤ M := by
  classical
  by_cases h : (degree G v : ℝ) ≤ M
  · refine le_trans ?_ h
    exact_mod_cast degree_mono (pruneHigh_subset G M) v
  · have hz : degree (pruneHigh G M) v = 0 := by
      rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      simp only [pruneHigh, Finset.mem_filter] at he
      intro hve
      exact h (he.2 v hve)
    rw [hz]
    simpa using hM
/-- **The deleted edges are few.** Every deleted edge contains a vertex of degree `> M`, so their
number is at most the total degree of the high-degree vertices. -/
theorem card_prunedEdges_le (G : Finset (Finset V)) (M : ℝ) :
    (((G \ pruneHigh G M).card : ℕ) : ℝ) ≤ ∑ u ∈ highDeg G M, (degree G u : ℝ) := by
  classical
  have hsub : G \ pruneHigh G M ⊆ (highDeg G M).biUnion (fun u => G.filter (fun e => u ∈ e)) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨heG, henot⟩ := he
    have : ¬ (∀ v ∈ e, (degree G v : ℝ) ≤ M) := by
      intro hall
      exact henot (by simp only [pruneHigh, Finset.mem_filter]; exact ⟨heG, hall⟩)
    push_neg at this
    obtain ⟨u, hue, hu⟩ := this
    refine Finset.mem_biUnion.mpr ⟨u, ?_, ?_⟩
    · simp only [highDeg, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hu
    · simp only [Finset.mem_filter]
      exact ⟨heG, hue⟩
  have h1 : (G \ pruneHigh G M).card
      ≤ ∑ u ∈ highDeg G M, (G.filter (fun e => u ∈ e)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have h2 : ((G \ pruneHigh G M).card : ℝ)
      ≤ ((∑ u ∈ highDeg G M, (G.filter (fun e => u ∈ e)).card : ℕ) : ℝ) := by
    exact_mod_cast h1
  simpa [degree] using h2

/-- **The damage of pruning is small.** The number of vertices whose degree drops by more than `t`
is at most `r · #(deleted edges) / t`. -/
theorem card_pruneDamaged_le {G : Finset (Finset V)} {r : ℕ} (hr : IsUniform G r) (M t : ℝ) :
    ((pruneDamaged G M t).card : ℝ) * t ≤ (r : ℝ) * (((G \ pruneHigh G M).card : ℕ) : ℝ) := by
  classical
  set P := pruneHigh G M with hPdef
  have hPG : P ⊆ G := pruneHigh_subset G M
  -- the total degree drop equals `r · #(deleted edges)`
  have hsum : ∑ v : V, ((degree G v : ℝ) - (degree P v : ℝ))
      = (r : ℝ) * (((G \ P).card : ℕ) : ℝ) := by
    have h1 : ∑ v : V, (degree G v : ℝ) = (r : ℝ) * (G.card : ℝ) := by
      have hs := Hypergraph.sum_degree G hr
      have hc : ((∑ v : V, degree G v : ℕ) : ℝ) = ((r * G.card : ℕ) : ℝ) := by rw [hs]
      push_cast at hc
      exact hc
    have h2 : ∑ v : V, (degree P v : ℝ) = (r : ℝ) * (P.card : ℝ) := by
      have hPu : IsUniform P r := fun e he => hr e (hPG he)
      have hs := Hypergraph.sum_degree P hPu
      have hc : ((∑ v : V, degree P v : ℕ) : ℝ) = ((r * P.card : ℕ) : ℝ) := by rw [hs]
      push_cast at hc
      exact hc
    have h3 : ((G \ P).card : ℝ) = (G.card : ℝ) - (P.card : ℝ) := by
      have hadd : (G \ P).card + P.card = G.card := Finset.card_sdiff_add_card_eq_card hPG
      have : (((G \ P).card + P.card : ℕ) : ℝ) = ((G.card : ℕ) : ℝ) := by rw [hadd]
      push_cast at this
      linarith
    rw [Finset.sum_sub_distrib, h1, h2, h3]
    ring
  -- each damaged vertex contributes more than `t`
  have hnonneg : ∀ v : V, 0 ≤ (degree G v : ℝ) - (degree P v : ℝ) := by
    intro v
    have : degree P v ≤ degree G v := degree_mono hPG v
    have : (degree P v : ℝ) ≤ (degree G v : ℝ) := by exact_mod_cast this
    linarith
  have hDsum : ((pruneDamaged G M t).card : ℝ) * t
      ≤ ∑ v ∈ pruneDamaged G M t, ((degree G v : ℝ) - (degree P v : ℝ)) := by
    have hconst : ∑ _v ∈ pruneDamaged G M t, t = ((pruneDamaged G M t).card : ℝ) * t := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    refine Finset.sum_le_sum ?_
    intro v hv
    simp only [pruneDamaged, Finset.mem_filter] at hv
    have h := hv.2
    simp only [hPdef]
    linarith
  have hmono : ∑ v ∈ pruneDamaged G M t, ((degree G v : ℝ) - (degree P v : ℝ))
      ≤ ∑ v : V, ((degree G v : ℝ) - (degree P v : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hnonneg v)
  calc ((pruneDamaged G M t).card : ℝ) * t
      ≤ ∑ v ∈ pruneDamaged G M t, ((degree G v : ℝ) - (degree P v : ℝ)) := hDsum
    _ ≤ ∑ v : V, ((degree G v : ℝ) - (degree P v : ℝ)) := hmono
    _ = (r : ℝ) * (((G \ P).card : ℕ) : ℝ) := hsum

/-- **The damage of pruning, in terms of the number of high-degree vertices.** -/
theorem card_pruneDamaged_le_of_bounds {G : Finset (Finset V)} {r : ℕ} (hr : IsUniform G r)
    {M Δ b t : ℝ} (hΔ : ∀ u : V, (degree G u : ℝ) ≤ Δ) (hΔ0 : 0 ≤ Δ)
    (hb : ((highDeg G M).card : ℝ) ≤ b) :
    ((pruneDamaged G M t).card : ℝ) * t ≤ (r : ℝ) * b * Δ := by
  classical
  have h1 := card_pruneDamaged_le hr M t
  have h2 : (((G \ pruneHigh G M).card : ℕ) : ℝ) ≤ b * Δ := by
    refine le_trans (card_prunedEdges_le G M) ?_
    have hsum : ∑ u ∈ highDeg G M, (degree G u : ℝ)
        ≤ ∑ _u ∈ highDeg G M, Δ := Finset.sum_le_sum (fun u _ => hΔ u)
    have : ∑ _u ∈ highDeg G M, Δ = ((highDeg G M).card : ℝ) * Δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [this] at hsum
    exact le_trans hsum (mul_le_mul_of_nonneg_right hb hΔ0)
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  calc ((pruneDamaged G M t).card : ℝ) * t
      ≤ (r : ℝ) * (((G \ pruneHigh G M).card : ℕ) : ℝ) := h1
    _ ≤ (r : ℝ) * (b * Δ) := mul_le_mul_of_nonneg_left h2 hrnn
    _ = (r : ℝ) * b * Δ := by ring

end LeanPool.AsymptoticTrianglePacking.Internal
