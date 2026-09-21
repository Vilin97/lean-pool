/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the star (complete bipartite) counterexample to the *majority* interfaces

Standalone, Mathlib-only.  This file builds the hypergraph witness that refutes the **majority**
near-regularity interface `LeanPool.AsymptoticTrianglePacking.Internal.NibbleTheoremMost` — and therefore also the adaptive oracle atom
`LeanPool.AsymptoticTrianglePacking.Internal.AdaptiveOracleExists`, which implies it (`LeanPool.AsymptoticTrianglePacking.Internal.nibbleTheoremMost_of_adaptiveOracle`).

The witness is the complete bipartite graph `K_{m,D}` on `Fin m ⊕ Fin D`, viewed as a `2`-uniform
hypergraph:

* every *left* vertex has degree exactly `D`, so the graph is exactly `D`-regular outside the
  exceptional set `Exc = {right vertices}` of size `D`, which is `≤ η·(m+D)` once `m` is large;
* the codegree of any two distinct vertices is at most `1` (in a graph, two vertices lie in at most
  one edge), hence `≤ μ·D` as soon as `D ≥ 1/μ`;
* but every edge meets the right side, so **every matching has at most `D` edges**, while the
  majority interface demands a matching of size `≥ (1-β)·(m+D)/2`.

Taking `m > 3D` contradicts the demand at `β = 1/2`.  Morally: the `η`-fraction exceptional set of
`NearlyRegularMost` is allowed to carry *all* the edges, so majority near-regularity alone (without a
global degree ceiling) says nothing about the matching number.  The repaired interface is
`NibbleTheoremMostCeil`, which adds the global ceiling `deg ≤ (1+μ)d` — the star witness has right
degrees `m ≫ (1+μ)D`, so it is excluded there.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Regular
import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-! ## The star (complete bipartite) hypergraph -/

/-- Vertex type of the counterexample: `m` "good" vertices and `D` "exceptional" ones. -/
abbrev StarVtx (m D : ℕ) : Type := Fin m ⊕ Fin D

/-- The complete bipartite graph `K_{m,D}` as a `2`-uniform hypergraph. -/
def starHG (m D : ℕ) : Finset (Finset (StarVtx m D)) :=
  Finset.image (fun q : Fin m × Fin D => ({Sum.inl q.1, Sum.inr q.2} : Finset (StarVtx m D)))
    Finset.univ

theorem mem_starHG (m D : ℕ) (e : Finset (StarVtx m D)) :
    e ∈ starHG m D ↔ ∃ a b, e = ({Sum.inl a, Sum.inr b} : Finset (StarVtx m D)) := by
  simp [starHG, eq_comm]

/-- The star hypergraph is `2`-uniform. -/
theorem starHG_isUniform (m D : ℕ) : IsUniform (starHG m D) 2 := by
  intro e he
  obtain ⟨a, b, rfl⟩ := (mem_starHG m D e).mp he
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

/-- Left vertices have degree exactly `D`. -/
theorem starHG_degree_inl (m D : ℕ) (a : Fin m) :
    degree (starHG m D) (Sum.inl a) = D := by
  classical
  have hfil : (starHG m D).filter (fun e => (Sum.inl a : StarVtx m D) ∈ e)
      = Finset.image (fun b : Fin D => ({Sum.inl a, Sum.inr b} : Finset (StarVtx m D)))
          Finset.univ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, mem_starHG, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a', b', rfl⟩, ha⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h | h
      · exact ⟨b', by rw [Sum.inl.inj h]⟩
      · exact absurd h (by simp)
    · rintro ⟨b, rfl⟩
      exact ⟨⟨a, b, rfl⟩, by simp⟩
  rw [degree, hfil, Finset.card_image_of_injective _ ?inj, Finset.card_univ, Fintype.card_fin]
  case inj =>
    intro b b' h
    simp only at h
    have : (Sum.inr b : StarVtx m D) ∈ ({Sum.inl a, Sum.inr b'} : Finset (StarVtx m D)) := by
      rw [← h]; simp
    simpa using this

/-- Right vertices have degree exactly `m`.  Together with `starHG_degree_inl` this records that the
witness violates the global degree ceiling `deg ≤ (1+μ)·D` as soon as `m > (1+μ)·D` — which is why
the repaired interface `NibbleTheoremMostCeil` is not touched by it. -/
theorem starHG_degree_inr (m D : ℕ) (b : Fin D) :
    degree (starHG m D) (Sum.inr b) = m := by
  classical
  have hfil : (starHG m D).filter (fun e => (Sum.inr b : StarVtx m D) ∈ e)
      = Finset.image (fun a : Fin m => ({Sum.inl a, Sum.inr b} : Finset (StarVtx m D)))
          Finset.univ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, mem_starHG, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a', b', rfl⟩, hb⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with h | h
      · exact absurd h (by simp)
      · exact ⟨a', by rw [Sum.inr.inj h]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, b, rfl⟩, by simp⟩
  rw [degree, hfil, Finset.card_image_of_injective _ ?inj, Finset.card_univ, Fintype.card_fin]
  case inj =>
    intro a a' h
    simp only at h
    have : (Sum.inl a : StarVtx m D) ∈ ({Sum.inl a', Sum.inr b} : Finset (StarVtx m D)) := by
      rw [← h]; simp
    simpa using this

/-- In a graph, two distinct vertices lie in at most one edge. -/
theorem starHG_codegree_le_one (m D : ℕ) {x y : StarVtx m D} (hxy : x ≠ y) :
    codegree (starHG m D) x y ≤ 1 := by
  classical
  have hsub : (starHG m D).filter (fun e => x ∈ e ∧ y ∈ e) ⊆ {({x, y} : Finset (StarVtx m D))} := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨he, hx, hy⟩ := he
    have hcard : e.card = 2 := starHG_isUniform m D e he
    have hxy2 : ({x, y} : Finset (StarVtx m D)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    have hincl : ({x, y} : Finset (StarVtx m D)) ⊆ e := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have : e = ({x, y} : Finset (StarVtx m D)) :=
      (Finset.eq_of_subset_of_card_le hincl (by rw [hcard, hxy2])).symm
    simp [this]
  calc codegree (starHG m D) x y ≤ ({({x, y} : Finset (StarVtx m D))} : Finset _).card :=
        Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- **Every matching of the star hypergraph has at most `D` edges**: each edge uses exactly one of
the `D` right vertices, and matching edges are disjoint. -/
theorem starHG_matching_card_le {m D : ℕ} {M : Finset (Finset (StarVtx m D))}
    (hM : IsMatching (starHG m D) M) : M.card ≤ D := by
  classical
  have hright : ∀ (a : Fin m) (b : Fin D),
      ({Sum.inl a, Sum.inr b} : Finset (StarVtx m D)).filter (fun v => v.isRight)
        = {(Sum.inr b : StarVtx m D)} := by
    intro a b
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hr⟩
      · subst h; simp at hr
      · exact h
    · rintro rfl; exact ⟨Or.inr rfl, by simp⟩
  set f : Finset (StarVtx m D) → Finset (StarVtx m D) :=
    fun e => e.filter (fun v => v.isRight) with hf
  have hmaps : ∀ e ∈ M, f e ∈
      Finset.image (fun b : Fin D => ({Sum.inr b} : Finset (StarVtx m D))) Finset.univ := by
    intro e he
    obtain ⟨a, b, rfl⟩ := (mem_starHG m D e).mp (hM.subset he)
    rw [hf]
    simp only
    rw [hright]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hinj : Set.InjOn f (M : Set (Finset (StarVtx m D))) := by
    intro e he g hg hef
    by_contra hne
    obtain ⟨a, b, rfl⟩ := (mem_starHG m D e).mp (hM.subset he)
    obtain ⟨a', b', rfl⟩ := (mem_starHG m D g).mp (hM.subset hg)
    rw [hf] at hef
    simp only [hright] at hef
    have hb : b = b' := by simpa using hef
    subst hb
    exact (Finset.disjoint_left.mp (hM.disjoint _ he _ hg hne)
      (show (Sum.inr b : StarVtx m D) ∈ _ by simp)) (by simp)
  calc M.card
      ≤ (Finset.image (fun b : Fin D => ({Sum.inr b} : Finset (StarVtx m D))) Finset.univ).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ D := le_trans Finset.card_image_le (by simp)

/-- The number of vertices of the star witness. -/
@[simp] theorem card_starVtx (m D : ℕ) : Fintype.card (StarVtx m D) = m + D := by
  simp

/-- The exceptional set: the `D` right vertices. -/
theorem starHG_nearlyRegularMost {m D : ℕ} {μ η : ℝ} (hμ : 0 ≤ μ)
    (hcard : (D : ℝ) ≤ η * ((m : ℝ) + D)) :
    NearlyRegularMost (starHG m D) (D : ℝ) μ η := by
  classical
  refine ⟨Finset.image Sum.inr Finset.univ, ?_, ?_⟩
  · have hc : (Finset.image (Sum.inr : Fin D → StarVtx m D) Finset.univ).card = D := by
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
    rw [hc, card_starVtx]
    push_cast
    exact hcard
  · intro v hv
    obtain ⟨a, rfl⟩ : ∃ a : Fin m, v = Sum.inl a := by
      cases v with
      | inl a => exact ⟨a, rfl⟩
      | inr b => exact absurd (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩) hv
    rw [starHG_degree_inl]
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) D]

/-! ## The refutation -/

/-- **The majority interface `NibbleTheoremMost` is FALSE.**  For `r = 2` and `β = 1/2` no choice of
`μ, η, d₀ > 0` works: the complete bipartite witness `K_{m,D}` with `D ≥ max (d₀, 1/μ, 1)` and
`m > max (3D, D/η)` satisfies every hypothesis but has matching number `≤ D < (1-β)·|V|/2`. -/
theorem not_nibbleTheoremMost : ¬ NibbleTheoremMost := by
  classical
  intro h
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h 2 (le_refl 2) (1 / 2) (by norm_num)
  -- choose the right-side size `D`
  obtain ⟨D₀, hD₀⟩ := exists_nat_ge (max d₀ (1 / μ))
  set D : ℕ := max D₀ 1 with hDdef
  have hDD₀ : (D₀ : ℝ) ≤ (D : ℝ) := by exact_mod_cast le_max_left D₀ 1
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast le_max_right D₀ 1
  have hDd₀ : d₀ ≤ (D : ℝ) := le_trans (le_trans (le_max_left _ _) hD₀) hDD₀
  have hDμ : (1 : ℝ) / μ ≤ (D : ℝ) := le_trans (le_trans (le_max_right _ _) hD₀) hDD₀
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le one_pos hD1
  -- choose the left-side size `m`
  obtain ⟨m, hm⟩ := exists_nat_ge (max (3 * (D : ℝ) + 1) ((D : ℝ) / η))
  have hm3 : 3 * (D : ℝ) + 1 ≤ (m : ℝ) := le_trans (le_max_left _ _) hm
  have hmη : (D : ℝ) / η ≤ (m : ℝ) := le_trans (le_max_right _ _) hm
  -- the witness satisfies all the hypotheses
  have hreg : NearlyRegularMost (starHG m D) (D : ℝ) μ η := by
    refine starHG_nearlyRegularMost hμ.le ?_
    have : (D : ℝ) ≤ η * (m : ℝ) := by
      rw [div_le_iff₀ hη] at hmη; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hcod : CodegreeBounded (starHG m D) (μ * (D : ℝ)) := by
    intro x y hxy
    have h1 : (codegree (starHG m D) x y : ℝ) ≤ 1 := by
      exact_mod_cast starHG_codegree_le_one m D hxy
    have h2 : (1 : ℝ) ≤ μ * (D : ℝ) := by
      rw [div_le_iff₀ hμ] at hDμ; linarith
    linarith
  obtain ⟨M, hM, hcard⟩ :=
    hmain (V := StarVtx m D) (starHG m D) (D : ℝ) hDpos hDd₀ (starHG_isUniform m D) hreg hcod
  -- but the matching number is at most `D`
  have hMD : (M.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast starHG_matching_card_le hM
  rw [card_starVtx] at hcard
  push_cast at hcard
  linarith

end LeanPool.AsymptoticTrianglePacking.Internal
