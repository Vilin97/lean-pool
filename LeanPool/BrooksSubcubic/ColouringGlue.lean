/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Subcubic Brooks theorem: ColouringGlue

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Glue lemma at a cut vertex.** If A and B cover V, x belongs to both,
no G-edge joins A∖{x} to B∖{x}, and both induced subgraphs
`G[A]`, `G[B]` are 3-colourable, then `G` is 3-colourable. Proof: pick colourings `cA, cB`;
recolour `B` by the transposition `swap (cB x) (cA x)` so both agree at `x`; glue with `A` taking
priority. Every edge lies inside `A` or inside `B` — a cross edge would violate the no-cross
hypothesis — so the glued map inherits properness, and the alignment at `x` handles the boundary. -/
theorem colorable_glue_at_vertex (G : SimpleGraph V)
    (A B : Finset V) (x : V)
    (hcover : A ∪ B = Finset.univ)
    (hxA : x ∈ A) (hxB : x ∈ B)
    (hcross : ∀ u ∈ A, ∀ w ∈ B, u ≠ x → w ≠ x → ¬ G.Adj u w)
    (hA : (G.induce (A : Set V)).Colorable 3)
    (hB : (G.induce (B : Set V)).Colorable 3) :
    G.Colorable 3 := by
  classical
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  set α : Fin 3 := cA ⟨x, by exact_mod_cast hxA⟩ with hα
  set β : Fin 3 := cB ⟨x, by exact_mod_cast hxB⟩ with hβ
  set σ : Equiv.Perm (Fin 3) := Equiv.swap β α with hσ
  have hmemB : ∀ v : V, v ∉ A → v ∈ B := by
    intro v hv
    have h : v ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ v
    exact (Finset.mem_union.mp h).resolve_left hv
  let c : V → Fin 3 := fun v =>
    if hv : v ∈ A then cA ⟨v, by exact_mod_cast hv⟩
    else σ (cB ⟨v, by exact_mod_cast hmemB v hv⟩)
  have hcA_val : ∀ (v : V) (hv : v ∈ A), c v = cA ⟨v, by exact_mod_cast hv⟩ := by
    intro v hv; simp only [c, dite_eq_left hv]
  have hcB_val : ∀ (v : V) (hv : v ∉ A),
      c v = σ (cB ⟨v, by exact_mod_cast hmemB v hv⟩) := by
    intro v hv; simp only [c, dite_eq_right hv]
  have hAadj : ∀ (u v : V) (hu : u ∈ A) (hv : v ∈ A), G.Adj u v →
      cA ⟨u, by exact_mod_cast hu⟩ ≠ cA ⟨v, by exact_mod_cast hv⟩ := by
    intro u v hu hv hadj
    exact cA.valid (by simpa using hadj)
  have hBadj : ∀ (u v : V) (hu : u ∈ B) (hv : v ∈ B), G.Adj u v →
      cB ⟨u, by exact_mod_cast hu⟩ ≠ cB ⟨v, by exact_mod_cast hv⟩ := by
    intro u v hu hv hadj
    exact cB.valid (by simpa using hadj)
  have hαβ : α = σ β := by rw [hσ, Equiv.swap_apply_left]
  refine ⟨Coloring.mk c ?_⟩
  intro u v hadj
  by_cases hua : u ∈ A
  · by_cases hva : v ∈ A
    · rw [hcA_val u hua, hcA_val v hva]
      exact hAadj u v hua hva hadj
    · have hvB : v ∈ B := hmemB v hva
      have hvx : v ≠ x := fun h => hva (h ▸ hxA)
      by_cases hux : u = x
      · subst hux
        rw [hcA_val u hua, hcB_val v hva]
        have hxeq : cA ⟨u, by exact_mod_cast hua⟩ = α := by rw [hα]
        rw [hxeq, hαβ]
        intro hcontra
        have hinj : β = cB ⟨v, by exact_mod_cast hvB⟩ := σ.injective hcontra
        exact hBadj u v hxB hvB hadj (by rw [← hβ]; exact hinj)
      · exact absurd hadj (hcross u hua v hvB hux hvx)
  · have huB : u ∈ B := hmemB u hua
    have hux : u ≠ x := fun h => hua (h ▸ hxA)
    by_cases hva : v ∈ A
    · by_cases hvx : v = x
      · subst hvx
        rw [hcA_val v hva, hcB_val u hua]
        have hxeq : cA ⟨v, by exact_mod_cast hva⟩ = α := by rw [hα]
        rw [hxeq, hαβ]
        intro hcontra
        have hinj : cB ⟨u, by exact_mod_cast huB⟩ = β := σ.injective hcontra
        exact hBadj u v huB hxB hadj (by rw [← hβ]; exact hinj)
      · exact absurd hadj.symm (hcross v hva u huB hvx hux)
    · have hvB : v ∈ B := hmemB v hva
      rw [hcB_val u hua, hcB_val v hva]
      intro hcontra
      have hinj : cB ⟨u, by exact_mod_cast huB⟩ = cB ⟨v, by exact_mod_cast hvB⟩ :=
        σ.injective hcontra
      exact hBadj u v huB hvB hadj hinj

end BrooksSubcubic
end
