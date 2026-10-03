/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.Push

/-!
# Subcubic Brooks theorem: ComponentAttachments

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- If `W` is closed under `G`-adjacency, a walk starting in `W` stays in `W`. -/
theorem mem_of_walk_closed (G : SimpleGraph V) (W : Set V)
    (hW : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W) {u v : V} (p : G.Walk u v) :
    u ∈ W → v ∈ W := by
  classical
  induction p with
  | nil => exact id
  | @cons a b c hadj q ih => exact fun ha => ih (hW a ha b hadj)

omit [Fintype V] in
/-- **Linchpin.** In a connected `G`, for any `d ≠ x`, `x` is adjacent to some vertex `z` in the
same `G−x`-component as `d`. -/
theorem exists_adj_in_class (G : SimpleGraph V) (hconn : G.Connected)
    {x d : V} (hd : d ≠ x) :
    ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ =
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ with hD
  set W : Set V := {v | ∃ hv : v ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdW : d ∈ W := ⟨hd, rfl⟩
  have hxW : x ∉ W := by rintro ⟨hx, _⟩; exact hx rfl
  have hclosed : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W := by
    rintro w ⟨hwx, hwD⟩ y hadj
    by_cases hyx : y = x
    · subst hyx
      exact absurd (hwD ▸ rfl) (hcon w hadj.symm hwx)
    · refine ⟨hyx, ?_⟩
      have hadj' : (G.induce ({x}ᶜ : Set V)).Adj ⟨w, hwx⟩ ⟨y, hyx⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hconn.preconnected d x
  exact hxW (mem_of_walk_closed G W hclosed p hdW)

end BrooksSubcubic
end
