/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.Komlos.Main
public import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# The Beck–Fiala bound

Adapted for Lean Pool by changing module paths and selecting explicit imports.

If every vertex of a finite hypergraph belongs to at most `t` edges, each column of its
incidence matrix has Euclidean norm at most `√t`. The scaled Komlós bound therefore gives
an edge discrepancy bound of `36 * √t`.

`Hypergraph.incidenceMatrix` has rows indexed by edges and columns indexed by vertices.
`Hypergraph.discrepancy_incidenceMatrix_le` proves the matrix bound;
`Hypergraph.exists_isColouring_forall_abs_finsum_le` states it as a vertex colouring.
-/

@[expose] public section

namespace Hypergraph

open Komlos Finset

variable {α : Type*} {H : Hypergraph α}

/-- A hypergraph with finitely many vertices has finitely many edges. -/
lemma edgeSet_finite (hV : V(H).Finite) : E(H).Finite :=
  hV.finite_subsets.subset edgeSet_subset_powerset_vertexSet

open Classical in
/-- The incidence matrix of a hypergraph with finitely many vertices: its rows are indexed by
the edges, its columns by the vertices, and an entry is `1` when the vertex lies in the edge
and `0` otherwise. -/
noncomputable def incidenceMatrix (H : Hypergraph α) (hV : V(H).Finite) :
    Matrix (edgeSet_finite hV).toFinset hV.toFinset ℝ :=
  Matrix.of fun e x ↦ if (x : α) ∈ (e : Set α) then 1 else 0

open Classical in
lemma incidenceMatrix_apply (hV : V(H).Finite) (e : (edgeSet_finite hV).toFinset)
    (x : hV.toFinset) :
    H.incidenceMatrix hV e x = if (x : α) ∈ (e : Set α) then 1 else 0 := rfl

/-- The squared entries of a column of the incidence matrix count the edges containing the
vertex. -/
lemma sum_incidenceMatrix_sq (hV : V(H).Finite) (x : hV.toFinset) :
    ∑ e, H.incidenceMatrix hV e x ^ 2 = {e ∈ E(H) | (x : α) ∈ e}.ncard := by
  classical
  calc ∑ e, H.incidenceMatrix hV e x ^ 2
      = ∑ e ∈ (edgeSet_finite hV).toFinset, if (x : α) ∈ e then (1 : ℝ) else 0 := by
        refine Eq.trans ?_ (sum_coe_sort _ _)
        congr with e
        simp [incidenceMatrix_apply]
    _ = {e ∈ E(H) | (x : α) ∈ e}.ncard := by
        rw [sum_boole, ← Set.ncard_coe_finset, coe_filter]
        simp

/-- The Beck–Fiala conjecture, with constant `36`: if every vertex of a hypergraph lies in at
most `t` edges, then its incidence matrix has discrepancy at most `36 * √t`. -/
theorem discrepancy_incidenceMatrix_le {t : ℕ} (hV : V(H).Finite)
    (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    discrepancy (H.incidenceMatrix hV) ≤ 36 * Real.sqrt t := by
  apply discrepancy_le_of_forall_sum_sq_le _ (Real.sqrt_nonneg _)
  intro x
  rw [Real.sq_sqrt (Nat.cast_nonneg _), sum_incidenceMatrix_sq]
  exact_mod_cast hdeg x (hV.mem_toFinset.1 x.2)

/-- The Beck–Fiala conjecture, colouring form: if every vertex of a hypergraph lies in at
most `t` edges, then some colouring of the vertices gives every edge discrepancy at most
`36 * √t`. -/
theorem exists_isColouring_forall_abs_finsum_le {t : ℕ} (hV : V(H).Finite)
    (hdeg : ∀ x ∈ V(H), {e ∈ E(H) | x ∈ e}.ncard ≤ t) :
    ∃ χ : α → ℝ, IsColouring χ ∧ ∀ e ∈ E(H), |∑ᶠ x ∈ e, χ x| ≤ 36 * Real.sqrt t := by
  classical
  obtain ⟨ε, hε, hbd⟩ := discrepancy_le_iff.1 (discrepancy_incidenceMatrix_le hV hdeg)
  rw [colouringDiscrepancy_le_iff (by positivity)] at hbd
  let χ : α → ℝ := fun x ↦ if hx : x ∈ V(H) then ε ⟨x, hV.mem_toFinset.2 hx⟩ else 1
  refine ⟨χ, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ V(H)
    · simpa only [χ, hx, ↓reduceDIte] using hε _
    · simp [χ, hx]
  · intro e he
    refine le_of_eq_of_le ?_ (hbd ⟨e, (edgeSet_finite hV).mem_toFinset.2 he⟩)
    rw [finsum_mem_eq_sum_of_subset χ (t := hV.toFinset.filter (· ∈ e)) ?_
      (by simp), sum_filter, ← sum_coe_sort]
    · congr 1
      congr with i
      simp [incidenceMatrix_apply, χ, hV.mem_toFinset.1 i.2]
    · intro x hx
      simpa using ⟨subset_vertexSet_of_mem_edgeSet he hx.1, hx.1⟩

end Hypergraph
