/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Adding an edge to a chip-firing graph

This file develops the graph-theoretic infrastructure for genus induction by
adding a single edge.  The construction keeps the vertex type definitionally
unchanged, so divisors and firing scripts on the old and new graphs are the
same functions.
-/

open Multiset Finset

namespace Utilities

/-- Add one edge between two distinct existing vertices. -/
abbrev addEdge (H : CFGraph) (x y : H.V) (hxy : x ≠ y) : CFGraph where
  V := H.V
  edges := (x, y) ::ₘ H.edges
  loopless := by
    intro v hv
    simp only [Multiset.mem_cons] at hv
    rcases hv with h | h
    · exact hxy ((Prod.mk.inj h).1.symm.trans (Prod.mk.inj h).2)
    · exact H.loopless v h

@[simp] theorem addEdge_edges
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    (addEdge H x y hxy).edges = (x, y) ::ₘ H.edges := rfl

@[simp] theorem num_edges_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (v w : H.V) :
    num_edges (addEdge H x y hxy) v w =
      num_edges H v w +
        if (v = x ∧ w = y) ∨ (v = y ∧ w = x) then 1 else 0 := by
  change
    (Multiset.filter (fun e : H.V × H.V => e = (v, w) ∨ e = (w, v))
      ((x, y) ::ₘ H.edges)).card =
      (Multiset.filter (fun e : H.V × H.V => e = (v, w) ∨ e = (w, v))
        H.edges).card +
        if (v = x ∧ w = y) ∨ (v = y ∧ w = x) then 1 else 0
  rw [Multiset.filter_cons]
  have hiff :
      ((x, y) = (v, w) ∨ (x, y) = (w, v)) ↔
        ((v = x ∧ w = y) ∨ (v = y ∧ w = x)) := by
    simp only [Prod.mk.injEq]
    aesop
  by_cases h : (v = x ∧ w = y) ∨ (v = y ∧ w = x)
  · rw [if_pos (hiff.mpr h), if_pos h]
    simp
  · rw [if_neg (mt hiff.mp h), if_neg h]
    simp

theorem num_edges_le_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (v w : H.V) :
    num_edges H v w ≤ num_edges (addEdge H x y hxy) v w := by
  rw [num_edges_addEdge]
  omega

/-- A divisor has the same degree when regarded on the graph with the added
edge, since the vertex type and its finite structure are unchanged. -/
@[simp] theorem deg_on_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (D : H.V → ℤ) :
    @deg (addEdge H x y hxy) D = @deg H D := by
  rfl

@[simp] theorem num_edges_addEdge_endpoints
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    num_edges (addEdge H x y hxy) x y = num_edges H x y + 1 := by
  simp [num_edges_addEdge]

@[simp] theorem num_edges_addEdge_of_not_endpoints
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (v w : H.V)
    (hvw : ¬ ((v = x ∧ w = y) ∨ (v = y ∧ w = x))) :
    num_edges (addEdge H x y hxy) v w = num_edges H v w := by
  simp [num_edges_addEdge, hvw]

@[simp] theorem genus_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    genus (addEdge H x y hxy) = genus H + 1 := by
  change
    ((↑((x, y) ::ₘ H.edges).card : ℤ) - ↑(Fintype.card H.V) + 1) =
      (↑H.edges.card - ↑(Fintype.card H.V) + 1) + 1
  simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
  ring

theorem graph_connected_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (hH : graph_connected H) :
    graph_connected (addEdge H x y hxy) := by
  intro S hS
  rcases hH S hS with ⟨v, hv, w, hw, hvw⟩
  exact ⟨v, hv, w, hw, lt_of_lt_of_le hvw (num_edges_le_addEdge H x y hxy v w)⟩

@[simp] theorem vertex_degree_addEdge_left
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    vertex_degree (addEdge H x y hxy) x = vertex_degree H x + 1 := by
  change
    (∑ u : H.V, (num_edges (addEdge H x y hxy) x u : ℤ)) =
      (∑ u : H.V, (num_edges H x u : ℤ)) + 1
  simp_rw [num_edges_addEdge]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_add_distrib]
  simp [hxy]

@[simp] theorem vertex_degree_addEdge_right
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    vertex_degree (addEdge H x y hxy) y = vertex_degree H y + 1 := by
  change
    (∑ u : H.V, (num_edges (addEdge H x y hxy) y u : ℤ)) =
      (∑ u : H.V, (num_edges H y u : ℤ)) + 1
  simp_rw [num_edges_addEdge]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_add_distrib]
  simp [hxy.symm]

@[simp] theorem vertex_degree_addEdge_of_ne
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) (v : H.V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    vertex_degree (addEdge H x y hxy) v = vertex_degree H v := by
  change
    (∑ u : H.V, (num_edges (addEdge H x y hxy) v u : ℤ)) =
      ∑ u : H.V, (num_edges H v u : ℤ)
  simp_rw [num_edges_addEdge]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_add_distrib]
  simp [hvx, hvy]

/-- The degree-zero divisor supported with opposite signs at the new edge's endpoints. -/
def seamDivisor {H : CFGraph} (x y : H.V) : CFDiv H :=
  one_chip x - one_chip y

@[simp] theorem deg_seamDivisor {H : CFGraph} (x y : H.V) :
    deg (seamDivisor x y) = 0 := by
  simp [seamDivisor]

@[simp] theorem deg_add_zsmul_seamDivisor
    {H : CFGraph} (D : CFDiv H) (x y : H.V) (n : ℤ) :
    deg (D + n • seamDivisor x y) = deg D := by
  simp only [deg.map_add, map_zsmul, deg_seamDivisor, smul_zero, add_zero]

@[simp] theorem prin_addEdge_apply_left
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (σ : firing_script H) :
    prin (addEdge H x y hxy) σ x = prin H σ x + (σ y - σ x) := by
  change
    (∑ u : H.V,
      (σ u - σ x) * (num_edges (addEdge H x y hxy) x u : ℤ)) =
      (∑ u : H.V, (σ u - σ x) * (num_edges H x u : ℤ)) +
        (σ y - σ x)
  simp_rw [num_edges_addEdge]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add]
  rw [Finset.sum_add_distrib]
  simp [hxy]

@[simp] theorem prin_addEdge_apply_right
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (σ : firing_script H) :
    prin (addEdge H x y hxy) σ y = prin H σ y + (σ x - σ y) := by
  change
    (∑ u : H.V,
      (σ u - σ y) * (num_edges (addEdge H x y hxy) y u : ℤ)) =
      (∑ u : H.V, (σ u - σ y) * (num_edges H y u : ℤ)) +
        (σ x - σ y)
  simp_rw [num_edges_addEdge]
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add]
  rw [Finset.sum_add_distrib]
  simp [hxy.symm]

@[simp] theorem prin_addEdge_apply_of_ne
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (σ : firing_script H) (v : H.V) (hvx : v ≠ x) (hvy : v ≠ y) :
    prin (addEdge H x y hxy) σ v = prin H σ v := by
  change
    (∑ u : H.V,
      (σ u - σ v) * (num_edges (addEdge H x y hxy) v u : ℤ)) =
      ∑ u : H.V, (σ u - σ v) * (num_edges H v u : ℤ)
  simp_rw [num_edges_addEdge]
  simp [hvx, hvy]

/-- Adding an edge changes the principal divisor by a rank-one term.

The sign reflects the convention in `ChipFiringWithLean`: `prin` is the
negative of the usual graph Laplacian applied to the firing script.
-/
theorem prin_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (σ : firing_script H) :
    prin H σ =
      fun v : H.V =>
        prin (addEdge H x y hxy) σ v +
          (σ x - σ y) * seamDivisor x y v := by
  funext v
  by_cases hvx : v = x
  · subst v
    rw [prin_addEdge_apply_left]
    simp only [seamDivisor, Pi.sub_apply, one_chip, ↓reduceIte, hxy, sub_zero, mul_one]
    ring
  · by_cases hvy : v = y
    · subst v
      rw [prin_addEdge_apply_right]
      simp only [seamDivisor, Pi.sub_apply, one_chip, hvx, ↓reduceIte, zero_sub, Int.reduceNeg,
        mul_neg, mul_one, neg_sub]
      ring
    · rw [prin_addEdge_apply_of_ne H x y hxy σ v hvx hvy]
      simp [seamDivisor, one_chip, hvx, hvy]

/-- Linear equivalence on the old graph transfers to linear equivalence on
the new graph after translating by an integral multiple of the seam divisor. -/
theorem linear_equiv_phase_transfer
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (D E : CFDiv H) (hDE : linear_equiv H D E) :
    ∃ n : ℤ,
      linear_equiv (addEdge H x y hxy)
        (D + n • seamDivisor x y) E := by
  obtain ⟨σ, hσ⟩ :=
    (principal_iff_eq_prin H (E - D)).mp hDE
  refine ⟨σ x - σ y, ?_⟩
  apply (principal_iff_eq_prin (addEdge H x y hxy)
    (E - (D + (σ x - σ y) • seamDivisor x y))).mpr
  refine ⟨σ, ?_⟩
  funext v
  have hσv := congrFun hσ v
  have hpv := congrFun (prin_addEdge H x y hxy σ) v
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hσv ⊢
  calc
    E v - (D v + (σ x - σ y) * seamDivisor x y v) =
        (E v - D v) - (σ x - σ y) * seamDivisor x y v := by ring
    _ = prin H σ v - (σ x - σ y) * seamDivisor x y v := by rw [hσv]
    _ = prin (addEdge H x y hxy) σ v := by rw [hpv]; ring

/-- Conversely, every integral seam phase is represented on the enlarged
graph by a divisor linearly equivalent to `D` on the old graph. -/
theorem phase_represented_by_old_linear_class
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (D : CFDiv H) (n : ℤ) :
    ∃ E : CFDiv H,
      linear_equiv H D E ∧
      linear_equiv (addEdge H x y hxy)
        (D + n • seamDivisor x y) E := by
  let σ : firing_script H := n • one_chip x
  let E : CFDiv H := D + prin H σ
  have hDrop : σ x - σ y = n := by
    simp [σ, one_chip, hxy.symm]
  have hPrin (v : H.V) :
      prin H σ v =
        prin (addEdge H x y hxy) σ v + n * seamDivisor x y v := by
    have hv := congrFun (prin_addEdge H x y hxy σ) v
    rw [hv, hDrop]
  refine ⟨E, ?_, ?_⟩
  · apply (principal_iff_eq_prin H (E - D)).mpr
    refine ⟨σ, ?_⟩
    dsimp [E]
    abel
  · apply (principal_iff_eq_prin (addEdge H x y hxy)
      (E - (D + n • seamDivisor x y))).mpr
    refine ⟨σ, ?_⟩
    funext v
    simp only [E, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hPrin v]
    ring

/-- Exact orbit description: the classes on the enlarged graph represented
by the old linear class of `D` are precisely the integral seam phases of
`D`. -/
theorem old_linear_class_iff_seam_phase_orbit
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (D F : CFDiv H) :
    (∃ E : CFDiv H,
      linear_equiv H D E ∧
      linear_equiv (addEdge H x y hxy) E F) ↔
    ∃ n : ℤ,
      linear_equiv (addEdge H x y hxy)
        (D + n • seamDivisor x y) F := by
  constructor
  · rintro ⟨E, hDE, hEF⟩
    obtain ⟨n, hn⟩ := linear_equiv_phase_transfer H x y hxy D E hDE
    exact ⟨n, linear_equiv.trans hn hEF⟩
  · rintro ⟨n, hn⟩
    obtain ⟨E, hDE, hPhaseE⟩ :=
      phase_represented_by_old_linear_class H x y hxy D n
    exact ⟨E, hDE,
      linear_equiv.trans (linear_equiv.symm hPhaseE) hn⟩

/-- A winnable divisor on the old graph has a winnable phase after the edge
is added.  This is edge normalization in rank zero, without a BN hypothesis. -/
theorem winnable_phase_transfer
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y)
    (D : CFDiv H) (hD : winnable H D) :
    ∃ n : ℤ,
      winnable (addEdge H x y hxy)
        (D + n • seamDivisor x y) := by
  obtain ⟨E, hE, hDE⟩ := (winnable_iff_exists_effective H D).mp hD
  obtain ⟨n, hn⟩ := linear_equiv_phase_transfer H x y hxy D E hDE
  refine ⟨n, (winnable_iff_exists_effective
    (addEdge H x y hxy) (D + n • seamDivisor x y)).mpr ?_⟩
  exact ⟨E, hE, hn⟩

/-- Adding the edge increases the canonical divisor by one chip at each
endpoint.  The pointwise RHS makes the definitional identification of vertex
types explicit. -/
theorem canonical_divisor_addEdge
    (H : CFGraph) (x y : H.V) (hxy : x ≠ y) :
    canonical_divisor (addEdge H x y hxy) =
      fun v : H.V => canonical_divisor H v + one_chip x v + one_chip y v := by
  change
    (fun v : H.V => vertex_degree (addEdge H x y hxy) v - 2) =
      fun v : H.V => canonical_divisor H v + one_chip x v + one_chip y v
  funext v
  by_cases hvx : v = x
  · subst v
    rw [vertex_degree_addEdge_left]
    simp only [canonical_divisor, one_chip, ↓reduceIte, hxy, add_zero]
    ring
  · by_cases hvy : v = y
    · subst v
      rw [vertex_degree_addEdge_right]
      simp only [canonical_divisor, one_chip, hvx, ↓reduceIte, add_zero]
      ring
    · rw [vertex_degree_addEdge_of_ne H x y hxy v hvx hvy]
      simp [canonical_divisor, one_chip, hvx, hvy]

end Utilities
