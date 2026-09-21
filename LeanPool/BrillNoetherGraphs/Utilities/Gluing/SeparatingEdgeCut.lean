/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator
import Mathlib.Tactic

/-!
# Occurrence-safe separating edges

`SeparatingEdgeCut G x y` records a vertex cut crossed by exactly one edge
occurrence, from `x` on the chosen side to `y` outside it.  The full
multiplicity equation is important for multigraphs: a bridge in the
underlying simple graph is not enough when parallel edge occurrences exist.
-/

namespace Utilities

open Finset
open Certificate.StrongSeparator

universe u

/-- A finite cut whose unique crossing edge occurrence is `x-y`. -/
structure SeparatingEdgeCut (G : CFGraph.{u}) (x y : G.V) where
  side : Finset G.V
  left_mem : x ∈ side
  right_not_mem : y ∉ side
  cross_num_edges : ∀ a b : G.V, a ∈ side → b ∉ side →
    num_edges G a b = if a = x ∧ b = y then 1 else 0

namespace SeparatingEdgeCut

variable {G : CFGraph.{u}} {x y : G.V}

theorem endpoints_ne (cut : SeparatingEdgeCut G x y) : x ≠ y := by
  intro h
  exact cut.right_not_mem (h ▸ cut.left_mem)

/-- The distinguished endpoints are joined by exactly one edge occurrence. -/
theorem num_edges_endpoints (cut : SeparatingEdgeCut G x y) :
    num_edges G x y = 1 := by
  simpa using cut.cross_num_edges x y cut.left_mem cut.right_not_mem

/-- A vertex on the chosen side has one outgoing edge exactly when it is the
distinguished endpoint. -/
theorem outdeg_eq (cut : SeparatingEdgeCut G x y)
    {a : G.V} (ha : a ∈ cut.side) :
    outdeg_S G cut.side a = if a = x then 1 else 0 := by
  unfold outdeg_S
  rw [Finset.sum_eq_single y]
  · rw [cut.cross_num_edges a y ha cut.right_not_mem]
    by_cases hax : a = x <;> simp [hax]
  · intro b hb hby
    have hbOutside : b ∉ cut.side := (Finset.mem_sdiff.mp hb).2
    rw [cut.cross_num_edges a b ha hbOutside]
    by_cases hax : a = x <;> simp [hax, hby]
  · simp [cut.right_not_mem]

/-- A vertex outside the chosen side has one incoming edge exactly when it is
the distinguished endpoint. -/
theorem intoMultiplicity_eq (cut : SeparatingEdgeCut G x y)
    {b : G.V} (hb : b ∉ cut.side) :
    intoMultiplicity G cut.side b = if b = y then 1 else 0 := by
  unfold intoMultiplicity
  rw [Finset.sum_eq_single x]
  · rw [num_edges_symmetric,
      cut.cross_num_edges x b cut.left_mem hb]
    by_cases hby : b = y <;> simp [hby]
  · intro a ha hax
    rw [num_edges_symmetric,
      cut.cross_num_edges a b ha hb]
    by_cases hby : b = y <;> simp [hax, hby]
  · intro hx
    exact (hx cut.left_mem).elim

/-- Firing the chosen side transfers one chip across its unique separating
edge. -/
theorem prin_indicator_script (cut : SeparatingEdgeCut G x y) :
    prin G (indicator_script G cut.side) = one_chip y - one_chip x := by
  funext v
  by_cases hv : v ∈ cut.side
  · rw [prin_indicator_script_of_mem hv, cut.outdeg_eq hv]
    have hvy : v ≠ y := fun h => cut.right_not_mem (h ▸ hv)
    by_cases hvx : v = x
    · subst v
      simp [one_chip, cut.endpoints_ne]
    · simp [one_chip, hvx, hvy]
  · rw [prin_indicator_script_of_not_mem hv, cut.intoMultiplicity_eq hv]
    have hvx : v ≠ x := fun h => hv (h ▸ cut.left_mem)
    by_cases hvy : v = y
    · subst v
      simp [one_chip, cut.endpoints_ne.symm]
    · simp [one_chip, hvx, hvy]

/-- The endpoints of a separating edge represent the same degree-one divisor
class. -/
theorem chipEquivalent (cut : SeparatingEdgeCut G x y) :
    linear_equiv G (one_chip x) (one_chip y) := by
  unfold linear_equiv
  apply (principal_iff_eq_prin G (one_chip y - one_chip x)).mpr
  exact ⟨indicator_script G cut.side, cut.prin_indicator_script.symm⟩

/-! ## Normalizing a firing script across one separating edge -/

/-- Add a constant on the chosen side so that the firing levels at the two
bridge endpoints agree. -/
def normalizeScript (cut : SeparatingEdgeCut G x y)
    (sigma : firing_script G) : firing_script G :=
  sigma + (sigma y - sigma x) • indicator_script G cut.side

@[simp] theorem normalizeScript_left (cut : SeparatingEdgeCut G x y)
    (sigma : firing_script G) :
    cut.normalizeScript sigma x = sigma y := by
  simp [normalizeScript, indicator_script, cut.left_mem]

@[simp] theorem normalizeScript_right (cut : SeparatingEdgeCut G x y)
    (sigma : firing_script G) :
    cut.normalizeScript sigma y = sigma y := by
  simp [normalizeScript, indicator_script, cut.right_not_mem]

/-- Normalization really equalizes the two endpoint levels. -/
theorem normalizeScript_endpoints_eq (cut : SeparatingEdgeCut G x y)
    (sigma : firing_script G) :
    cut.normalizeScript sigma x = cut.normalizeScript sigma y := by
  simp

/-- The exact change in the principal divisor under one bridge
normalization. -/
theorem prin_normalizeScript (cut : SeparatingEdgeCut G x y)
    (sigma : firing_script G) :
    prin G (cut.normalizeScript sigma) =
      prin G sigma + (sigma y - sigma x) • (one_chip y - one_chip x) := by
  unfold normalizeScript
  rw [map_add, map_zsmul, cut.prin_indicator_script]

/-- Two separating edges cannot cross one another.  Relative to the chosen
side of `cut`, the endpoints of `other` lie on the same side unless `other`
is the very same unoriented bridge occurrence. -/
theorem endpoints_same_side_or_same_edge
    {a b : G.V} (cut : SeparatingEdgeCut G x y)
    (other : SeparatingEdgeCut G a b) :
    (a ∈ cut.side ↔ b ∈ cut.side) ∨
      (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  by_cases ha : a ∈ cut.side
  · by_cases hb : b ∈ cut.side
    · exact Or.inl ⟨fun _ => hb, fun _ => ha⟩
    · right
      left
      have hCross := cut.cross_num_edges a b ha hb
      rw [other.num_edges_endpoints] at hCross
      by_contra hne
      simp [hne] at hCross
  · by_cases hb : b ∈ cut.side
    · right
      right
      have hCross := cut.cross_num_edges b a hb ha
      rw [num_edges_symmetric G b a, other.num_edges_endpoints] at hCross
      have hPair : b = x ∧ a = y := by
        by_contra hne
        simp [hne] at hCross
      exact ⟨hPair.2, hPair.1⟩
    · exact Or.inl ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩

/-- Normalizing across one separating edge preserves equality across every
other separating edge that was already normalized. -/
theorem normalizeScript_preserves_endpoints_eq
    {a b : G.V} (cut : SeparatingEdgeCut G x y)
    (other : SeparatingEdgeCut G a b) (sigma : firing_script G)
    (hEqual : sigma a = sigma b) :
    cut.normalizeScript sigma a = cut.normalizeScript sigma b := by
  rcases cut.endpoints_same_side_or_same_edge other with hSide | hSame | hSame
  · unfold normalizeScript
    simp only [Pi.add_apply, Pi.smul_apply]
    have hIndicator :
        indicator_script G cut.side a = indicator_script G cut.side b := by
      unfold indicator_script
      by_cases ha : a ∈ cut.side
      · rw [if_pos ha, if_pos (hSide.mp ha)]
      · rw [if_neg ha, if_neg (fun hb => ha (hSide.mpr hb))]
    rw [hEqual, hIndicator]
  · rcases hSame with ⟨rfl, rfl⟩
    exact cut.normalizeScript_endpoints_eq sigma
  · rcases hSame with ⟨rfl, rfl⟩
    exact (cut.normalizeScript_endpoints_eq sigma).symm

end SeparatingEdgeCut

end Utilities
