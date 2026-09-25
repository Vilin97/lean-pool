/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.Interpolation

/-!
# Threshold subforests for BKAR interpolation

This file records the finite graph fact behind the component representation of
BKAR interpolation points: threshold connectivity in a forest is equivalent to
the path-min inequality along the unique forest path.
-/

@[expose] public section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Edges of a forest whose parameter is at least the threshold `s`. -/
def thresholdEdges (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Finset (Edge V) :=
  F.edges.filter fun e => s ≤ F.paramValue u e

@[simp]
theorem mem_thresholdEdges (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (e : Edge V) :
    e ∈ F.thresholdEdges u s ↔ e ∈ F.edges ∧ s ≤ F.paramValue u e := by
  simp [thresholdEdges]

/-- The threshold edge set is again an acyclic forest index. -/
def thresholdIndex (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    ForestIndex V where
  edges := F.thresholdEdges u s
  acyclic := F.isAcyclicEdgeSet.mono (by
    intro e he
    exact (F.mem_thresholdEdges u s e).mp he |>.1)

/--
Two vertices are threshold-connected when a simple forest path joins them using
only edges whose parameter is at least `s`.
-/
def thresholdConnected (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (i j : V) : Prop :=
  ∃ γ : List (Edge V),
    IsSimplePath F γ i j ∧ ∀ e ∈ γ, s ≤ F.paramValue u e

theorem le_pathMinAux_iff (F : Forest V) (u : F.EdgeParam → ℝ)
    (s a : ℝ) :
    ∀ γ : List (Edge V),
      s ≤ F.pathMinAux u a γ ↔
        s ≤ a ∧ ∀ e ∈ γ, s ≤ F.paramValue u e
  | [] => by
      simp [pathMinAux]
  | e :: γ => by
      rw [pathMinAux]
      rw [le_pathMinAux_iff F u s (min a (F.paramValue u e)) γ]
      rw [le_min_iff]
      constructor
      · rintro ⟨⟨hsa, hse⟩, htail⟩
        refine ⟨hsa, ?_⟩
        intro e' he'
        rw [List.mem_cons] at he'
        exact he'.elim (fun heq => heq ▸ hse) (htail e')
      · rintro ⟨hsa, hall⟩
        refine ⟨⟨hsa, hall e (by simp)⟩, ?_⟩
        intro e' he'
        exact hall e' (by simp [he'])

theorem le_pathMin_of_forall_edges
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs : s ≤ 1) :
    ∀ γ : List (Edge V),
      (∀ e ∈ γ, s ≤ F.paramValue u e) →
        s ≤ F.pathMin u γ
  | [] => fun _ => by
      simpa [pathMin] using hs
  | e :: γ => fun hγ => by
      rw [pathMin_cons]
      exact (le_pathMinAux_iff F u s (F.paramValue u e) γ).mpr
        ⟨hγ e (by simp), fun e' he' => hγ e' (by simp [he'])⟩

theorem forall_edges_of_le_pathMin
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} :
    ∀ γ : List (Edge V),
      s ≤ F.pathMin u γ →
        ∀ e ∈ γ, s ≤ F.paramValue u e
  | [] => fun _ e he => by cases he
  | e :: γ => fun hmin e' he' => by
      rw [pathMin_cons] at hmin
      have hall :=
        (le_pathMinAux_iff F u s (F.paramValue u e) γ).mp hmin
      rw [List.mem_cons] at he'
      exact he'.elim (fun heq => heq ▸ hall.1) (hall.2 e')

/--
Threshold connectivity is the same as being in the original forest component
with path minimum at least `s`.
-/
theorem thresholdConnected_iff_exists_le_pathMin
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs : s ≤ 1) (i j : V) :
    F.thresholdConnected u s i j ↔
      ∃ h : F.inSameComponent i j,
        s ≤ F.pathMin u (F.pathInF i j h) := by
  constructor
  · rintro ⟨γ, hγ, hall⟩
    let hcomp : F.inSameComponent i j := F.inSameComponent_of_isSimplePath hγ
    refine ⟨hcomp, ?_⟩
    have hpath : γ = F.pathInF i j hcomp :=
      F.pathInF_unique hcomp γ hγ
    rw [← hpath]
    exact F.le_pathMin_of_forall_edges u hs γ hall
  · rintro ⟨hcomp, hmin⟩
    refine ⟨F.pathInF i j hcomp, F.pathInF_isSimple hcomp, ?_⟩
    exact F.forall_edges_of_le_pathMin u (F.pathInF i j hcomp) hmin

/--
For positive thresholds, the standard BKAR edge value is above threshold
exactly when its endpoints are threshold-connected.
-/
theorem le_standardInterp_iff_thresholdConnected
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      F.thresholdConnected u s e.left e.right := by
  by_cases hcomp : F.inSameComponent e.left e.right
  · rw [standardInterp, dite_eq_left hcomp]
    constructor
    · intro hmin
      exact (F.thresholdConnected_iff_exists_le_pathMin u hs1 e.left e.right).mpr
        ⟨hcomp, hmin⟩
    · intro hconn
      rcases (F.thresholdConnected_iff_exists_le_pathMin u hs1 e.left e.right).mp
          hconn with
        ⟨hcomp', hmin⟩
      have hpath :
          F.pathInF e.left e.right hcomp' =
            F.pathInF e.left e.right hcomp :=
        F.pathInF_eq_of_edges_eq F rfl hcomp' hcomp
      simpa [hpath] using hmin
  · rw [standardInterp, dite_eq_right hcomp]
    constructor
    · intro hle
      exact False.elim ((not_le_of_gt hs0) hle)
    · intro hconn
      rcases hconn with ⟨γ, hγ, _hall⟩
      exact False.elim (hcomp (F.inSameComponent_of_isSimplePath hγ))

end

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
