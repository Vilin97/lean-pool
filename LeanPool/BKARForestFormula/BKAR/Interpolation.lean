/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.Real.Basic
import LeanPool.BKARForestFormula.BKAR.Forest

/-! # Path-minimum forest interpolation

The interpolation scheme at the heart of the BKAR forest interpolation
formula (see `BKAR.Formula`).  For a forest `F` with edge parameters
`u : F.EdgeParam → ℝ`, the interpolation point `standardInterp` (the point
`x^F(u)`) assigns to an edge `{i, j}` the minimum of `u` along the unique
forest path joining `i` to `j` when both lie in the same component of `F`,
and `0` otherwise.  Also provides the constant, zero, and all-ones edge
configurations, the extended parameter reading `paramValue`, the path
minimum `pathMin`, the one-parameter family `interpWithFill` driving the
inductive proof, and one-edge extensions `EdgeExtension` with their
parameter transport.
-/

namespace BKAR

variable {V : Type*} [DecidableEq V]

/-- The constant BKAR configuration. -/
def constantConfig (t : ℝ) : Edge V → ℝ :=
  fun _ => t

/-- The zero BKAR configuration. -/
def zeroConfig : Edge V → ℝ :=
  constantConfig 0

/-- The all-one BKAR configuration. -/
def oneConfig : Edge V → ℝ :=
  constantConfig 1

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge parameters attached only to the edge set of a forest. -/
abbrev EdgeParam (F : Forest V) : Type _ :=
  { e : Edge V // e ∈ F.edges }

/-- The unique edge-parameter function on the empty forest. -/
def emptyParam : (Forest.empty V).EdgeParam → ℝ :=
  fun e => False.elim (by
    have he : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← Forest.empty_edges V]
      exact e.property
    exact Finset.notMem_empty e.val he)

theorem emptyParam_unique (u : (Forest.empty V).EdgeParam → ℝ) :
    u = emptyParam := by
  funext e
  exact False.elim (by
    have he : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← Forest.empty_edges V]
      exact e.property
    exact Finset.notMem_empty e.val he)

/-- Look up the value of an edge parameter, with default value `1` off the forest. -/
def paramValue (F : Forest V) (u : F.EdgeParam → ℝ) (e : Edge V) : ℝ :=
  if he : e ∈ F.edges then u ⟨e, he⟩ else 1

@[simp]
theorem paramValue_of_mem (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.paramValue u e = u ⟨e, he⟩ := by
  rw [paramValue, dif_pos he]

/-- Auxiliary minimum, seeded by the first edge of a nonempty path. -/
def pathMinAux (F : Forest V) (u : F.EdgeParam → ℝ) :
    ℝ → List (Edge V) → ℝ
  | a, [] => a
  | a, e :: γ => F.pathMinAux u (min a (F.paramValue u e)) γ

/-- Minimum of forest parameters along a path, with empty path convention `1`. -/
def pathMin (F : Forest V) (u : F.EdgeParam → ℝ) : List (Edge V) → ℝ
  | [] => 1
  | e :: γ => F.pathMinAux u (F.paramValue u e) γ

@[simp]
theorem pathMin_nil (F : Forest V) (u : F.EdgeParam → ℝ) :
    F.pathMin u [] = 1 :=
  rfl

@[simp]
theorem pathMin_cons (F : Forest V) (u : F.EdgeParam → ℝ)
    (e : Edge V) (γ : List (Edge V)) :
    F.pathMin u (e :: γ) = F.pathMinAux u (F.paramValue u e) γ :=
  rfl

theorem pathMin_singleton (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.pathMin u [e] = u ⟨e, he⟩ := by
  rw [pathMin_cons, paramValue_of_mem F u he]
  rfl

theorem paramValue_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.paramValue u e ∧ F.paramValue u e ≤ 1 := by
  by_cases he : e ∈ F.edges
  · rw [paramValue_of_mem F u he]
    exact hu ⟨e, he⟩
  · rw [paramValue, dif_neg he]
    exact ⟨zero_le_one, le_rfl⟩

theorem pathMinAux_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    ∀ {a : ℝ}, 0 ≤ a ∧ a ≤ 1 → ∀ γ : List (Edge V),
      0 ≤ F.pathMinAux u a γ ∧ F.pathMinAux u a γ ≤ 1
  | a, ha, [] => ha
  | a, ha, e :: γ => by
      have he := F.paramValue_mem_Icc u hu e
      have hmin : 0 ≤ min a (F.paramValue u e) ∧
          min a (F.paramValue u e) ≤ 1 :=
        ⟨le_min ha.1 he.1, (min_le_left _ _).trans ha.2⟩
      exact F.pathMinAux_mem_Icc u hu hmin γ

theorem pathMin_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    ∀ γ : List (Edge V), 0 ≤ F.pathMin u γ ∧ F.pathMin u γ ≤ 1
  | [] => ⟨zero_le_one, le_rfl⟩
  | e :: γ => by
      exact F.pathMinAux_mem_Icc u hu (F.paramValue_mem_Icc u hu e) γ

/-- The standard BKAR interpolation point `x^F(u)`. -/
noncomputable def standardInterp (F : Forest V) (u : F.EdgeParam → ℝ) :
    Edge V → ℝ :=
  fun e =>
    if h : F.inSameComponent e.left e.right then
      F.pathMin u (F.pathInF e.left e.right h)
    else
      0

/-- The one-parameter family `W^F(u; t)` used in the iterative proof. -/
noncomputable def interpWithFill (F : Forest V) (u : F.EdgeParam → ℝ)
    (t : ℝ) : Edge V → ℝ :=
  fun e =>
    if h : F.inSameComponent e.left e.right then
      F.pathMin u (F.pathInF e.left e.right h)
    else
      t

theorem interpWithFill_zero (F : Forest V) (u : F.EdgeParam → ℝ) :
    F.interpWithFill u 0 = F.standardInterp u :=
  rfl

theorem standardInterp_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.standardInterp u e = 0 := by
  rw [standardInterp, dif_neg he]

theorem interpWithFill_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = t := by
  rw [interpWithFill, dif_neg he]

theorem standardInterp_of_mem (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.standardInterp u e = u ⟨e, he⟩ := by
  rw [standardInterp, dif_pos (F.edge_inSameComponent he),
    F.pathInF_eq_singleton_of_edge_mem he, F.pathMin_singleton u he]

theorem interpWithFill_of_mem (F : Forest V) (u : F.EdgeParam → ℝ)
    (t : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    F.interpWithFill u t e = u ⟨e, he⟩ := by
  rw [interpWithFill, dif_pos (F.edge_inSameComponent he),
    F.pathInF_eq_singleton_of_edge_mem he, F.pathMin_singleton u he]

theorem standardInterp_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.standardInterp u e ∧ F.standardInterp u e ≤ 1 := by
  by_cases h : F.inSameComponent e.left e.right
  · rw [standardInterp, dif_pos h]
    exact F.pathMin_mem_Icc u hu (F.pathInF e.left e.right h)
  · rw [standardInterp, dif_neg h]
    exact ⟨le_rfl, zero_le_one⟩

theorem interpWithFill_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (e : Edge V) :
    0 ≤ F.interpWithFill u t e ∧ F.interpWithFill u t e ≤ 1 := by
  by_cases h : F.inSameComponent e.left e.right
  · rw [interpWithFill, dif_pos h]
    exact F.pathMin_mem_Icc u hu (F.pathInF e.left e.right h)
  · rw [interpWithFill, dif_neg h]
    exact ht

theorem empty_standardInterp (u : (Forest.empty V).EdgeParam → ℝ) :
    (Forest.empty V).standardInterp u = zeroConfig := by
  funext e
  rw [standardInterp]
  rw [dif_neg]
  · rfl
  · intro hcomp
    exact e.left_ne_right ((Forest.empty_inSameComponent_iff.mp hcomp))

theorem empty_interpWithFill (u : (Forest.empty V).EdgeParam → ℝ)
    (t : ℝ) :
    (Forest.empty V).interpWithFill u t = constantConfig t := by
  funext e
  rw [interpWithFill]
  rw [dif_neg]
  · rfl
  · intro hcomp
    exact e.left_ne_right ((Forest.empty_inSameComponent_iff.mp hcomp))

theorem empty_interpWithFill_one (u : (Forest.empty V).EdgeParam → ℝ) :
    (Forest.empty V).interpWithFill u 1 = oneConfig :=
  empty_interpWithFill u 1

theorem emptyParam_standardInterp :
    (Forest.empty V).standardInterp emptyParam = zeroConfig :=
  empty_standardInterp emptyParam

theorem emptyParam_interpWithFill (t : ℝ) :
    (Forest.empty V).interpWithFill emptyParam t = constantConfig t :=
  empty_interpWithFill emptyParam t

theorem emptyParam_interpWithFill_one :
    (Forest.empty V).interpWithFill emptyParam 1 = oneConfig :=
  emptyParam_interpWithFill 1

theorem pathMinAux_eq_of_forall (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ {a b : ℝ}, a = b → ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMinAux u a γ = G.pathMinAux v b γ
  | a, b, hab, [] => fun _ => hab
  | a, b, hab, e :: γ => by
      intro hγ
      apply pathMinAux_eq_of_forall F G u v
        (a := min a (F.paramValue u e)) (b := min b (G.paramValue v e))
      · rw [hab, hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial)]
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')

theorem pathMin_eq_of_forall (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMin u γ = G.pathMin v γ
  | [] => fun _ => rfl
  | e :: γ => by
      intro hγ
      apply pathMinAux_eq_of_forall F G u v
      · exact hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial)
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')

/--
The standard BKAR interpolation point only depends on the underlying edge set
and the ambient edge-parameter values, not on the particular path data
stored in a `Forest`.
-/
theorem standardInterp_eq_of_edges_eq (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ)
    (hedges : F.edges = G.edges)
    (hparam : ∀ e : Edge V, F.paramValue u e = G.paramValue v e) :
    F.standardInterp u = G.standardInterp v := by
  funext e
  by_cases hF : F.inSameComponent e.left e.right
  · have hG : G.inSameComponent e.left e.right :=
      F.inSameComponent_of_edges_eq G hedges hF
    rw [standardInterp, dif_pos hF]
    rw [standardInterp, dif_pos hG]
    rw [F.pathInF_eq_of_edges_eq G hedges hF hG]
    exact F.pathMin_eq_of_forall G u v
      (G.pathInF e.left e.right hG)
      (fun e' _he' => hparam e')
  · have hG : ¬ G.inSameComponent e.left e.right := by
      intro hG
      exact hF (G.inSameComponent_of_edges_eq F hedges.symm hG)
    rw [standardInterp, dif_neg hF]
    rw [standardInterp, dif_neg hG]

theorem pathMinAux_le_seed (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (a : ℝ) (γ : List (Edge V)), F.pathMinAux u a γ ≤ a
  | _, [] => le_rfl
  | a, e :: γ =>
      (F.pathMinAux_le_seed u (min a (F.paramValue u e)) γ).trans
        (min_le_left _ _)

theorem le_pathMinAux_of_forall (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} :
    ∀ {a : ℝ}, s ≤ a → ∀ γ : List (Edge V),
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMinAux u a γ
  | a, ha, [] => fun _ => ha
  | a, ha, e :: γ => by
      intro hγ
      apply F.le_pathMinAux_of_forall u
        (a := min a (F.paramValue u e))
      · exact le_min ha (hγ e (by
          simp only [List.mem_cons]
          exact Or.inl trivial))
      · intro e' he'
        exact hγ e' (by
          simp only [List.mem_cons]
          exact Or.inr he')

theorem le_pathMin_of_mem_forall (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMin u γ
  | [], hmem => by
      cases hmem
  | e :: γ, _ => by
      intro hγ
      exact F.le_pathMinAux_of_forall u
        (hγ e (by simp only [List.mem_cons, true_or])) γ
        (fun e' he' => hγ e' (by simp only [List.mem_cons, he', or_true]))

theorem pathMinAux_le_of_mem_eq (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {a : ℝ} (γ : List (Edge V)), e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMinAux u a γ ≤ s
  | a, [], hmem => by
      cases hmem
  | a, e :: γ, hmem => by
      intro heq
      by_cases hhead : e = e₀
      · have hseed : min a (F.paramValue u e) ≤ s := by
          rw [hhead, heq]
          exact min_le_right _ _
        exact (F.pathMinAux_le_seed u (min a (F.paramValue u e)) γ).trans hseed
      · have htail : e₀ ∈ γ := by
          rw [List.mem_cons] at hmem
          exact hmem.elim (fun h => False.elim (hhead h.symm)) id
        exact F.pathMinAux_le_of_mem_eq u γ htail heq

theorem pathMin_le_of_mem_eq (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMin u γ ≤ s
  | [], hmem => by
      cases hmem
  | e :: γ, hmem => by
      intro heq
      by_cases hhead : e = e₀
      · have hseed : F.paramValue u e ≤ s := by
          rw [hhead, heq]
        exact (F.pathMinAux_le_seed u (F.paramValue u e) γ).trans hseed
      · have htail : e₀ ∈ γ := by
          rw [List.mem_cons] at hmem
          exact hmem.elim (fun h => False.elim (hhead h.symm)) id
        exact F.pathMinAux_le_of_mem_eq u γ htail heq

namespace EdgeExtension

variable {F F' : Forest V} {e₀ : Edge V}

/-- Extend forest-edge parameters to a one-edge extension. -/
def extendParam (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) : F'.EdgeParam → ℝ :=
  fun e =>
    if he : e.val = e₀ then
      s
    else
      u ⟨e.val, h.mem_old_of_mem_of_ne e.property he⟩

theorem extendParam_new (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) :
    h.extendParam u s ⟨e₀, h.new_mem⟩ = s := by
  rw [extendParam, dif_pos rfl]

theorem extendParam_old (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.extendParam u s ⟨e, h.old_mem he⟩ = u ⟨e, he⟩ := by
  have hne : (⟨e, h.old_mem he⟩ : F'.EdgeParam).val ≠ e₀ := by
    intro heq
    have heq' : e = e₀ := heq
    exact h.new_not_mem (heq' ▸ he)
  rw [extendParam, dif_neg hne]

theorem paramValue_extend_new (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) :
    F'.paramValue (h.extendParam u s) e₀ = s := by
  rw [paramValue_of_mem F' (h.extendParam u s) h.new_mem,
    h.extendParam_new u s]

theorem paramValue_extend_old (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    F'.paramValue (h.extendParam u s) e = F.paramValue u e := by
  rw [paramValue_of_mem F' (h.extendParam u s) (h.old_mem he),
    h.extendParam_old u s he, paramValue_of_mem F u he]

theorem le_extendParam (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) (e : F'.EdgeParam) :
    s ≤ h.extendParam u s e := by
  by_cases he : e.val = e₀
  · rw [extendParam, dif_pos he]
  · rw [extendParam, dif_neg he]
    exact hu ⟨e.val, h.mem_old_of_mem_of_ne e.property he⟩

theorem paramValue_extend_le (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) {e : Edge V}
    (he : e ∈ F'.edges) :
    s ≤ F'.paramValue (h.extendParam u s) e := by
  rw [paramValue_of_mem F' (h.extendParam u s) he]
  exact h.le_extendParam u hu ⟨e, he⟩

/--
Ordered-step reinterpretation: if the newly-added edge receives the current
global parameter `s`, and all old forest parameters are at least `s`, then the
old and extended fill-parameter configurations agree at `s`.
-/
theorem interpWithFill_extend_eq (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    F.interpWithFill u s = F'.interpWithFill (h.extendParam u s) s := by
  funext e
  by_cases hF : F.inSameComponent e.left e.right
  · rw [interpWithFill, dif_pos hF, interpWithFill,
      dif_pos (h.old_component hF), h.old_path hF]
    apply pathMin_eq_of_forall
    intro e' he'
    have heF : e' ∈ F.edges :=
      F.edge_mem_of_isSimplePath (F.pathInF_isSimple hF) e' he'
    exact (h.paramValue_extend_old u s heF).symm
  · by_cases hF' : F'.inSameComponent e.left e.right
    · rw [interpWithFill, dif_neg hF, interpWithFill, dif_pos hF']
      have huse : e₀ ∈ F'.pathInF e.left e.right hF' :=
        h.new_path_uses hF hF'
      have hlower :
          s ≤ F'.pathMin (h.extendParam u s)
            (F'.pathInF e.left e.right hF') :=
        F'.le_pathMin_of_mem_forall (h.extendParam u s) huse
          (fun e' he' => by
            have heF' : e' ∈ F'.edges :=
              F'.edge_mem_of_isSimplePath (F'.pathInF_isSimple hF') e' he'
            exact h.paramValue_extend_le u hu heF')
      have hupper :
          F'.pathMin (h.extendParam u s)
            (F'.pathInF e.left e.right hF') ≤ s :=
        F'.pathMin_le_of_mem_eq (h.extendParam u s) huse
          (h.paramValue_extend_new u s)
      exact (le_antisymm hupper hlower).symm
    · rw [interpWithFill, dif_neg hF, interpWithFill, dif_neg hF']

end EdgeExtension

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
