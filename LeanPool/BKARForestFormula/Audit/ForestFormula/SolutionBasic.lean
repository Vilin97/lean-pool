/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
import LeanPool.BKARForestFormula.BKAR

/-!
# BKAR forest formula — Challenge → repository bridges

Shared statement vocabulary (byte-identical to `Challenge.lean`) together with
the bridge lemmas connecting the Mathlib-only mirror to the repository flagship
`BKAR.bkar_formula_forestIndex_cube_contributions`.

This file is `sorry`-free and importable.  `Solution.lean` uses it to prove the
byte-identical challenge statement.

## Bridge outline

* **Q1** `acyclic_bridge` — Mathlib graph acyclicity `SimpleGraph.IsAcyclic` on
  `edgeGraph` is equivalent to the repository certificate `IsAcyclicEdgeSet`.
  Forward reuses `AcyclicEdgeSetData.edgeSetGraph_isAcyclic`; the reverse builds
  an `AcyclicEdgeSetData` from graph acyclicity (the constructor extracted from
  `isAcyclicEdgeSet_insert_of_not_inSameComponent`).
* **Q2** `standardInterp_bridge` — the threshold / `sSup` interpolation point
  agrees with the repository path-minimum `Forest.standardInterp`, via
  `le_standardInterp_iff_thresholdConnected` and a graph-reachability ↔
  threshold-connectivity comparison, closed by `csSup` antisymmetry (with the
  `sSup ∅ = 0` boundary handled by `Real.sSup_nonneg`).
* **Q3/Q4** `mixedPartial_bridge`, `cubeContribution_bridge` — the verbatim
  mixed partial and the cube integral agree; choice-independence is discharged
  through `cubeContribution_eq_canonicalGrownForestForSupport` and
  `cubeContribution_eq_of_edges_eq`.
* `sum_bridge` transports the mirror sum to the repository sum along
  `indexEquiv`.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace BKARMirror

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Mirror vocabulary (byte-identical to `Challenge.lean`) -/

/-- Off-diagonal unordered pairs = edges of the complete graph on `V`. -/
abbrev Edge (V : Type*) [DecidableEq V] : Type _ := {e : Sym2 V // ¬ e.IsDiag}

noncomputable instance : Fintype (Edge V) := Fintype.ofFinite _

/-- A fixed orientation of an edge (Mathlib `Sym2.out`). -/
def Edge.left  (e : Edge V) : V := e.val.out.1
def Edge.right (e : Edge V) : V := e.val.out.2

/-- The simple graph carried by a finite edge set. -/
def edgeGraph (S : Finset (Edge V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {x : Sym2 V | ∃ e : Edge V, e ∈ S ∧ e.val = x}

/-- Q1: the forest index, indexed by an edge set whose carried graph is acyclic. -/
structure ForestIndex (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Edge V)
  acyclic : (edgeGraph edges).IsAcyclic

namespace ForestIndex

/-- `ForestIndex V` is a `Fintype` (mirrors the repo's `Classical`-decidable route). -/
noncomputable instance instFintype : Fintype (ForestIndex V) := by
  classical
  letI : DecidablePred (fun S : Finset (Edge V) => (edgeGraph S).IsAcyclic) :=
    fun _ => Classical.propDecidable _
  let e : ForestIndex V ≃ {S : Finset (Edge V) // (edgeGraph S).IsAcyclic} :=
    { toFun := fun F => ⟨F.edges, F.acyclic⟩
      invFun := fun S => ⟨S.1, S.2⟩
      left_inv := by intro F; cases F; rfl
      right_inv := by intro S; cases S; rfl }
  exact Fintype.ofEquiv _ e.symm

end ForestIndex

/-- Look up an edge parameter, defaulting to `1` off the forest. -/
def paramValue (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) (e : Edge V) : ℝ :=
  if h : e ∈ J.edges then u ⟨e, h⟩ else 1

/-- The threshold subgraph: edges of `J` whose parameter is `≥ s`. -/
def thresholdGraph (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {x : Sym2 V | ∃ e : Edge V, e ∈ J.edges ∧ e.val = x ∧ s ≤ paramValue J u e}

/--
Q2: the BKAR interpolation point `x^F(u)_e`, as the largest threshold `s ∈ [0,1]`
at which the endpoints of `e` remain connected using only couplings `≥ s`
(the bottleneck / max-min connectivity value; `sSup ∅ = 0` handles disconnection).
-/
def standardInterp (J : ForestIndex V) (u : {e : Edge V // e ∈ J.edges} → ℝ) :
    Edge V → ℝ :=
  fun e => sSup {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ (thresholdGraph J u s).Reachable e.left e.right}

/-- Replace one edge coordinate (verbatim). -/
def updateCoord (x : Edge V → ℝ) (e : Edge V) (t : ℝ) : Edge V → ℝ := Function.update x e t

/-- Partial derivative along one edge coordinate (verbatim). -/
def partialDeriv (e : Edge V) (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) : ℝ :=
  deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e)

/-- Q3: iterated mixed partial along a list of edges (verbatim). -/
def mixedPartialList : List (Edge V) → ((Edge V → ℝ) → ℝ) → (Edge V → ℝ) → ℝ
  | [], ρ => ρ
  | e :: es, ρ => partialDeriv e (mixedPartialList es ρ)

/-- The forest-indexed mixed partial (verbatim: over `Finset.toList`). -/
def mixedPartial (J : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : (Edge V → ℝ) → ℝ :=
  mixedPartialList J.edges.toList ρ

/-- Q4: the unit cube `[0,1]^{E(J)}`. -/
def unitCube (J : ForestIndex V) : Set ({e : Edge V // e ∈ J.edges} → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

/-- Q4: the ordinary BKAR cube contribution of a forest index (direct, choice-free). -/
def cubeContribution (J : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in unitCube J, mixedPartial J ρ (standardInterp J u)

/-- BKAR smoothness hypothesis (mirror of `BKARContDiff`). -/
def ContDiffHyp (ρ : (Edge V → ℝ) → ℝ) : Prop := ContDiff ℝ (∞ : WithTop ℕ∞) ρ

/-! ## Q1 bridge: mirror graph acyclicity ↔ repository certificate -/

omit [Fintype V] in
/-- The mirror graph on an edge set is byte-identical to the repository's
`EdgePath.edgeSetGraph`. -/
theorem edgeGraph_eq (S : Finset (Edge V)) :
    edgeGraph S = BKAR.EdgePath.edgeSetGraph S := rfl

/-- **Q1 bridge.**  Mirror graph acyclicity ↔ repository acyclicity certificate. -/
theorem acyclic_bridge (S : Finset (Edge V)) :
    (edgeGraph S).IsAcyclic ↔ BKAR.IsAcyclicEdgeSet S := by
  constructor
  · intro h
    -- `hG : (edgeSetGraph S).IsAcyclic`; build an `AcyclicEdgeSetData S`
    -- (the constructor from `isAcyclicEdgeSet_insert_of_not_inSameComponent`).
    have hG : (BKAR.EdgePath.edgeSetGraph S).IsAcyclic := h
    refine ⟨{
      inSameComponent := fun i j =>
        ∃ γ : List (Edge V), BKAR.EdgePath.IsSimplePath S γ i j
      isSimplePath := fun γ i j =>
        BKAR.EdgePath.IsSimplePath S γ i j
      pathIn := fun _ _ h => Classical.choose h
      pathIn_isSimple := ?_
      isSimplePath_iff := ?_
      sameComponent_of_simplePath := ?_
      path_unique := ?_
      path_edges_mem := ?_
      edge_isSimplePath := ?_ }⟩
    · intro i j h
      exact Classical.choose_spec h
    · intro i j γ
      rfl
    · intro i j γ hγ
      exact ⟨γ, hγ⟩
    · intro i j γ₁ γ₂ hγ₁ hγ₂
      exact BKAR.EdgePath.IsSimplePath.unique_of_isAcyclic hG hγ₁ hγ₂
    · intro i j γ hγ e' he'
      exact hγ.edge_mem e' he'
    · intro e' he'
      exact
        ⟨BKAR.EdgePath.IsPath.cons he' e'.between_left_right
          (BKAR.EdgePath.IsPath.nil e'.right), by simp⟩
  · rintro ⟨data⟩
    exact data.edgeSetGraph_isAcyclic

/-- The forest-index types are equivalent (from the acyclicity iff). -/
def indexEquiv : ForestIndex V ≃ BKAR.ForestIndex V where
  toFun J := ⟨J.edges, (acyclic_bridge J.edges).mp J.acyclic⟩
  invFun I := ⟨I.edges, (acyclic_bridge I.edges).mpr I.acyclic⟩
  left_inv := by intro J; cases J; rfl
  right_inv := by intro I; cases I; rfl

/-! ## Q2 bridge: threshold `sSup` interpolation ↔ repository path-minimum -/

omit [Fintype V] in
/-- Reachability in `edgeSetGraph S` is the existence of a simple edge path. -/
theorem edgeSetGraph_reachable_iff_exists_isSimplePath
    (S : Finset (Edge V)) (i j : V) :
    (BKAR.EdgePath.edgeSetGraph S).Reachable i j ↔
      ∃ γ, BKAR.EdgePath.IsSimplePath S γ i j := by
  constructor
  · rintro ⟨w⟩
    exact ⟨_, BKAR.EdgePath.Walk.toEdgePath_isSimplePath_of_isPath w.toPath.2⟩
  · rintro ⟨γ, hγ⟩
    rcases hγ.1.exists_walk with ⟨p, _⟩
    exact ⟨p⟩

/-- Threshold connectivity is the existence of a simple path in the threshold
edge set. -/
theorem thresholdConnected_iff_exists_isSimplePath
    (G : BKAR.Forest V) (u : G.EdgeParam → ℝ) (s : ℝ) (i j : V) :
    G.thresholdConnected u s i j ↔
      ∃ γ, BKAR.EdgePath.IsSimplePath (G.thresholdEdges u s) γ i j := by
  constructor
  · intro h
    rw [G.thresholdConnected_iff_thresholdForest_inSameComponent u s] at h
    exact
      (BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
        (G.thresholdForest u s).acyclic).mp h
  · intro h
    rw [G.thresholdConnected_iff_thresholdForest_inSameComponent u s]
    exact
      (BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
        (G.thresholdForest u s).acyclic).mpr h

/-- The mirror threshold graph coincides with the repository threshold-edge
graph. -/
theorem thresholdGraph_eq (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) :
    thresholdGraph J u s
      = BKAR.EdgePath.edgeSetGraph ((data.toForest).thresholdEdges u s) := by
  unfold thresholdGraph BKAR.EdgePath.edgeSetGraph
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, heJ, heq, hs⟩
    refine ⟨e, ?_, heq⟩
    exact (BKAR.Forest.mem_thresholdEdges data.toForest u s e).mpr ⟨heJ, hs⟩
  · rintro ⟨e, hmem, heq⟩
    have hmem' := (BKAR.Forest.mem_thresholdEdges data.toForest u s e).mp hmem
    exact ⟨e, hmem'.1, heq, hmem'.2⟩

/-- Threshold-graph reachability matches repository threshold connectivity. -/
theorem reachable_thresholdGraph_iff (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) (e : Edge V) :
    (thresholdGraph J u s).Reachable e.left e.right ↔
      (data.toForest).thresholdConnected u s e.left e.right := by
  rw [thresholdGraph_eq J data u s]
  rw [edgeSetGraph_reachable_iff_exists_isSimplePath]
  exact (thresholdConnected_iff_exists_isSimplePath data.toForest u s e.left e.right).symm

/-- **Q2 bridge.**  The mirror threshold / `sSup` interpolation point agrees with
the repository path-minimum `Forest.standardInterp`, on the unit cube. -/
theorem standardInterp_bridge (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ)
    (hu : ∀ e : {e : Edge V // e ∈ J.edges}, 0 ≤ u e ∧ u e ≤ 1) :
    standardInterp J u = (data.toForest).standardInterp u := by
  funext e
  have hu' : ∀ e : (data.toForest).EdgeParam, 0 ≤ u e ∧ u e ≤ 1 := hu
  have hr := (data.toForest).standardInterp_mem_Icc u hu' e
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ((thresholdGraph J u s).Reachable e.left e.right ↔
        s ≤ (data.toForest).standardInterp u e) := by
    intro s hs0 hs1
    rw [(data.toForest).le_standardInterp_iff_thresholdConnected u hs0 hs1 e]
    exact reachable_thresholdGraph_iff J data u s e
  show sSup {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧
      (thresholdGraph J u s).Reachable e.left e.right}
      = (data.toForest).standardInterp u e
  apply le_antisymm
  · apply Real.sSup_le
    · rintro s ⟨hs0, hs1, hreach⟩
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · exact h0 ▸ hr.1
      · exact (key s h0 hs1).mp hreach
    · exact hr.1
  · rcases eq_or_lt_of_le hr.1 with h0 | h0
    · rw [← h0]
      apply Real.sSup_nonneg
      rintro s ⟨hs0, _, _⟩
      exact hs0
    · apply le_csSup
      · exact ⟨1, fun s hs => hs.2.1⟩
      · exact ⟨hr.1, hr.2, (key _ h0 hr.2).mpr le_rfl⟩

/-! ## Q3/Q4 bridges and choice removal -/

omit [Fintype V] in
/-- Q3: the mirror iterated mixed partial coincides with the repository one. -/
theorem mixedPartialList_bridge :
    ∀ (l : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      mixedPartialList l ρ = BKAR.mixedPartialList l ρ
  | [], _ρ => rfl
  | e :: es, ρ => by
      show partialDeriv e (mixedPartialList es ρ)
        = BKAR.partialDeriv e (BKAR.mixedPartialList es ρ)
      rw [mixedPartialList_bridge es ρ]
      rfl

/-- The forest mixed partial agrees with the mirror mixed partial. -/
theorem mixedPartial_bridge (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges) (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartial J ρ = (data.toForest).mixedPartial ρ :=
  mixedPartialList_bridge J.edges.toList ρ

/-- **Q2 + Q3 + Q4 bridge.**  The mirror direct cube contribution equals the
repository choice-routed `ForestIndex.cubeContribution`. -/
theorem cubeContribution_bridge (J : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : ContDiffHyp ρ) :
    cubeContribution J ρ = (indexEquiv J).cubeContribution ρ := by
  classical
  obtain ⟨data⟩ := (acyclic_bridge J.edges).mp J.acyclic
  obtain ⟨choices⟩ := BKAR.Forest.nonempty_activeExtensionChoice V
  -- Core: the mirror integral equals the repository cube contribution.
  have hcore : cubeContribution J ρ = (data.toForest).cubeContribution ρ := by
    unfold cubeContribution BKAR.Forest.cubeContribution
    apply setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    intro u hu
    have hu' : ∀ e : {e : Edge V // e ∈ J.edges}, 0 ≤ u e ∧ u e ≤ 1 :=
      fun e => Set.mem_Icc.mp (Set.mem_univ_pi.mp hu e)
    show mixedPartial J ρ (standardInterp J u)
      = (data.toForest).mixedPartial ρ ((data.toForest).standardInterp u)
    rw [standardInterp_bridge J data u hu']
    exact congrFun (mixedPartial_bridge J data ρ) _
  rw [hcore,
    BKAR.ForestIndex.cubeContribution_eq_canonicalGrownForestForSupport
      (indexEquiv J) choices ρ hρ]
  apply BKAR.Forest.cubeContribution_eq_of_edges_eq
  · rw [BKAR.Forest.canonicalGrownForestForSupport_edges]
    rfl
  · exact hρ

/-! ## Configuration and sum bridges -/

omit [Fintype V] in
/-- The all-ones config agrees (definitional). -/
theorem oneConfig_bridge :
    (fun _ : Edge V => (1 : ℝ)) = BKAR.oneConfig := rfl

/-- **Sum bridge.**  Transport the mirror sum to the repository sum via `indexEquiv`. -/
theorem sum_bridge (ρ : (Edge V → ℝ) → ℝ) (hρ : ContDiffHyp ρ) :
    (∑ J : ForestIndex V, cubeContribution J ρ) =
      ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
  calc (∑ J : ForestIndex V, cubeContribution J ρ)
      = ∑ J : ForestIndex V, (indexEquiv J).cubeContribution ρ :=
        Finset.sum_congr rfl (fun J _ => cubeContribution_bridge J ρ hρ)
    _ = ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
        Equiv.sum_comp indexEquiv (fun I => I.cubeContribution ρ)

end BKARMirror

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
