/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionTopology
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import Mathlib.Tactic

/-!
# Cut counting and bridgelessness for contractions and subdivisions

This module proves a double-sum normal form for `cutMultiplicity`, develops
two-edge connectivity for an ordered core, counts crossing steps in a
subdivision, and proves bridgelessness of positive subdivisions
(`twoEdgeCutCondition_graph_of_coreTwoEdgeConnected`).
-/

@[expose] public section
namespace Utilities.Certificate

open Finset

universe u v

/-! ## A double-sum normal form for `cutMultiplicity` -/

/-- `cutMultiplicity` written as an unrestricted double sum with an
indicator.  This is the form in which the quotient equation of a contraction
certificate can be substituted. -/
theorem cutMultiplicity_eq_double_sum (K : CFGraph) (S : Finset K.V) :
    cutMultiplicity K S =
      ∑ v : K.V, ∑ w : K.V,
        if v ∈ S ∧ w ∉ S then (numEdges K v w : ℤ) else 0 := by
  classical
  have hInner : ∀ v : K.V,
      (∑ w : K.V, if v ∈ S ∧ w ∉ S then (numEdges K v w : ℤ) else 0)
        = if v ∈ S then outdegreeSet K S v else 0 := by
    intro v
    by_cases hv : v ∈ S
    · simp [hv, outdeg_S_eq_sum_filter, Finset.sum_filter]
    · simp [hv]
  simp_rw [hInner]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rfl

namespace GraphContractionCertificate

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- The full preimage of a target vertex set. -/
def preimageFinset (c : GraphContractionCertificate G H) (S : Finset H.V) :
    Finset G.V :=
  Finset.univ.filter fun x => c.vertexMap x ∈ S

@[simp] theorem mem_preimageFinset (c : GraphContractionCertificate G H)
    (S : Finset H.V) (x : G.V) :
    x ∈ c.preimageFinset S ↔ c.vertexMap x ∈ S := by
  simp [preimageFinset]

/-- A nonempty target cut has a nonempty preimage. -/
theorem preimageFinset_nonempty (c : GraphContractionCertificate G H)
    (hValid : c.Valid) {S : Finset H.V} (hS : S.Nonempty) :
    (c.preimageFinset S).Nonempty := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨x, hx⟩ := hValid.1 a
  exact ⟨x, by simp [hx, ha]⟩

/-- A proper target cut has a proper preimage. -/
theorem preimageFinset_ne_univ (c : GraphContractionCertificate G H)
    (hValid : c.Valid) {S : Finset H.V} (hS : S ≠ Finset.univ) :
    c.preimageFinset S ≠ Finset.univ := by
  have hExists : ∃ b : H.V, b ∉ S := by
    by_contra hAll
    push Not at hAll
    exact hS (Finset.eq_univ_iff_forall.mpr hAll)
  obtain ⟨b, hb⟩ := hExists
  obtain ⟨y, hy⟩ := hValid.1 b
  intro hUniv
  have : y ∈ c.preimageFinset S := by rw [hUniv]; exact Finset.mem_univ y
  rw [mem_preimageFinset, hy] at this
  exact hb this

/-- **Cuts pull back exactly.**  The crossing multiplicity of a target cut
equals the crossing multiplicity of its full preimage.  Only the quotient
equation is used: the edges of the target are, with multiplicity, exactly the
edges of the source running between distinct fibres. -/
theorem cutMultiplicity_preimageFinset (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (S : Finset H.V) :
    cutMultiplicity G (c.preimageFinset S) = cutMultiplicity H S := by
  classical
  rw [cutMultiplicity_eq_double_sum, cutMultiplicity_eq_double_sum]
  have hEdge : ∀ a b : H.V, a ≠ b →
      (numEdges H a b : ℤ) =
        ∑ q : G.V × G.V,
          if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
            (numEdges G q.1 q.2 : ℤ) else 0 := by
    intro a b hab
    rw [Fintype.sum_prod_type]
    exact_mod_cast hValid.2 a b hab
  -- the summand of the target double sum, expanded along fibres
  have hTargetTerm : ∀ a b : H.V,
      (if a ∈ S ∧ b ∉ S then (numEdges H a b : ℤ) else 0) =
        ∑ q : G.V × G.V,
          if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
            (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0 := by
    intro a b
    by_cases hMem : a ∈ S ∧ b ∉ S
    · have hab : a ≠ b := fun h => hMem.2 (h ▸ hMem.1)
      rw [ite_eq_left hMem, hEdge a b hab]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b <;> simp [hq, hMem]
    · rw [ite_eq_right hMem]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hq : c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b <;> simp [hq, hMem]
  have hSwapInner : ∀ a : H.V,
      (∑ b : H.V, ∑ q : G.V × G.V,
        (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
          (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0)) =
      ∑ q : G.V × G.V, ∑ b : H.V,
        (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
          (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0) :=
    fun _ => Finset.sum_comm
  have hCollapse : ∀ q : G.V × G.V,
      (∑ a : H.V, ∑ b : H.V,
        (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
          (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0)) =
      (if c.vertexMap q.1 ∈ S ∧ c.vertexMap q.2 ∉ S then
        (numEdges G q.1 q.2 : ℤ) else 0) := by
    intro q
    simp [ite_and, Finset.sum_ite_eq]
  calc
    (∑ v : G.V, ∑ w : G.V,
        if v ∈ c.preimageFinset S ∧ w ∉ c.preimageFinset S then
          (numEdges G v w : ℤ) else 0)
        = ∑ q : G.V × G.V,
            if c.vertexMap q.1 ∈ S ∧ c.vertexMap q.2 ∉ S then
              (numEdges G q.1 q.2 : ℤ) else 0 := by
          rw [Fintype.sum_prod_type]
          simp [mem_preimageFinset]
    _ = ∑ q : G.V × G.V, ∑ a : H.V, ∑ b : H.V,
            (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
              (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0) := by
          exact Finset.sum_congr rfl fun q _ => (hCollapse q).symm
    _ = ∑ a : H.V, ∑ q : G.V × G.V, ∑ b : H.V,
            (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
              (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0) :=
          Finset.sum_comm
    _ = ∑ a : H.V, ∑ b : H.V, ∑ q : G.V × G.V,
            (if c.vertexMap q.1 = a ∧ c.vertexMap q.2 = b then
              (if a ∈ S ∧ b ∉ S then (numEdges G q.1 q.2 : ℤ) else 0) else 0) :=
          Finset.sum_congr rfl fun a _ => (hSwapInner a).symm
    _ = ∑ a : H.V, ∑ b : H.V,
            if a ∈ S ∧ b ∉ S then (numEdges H a b : ℤ) else 0 := by
          exact Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => (hTargetTerm a b).symm

/-- **Two-edge connectivity descends to contractions.**  A small cut of the
target pulls back to an equally small cut of the source. -/
theorem twoEdgeCutCondition_of_valid (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (hSource : TwoEdgeCutCondition G) :
    TwoEdgeCutCondition H := by
  intro S hNonempty hProper
  rw [← c.cutMultiplicity_preimageFinset hValid S]
  exact hSource _ (c.preimageFinset_nonempty hValid hNonempty)
    (c.preimageFinset_ne_univ hValid hProper)

/-- The topological form of the previous theorem, matching the shape in which
contraction certificates are consumed downstream. -/
theorem twoEdgeCutCondition_of_topologicalValid
    (c : GraphContractionCertificate G H)
    (hTopological : c.TopologicalValid) (hSource : TwoEdgeCutCondition G) :
    TwoEdgeCutCondition H :=
  c.twoEdgeCutCondition_of_valid hTopological.1 hSource

end GraphContractionCertificate

/-! ## Two-edge connectivity of an ordered core -/

namespace ExplicitPotential.Core

variable {n p : ℕ}

/-- Two-edge connectedness for an ordered loopless core: every nonempty
proper vertex set is crossed by at least two edge *slots*.  Parallel slots are
counted separately, exactly as they are in the subdivision. -/
def TwoEdgeConnected (core : ExplicitPotential.Core n p) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    2 ≤ ((Finset.univ : Finset (Fin p)).filter fun edge =>
      (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
      (core.head edge ∈ S ∧ core.tail edge ∉ S)).card

/-- Exact finite Boolean checker for core two-edge connectedness. -/
def twoEdgeConnectedCheck (core : ExplicitPotential.Core n p) : Bool :=
  AffineCover.allFinset (Finset.univ : Finset (Finset (Fin n))) fun S =>
    decide (S.Nonempty → S ≠ Finset.univ →
      2 ≤ ((Finset.univ : Finset (Fin p)).filter fun edge =>
        (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
        (core.head edge ∈ S ∧ core.tail edge ∉ S)).card)

@[simp] theorem twoEdgeConnectedCheck_eq_true_iff
    (core : ExplicitPotential.Core n p) :
    core.twoEdgeConnectedCheck = true ↔ core.TwoEdgeConnected := by
  rw [twoEdgeConnectedCheck, AffineCover.allFinset_eq_true_iff]
  simp only [Finset.mem_univ, true_implies, decide_eq_true_eq]
  exact Iff.rfl

/-- A two-edge connected core is connected. -/
theorem connected_of_twoEdgeConnected {core : ExplicitPotential.Core n p}
    (hTwo : core.TwoEdgeConnected) : core.Connected := by
  classical
  intro S hSplit
  obtain ⟨v, w, hv, hw⟩ := hSplit
  have hNonempty : S.Nonempty := ⟨v, hv⟩
  have hProper : S ≠ Finset.univ := by
    intro hUniv
    exact hw (hUniv ▸ Finset.mem_univ w)
  have hCard := hTwo S hNonempty hProper
  have hPos : 0 < ((Finset.univ : Finset (Fin p)).filter fun edge =>
      (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
      (core.head edge ∈ S ∧ core.tail edge ∉ S)).card := by omega
  obtain ⟨edge, hEdge⟩ := Finset.card_pos.mp hPos
  exact ⟨edge, (Finset.mem_filter.mp hEdge).2⟩

end ExplicitPotential.Core

/-! ## Cuts of a subdivision are counted by crossing unit steps -/

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- The unit steps of the subdivision whose two endpoints lie on opposite
sides of a vertex cut. -/
def crossingSteps (A : Finset spec.Vertex) : Finset spec.Step :=
  (Finset.univ : Finset spec.Step).filter fun step =>
    (spec.stepLeft step.1 step.2 ∈ A ∧ spec.stepRight step.1 step.2 ∉ A) ∨
    (spec.stepRight step.1 step.2 ∈ A ∧ spec.stepLeft step.1 step.2 ∉ A)

@[simp] theorem mem_crossingSteps (A : Finset spec.Vertex) (step : spec.Step) :
    step ∈ spec.crossingSteps A ↔
      (spec.stepLeft step.1 step.2 ∈ A ∧ spec.stepRight step.1 step.2 ∉ A) ∨
      (spec.stepRight step.1 step.2 ∈ A ∧ spec.stepLeft step.1 step.2 ∉ A) := by
  simp [crossingSteps]

/-- **Exact cut count.**  The crossing multiplicity of a vertex cut of a
subdivision is the number of emitted unit steps which cross it. -/
theorem cutMultiplicity_eq_card_crossingSteps (A : Finset spec.Vertex) :
    cutMultiplicity spec.graph A = ((spec.crossingSteps A).card : ℤ) := by
  classical
  rw [cutMultiplicity_eq_double_sum]
  have hnum : ∀ v w : spec.Vertex, (numEdges spec.graph v w : ℤ) =
      ∑ step : spec.Step,
        if spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) then
          (1 : ℤ) else 0 := by
    intro v w
    rw [spec.num_edges_eq_sum_steps]
    push_cast
    exact Finset.sum_congr rfl fun step _ => by
      by_cases h : spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) <;>
        simp [h]
  have hTerm : ∀ (step : spec.Step) (v w : spec.Vertex),
      (if v ∈ A ∧ w ∉ A then
        (if spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) then
          (1 : ℤ) else 0) else 0) =
      (if v = spec.stepLeft step.1 step.2 ∧ w = spec.stepRight step.1 step.2 then
        (if v ∈ A ∧ w ∉ A then (1 : ℤ) else 0) else 0) +
      (if v = spec.stepRight step.1 step.2 ∧ w = spec.stepLeft step.1 step.2 then
        (if v ∈ A ∧ w ∉ A then (1 : ℤ) else 0) else 0) := by
    intro step v w
    have hne : spec.stepLeft step.1 step.2 ≠ spec.stepRight step.1 step.2 :=
      spec.stepLeft_ne_stepRight step.1 step.2
    have hcond : (spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v)) ↔
        ((v = spec.stepLeft step.1 step.2 ∧
            w = spec.stepRight step.1 step.2) ∨
          (v = spec.stepRight step.1 step.2 ∧
            w = spec.stepLeft step.1 step.2)) := by
      simp only [unitEdge, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
    simp only [hcond]
    by_cases h1 : v = spec.stepLeft step.1 step.2 ∧
        w = spec.stepRight step.1 step.2
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hne]
    · by_cases h2 : v = spec.stepRight step.1 step.2 ∧
          w = spec.stepLeft step.1 step.2
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hne, Ne.symm hne]
      · simp [h1, h2]
  have hSwapInner : ∀ v : spec.Vertex,
      (∑ w : spec.Vertex, ∑ step : spec.Step,
        (if v ∈ A ∧ w ∉ A then
          (if spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) then
            (1 : ℤ) else 0) else 0)) =
      ∑ step : spec.Step, ∑ w : spec.Vertex,
        (if v ∈ A ∧ w ∉ A then
          (if spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) then
            (1 : ℤ) else 0) else 0) :=
    fun _ => Finset.sum_comm
  have hStepSum : ∀ step : spec.Step,
      (∑ v : spec.Vertex, ∑ w : spec.Vertex,
        (if v ∈ A ∧ w ∉ A then
          (if spec.unitEdge step = (v, w) ∨ spec.unitEdge step = (w, v) then
            (1 : ℤ) else 0) else 0)) =
      (if step ∈ spec.crossingSteps A then (1 : ℤ) else 0) := by
    intro step
    have hne : spec.stepLeft step.1 step.2 ≠ spec.stepRight step.1 step.2 :=
      spec.stepLeft_ne_stepRight step.1 step.2
    have hFirst : (∑ v : spec.Vertex, ∑ w : spec.Vertex,
        (if v = spec.stepLeft step.1 step.2 ∧
            w = spec.stepRight step.1 step.2 then
          (if v ∈ A ∧ w ∉ A then (1 : ℤ) else 0) else 0)) =
        (if spec.stepLeft step.1 step.2 ∈ A ∧
          spec.stepRight step.1 step.2 ∉ A then (1 : ℤ) else 0) := by
      simp [ite_and, Finset.sum_ite_eq']
    have hSecond : (∑ v : spec.Vertex, ∑ w : spec.Vertex,
        (if v = spec.stepRight step.1 step.2 ∧
            w = spec.stepLeft step.1 step.2 then
          (if v ∈ A ∧ w ∉ A then (1 : ℤ) else 0) else 0)) =
        (if spec.stepRight step.1 step.2 ∈ A ∧
          spec.stepLeft step.1 step.2 ∉ A then (1 : ℤ) else 0) := by
      simp [ite_and, Finset.sum_ite_eq']
    simp_rw [hTerm step, Finset.sum_add_distrib]
    rw [hFirst, hSecond]
    simp only [spec.mem_crossingSteps]
    by_cases hL : spec.stepLeft step.1 step.2 ∈ A <;>
      by_cases hR : spec.stepRight step.1 step.2 ∈ A <;> simp [hL, hR]
  calc
    (∑ v : spec.Vertex, ∑ w : spec.Vertex,
        if v ∈ A ∧ w ∉ A then (numEdges spec.graph v w : ℤ) else 0)
        = ∑ v : spec.Vertex, ∑ w : spec.Vertex, ∑ step : spec.Step,
            (if v ∈ A ∧ w ∉ A then
              (if spec.unitEdge step = (v, w) ∨
                  spec.unitEdge step = (w, v) then (1 : ℤ) else 0) else 0) := by
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
          by_cases hMem : v ∈ A ∧ w ∉ A
          · rw [ite_eq_left hMem, hnum v w]
            exact Finset.sum_congr rfl fun step _ => by rw [ite_eq_left hMem]
          · rw [ite_eq_right hMem]
            symm
            exact Finset.sum_eq_zero fun step _ => by rw [ite_eq_right hMem]
    _ = ∑ v : spec.Vertex, ∑ step : spec.Step, ∑ w : spec.Vertex,
            (if v ∈ A ∧ w ∉ A then
              (if spec.unitEdge step = (v, w) ∨
                  spec.unitEdge step = (w, v) then (1 : ℤ) else 0) else 0) :=
          Finset.sum_congr rfl fun v _ => hSwapInner v
    _ = ∑ step : spec.Step, ∑ v : spec.Vertex, ∑ w : spec.Vertex,
            (if v ∈ A ∧ w ∉ A then
              (if spec.unitEdge step = (v, w) ∨
                  spec.unitEdge step = (w, v) then (1 : ℤ) else 0) else 0) :=
          Finset.sum_comm
    _ = ∑ step : spec.Step,
            (if step ∈ spec.crossingSteps A then (1 : ℤ) else 0) :=
          Finset.sum_congr rfl fun step _ => hStepSum step
    _ = ((spec.crossingSteps A).card : ℤ) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
          simp

/-! ## Crossing steps along one subdivided slot -/

/-- Membership in a finite set must change across some unit step between two
path positions whose endpoints disagree. -/
theorem exists_crossing_step_between (A : Finset spec.Vertex) (edge : Fin p)
    (lo hi : spec.PathPosition edge) (hlt : lo.val < hi.val)
    (hIn : spec.pathVertex edge lo ∈ A)
    (hOut : spec.pathVertex edge hi ∉ A) :
    ∃ offset : Fin (spec.length edge), lo.val ≤ offset.val ∧
      offset.val < hi.val ∧
      spec.stepLeft edge offset ∈ A ∧ spec.stepRight edge offset ∉ A := by
  classical
  by_contra hNone
  push Not at hNone
  have hHiLe : hi.val ≤ spec.length edge := by
    have := hi.isLt
    omega
  have key : ∀ m : ℕ, ∀ hm : lo.val + m ≤ hi.val,
      spec.pathVertex edge ⟨lo.val + m, by omega⟩ ∈ A := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using hIn
    | succ m inductionHypothesis =>
        intro hm
        have hPrevious := inductionHypothesis (by omega)
        have hStep : lo.val + m < spec.length edge := by omega
        have hLeft : spec.stepLeft edge ⟨lo.val + m, hStep⟩ =
            spec.pathVertex edge ⟨lo.val + m, by omega⟩ :=
          (spec.pathVertex_stepLeftPosition edge ⟨lo.val + m, hStep⟩).symm
        have hRight : spec.stepRight edge ⟨lo.val + m, hStep⟩ =
            spec.pathVertex edge ⟨lo.val + m + 1, by omega⟩ :=
          (spec.pathVertex_stepRightPosition edge ⟨lo.val + m, hStep⟩).symm
        have hInLeft : spec.stepLeft edge ⟨lo.val + m, hStep⟩ ∈ A := by
          rw [hLeft]; exact hPrevious
        have hInRight := hNone ⟨lo.val + m, hStep⟩
          (show lo.val ≤ lo.val + m by omega)
          (show lo.val + m < hi.val by omega) hInLeft
        rw [hRight] at hInRight
        exact hInRight
  have hFinal := key (hi.val - lo.val) (by omega)
  apply hOut
  have hEq : (⟨lo.val + (hi.val - lo.val), by omega⟩ :
      spec.PathPosition edge) = hi := by
    apply Fin.ext
    simp only
    omega
  rw [hEq] at hFinal
  exact hFinal

/-- The same statement with the disagreement in either direction, phrased
directly in terms of `crossingSteps`. -/
theorem exists_crossingStep_between (A : Finset spec.Vertex) (edge : Fin p)
    (lo hi : spec.PathPosition edge) (hlt : lo.val < hi.val)
    (hDiff : (spec.pathVertex edge lo ∈ A ∧ spec.pathVertex edge hi ∉ A) ∨
      (spec.pathVertex edge lo ∉ A ∧ spec.pathVertex edge hi ∈ A)) :
    ∃ offset : Fin (spec.length edge), lo.val ≤ offset.val ∧
      offset.val < hi.val ∧
      (⟨edge, offset⟩ : spec.Step) ∈ spec.crossingSteps A := by
  classical
  rcases hDiff with ⟨hIn, hOut⟩ | ⟨hOut, hIn⟩
  · obtain ⟨offset, hLo, hHi, hLeft, hRight⟩ :=
      spec.exists_crossing_step_between A edge lo hi hlt hIn hOut
    exact ⟨offset, hLo, hHi, by simp [hLeft, hRight]⟩
  · have hInC : spec.pathVertex edge lo ∈ Aᶜ := Finset.mem_compl.mpr hOut
    have hOutC : spec.pathVertex edge hi ∉ Aᶜ := by
      simp [Finset.mem_compl, hIn]
    obtain ⟨offset, hLo, hHi, hLeft, hRight⟩ :=
      spec.exists_crossing_step_between Aᶜ edge lo hi hlt hInC hOutC
    rw [Finset.mem_compl] at hLeft
    have hRight' : spec.stepRight edge offset ∈ A := by
      by_contra hcon
      exact hRight (Finset.mem_compl.mpr hcon)
    exact ⟨offset, hLo, hHi, by simp [hLeft, hRight']⟩

/-! ## Bridgelessness of positive subdivisions -/

/-- The tail endpoint as a path position. -/
private def zeroPosition (edge : Fin p) : spec.PathPosition edge :=
  ⟨0, by omega⟩

/-- The head endpoint as a path position. -/
private def lastPosition (edge : Fin p) : spec.PathPosition edge :=
  ⟨spec.length edge, by omega⟩

/-- An interior coordinate as a path position. -/
private def interiorPosition (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) : spec.PathPosition edge :=
  ⟨offset.val + 1, by have := offset.isLt; omega⟩

private theorem pathVertex_interiorPosition (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.pathVertex edge (spec.interiorPosition edge offset) =
      spec.interiorVertex edge offset := by
  have hIsLt := offset.isLt
  unfold pathVertex interiorPosition
  rw [dite_eq_right (by simp), dite_eq_right (by simp; omega)]
  congr 1

/-- **Positive subdivisions of two-edge connected cores are bridgeless.**
Every nonempty proper vertex cut of the subdivision is crossed by at least
two unit steps.  No further hypothesis is needed: a cut which separates a
slot interior from both of its core endpoints is crossed twice inside that
slot, and any other cut induces a nontrivial core cut, which is crossed by
two distinct core slots. -/
theorem twoEdgeCutCondition_graph_of_coreTwoEdgeConnected
    (hCore : spec.core.TwoEdgeConnected) :
    TwoEdgeCutCondition spec.graph := by
  classical
  intro A hNonempty hProper
  rw [spec.cutMultiplicity_eq_card_crossingSteps A]
  have hTwoCard : ∀ s₁ s₂ : spec.Step, s₁ ≠ s₂ →
      s₁ ∈ spec.crossingSteps A → s₂ ∈ spec.crossingSteps A →
      (2 : ℤ) ≤ ((spec.crossingSteps A).card : ℤ) := by
    intro s₁ s₂ hne h₁ h₂
    have : 1 < (spec.crossingSteps A).card :=
      Finset.one_lt_card.mpr ⟨s₁, h₁, s₂, h₂, hne⟩
    exact_mod_cast this
  -- the induced core cut
  set coreSide : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun vertex =>
      spec.coreVertex vertex ∈ A with hCoreSide
  by_cases hCoreProper : coreSide.Nonempty ∧ coreSide ≠ Finset.univ
  · -- two distinct core slots cross the induced core cut
    have hCard := hCore coreSide hCoreProper.1 hCoreProper.2
    obtain ⟨e₁, he₁, e₂, he₂, hDistinct⟩ :=
      Finset.one_lt_card.mp (by omega :
        1 < ((Finset.univ : Finset (Fin p)).filter fun edge =>
          (spec.core.tail edge ∈ coreSide ∧ spec.core.head edge ∉ coreSide) ∨
          (spec.core.head edge ∈ coreSide ∧
            spec.core.tail edge ∉ coreSide)).card)
    have hSlot : ∀ e : Fin p,
        e ∈ ((Finset.univ : Finset (Fin p)).filter fun edge =>
          (spec.core.tail edge ∈ coreSide ∧ spec.core.head edge ∉ coreSide) ∨
          (spec.core.head edge ∈ coreSide ∧
            spec.core.tail edge ∉ coreSide)) →
        ∃ offset : Fin (spec.length e),
          (⟨e, offset⟩ : spec.Step) ∈ spec.crossingSteps A := by
      intro e he
      have hDiff := (Finset.mem_filter.mp he).2
      have hLt : (spec.zeroPosition e).val < (spec.lastPosition e).val := by
        have := spec.length_pos e
        simpa [zeroPosition, lastPosition] using this
      have hTail : spec.pathVertex e (spec.zeroPosition e) =
          spec.coreVertex (spec.core.tail e) := by
        simpa [zeroPosition] using spec.pathVertex_zero e
      have hHead : spec.pathVertex e (spec.lastPosition e) =
          spec.coreVertex (spec.core.head e) := by
        simp [lastPosition]
      have hDiffPath :
          (spec.pathVertex e (spec.zeroPosition e) ∈ A ∧
            spec.pathVertex e (spec.lastPosition e) ∉ A) ∨
          (spec.pathVertex e (spec.zeroPosition e) ∉ A ∧
            spec.pathVertex e (spec.lastPosition e) ∈ A) := by
        rw [hTail, hHead]
        rcases hDiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by simpa [hCoreSide] using h1,
            by simpa [hCoreSide] using h2⟩
        · exact Or.inr ⟨by simpa [hCoreSide] using h2,
            by simpa [hCoreSide] using h1⟩
      obtain ⟨offset, _, _, hMem⟩ :=
        spec.exists_crossingStep_between A e _ _ hLt hDiffPath
      exact ⟨offset, hMem⟩
    obtain ⟨k₁, hk₁⟩ := hSlot e₁ he₁
    obtain ⟨k₂, hk₂⟩ := hSlot e₂ he₂
    refine hTwoCard ⟨e₁, k₁⟩ ⟨e₂, k₂⟩ ?_ hk₁ hk₂
    intro hEq
    exact hDistinct (congrArg Sigma.fst hEq)
  · -- all core vertices lie on the same side; an interior vertex is separated
    have hUniform : ∀ u v : Fin n,
        (spec.coreVertex u ∈ A ↔ spec.coreVertex v ∈ A) := by
      intro u v
      by_contra hcon
      apply hCoreProper
      constructor
      · by_cases hu : spec.coreVertex u ∈ A
        · exact ⟨u, by simp [hCoreSide, hu]⟩
        · exact ⟨v, by
            simp only [hCoreSide, Finset.mem_filter, Finset.mem_univ, true_and]
            tauto⟩
      · intro hUniv
        by_cases hu : spec.coreVertex u ∈ A
        · have hv : v ∈ coreSide := hUniv ▸ Finset.mem_univ v
          simp only [hCoreSide, Finset.mem_filter, Finset.mem_univ,
            true_and] at hv
          exact hcon ⟨fun _ => hv, fun _ => hu⟩
        · have hu' : u ∈ coreSide := hUniv ▸ Finset.mem_univ u
          simp only [hCoreSide, Finset.mem_filter, Finset.mem_univ,
            true_and] at hu'
          exact hu hu'
    -- an interior vertex whose side differs from the (uniform) core side
    have hInterior : ∃ (edge : Fin p) (offset : Fin (spec.length edge - 1)),
        (spec.interiorVertex edge offset ∈ A) ≠
          (spec.coreVertex (spec.core.tail edge) ∈ A) ∧
        (spec.interiorVertex edge offset ∈ A) ≠
          (spec.coreVertex (spec.core.head edge) ∈ A) := by
      obtain ⟨a, ha⟩ := hNonempty
      have hExistsOut : ∃ b : spec.Vertex, b ∉ A := by
        by_contra hAll
        push Not at hAll
        exact hProper (Finset.eq_univ_iff_forall.mpr hAll)
      obtain ⟨b, hb⟩ := hExistsOut
      -- one of `a`, `b` is an interior vertex disagreeing with the core side
      have hCase : ∀ z : spec.Vertex, (z ∈ A) ≠
            (spec.coreVertex (⟨0, spec.core_nonempty⟩ : Fin n) ∈ A) →
          ∃ (edge : Fin p) (offset : Fin (spec.length edge - 1)),
            (spec.interiorVertex edge offset ∈ A) ≠
              (spec.coreVertex (spec.core.tail edge) ∈ A) ∧
            (spec.interiorVertex edge offset ∈ A) ≠
              (spec.coreVertex (spec.core.head edge) ∈ A) := by
        intro z hz
        rcases z with vertex | interior
        · exact absurd (propext (hUniform vertex ⟨0, spec.core_nonempty⟩)) hz
        · obtain ⟨edge, offset⟩ := interior
          refine ⟨edge, offset, ?_, ?_⟩
          · rw [propext (hUniform (spec.core.tail edge)
              ⟨0, spec.core_nonempty⟩)]
            exact hz
          · rw [propext (hUniform (spec.core.head edge)
              ⟨0, spec.core_nonempty⟩)]
            exact hz
      by_cases hBase : spec.coreVertex (⟨0, spec.core_nonempty⟩ : Fin n) ∈ A
      · refine hCase b ?_
        simp [hb, hBase]
      · refine hCase a ?_
        simp [ha, hBase]
    obtain ⟨edge, offset, hTailDiff, hHeadDiff⟩ := hInterior
    have hIsLt := offset.isLt
    have hLengthPos := spec.length_pos edge
    have hMid : spec.pathVertex edge (spec.interiorPosition edge offset) =
        spec.interiorVertex edge offset :=
      spec.pathVertex_interiorPosition edge offset
    have hTail : spec.pathVertex edge (spec.zeroPosition edge) =
        spec.coreVertex (spec.core.tail edge) := by
      simpa [zeroPosition] using spec.pathVertex_zero edge
    have hHead : spec.pathVertex edge (spec.lastPosition edge) =
        spec.coreVertex (spec.core.head edge) := by
      simp [lastPosition]
    have hLtFirst : (spec.zeroPosition edge).val <
        (spec.interiorPosition edge offset).val := by
      simp [zeroPosition, interiorPosition]
    have hLtSecond : (spec.interiorPosition edge offset).val <
        (spec.lastPosition edge).val := by
      simp only [interiorPosition, lastPosition]
      omega
    have hFirstDiff :
        (spec.pathVertex edge (spec.zeroPosition edge) ∈ A ∧
          spec.pathVertex edge (spec.interiorPosition edge offset) ∉ A) ∨
        (spec.pathVertex edge (spec.zeroPosition edge) ∉ A ∧
          spec.pathVertex edge (spec.interiorPosition edge offset) ∈ A) := by
      rw [hTail, hMid]
      by_cases hInt : spec.interiorVertex edge offset ∈ A
      · have : spec.coreVertex (spec.core.tail edge) ∉ A := by
          intro hc
          exact hTailDiff (by simp [hInt, hc])
        exact Or.inr ⟨this, hInt⟩
      · have : spec.coreVertex (spec.core.tail edge) ∈ A := by
          by_contra hc
          exact hTailDiff (by simp [hInt, hc])
        exact Or.inl ⟨this, hInt⟩
    have hSecondDiff :
        (spec.pathVertex edge (spec.interiorPosition edge offset) ∈ A ∧
          spec.pathVertex edge (spec.lastPosition edge) ∉ A) ∨
        (spec.pathVertex edge (spec.interiorPosition edge offset) ∉ A ∧
          spec.pathVertex edge (spec.lastPosition edge) ∈ A) := by
      rw [hHead, hMid]
      by_cases hInt : spec.interiorVertex edge offset ∈ A
      · have : spec.coreVertex (spec.core.head edge) ∉ A := by
          intro hc
          exact hHeadDiff (by simp [hInt, hc])
        exact Or.inl ⟨hInt, this⟩
      · have : spec.coreVertex (spec.core.head edge) ∈ A := by
          by_contra hc
          exact hHeadDiff (by simp [hInt, hc])
        exact Or.inr ⟨hInt, this⟩
    obtain ⟨k₁, _, hk₁Lt, hk₁⟩ :=
      spec.exists_crossingStep_between A edge _ _ hLtFirst hFirstDiff
    obtain ⟨k₂, hk₂Ge, _, hk₂⟩ :=
      spec.exists_crossingStep_between A edge _ _ hLtSecond hSecondDiff
    refine hTwoCard ⟨edge, k₁⟩ ⟨edge, k₂⟩ ?_ hk₁ hk₂
    intro hEq
    have hVals : k₁.val = k₂.val :=
      congrArg (fun s : spec.Step => s.2.val) hEq
    simp only [interiorPosition] at hk₁Lt hk₂Ge
    omega

end SubdivisionGraph.Spec

end Utilities.Certificate
