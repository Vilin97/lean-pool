/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotential
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.RankOne
public import Mathlib.Tactic

/-!
# Subdivision graphs from finite edge slots

This module turns a loopless finite core with positive integral edge lengths
into an actual `CFGraph`.  Edge slots, rather than endpoint pairs, are the
primary objects.  Consequently parallel core edges remain distinct throughout
the construction.

For an edge slot of length `L`, its interior vertices are indexed by
`Fin (L - 1)`: index `j` denotes offset `j + 1` from the tail.  Its unit steps
are indexed by `Fin L`.  The graph edge multiset is the image of the finite
type of all unit steps, so every unit edge is emitted exactly once even when
several emitted pairs coincide.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph

open Finset Multiset

open ExplicitPotential

/-- Complete input data for subdividing a finite loopless core. -/
structure Spec (n p : ℕ) where
  /-- The finite nonempty loopless core whose slots are subdivided. -/
  core : ExplicitPotential.Core n p
  /-- The positive number of unit edges replacing each core slot. -/
  length : Fin p → ℕ
  core_nonempty : 0 < n
  core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge
  length_pos : ∀ edge : Fin p, 0 < length edge

/-- Package a positive length assignment on a fixed finite loopless core as a
subdivision specification, without repeating the structure fields. -/
def Spec.ofCore {n p : ℕ} (core : ExplicitPotential.Core n p)
    (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (length : Fin p → ℕ) (length_pos : ∀ edge, 0 < length edge) :
    Spec n p where
  core := core
  length := length
  core_nonempty := core_nonempty
  core_loopless := core_loopless
  length_pos := length_pos

variable {n p : ℕ} (spec : Spec n p)

namespace Spec

/-- An interior vertex remembers its edge slot.  Its `Fin (L - 1)` coordinate
`j` represents path offset `j + 1`. -/
abbrev Interior := Σ edge : Fin p, Fin (spec.length edge - 1)

/-- Vertices of the subdivision are core vertices together with the disjoint
interiors of all edge slots. -/
abbrev Vertex := Fin n ⊕ spec.Interior

/-- A unit step remembers its edge slot and its zero-based step offset. -/
abbrev Step := Σ edge : Fin p, Fin (spec.length edge)

/-- Injection of a core vertex into the subdivision. -/
def coreVertex (vertex : Fin n) : spec.Vertex :=
  Sum.inl vertex

/-- Injection of an edge-interior coordinate into the subdivision. -/
def interiorVertex (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.Vertex :=
  Sum.inr ⟨edge, offset⟩

/-- The left endpoint of a unit step. -/
def stepLeft (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.Vertex :=
  if hzero : offset.val = 0 then
    spec.coreVertex (spec.core.tail edge)
  else
    spec.interiorVertex edge
      ⟨offset.val - 1, by
        have hoffset := offset.isLt
        omega⟩

/-- The right endpoint of a unit step. -/
def stepRight (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.Vertex :=
  if hlast : offset.val + 1 = spec.length edge then
    spec.coreVertex (spec.core.head edge)
  else
    spec.interiorVertex edge
      ⟨offset.val, by
        have hoffset := offset.isLt
        omega⟩

/-- The ordered pair emitted by one unit step.  Its orientation is only a
storage convention; `numEdges` treats it as undirected. -/
def unitEdge (step : spec.Step) : spec.Vertex × spec.Vertex :=
  (spec.stepLeft step.1 step.2, spec.stepRight step.1 step.2)

@[simp] theorem stepLeft_zero (edge : Fin p) :
    spec.stepLeft edge ⟨0, spec.length_pos edge⟩ =
      spec.coreVertex (spec.core.tail edge) := by
  simp [stepLeft]

@[simp] theorem stepRight_last (edge : Fin p) :
    spec.stepRight edge
        ⟨spec.length edge - 1, by
          have hpos := spec.length_pos edge
          omega⟩ =
      spec.coreVertex (spec.core.head edge) := by
  have hpos := spec.length_pos edge
  have hlast : spec.length edge - 1 + 1 = spec.length edge := by omega
  rw [stepRight, dite_eq_left hlast]

@[simp] theorem stepRight_before_last
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.stepRight edge
        ⟨offset.val, by have := offset.isLt; omega⟩ =
      spec.interiorVertex edge offset := by
  simp only [stepRight]
  rw [dite_eq_right (by have := offset.isLt; omega)]

@[simp] theorem stepLeft_after_zero
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.stepLeft edge
        ⟨offset.val + 1, by have := offset.isLt; omega⟩ =
      spec.interiorVertex edge offset := by
  simp only [stepLeft]
  rw [dite_eq_right (by omega)]
  congr 3

/-- Consecutive path positions are always distinct.  In the length-one case
this is exactly the looplessness assumption on the core slot. -/
theorem stepLeft_ne_stepRight (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    spec.stepLeft edge offset ≠ spec.stepRight edge offset := by
  unfold stepLeft stepRight
  split_ifs with hzero hlast
  · intro heq
    have hEnds : spec.core.tail edge = spec.core.head edge :=
      Sum.inl.inj heq
    exact spec.core_loopless edge hEnds
  · simp [coreVertex, interiorVertex]
  · simp [coreVertex, interiorVertex]
  · intro heq
    have hSigma :
        (⟨edge, ⟨offset.val - 1, by
          have := offset.isLt
          omega⟩⟩ : spec.Interior) =
        ⟨edge, ⟨offset.val, by
          have := offset.isLt
          omega⟩⟩ :=
      Sum.inr.inj heq
    have hOffsets : offset.val - 1 = offset.val := by
      exact congrArg (fun x : spec.Interior => x.2.val) hSigma
    omega

/-- The subdivided graph.  The underlying multiset is the image of all unit
steps, retaining multiplicity when distinct slots emit the same pair. -/
abbrev graph (spec : Spec n p) : CFGraph where
  V := spec.Vertex
  instNonempty := ⟨spec.coreVertex ⟨0, spec.core_nonempty⟩⟩
  edges := (Finset.univ : Finset spec.Step).val.map spec.unitEdge
  loopless := by
    intro vertex hmem
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
      at hmem
    obtain ⟨step, hstep⟩ := hmem
    rcases step with ⟨edge, offset⟩
    simp only [unitEdge, Prod.mk.injEq] at hstep
    exact spec.stepLeft_ne_stepRight edge offset (hstep.1.trans hstep.2.symm)

@[simp] theorem graph_edges :
    spec.graph.edges =
      (Finset.univ : Finset spec.Step).val.map spec.unitEdge := rfl

/-- Exact edge count: subdividing a slot of length `L` emits `L` edges. -/
@[simp] theorem card_edges :
    spec.graph.edges.card = ∑ edge : Fin p, spec.length edge := by
  simp [graph, Fintype.card_sigma]

/-- Exact vertex count: each slot of length `L` contributes `L - 1`
interior vertices. -/
@[simp] theorem card_vertices :
    Fintype.card spec.graph.V =
      n + ∑ edge : Fin p, (spec.length edge - 1) := by
  simp [graph, Vertex, Interior, Fintype.card_sigma]

/-- Subdivision preserves cyclomatic genus.  The right side is the genus of
the abstract core with `p` edge slots and `n` vertices. -/
@[simp] theorem genus_graph :
    genus spec.graph = (p : ℤ) - (n : ℤ) + 1 := by
  have hTerm (edge : Fin p) : spec.length edge - 1 + 1 = spec.length edge := by
    have := spec.length_pos edge
    omega
  have hSum :
      (∑ edge : Fin p, (spec.length edge - 1)) + p =
        ∑ edge : Fin p, spec.length edge := by
    calc
      (∑ edge : Fin p, (spec.length edge - 1)) + p =
          ∑ edge : Fin p, ((spec.length edge - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ edge : Fin p, spec.length edge := by
        apply Finset.sum_congr rfl
        intro edge _hedge
        exact hTerm edge
  unfold genus
  rw [spec.card_edges, spec.card_vertices]
  have hSumInt :
      ((∑ edge : Fin p, (spec.length edge - 1) : ℕ) : ℤ) + (p : ℤ) =
        ((∑ edge : Fin p, spec.length edge : ℕ) : ℤ) := by
    exact_mod_cast hSum
  push_cast at hSumInt ⊢
  omega

/-- Exact multiplicity formula, expressed directly as a finite filter of unit
steps.  This is often the most convenient interface for executable proofs. -/
theorem num_edges_eq_card_filter_steps (x y : spec.Vertex) :
    numEdges spec.graph x y =
      ((Finset.univ : Finset spec.Step).filter fun step =>
        spec.unitEdge step = (x, y) ∨ spec.unitEdge step = (y, x)).card := by
  unfold numEdges
  change Multiset.card
      (((Finset.univ : Finset spec.Step).val.map spec.unitEdge).filter
        (fun edge => edge = (x, y) ∨ edge = (y, x))) = _
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Expanded indicator-sum form of the exact edge multiplicity. -/
theorem num_edges_eq_sum_steps (x y : spec.Vertex) :
    numEdges spec.graph x y =
      ∑ step : spec.Step,
        if spec.unitEdge step = (x, y) ∨
            spec.unitEdge step = (y, x) then 1 else 0 := by
  rw [spec.num_edges_eq_card_filter_steps]
  simpa only [Finset.sum_filter, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.mem_univ, ite_true] using
    (Finset.card_filter
      (fun step : spec.Step =>
        spec.unitEdge step = (x, y) ∨ spec.unitEdge step = (y, x))
      Finset.univ)

/-- Positive multiplicity is equivalent to the existence of an emitted unit
step with the requested unordered endpoints. -/
theorem num_edges_pos_iff (x y : spec.Vertex) :
    0 < numEdges spec.graph x y ↔
      ∃ step : spec.Step,
        spec.unitEdge step = (x, y) ∨ spec.unitEdge step = (y, x) := by
  rw [spec.num_edges_eq_card_filter_steps, Finset.card_pos]
  constructor
  · rintro ⟨step, hstep⟩
    exact ⟨step, (Finset.mem_filter.mp hstep).2⟩
  · rintro ⟨step, hstep⟩
    exact ⟨step, Finset.mem_filter.mpr ⟨Finset.mem_univ step, hstep⟩⟩

/-- Every emitted unit step really is present, with multiplicity at least
one.  Parallel slots may make the inequality strict. -/
theorem unitStep_num_edges_pos (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    0 < numEdges spec.graph (spec.stepLeft edge offset)
      (spec.stepRight edge offset) := by
  rw [spec.num_edges_pos_iff]
  exact ⟨⟨edge, offset⟩, Or.inl rfl⟩

/-- The neighbor of a core tail on its first unit step. -/
def tailNeighbor (edge : Fin p) : spec.Vertex :=
  spec.stepRight edge ⟨0, spec.length_pos edge⟩

/-- The neighbor of a core head on its final unit step. -/
def headNeighbor (edge : Fin p) : spec.Vertex :=
  spec.stepLeft edge
    ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩

theorem tail_num_edges_pos (edge : Fin p) :
    0 < numEdges spec.graph
      (spec.coreVertex (spec.core.tail edge)) (spec.tailNeighbor edge) := by
  simpa [tailNeighbor] using
    spec.unitStep_num_edges_pos edge ⟨0, spec.length_pos edge⟩

theorem head_num_edges_pos (edge : Fin p) :
    0 < numEdges spec.graph
      (spec.coreVertex (spec.core.head edge)) (spec.headNeighbor edge) := by
  rw [num_edges_symmetric]
  simpa [headNeighbor] using
    spec.unitStep_num_edges_pos edge
      ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩

/-- The step immediately before the interior vertex with coordinate `j`. -/
def previousStep (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    Fin (spec.length edge) :=
  ⟨offset.val, by have := offset.isLt; omega⟩

/-- The step immediately after the interior vertex with coordinate `j`. -/
def nextStep (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    Fin (spec.length edge) :=
  ⟨offset.val + 1, by have := offset.isLt; omega⟩

/-- The preceding path vertex of an interior vertex. -/
def previousVertex (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) : spec.Vertex :=
  spec.stepLeft edge (spec.previousStep edge offset)

/-- The following path vertex of an interior vertex. -/
def nextVertex (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) : spec.Vertex :=
  spec.stepRight edge (spec.nextStep edge offset)

@[simp] theorem stepRight_previousStep (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.stepRight edge (spec.previousStep edge offset) =
      spec.interiorVertex edge offset := by
  exact spec.stepRight_before_last edge offset

@[simp] theorem stepLeft_nextStep (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.stepLeft edge (spec.nextStep edge offset) =
      spec.interiorVertex edge offset := by
  exact spec.stepLeft_after_zero edge offset

/-- An interior vertex is the right endpoint of exactly its preceding unit
step.  Packaging the edge and offset as one sigma value avoids any transport
ambiguity in the dependent indices. -/
theorem stepRight_eq_interiorVertex_iff (step : spec.Step)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.stepRight step.1 step.2 = spec.interiorVertex edge offset ↔
      step = ⟨edge, spec.previousStep edge offset⟩ := by
  rcases step with ⟨otherEdge, otherOffset⟩
  constructor
  · intro hEqual
    unfold stepRight at hEqual
    by_cases hlast : otherOffset.val + 1 = spec.length otherEdge
    · rw [dite_eq_left hlast] at hEqual
      simp [coreVertex, interiorVertex] at hEqual
    · rw [dite_eq_right hlast] at hEqual
      have hSigma :
          (⟨otherEdge, ⟨otherOffset.val, by
            have := otherOffset.isLt
            omega⟩⟩ : spec.Interior) = ⟨edge, offset⟩ :=
        Sum.inr.inj hEqual
      have hEdge : otherEdge = edge :=
        congrArg Sigma.fst hSigma
      subst otherEdge
      congr 1
      apply Fin.ext
      exact congrArg (fun interior : spec.Interior => interior.2.val) hSigma
  · intro hStep
    cases hStep
    exact spec.stepRight_previousStep edge offset

/-- An interior vertex is the left endpoint of exactly its following unit
step. -/
theorem stepLeft_eq_interiorVertex_iff (step : spec.Step)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset ↔
      step = ⟨edge, spec.nextStep edge offset⟩ := by
  rcases step with ⟨otherEdge, otherOffset⟩
  constructor
  · intro hEqual
    unfold stepLeft at hEqual
    by_cases hzero : otherOffset.val = 0
    · rw [dite_eq_left hzero] at hEqual
      simp [coreVertex, interiorVertex] at hEqual
    · rw [dite_eq_right hzero] at hEqual
      have hSigma :
          (⟨otherEdge, ⟨otherOffset.val - 1, by
            have := otherOffset.isLt
            omega⟩⟩ : spec.Interior) = ⟨edge, offset⟩ :=
        Sum.inr.inj hEqual
      have hEdge : otherEdge = edge :=
        congrArg Sigma.fst hSigma
      subst otherEdge
      have hValue : otherOffset.val - 1 = offset.val :=
        congrArg (fun interior : spec.Interior => interior.2.val) hSigma
      congr 1
      apply Fin.ext
      change otherOffset.val = offset.val + 1
      omega
  · intro hStep
    cases hStep
    exact spec.stepLeft_nextStep edge offset

theorem previous_num_edges_pos (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    0 < numEdges spec.graph (spec.interiorVertex edge offset)
      (spec.previousVertex edge offset) := by
  rw [num_edges_symmetric]
  simpa [previousVertex] using
    spec.unitStep_num_edges_pos edge (spec.previousStep edge offset)

theorem next_num_edges_pos (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    0 < numEdges spec.graph (spec.interiorVertex edge offset)
      (spec.nextVertex edge offset) := by
  simpa [nextVertex] using
    spec.unitStep_num_edges_pos edge (spec.nextStep edge offset)

/-- A principal-divisor coefficient is the sum of the contributions of the
individual emitted unit steps incident to the vertex. -/
theorem prin_eq_sum_steps (script : firingScript spec.graph)
    (vertex : spec.Vertex) :
    prin spec.graph script vertex =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 = vertex then
            script (spec.stepRight step.1 step.2) - script vertex else 0) +
          (if spec.stepRight step.1 step.2 = vertex then
            script (spec.stepLeft step.1 step.2) - script vertex else 0)) := by
  change (∑ neighbor : spec.graph.V,
    (script neighbor - script vertex) *
      (numEdges spec.graph vertex neighbor : ℤ)) = _
  simp_rw [spec.num_edges_eq_sum_steps]
  push_cast
  simp_rw [mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro step _hstep
  rcases step with ⟨edge, offset⟩
  have hne := spec.stepLeft_ne_stepRight edge offset
  by_cases hleft : spec.stepLeft edge offset = vertex
  · subst vertex
    simp only [unitEdge, Prod.mk.injEq]
    simp [hne.symm]
  · by_cases hright : spec.stepRight edge offset = vertex
    · subst vertex
      simp only [unitEdge, Prod.mk.injEq]
      simp [hne]
    · simp only [unitEdge, Prod.mk.injEq]
      simp [hleft, hright]

/-- A principal-divisor coefficient depends only on the oriented difference
of the firing script along each emitted unit step.  This form is convenient
for scripts described by slopes rather than by vertex values. -/
theorem prin_eq_sum_step_differences (script : firingScript spec.graph)
    (vertex : spec.Vertex) :
    prin spec.graph script vertex =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 = vertex then
            script (spec.stepRight step.1 step.2) -
              script (spec.stepLeft step.1 step.2) else 0) +
          (if spec.stepRight step.1 step.2 = vertex then
            -(script (spec.stepRight step.1 step.2) -
              script (spec.stepLeft step.1 step.2)) else 0)) := by
  classical
  rw [spec.prin_eq_sum_steps]
  apply Finset.sum_congr rfl
  intro step _hstep
  have hDistinct := spec.stepLeft_ne_stepRight step.1 step.2
  by_cases hLeft : spec.stepLeft step.1 step.2 = vertex
  · have hRight : spec.stepRight step.1 step.2 ≠ vertex := by
      intro h
      apply hDistinct
      exact hLeft.trans h.symm
    subst vertex
    simp [hRight]
  · by_cases hRight : spec.stepRight step.1 step.2 = vertex
    · subst vertex
      simp [hLeft]
    · simp [hLeft, hRight]

/-! ## Canonical integer interpolation on the constructed graph -/

/-- Rise of a core potential along an oriented edge slot. -/
def coreRise (potential : Fin n → ℤ) (edge : Fin p) : ℤ :=
  potential (spec.core.head edge) - potential (spec.core.tail edge)

/-- Value at a numerical path offset, normalized by the tail potential. -/
def pathValue (potential : Fin n → ℤ) (edge : Fin p)
    (offset : ℕ) : ℤ :=
  potential (spec.core.tail edge) +
    SubdivisionArithmetic.potential (spec.length edge)
      (spec.coreRise potential edge) offset

/-- Extend an integral core potential over every subdivided slot by the
canonical convex interpolation from `SubdivisionArithmetic`. -/
def interpolatedScript (potential : Fin n → ℤ) : firingScript spec.graph
  | Sum.inl vertex => potential vertex
  | Sum.inr interior =>
      spec.pathValue potential interior.1 (interior.2.val + 1)

@[simp] theorem interpolatedScript_core (potential : Fin n → ℤ)
    (vertex : Fin n) :
    spec.interpolatedScript potential (spec.coreVertex vertex) =
      potential vertex := rfl

@[simp] theorem interpolatedScript_interior (potential : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.interpolatedScript potential (spec.interiorVertex edge offset) =
      spec.pathValue potential edge (offset.val + 1) := rfl

/-- On the left endpoint of step `i`, the interpolated script has path value
at offset `i`. -/
theorem interpolatedScript_stepLeft (potential : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.interpolatedScript potential (spec.stepLeft edge offset) =
      spec.pathValue potential edge offset.val := by
  unfold stepLeft
  by_cases hzero : offset.val = 0
  · rw [dite_eq_left hzero]
    change potential (spec.core.tail edge) =
      spec.pathValue potential edge offset.val
    rw [hzero]
    simp [pathValue, SubdivisionArithmetic.potential_zero,
      spec.length_pos edge]
  · rw [dite_eq_right hzero]
    change spec.pathValue potential edge ((offset.val - 1) + 1) =
      spec.pathValue potential edge offset.val
    congr 2
    omega

/-- On the right endpoint of step `i`, the interpolated script has path value
at offset `i + 1`. -/
theorem interpolatedScript_stepRight (potential : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.interpolatedScript potential (spec.stepRight edge offset) =
      spec.pathValue potential edge (offset.val + 1) := by
  unfold stepRight
  by_cases hlast : offset.val + 1 = spec.length edge
  · rw [dite_eq_left hlast]
    change potential (spec.core.head edge) =
      spec.pathValue potential edge (offset.val + 1)
    unfold pathValue
    rw [hlast, SubdivisionArithmetic.potential_length
      (spec.coreRise potential edge) (spec.length_pos edge)]
    unfold coreRise
    ring
  · rw [dite_eq_right hlast]
    rfl

/-- The script difference across a unit edge is exactly the arithmetic
interpolator's step slope. -/
theorem interpolatedScript_stepDifference (potential : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.interpolatedScript potential (spec.stepRight edge offset) -
        spec.interpolatedScript potential (spec.stepLeft edge offset) =
      SubdivisionArithmetic.step (spec.length edge)
        (spec.coreRise potential edge) offset.val := by
  rw [spec.interpolatedScript_stepRight,
    spec.interpolatedScript_stepLeft]
  simp only [pathValue, SubdivisionArithmetic.step]
  ring

/-- Exact principal divisor of the interpolated script, written entirely in
terms of the certified unit-step slopes.  This is the direct bridge from the
arithmetic certificate to the graph Laplacian. -/
theorem prin_interpolatedScript_eq_sum_steps
    (potential : Fin n → ℤ) (vertex : spec.Vertex) :
    prin spec.graph (spec.interpolatedScript potential) vertex =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 = vertex then
            SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0) +
          (if spec.stepRight step.1 step.2 = vertex then
            -SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0)) := by
  rw [spec.prin_eq_sum_steps]
  apply Finset.sum_congr rfl
  intro step _hstep
  rcases step with ⟨edge, offset⟩
  have hDifference :=
    spec.interpolatedScript_stepDifference potential edge offset
  by_cases hleft : spec.stepLeft edge offset = vertex <;>
    by_cases hright : spec.stepRight edge offset = vertex
  · exfalso
    exact spec.stepLeft_ne_stepRight edge offset (hleft.trans hright.symm)
  · subst vertex
    simp only [↓reduceIte, hright, add_zero]
    exact hDifference
  · subst vertex
    simp only [hleft, ↓reduceIte, zero_add]
    omega
  · simp [hleft, hright]

/-- Core-vertex specialization of the exact interpolated Laplacian formula. -/
theorem prin_interpolatedScript_core (potential : Fin n → ℤ)
    (vertex : Fin n) :
    prin spec.graph (spec.interpolatedScript potential)
        (spec.coreVertex vertex) =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 = spec.coreVertex vertex then
            SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0) +
          (if spec.stepRight step.1 step.2 = spec.coreVertex vertex then
            -SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0)) :=
  spec.prin_interpolatedScript_eq_sum_steps potential (spec.coreVertex vertex)

/-- Interior-vertex specialization of the exact interpolated Laplacian
formula. -/
theorem prin_interpolatedScript_interior (potential : Fin n → ℤ)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (spec.interpolatedScript potential)
        (spec.interiorVertex edge offset) =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 =
              spec.interiorVertex edge offset then
            SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0) +
          (if spec.stepRight step.1 step.2 =
              spec.interiorVertex edge offset then
            -SubdivisionArithmetic.step (spec.length step.1)
              (spec.coreRise potential step.1) step.2.val else 0)) :=
  spec.prin_interpolatedScript_eq_sum_steps potential
    (spec.interiorVertex edge offset)

end Spec

end Utilities.Certificate.SubdivisionGraph
