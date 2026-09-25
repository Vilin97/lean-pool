/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Segments.AtanasovRanganathanConfigurations

/-!
# Reflection on one subdivision segment

The firing potential on a path starts at zero, has slope `-1` until the first
of a position and its mirror image, is constant between them, and has slope
`+1` after the second.  It therefore returns to zero at the other endpoint,
so extending it by zero away from the chosen subdivision slot creates no
unwanted firing across the rest of the core.
-/

@[expose] public section

namespace Utilities

namespace SegmentReflection

open Finset
open Certificate
open Certificate.SubdivisionGraph

/-- The path position symmetric to `position` under reversal of the slot. -/
def symmetricPosition {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (edge : Fin p) (position : spec.PathPosition edge) :
    spec.PathPosition edge :=
  ⟨spec.length edge - position.val, by
    have := position.isLt
    omega⟩

@[simp] theorem symmetricPosition_val {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position : spec.PathPosition edge) :
    (symmetricPosition spec edge position).val =
      spec.length edge - position.val := rfl

/-- The integral plateau potential at numerical path offset `i`. -/
def value (length position i : ℕ) : ℤ :=
  let low := min position (length - position)
  let high := max position (length - position)
  if i ≤ low then -(i : ℤ)
  else if i ≤ high then -(low : ℤ)
  else (i : ℤ) - (length : ℤ)

/-- The oriented slope after numerical path position `i`. -/
def slope (length position i : ℕ) : ℤ :=
  if i < min position (length - position) then -1
  else if max position (length - position) ≤ i then 1
  else 0

theorem min_add_max_reflection {length position : ℕ}
    (hPosition : position ≤ length) :
    min position (length - position) +
      max position (length - position) = length := by
  rw [min_add_max]
  omega

@[simp] theorem value_zero (length position : ℕ) :
    value length position 0 = 0 := by
  simp [value]

theorem value_length {length position : ℕ}
    (hPosition : position ≤ length) :
    value length position length = 0 := by
  have hSum := min_add_max_reflection hPosition
  simp only [value]
  split_ifs <;> omega

/-- Consecutive values realize the advertised three-piece slope. -/
theorem value_succ_sub_value {length position i : ℕ}
    (hPosition : position ≤ length) :
    value length position (i + 1) - value length position i =
      slope length position i := by
  have hSum := min_add_max_reflection hPosition
  simp only [value, slope]
  split_ifs <;> omega

/-- The divergence of the slope is `-1` at either endpoint and `+1` at the
chosen position and its mirror.  Coincident terms add, including the midpoint
and endpoint cases. -/
theorem slope_divergence {length position j : ℕ}
    (hLength : 0 < length) (hPosition : position ≤ length)
    (hj : j ≤ length) :
    (if j < length then slope length position j else 0) -
        (if 0 < j then slope length position (j - 1) else 0) =
      -(if j = 0 then (1 : ℤ) else 0) -
        (if j = length then (1 : ℤ) else 0) +
        (if j = position then (1 : ℤ) else 0) +
        (if j = length - position then (1 : ℤ) else 0) := by
  have hSum := min_add_max_reflection hPosition
  simp only [slope]
  split_ifs <;> omega

/-! ## The slot-supported firing script -/

/-- Extend the plateau potential by zero over every core vertex and every
other subdivision slot. -/
def script {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (edge : Fin p) (position : spec.PathPosition edge) :
    firingScript spec.graph
  | Sum.inl _vertex => 0
  | Sum.inr interior =>
      if interior.1 = edge then
        value (spec.length edge) position.val (interior.2.val + 1)
      else 0

@[simp] theorem script_core {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position : spec.PathPosition edge) (vertex : Fin n) :
    script spec edge position (spec.coreVertex vertex) = 0 := rfl

@[simp] theorem script_interior_same {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position : spec.PathPosition edge)
    (offset : Fin (spec.length edge - 1)) :
    script spec edge position (spec.interiorVertex edge offset) =
      value (spec.length edge) position.val (offset.val + 1) := by
  simp [script, SubdivisionGraph.Spec.interiorVertex]

@[simp] theorem script_interior_other {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge other : Fin p)
    (position : spec.PathPosition edge) (hOther : other ≠ edge)
    (offset : Fin (spec.length other - 1)) :
    script spec edge position (spec.interiorVertex other offset) = 0 := by
  simp [script, SubdivisionGraph.Spec.interiorVertex, hOther]

/-- Script value at the left endpoint of any emitted unit step. -/
theorem script_stepLeft {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge other : Fin p)
    (position : spec.PathPosition edge)
    (offset : Fin (spec.length other)) :
    script spec edge position (spec.stepLeft other offset) =
      if other = edge then
        value (spec.length edge) position.val offset.val else 0 := by
  by_cases hOther : other = edge
  · subst other
    rw [ite_eq_left rfl]
    unfold SubdivisionGraph.Spec.stepLeft
    by_cases hZero : offset.val = 0
    · rw [dite_eq_left hZero]
      simp [hZero]
    · rw [dite_eq_right hZero]
      rw [script_interior_same]
      change value (spec.length edge) position.val
          ((offset.val - 1) + 1) =
        value (spec.length edge) position.val offset.val
      congr 1
      omega
  · rw [ite_eq_right hOther]
    unfold SubdivisionGraph.Spec.stepLeft
    by_cases hZero : offset.val = 0
    · rw [dite_eq_left hZero]
      rfl
    · rw [dite_eq_right hZero]
      exact script_interior_other spec edge other position hOther _

/-- Script value at the right endpoint of any emitted unit step. -/
theorem script_stepRight {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge other : Fin p)
    (position : spec.PathPosition edge)
    (offset : Fin (spec.length other)) :
    script spec edge position (spec.stepRight other offset) =
      if other = edge then
        value (spec.length edge) position.val (offset.val + 1) else 0 := by
  have hPosition : position.val ≤ spec.length edge := by
    have := position.isLt
    omega
  by_cases hOther : other = edge
  · subst other
    rw [ite_eq_left rfl]
    unfold SubdivisionGraph.Spec.stepRight
    by_cases hLast : offset.val + 1 = spec.length edge
    · rw [dite_eq_left hLast]
      rw [hLast, value_length hPosition]
      rfl
    · rw [dite_eq_right hLast]
      exact script_interior_same spec edge position _
  · rw [ite_eq_right hOther]
    unfold SubdivisionGraph.Spec.stepRight
    by_cases hLast : offset.val + 1 = spec.length other
    · rw [dite_eq_left hLast]
      rfl
    · rw [dite_eq_right hLast]
      exact script_interior_other spec edge other position hOther _

/-- The script difference along a unit step is the reflection slope on the
chosen slot and zero on every other slot. -/
theorem script_stepDifference {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge other : Fin p)
    (position : spec.PathPosition edge)
    (offset : Fin (spec.length other)) :
    script spec edge position (spec.stepRight other offset) -
        script spec edge position (spec.stepLeft other offset) =
      if other = edge then
        slope (spec.length edge) position.val offset.val else 0 := by
  rw [script_stepRight, script_stepLeft]
  by_cases hOther : other = edge
  · subst other
    simp only [ite_eq_left]
    apply value_succ_sub_value
    have := position.isLt
    omega
  · simp [hOther]

/-- The principal divisor of the slot-supported script is the divergence of
its slope along that one slot; every other emitted step contributes zero. -/
theorem prin_script_eq_slot_sum {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position : spec.PathPosition edge) (vertex : spec.Vertex) :
    prin spec.graph (script spec edge position) vertex =
      ∑ offset : Fin (spec.length edge),
        ((if spec.stepLeft edge offset = vertex then
            slope (spec.length edge) position.val offset.val else 0) +
          (if spec.stepRight edge offset = vertex then
            -slope (spec.length edge) position.val offset.val else 0)) := by
  classical
  rw [spec.prin_eq_sum_steps]
  have hTerm (step : spec.Step) :
      ((if spec.stepLeft step.1 step.2 = vertex then
          script spec edge position (spec.stepRight step.1 step.2) -
            script spec edge position vertex else 0) +
        (if spec.stepRight step.1 step.2 = vertex then
          script spec edge position (spec.stepLeft step.1 step.2) -
            script spec edge position vertex else 0)) =
      ((if spec.stepLeft step.1 step.2 = vertex then
          (if step.1 = edge then
            slope (spec.length edge) position.val step.2.val else 0) else 0) +
        (if spec.stepRight step.1 step.2 = vertex then
          -(if step.1 = edge then
            slope (spec.length edge) position.val step.2.val else 0) else 0)) := by
    let stepSlope : ℤ :=
      if step.1 = edge then
        slope (spec.length edge) position.val step.2.val else 0
    have hDifference :
        script spec edge position (spec.stepRight step.1 step.2) -
            script spec edge position (spec.stepLeft step.1 step.2) =
          stepSlope := by
      dsimp [stepSlope]
      exact script_stepDifference spec edge step.1 position step.2
    have hDistinct := spec.stepLeft_ne_stepRight step.1 step.2
    by_cases hLeft : spec.stepLeft step.1 step.2 = vertex
    · have hRight : spec.stepRight step.1 step.2 ≠ vertex := by
        intro h
        apply hDistinct
        exact hLeft.trans h.symm
      subst vertex
      simp only [hRight, ite_false, ite_true, add_zero]
      exact hDifference
    · by_cases hRight : spec.stepRight step.1 step.2 = vertex
      · subst vertex
        simp only [hLeft, ite_false, ite_true, zero_add]
        omega
      · simp [hLeft, hRight]
  simp_rw [hTerm]
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single edge]
  · simp
  · intro other hOther
    simp [hOther]

/-- The principal coefficient at a vertex of the chosen path is the discrete
divergence of the two adjacent slopes. -/
theorem prin_script_pathVertex {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position probe : spec.PathPosition edge) :
    prin spec.graph (script spec edge position) (spec.pathVertex edge probe) =
      -(if probe.val = 0 then (1 : ℤ) else 0) -
        (if probe.val = spec.length edge then (1 : ℤ) else 0) +
        (if probe.val = position.val then (1 : ℤ) else 0) +
        (if probe.val = spec.length edge - position.val then (1 : ℤ) else 0) := by
  classical
  have hPosition : position.val ≤ spec.length edge := by
    have := position.isLt
    omega
  have hAt : probe.val ≤ spec.length edge := by
    have := probe.isLt
    omega
  rw [prin_script_eq_slot_sum]
  have hLeftIff (offset : Fin (spec.length edge)) :
      spec.stepLeft edge offset = spec.pathVertex edge probe ↔
        offset.val = probe.val := by
    rw [← spec.pathVertex_stepLeftPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  have hRightIff (offset : Fin (spec.length edge)) :
      spec.stepRight edge offset = spec.pathVertex edge probe ↔
        offset.val + 1 = probe.val := by
    rw [← spec.pathVertex_stepRightPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  simp_rw [hLeftIff, hRightIff]
  rw [Finset.sum_add_distrib]
  have hLeftSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val = probe.val then
          slope (spec.length edge) position.val offset.val else 0) =
      if probe.val < spec.length edge then
        slope (spec.length edge) position.val probe.val else 0 := by
    by_cases hBefore : probe.val < spec.length edge
    · let selected : Fin (spec.length edge) := ⟨probe.val, hBefore⟩
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val = probe.val then
              slope (spec.length edge) position.val offset.val else 0) =
            (if selected.val = probe.val then
              slope (spec.length edge) position.val selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [ite_eq_right]
          intro hValue
          apply hOther
          apply Fin.ext
          exact hValue
        _ = _ := by simp [selected, hBefore]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val ≠ probe.val := by
        intro hValue
        have := offset.isLt
        omega
      simp [hBefore, hNever]
  have hRightSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = probe.val then
          -slope (spec.length edge) position.val offset.val else 0) =
      if 0 < probe.val then
        -slope (spec.length edge) position.val (probe.val - 1) else 0 := by
    by_cases hPositive : 0 < probe.val
    · let selected : Fin (spec.length edge) :=
        ⟨probe.val - 1, by omega⟩
      have hSelected : selected.val + 1 = probe.val := by
        dsimp [selected]
        omega
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val + 1 = probe.val then
              -slope (spec.length edge) position.val offset.val else 0) =
            (if selected.val + 1 = probe.val then
              -slope (spec.length edge) position.val selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [ite_eq_right]
          intro hValue
          apply hOther
          apply Fin.ext
          dsimp [selected]
          omega
        _ = _ := by simp [hPositive, hSelected, selected]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val + 1 ≠ probe.val := by omega
      simp [hPositive, hNever]
  rw [hLeftSum, hRightSum]
  have hDivergence := slope_divergence
    (spec.length_pos edge) hPosition hAt
  omega

/-- On the chosen path, the numerical divergence formula is exactly the
coefficient of the desired four-chip divisor. -/
theorem prin_script_pathVertex_eq_reflectionDivisor {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position probe : spec.PathPosition edge) :
    prin spec.graph (script spec edge position) (spec.pathVertex edge probe) =
      (-(oneChip (G := spec.graph)
            (spec.coreVertex (spec.core.tail edge))) -
          oneChip (G := spec.graph) (spec.coreVertex (spec.core.head edge)) +
          oneChip (G := spec.graph) (spec.pathVertex edge position) +
          oneChip (G := spec.graph)
            (spec.pathVertex edge (symmetricPosition spec edge position)))
        (spec.pathVertex edge probe) := by
  rw [prin_script_pathVertex]
  have hTail :
      spec.pathVertex edge probe =
          spec.coreVertex (spec.core.tail edge) ↔ probe.val = 0 := by
    rw [← spec.pathVertex_zero edge]
    simpa using spec.pathVertex_eq_iff_val_eq edge probe
      ⟨0, by omega⟩
  have hHead :
      spec.pathVertex edge probe =
          spec.coreVertex (spec.core.head edge) ↔
        probe.val = spec.length edge := by
    rw [← spec.pathVertex_length edge]
    simpa using spec.pathVertex_eq_iff_val_eq edge probe
      ⟨spec.length edge, by omega⟩
  have hTarget :
      spec.pathVertex edge probe = spec.pathVertex edge position ↔
        probe.val = position.val :=
    spec.pathVertex_eq_iff_val_eq edge probe position
  have hReflected :
      spec.pathVertex edge probe =
          spec.pathVertex edge (symmetricPosition spec edge position) ↔
        probe.val = spec.length edge - position.val := by
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  simp [oneChip, hTail, hHead, hTarget, hReflected]

/-- Exact principal-divisor identity for reflection on one arbitrary
subdivision slot. -/
theorem prin_script_eq_reflectionDivisor {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (position : spec.PathPosition edge) :
    prin spec.graph (script spec edge position) =
      -(oneChip (G := spec.graph)
          (spec.coreVertex (spec.core.tail edge))) -
        oneChip (G := spec.graph) (spec.coreVertex (spec.core.head edge)) +
        oneChip (G := spec.graph) (spec.pathVertex edge position) +
        oneChip (G := spec.graph)
          (spec.pathVertex edge (symmetricPosition spec edge position)) := by
  classical
  funext vertex
  rcases vertex with coreVertex | interior
  · change prin spec.graph (script spec edge position)
        (spec.coreVertex coreVertex) = _
    by_cases hTail : coreVertex = spec.core.tail edge
    · subst coreVertex
      let endpoint : spec.PathPosition edge := ⟨0, by omega⟩
      have hPath := prin_script_pathVertex_eq_reflectionDivisor
        spec edge position endpoint
      have hEndpoint : spec.pathVertex edge endpoint =
          spec.coreVertex (spec.core.tail edge) := by
        simpa [endpoint] using spec.pathVertex_zero edge
      rw [hEndpoint] at hPath
      exact hPath
    · by_cases hHead : coreVertex = spec.core.head edge
      · subst coreVertex
        let endpoint : spec.PathPosition edge :=
          ⟨spec.length edge, by omega⟩
        have hPath := prin_script_pathVertex_eq_reflectionDivisor
          spec edge position endpoint
        have hEndpoint : spec.pathVertex edge endpoint =
            spec.coreVertex (spec.core.head edge) := by
          exact spec.pathVertex_length edge
        rw [hEndpoint] at hPath
        exact hPath
      · have hLeft (offset : Fin (spec.length edge)) :
            spec.stepLeft edge offset ≠ spec.coreVertex coreVertex := by
          intro hEqual
          have hEnds :=
            (spec.stepLeft_eq_coreVertex_iff edge offset coreVertex).mp hEqual
          exact hTail hEnds.2.symm
        have hRight (offset : Fin (spec.length edge)) :
            spec.stepRight edge offset ≠ spec.coreVertex coreVertex := by
          intro hEqual
          have hEnds :=
            (spec.stepRight_eq_coreVertex_iff edge offset coreVertex).mp hEqual
          exact hHead hEnds.2.symm
        have hPathNe (probe : spec.PathPosition edge) :
            spec.pathVertex edge probe ≠ spec.coreVertex coreVertex := by
          intro hEqual
          unfold SubdivisionGraph.Spec.pathVertex at hEqual
          split_ifs at hEqual with hZero hLast
          · exact hTail (Sum.inl.inj hEqual).symm
          · exact hHead (Sum.inl.inj hEqual).symm
          · simp [SubdivisionGraph.Spec.coreVertex,
              SubdivisionGraph.Spec.interiorVertex] at hEqual
        have hTargetNe :
            spec.coreVertex coreVertex ≠ spec.pathVertex edge position :=
          (hPathNe position).symm
        have hReflectedNe :
            spec.coreVertex coreVertex ≠
              spec.pathVertex edge (symmetricPosition spec edge position) :=
          (hPathNe (symmetricPosition spec edge position)).symm
        have hTargetNe' :
            (Sum.inl coreVertex : spec.Vertex) ≠
              spec.pathVertex edge position := hTargetNe
        have hReflectedNe' :
            (Sum.inl coreVertex : spec.Vertex) ≠
              spec.pathVertex edge (symmetricPosition spec edge position) :=
          hReflectedNe
        have hTailVertex :
            (Sum.inl coreVertex : spec.Vertex) ≠
              spec.coreVertex (spec.core.tail edge) := by
          intro hEqual
          exact hTail (Sum.inl.inj hEqual)
        have hHeadVertex :
            (Sum.inl coreVertex : spec.Vertex) ≠
              spec.coreVertex (spec.core.head edge) := by
          intro hEqual
          exact hHead (Sum.inl.inj hEqual)
        rw [prin_script_eq_slot_sum]
        simp_rw [ite_eq_right (hLeft _), ite_eq_right (hRight _)]
        simp [oneChip, hTailVertex, hHeadVertex,
          hTargetNe', hReflectedNe']
  · obtain ⟨other, offset⟩ := interior
    change prin spec.graph (script spec edge position)
      (spec.interiorVertex other offset) = _
    by_cases hOther : other = edge
    · subst other
      let probe : spec.PathPosition edge :=
        ⟨offset.val + 1, by have := offset.isLt; omega⟩
      have hProbe :
          spec.pathVertex edge probe = spec.interiorVertex edge offset := by
        unfold SubdivisionGraph.Spec.pathVertex
        rw [dite_eq_right (by dsimp [probe]; omega)]
        rw [dite_eq_right (by dsimp [probe]; have := offset.isLt; omega)]
        congr 2
      have hPath := prin_script_pathVertex_eq_reflectionDivisor
        spec edge position probe
      rw [hProbe] at hPath
      exact hPath
    · have hLeft (stepOffset : Fin (spec.length edge)) :
          spec.stepLeft edge stepOffset ≠
            spec.interiorVertex other offset := by
        intro hEqual
        have hStep :=
          (spec.stepLeft_eq_interiorVertex_iff
            ⟨edge, stepOffset⟩ other offset).mp hEqual
        have hEdges := congrArg Sigma.fst hStep
        exact hOther hEdges.symm
      have hRight (stepOffset : Fin (spec.length edge)) :
          spec.stepRight edge stepOffset ≠
            spec.interiorVertex other offset := by
        intro hEqual
        have hStep :=
          (spec.stepRight_eq_interiorVertex_iff
            ⟨edge, stepOffset⟩ other offset).mp hEqual
        have hEdges := congrArg Sigma.fst hStep
        exact hOther hEdges.symm
      have hPathNe (probe : spec.PathPosition edge) :
          spec.pathVertex edge probe ≠
            spec.interiorVertex other offset := by
        intro hEqual
        unfold SubdivisionGraph.Spec.pathVertex at hEqual
        split_ifs at hEqual with hZero hLast
        · simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at hEqual
        · simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at hEqual
        · have hSigma := Sum.inr.inj hEqual
          have hEdges := congrArg Sigma.fst hSigma
          exact hOther hEdges.symm
      have hTargetNe :
          spec.interiorVertex other offset ≠ spec.pathVertex edge position :=
        (hPathNe position).symm
      have hReflectedNe :
          spec.interiorVertex other offset ≠
            spec.pathVertex edge (symmetricPosition spec edge position) :=
        (hPathNe (symmetricPosition spec edge position)).symm
      have hTargetNe' :
          (Sum.inr ⟨other, offset⟩ : spec.Vertex) ≠
            spec.pathVertex edge position := hTargetNe
      have hReflectedNe' :
          (Sum.inr ⟨other, offset⟩ : spec.Vertex) ≠
            spec.pathVertex edge (symmetricPosition spec edge position) :=
        hReflectedNe
      rw [prin_script_eq_slot_sum]
      simp_rw [ite_eq_right (hLeft _), ite_eq_right (hRight _)]
      simp [oneChip, SubdivisionGraph.Spec.coreVertex,
        hTargetNe', hReflectedNe']

/-! ## Public reflection and reachability interfaces -/

/-- Every named position on every subdivision slot satisfies the abstract
segment-reflection obligation. -/
theorem reflectsTo {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (edge : Fin p) (position : spec.PathPosition edge) :
    AtanasovRanganathan.Configurations.SegmentConfiguration.ReflectsTo
      spec edge position := by
  refine ⟨spec.pathVertex edge (symmetricPosition spec edge position),
    script spec edge position, ?_⟩
  exact prin_script_eq_reflectionDivisor spec edge position

/-- Endpoint chips on a slot reach every named path position. -/
theorem reaches_pathPosition {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (D : CFDiv spec.graph)
    (edge : Fin p) (position : spec.PathPosition edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge))) :
    Certificate.StrongSeparator.Reaches spec.graph D
      (spec.pathVertex edge position) := by
  exact AtanasovRanganathan.Configurations.SegmentConfiguration.reaches_pathPosition
    spec D edge position hEffective hTail hHead
      (reflectsTo spec edge position)

/-- `min(a,b)` specialization with the reflection obligation discharged. -/
theorem reaches_minLengthPosition {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (D : CFDiv spec.graph)
    (edge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge))) :
    Certificate.StrongSeparator.Reaches spec.graph D
      (spec.pathVertex edge
        (spec.minLengthPosition edge leftLength rightLength hBound)) := by
  exact reaches_pathPosition spec D edge
    (spec.minLengthPosition edge leftLength rightLength hBound)
    hEffective hTail hHead

/-- Truncated-difference specialization with the reflection obligation
discharged. -/
theorem reaches_differencePosition {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p) (D : CFDiv spec.graph)
    (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge))) :
    Certificate.StrongSeparator.Reaches spec.graph D
      (spec.pathVertex edge
        (spec.differencePosition edge minuend subtrahend hBound)) := by
  exact reaches_pathPosition spec D edge
    (spec.differencePosition edge minuend subtrahend hBound)
    hEffective hTail hHead

end SegmentReflection

end Utilities
