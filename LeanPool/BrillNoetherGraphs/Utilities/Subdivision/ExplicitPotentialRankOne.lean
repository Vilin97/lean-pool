/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
public import Mathlib.Tactic

/-!
# From explicit subdivision potentials to rank one

`ExplicitPotential.Certificate` checks the arithmetic data attached to one
affine length cone.  This file assembles those data on the concrete
subdivision graph from `SubdivisionGraph`.

The checked potentials make the degree-three divisor reach every *core*
vertex.  The final theorem deliberately takes a
`StrongSeparatorCertificate` for the embedded core as a hypothesis: the
sound strong-separator theorem then promotes core reachability to rank one.
The remaining graph-theoretic input is the uniform statement that the core
vertices form a strong separator in a subdivision.
-/

@[expose] public section

-- `Certificate` is a structure inside a namespace already ending in `Certificate`;
-- renaming either would ripple through every consumer.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate

open Finset

variable {m n p : ℕ}

/-! ## Exact Laplacian formulas on a subdivision -/

namespace SubdivisionGraph.Spec

variable (spec : SubdivisionGraph.Spec n p)

/-- A unit step starts at a core vertex exactly when it is the first step of
its edge slot and that slot has the requested tail. -/
theorem stepLeft_eq_coreVertex_iff (edge : Fin p)
    (offset : Fin (spec.length edge)) (vertex : Fin n) :
    spec.stepLeft edge offset = spec.coreVertex vertex ↔
      offset.val = 0 ∧ spec.core.tail edge = vertex := by
  unfold stepLeft
  by_cases hzero : offset.val = 0
  · rw [dite_eq_left hzero]
    simp [hzero, coreVertex]
  · rw [dite_eq_right hzero]
    simp [hzero, coreVertex, interiorVertex]

/-- A unit step ends at a core vertex exactly when it is the final step of
its edge slot and that slot has the requested head. -/
theorem stepRight_eq_coreVertex_iff (edge : Fin p)
    (offset : Fin (spec.length edge)) (vertex : Fin n) :
    spec.stepRight edge offset = spec.coreVertex vertex ↔
      offset.val + 1 = spec.length edge ∧
        spec.core.head edge = vertex := by
  unfold stepRight
  by_cases hlast : offset.val + 1 = spec.length edge
  · rw [dite_eq_left hlast]
    simp [hlast, coreVertex]
  · rw [dite_eq_right hlast]
    simp [hlast, coreVertex, interiorVertex]

private theorem sum_first_step (edge : Fin p) (value : Fin (spec.length edge) → ℤ) :
    (∑ offset : Fin (spec.length edge),
      if offset.val = 0 then value offset else 0) =
      value ⟨0, spec.length_pos edge⟩ := by
  classical
  let first : Fin (spec.length edge) := ⟨0, spec.length_pos edge⟩
  calc
    (∑ offset : Fin (spec.length edge),
        if offset.val = 0 then value offset else 0) =
        (if first.val = 0 then value first else 0) := by
      apply Fintype.sum_eq_single first
      intro offset hne
      rw [ite_eq_right]
      intro hzero
      apply hne
      apply Fin.ext
      simpa [first] using hzero
    _ = value ⟨0, spec.length_pos edge⟩ := by simp [first]

private theorem sum_last_step (edge : Fin p) (value : Fin (spec.length edge) → ℤ) :
    (∑ offset : Fin (spec.length edge),
      if offset.val + 1 = spec.length edge then value offset else 0) =
      value ⟨spec.length edge - 1, by
        have := spec.length_pos edge
        omega⟩ := by
  classical
  let last : Fin (spec.length edge) :=
    ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩
  calc
    (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = spec.length edge then value offset else 0) =
        (if last.val + 1 = spec.length edge then value last else 0) := by
      apply Fintype.sum_eq_single last
      intro offset hne
      rw [ite_eq_right]
      intro hlast
      apply hne
      apply Fin.ext
      change offset.val = spec.length edge - 1
      omega
    _ = value ⟨spec.length edge - 1, by
          have := spec.length_pos edge
          omega⟩ := by
      have hlast : last.val + 1 = spec.length edge := by
        dsimp [last]
        have := spec.length_pos edge
        omega
      simp [last, hlast]

/-- At a core vertex, only the first and final unit steps of incident core
slots contribute to the interpolated principal divisor. -/
theorem prin_interpolatedScript_core_eq_endpointSum
    (potential : Fin n → ℤ) (vertex : Fin n) :
    prin spec.graph (spec.interpolatedScript potential)
        (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then
            SubdivisionArithmetic.step (spec.length edge)
              (spec.coreRise potential edge) 0 else 0) +
          (if spec.core.head edge = vertex then
            -SubdivisionArithmetic.step (spec.length edge)
              (spec.coreRise potential edge)
              (spec.length edge - 1) else 0)) := by
  classical
  rw [spec.prin_interpolatedScript_core]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _hedge
  rw [Finset.sum_add_distrib]
  have hLeft :
      (∑ offset : Fin (spec.length edge),
        if spec.stepLeft edge offset = spec.coreVertex vertex then
          SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge)
            offset.val else 0) =
        if spec.core.tail edge = vertex then
          SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge) 0 else 0 := by
    by_cases hTail : spec.core.tail edge = vertex
    · simp_rw [spec.stepLeft_eq_coreVertex_iff edge]
      simp only [hTail, and_true]
      simpa using spec.sum_first_step edge
        (fun offset =>
          SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge) offset.val)
    · have hNever (offset : Fin (spec.length edge)) :
          spec.stepLeft edge offset ≠ spec.coreVertex vertex := by
          simp [spec.stepLeft_eq_coreVertex_iff edge, hTail]
      simp [hNever, hTail]
  have hRight :
      (∑ offset : Fin (spec.length edge),
        if spec.stepRight edge offset = spec.coreVertex vertex then
          -SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge)
            offset.val else 0) =
        if spec.core.head edge = vertex then
          -SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge)
            (spec.length edge - 1) else 0 := by
    by_cases hHead : spec.core.head edge = vertex
    · simp_rw [spec.stepRight_eq_coreVertex_iff edge]
      simp only [hHead, and_true]
      simpa using spec.sum_last_step edge
        (fun offset =>
          -SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise potential edge) offset.val)
    · have hNever (offset : Fin (spec.length edge)) :
          spec.stepRight edge offset ≠ spec.coreVertex vertex := by
          simp [spec.stepRight_eq_coreVertex_iff edge, hHead]
      simp [hNever, hHead]
  rw [hLeft, hRight]

/-- At an interior vertex, the interpolated principal divisor is the next
path slope minus the previous path slope. -/
theorem prin_interpolatedScript_interior_eq_stepDifference
    (potential : Fin n → ℤ) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (spec.interpolatedScript potential)
        (spec.interiorVertex edge offset) =
      SubdivisionArithmetic.step (spec.length edge)
        (spec.coreRise potential edge)
          (offset.val + 1) -
        SubdivisionArithmetic.step (spec.length edge)
          (spec.coreRise potential edge)
          offset.val := by
  classical
  rw [spec.prin_interpolatedScript_interior]
  rw [Finset.sum_add_distrib]
  have hLeft :
      (∑ step : spec.Step,
        if spec.stepLeft step.1 step.2 =
            spec.interiorVertex edge offset then
          SubdivisionArithmetic.step (spec.length step.1)
            (spec.coreRise potential step.1)
            step.2.val else 0) =
        SubdivisionArithmetic.step (spec.length edge)
          (spec.coreRise potential edge)
          (offset.val + 1) := by
    let selected : spec.Step := ⟨edge, spec.nextStep edge offset⟩
    let value : spec.Step → ℤ := fun step =>
      if spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset then
        SubdivisionArithmetic.step (spec.length step.1)
          (spec.coreRise potential step.1) step.2.val else 0
    change (∑ step : spec.Step, value step) = _
    calc
      (∑ step : spec.Step, value step) = value selected := by
        apply Fintype.sum_eq_single selected
        intro step hne
        by_cases hEqual : spec.stepLeft step.1 step.2 =
            spec.interiorVertex edge offset
        · exact (hne
            ((spec.stepLeft_eq_interiorVertex_iff step edge offset).mp
              hEqual)).elim
        · simp [value, hEqual]
      _ = _ := by simp [value, selected, nextStep]
  have hRight :
      (∑ step : spec.Step,
        if spec.stepRight step.1 step.2 =
            spec.interiorVertex edge offset then
          -SubdivisionArithmetic.step (spec.length step.1)
            (spec.coreRise potential step.1)
            step.2.val else 0) =
        -SubdivisionArithmetic.step (spec.length edge)
          (spec.coreRise potential edge)
          offset.val := by
    let selected : spec.Step := ⟨edge, spec.previousStep edge offset⟩
    let value : spec.Step → ℤ := fun step =>
      if spec.stepRight step.1 step.2 = spec.interiorVertex edge offset then
        -SubdivisionArithmetic.step (spec.length step.1)
          (spec.coreRise potential step.1) step.2.val else 0
    change (∑ step : spec.Step, value step) = _
    calc
      (∑ step : spec.Step, value step) = value selected := by
        apply Fintype.sum_eq_single selected
        intro step hne
        by_cases hEqual : spec.stepRight step.1 step.2 =
            spec.interiorVertex edge offset
        · exact (hne
            ((spec.stepRight_eq_interiorVertex_iff step edge offset).mp
              hEqual)).elim
        · simp [value, hEqual]
      _ = _ := by simp [value, selected, previousStep]
  rw [hLeft, hRight]
  ring

/-- The only neighbors of an interior subdivision vertex are its preceding
and following path vertices.  This positivity-level characterization is the
basic local input for constructing the embedded core's separator cells. -/
theorem interior_num_edges_pos_iff (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) (vertex : spec.Vertex) :
    0 < numEdges spec.graph (spec.interiorVertex edge offset) vertex ↔
      vertex = spec.previousVertex edge offset ∨
        vertex = spec.nextVertex edge offset := by
  rw [spec.num_edges_pos_iff]
  constructor
  · rintro ⟨step, hForward | hBackward⟩
    · simp only [unitEdge, Prod.mk.injEq] at hForward
      have hStep :=
        (spec.stepLeft_eq_interiorVertex_iff step edge offset).mp hForward.1
      subst step
      right
      change vertex = spec.stepRight edge (spec.nextStep edge offset)
      exact hForward.2.symm
    · simp only [unitEdge, Prod.mk.injEq] at hBackward
      have hStep :=
        (spec.stepRight_eq_interiorVertex_iff step edge offset).mp hBackward.2
      subst step
      left
      change vertex = spec.stepLeft edge (spec.previousStep edge offset)
      exact hBackward.1.symm
  · rintro (rfl | rfl)
    · refine ⟨⟨edge, spec.previousStep edge offset⟩, Or.inr ?_⟩
      simp [unitEdge, previousVertex]
    · refine ⟨⟨edge, spec.nextStep edge offset⟩, Or.inl ?_⟩
      simp [unitEdge, nextVertex]

end SubdivisionGraph.Spec

/-! ## Assembly of one checked explicit-potential cone -/

namespace ExplicitPotential.Certificate

/-- The concrete subdivision specified by an integral point of a checked
local cone. -/
def subdivisionSpec (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    SubdivisionGraph.Spec n p where
  core := certificate.core
  length := certificate.segmentNat point
  core_nonempty := core_nonempty
  core_loopless := hValid.1
  length_pos := certificate.segmentNat_positive hValid point hCone

/-- The core divisor, extended by zero over all subdivision-interior
vertices. -/
def subdivisionDivisor (certificate : ExplicitPotential.Certificate m n p)
    (spec : SubdivisionGraph.Spec n p) : CFDiv spec.graph
  | Sum.inl vertex => certificate.divisor vertex
  | Sum.inr _interior => 0

/-- Evaluate one affine core potential at the chosen integral length point. -/
def evaluatedPotential (certificate : ExplicitPotential.Certificate m n p)
    (anchor : Fin n) (point : Fin m → ℤ) (vertex : Fin n) : ℤ :=
  ((certificate.witness anchor).potential vertex).eval point

theorem coreRise_evaluatedPotential
    (certificate : ExplicitPotential.Certificate m n p) (anchor : Fin n)
    (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (edge : Fin p) :
    (certificate.subdivisionSpec point core_nonempty hValid hCone).coreRise
        (certificate.evaluatedPotential anchor point) edge =
      certificate.riseValue anchor point edge := by
  simp [evaluatedPotential, subdivisionSpec, SubdivisionGraph.Spec.coreRise,
    ExplicitPotential.Certificate.riseValue,
    ExplicitPotential.Certificate.rise]

/-- The extended divisor has exactly the degree checked on the core. -/
theorem deg_subdivisionDivisor
    (certificate : ExplicitPotential.Certificate m n p)
    (spec : SubdivisionGraph.Spec n p) :
    deg (certificate.subdivisionDivisor spec) =
      ∑ vertex : Fin n, certificate.divisor vertex := by
  simp [deg, subdivisionDivisor, Fintype.sum_sum_type]

/-- The firing script attached to a core anchor, assembled on the concrete
subdivision by canonical integral interpolation. -/
def coreAnchorScript (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (anchor : Fin n) :
    firingScript
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph :=
  SubdivisionGraph.Spec.interpolatedScript
    (certificate.subdivisionSpec point core_nonempty hValid hCone)
    (certificate.evaluatedPotential anchor point)

/-- The checked explicit potential for a core anchor makes the corresponding
removed-chip residual effective at every core and interior vertex. -/
theorem effective_coreAnchorResidual
    (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (anchor : Fin n) :
    effective
      (certificate.subdivisionDivisor
          (certificate.subdivisionSpec point core_nonempty hValid hCone) -
        oneChip
          (SubdivisionGraph.Spec.coreVertex
            (certificate.subdivisionSpec point core_nonempty hValid hCone)
            anchor) +
        prin (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
          (certificate.coreAnchorScript point core_nonempty hValid hCone
            anchor)) := by
  let spec := certificate.subdivisionSpec point core_nonempty hValid hCone
  change effective
    (certificate.subdivisionDivisor spec -
      oneChip (spec.coreVertex anchor) +
      prin spec.graph
        (spec.interpolatedScript
          (certificate.evaluatedPotential anchor point)))
  intro vertex
  rcases vertex with vertex | interior
  · simp only [Pi.add_apply, Pi.sub_apply, subdivisionDivisor,
      oneChip, SubdivisionGraph.Spec.coreVertex, Sum.inl.injEq]
    change 0 ≤ certificate.divisor vertex -
      (if vertex = anchor then 1 else 0) +
      prin spec.graph
        (spec.interpolatedScript
          (certificate.evaluatedPotential anchor point))
        (spec.coreVertex vertex)
    rw [spec.prin_interpolatedScript_core_eq_endpointSum]
    have hRise (edge : Fin p) :
        spec.coreRise (certificate.evaluatedPotential anchor point) edge =
          certificate.riseValue anchor point edge := by
      exact certificate.coreRise_evaluatedPotential anchor point core_nonempty
        hValid hCone edge
    simp_rw [hRise]
    change 0 ≤ certificate.targetCoefficient anchor vertex +
      certificate.endpointContribution anchor point vertex
    exact certificate.core_balance_nonnegative
      hValid point hCone anchor vertex
  · rcases interior with ⟨edge, offset⟩
    change 0 ≤ 0 - 0 +
      prin spec.graph
        (spec.interpolatedScript
          (certificate.evaluatedPotential anchor point))
        (spec.interiorVertex edge offset)
    rw [spec.prin_interpolatedScript_interior_eq_stepDifference]
    simpa [sub_nonneg, Nat.succ_eq_add_one] using
      (SubdivisionArithmetic.step_mono (Nat.le_succ offset.val) :
        SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise (certificate.evaluatedPotential anchor point) edge)
            offset.val ≤
          SubdivisionArithmetic.step (spec.length edge)
            (spec.coreRise (certificate.evaluatedPotential anchor point) edge)
            (offset.val + 1))

/-- Every core vertex is reached by the divisor assembled from a checked
explicit-potential record. -/
theorem reaches_coreVertex
    (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (anchor : Fin n) :
    StrongSeparator.Reaches
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      (certificate.subdivisionDivisor
        (certificate.subdivisionSpec point core_nonempty hValid hCone))
      (SubdivisionGraph.Spec.coreVertex
        (certificate.subdivisionSpec point core_nonempty hValid hCone)
        anchor) := by
  let spec := certificate.subdivisionSpec point core_nonempty hValid hCone
  let divisor := certificate.subdivisionDivisor spec
  let script := certificate.coreAnchorScript point core_nonempty hValid hCone
    anchor
  unfold StrongSeparator.Reaches winnable
  refine ⟨divisor - oneChip (spec.coreVertex anchor) + prin spec.graph script,
    certificate.effective_coreAnchorResidual point core_nonempty hValid hCone
      anchor, ?_⟩
  exact StrongSeparator.linearEquiv_add_prin
    (divisor - oneChip (spec.coreVertex anchor)) script

/-- The embedded core vertices of a subdivision. -/
def coreVertices (spec : SubdivisionGraph.Spec n p) : Finset spec.graph.V :=
  Finset.univ.image spec.coreVertex

theorem coreVertices_nonempty (spec : SubdivisionGraph.Spec n p) :
    (coreVertices spec).Nonempty := by
  let vertex : Fin n := ⟨0, spec.core_nonempty⟩
  exact ⟨spec.coreVertex vertex, Finset.mem_image.mpr
    ⟨vertex, Finset.mem_univ vertex, rfl⟩⟩

@[simp] theorem coreVertex_mem_coreVertices
    (spec : SubdivisionGraph.Spec n p) (vertex : Fin n) :
    spec.coreVertex vertex ∈ coreVertices spec := by
  exact Finset.mem_image.mpr ⟨vertex, Finset.mem_univ vertex, rfl⟩

@[simp] theorem interiorVertex_not_mem_coreVertices
    (spec : SubdivisionGraph.Spec n p) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.interiorVertex edge offset ∉ coreVertices spec := by
  simp [coreVertices, SubdivisionGraph.Spec.coreVertex,
    SubdivisionGraph.Spec.interiorVertex]

/-- End-to-end local soundness theorem.

An accepted explicit-potential record on one integral length point proves
`BNExists` for the resulting subdivision as soon as the embedded core is
supplied with the graph-theoretic strong-separator certificate.  No external
search result occurs among the hypotheses: `Valid`, `FormsHold`, and the
separator certificate are ordinary Lean propositions, and generated data can
discharge the first two through their Boolean checkers. -/
theorem bnExists_of_valid_of_strongSeparator
    (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ)
    (core_nonempty : 0 < n) (degree : ℤ)
    (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hConnected : graphConnected
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph)
    (hSeparator : StrongSeparator.StrongSeparatorCertificate
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      (coreVertices
        (certificate.subdivisionSpec point core_nonempty hValid hCone))) :
    BNExists
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      1 degree := by
  let spec := certificate.subdivisionSpec point core_nonempty hValid hCone
  let divisor := certificate.subdivisionDivisor spec
  refine ⟨divisor, ?_, ?_⟩
  · rw [certificate.deg_subdivisionDivisor spec]
    exact hValid.2.1
  · apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
      hConnected (coreVertices_nonempty spec) hSeparator
    intro coreVertex hCoreVertex
    obtain ⟨anchor, _hAnchor, rfl⟩ := Finset.mem_image.mp hCoreVertex
    exact certificate.reaches_coreVertex point core_nonempty hValid hCone anchor

end ExplicitPotential.Certificate

end Utilities.Certificate
