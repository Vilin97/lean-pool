/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.OneVertexCutCheck

/-!
# Checked core vertex cuts and subdivision lifts

The input data name an articulation vertex and one side of the cut on the
*core* vertices.  The other side is the complement, with the articulation
reinserted.  This module checks that finite data occurrence by occurrence,
and lifts it uniformly to every positive-length subdivision.

An interior path vertex belongs to the named side exactly when **both** core
endpoints of its slot belong to that side.  Thus a path from the articulation
to the complementary side is assigned wholly to the complementary factor;
there is no length-dependent case split and parallel slots are retained.
-/

@[expose] public section

namespace Utilities.Certificate

open Finset
open ExplicitPotential

namespace CoreVertexCut

universe u

/-- Proof-free articulation data on an ordered finite core.  `left` contains
the articulation; `right` is derived rather than redundantly emitted. -/
structure Data {n p : ℕ} (core : ExplicitPotential.Core n p) where
  /-- The proposed articulation vertex shared by the two sides of the cut. -/
  glue : Fin n
  /-- The chosen left vertex set; validity includes the articulation, which is also inserted
  into the complementary right side. -/
  left : Finset (Fin n)

namespace Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- The complementary core side, retaining the articulation in both sides. -/
def right (c : Data core) : Finset (Fin n) :=
  insert c.glue (univ \ c.left)

/-- A core slot whose two non-articulation endpoints lie on opposite sides.
Both orientations are included, since slots are stored as ordered pairs while
the graph is undirected. -/
def Crosses (c : Data core) (edge : Fin p) : Prop :=
  (core.tail edge ∈ c.left ∧ core.tail edge ≠ c.glue ∧
    core.head edge ∉ c.left) ∨
  (core.head edge ∈ c.left ∧ core.head edge ≠ c.glue ∧
    core.tail edge ∉ c.left)

instance crossesDecidable (c : Data core) (edge : Fin p) :
    Decidable (c.Crosses edge) := by
  unfold Crosses
  infer_instance

/-- Exact mathematical validity of passive core-cut data. -/
def Valid (c : Data core) : Prop :=
  c.glue ∈ c.left ∧ ∀ edge : Fin p, ¬ c.Crosses edge

/-- Transparent finite replay of `Valid`. -/
def check (c : Data core) : Bool :=
  decide (c.glue ∈ c.left) &&
  ExplicitPotential.allFin (fun edge : Fin p => decide (¬ c.Crosses edge))

@[simp] theorem check_eq_true_iff (c : Data core) :
    c.check = true ↔ c.Valid := by
  simp [check, Valid]

/-- A core vertex outside the named side is in the derived complementary
side. -/
theorem mem_right_of_not_mem_left (c : Data core) {vertex : Fin n}
    (hNotLeft : vertex ∉ c.left) : vertex ∈ c.right := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hNotLeft⟩

/-- The articulation cannot be outside the named side of valid data. -/
theorem ne_glue_of_not_mem_left (c : Data core) (h : c.Valid)
    {vertex : Fin n} (hNotLeft : vertex ∉ c.left) : vertex ≠ c.glue := by
  intro hEqual
  apply hNotLeft
  simpa [hEqual] using h.1

variable (spec : SubdivisionGraph.Spec n p)

/-- The named factor in a subdivision.  An interior is admitted precisely
when both endpoints of its original slot are admitted by the core cut. -/
noncomputable def leftVertices (c : Data spec.core) : Finset spec.Vertex := by
  classical
  exact Finset.univ.filter fun vertex =>
    match vertex with
    | Sum.inl coreVertex => coreVertex ∈ c.left
    | Sum.inr interior =>
        spec.core.tail interior.1 ∈ c.left ∧
          spec.core.head interior.1 ∈ c.left

/-- The complementary subdivision factor.  It is literally the complement of
`leftVertices`, with the embedded articulation reinserted. -/
noncomputable def rightVertices (c : Data spec.core) : Finset spec.Vertex :=
  insert (spec.coreVertex c.glue) (Finset.univ \ leftVertices spec c)

variable (c : Data spec.core)

@[simp] theorem mem_leftVertices_core (vertex : Fin n) :
    spec.coreVertex vertex ∈ leftVertices spec c ↔ vertex ∈ c.left := by
  simp [leftVertices, SubdivisionGraph.Spec.coreVertex]

@[simp] theorem mem_leftVertices_interior
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.interiorVertex edge offset ∈ leftVertices spec c ↔
      spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
  simp [leftVertices, SubdivisionGraph.Spec.interiorVertex]

@[simp] theorem mem_rightVertices_iff (vertex : spec.Vertex) :
    vertex ∈ rightVertices spec c ↔
      vertex = spec.coreVertex c.glue ∨ vertex ∉ leftVertices spec c := by
  simp [rightVertices]

/-- A unit step cannot leave the named subdivision side except through the
embedded articulation.  This is the key length-independent lift lemma. -/
theorem stepLeft_eq_glue_of_mem_not_mem (h : c.Valid)
    (edge : Fin p) (offset : Fin (spec.length edge))
    (hLeft : spec.stepLeft edge offset ∈ leftVertices spec c)
    (hRight : spec.stepRight edge offset ∉ leftVertices spec c) :
    spec.stepLeft edge offset = spec.coreVertex c.glue := by
  by_cases hzero : offset.val = 0
  · have hTailLeft : spec.core.tail edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepLeft, dite_eq_left hzero] at hLeft
      exact (c.mem_leftVertices_core spec _).mp hLeft
    have hHeadNotLeft : spec.core.head edge ∉ c.left := by
      unfold SubdivisionGraph.Spec.stepRight at hRight
      by_cases hlast : offset.val + 1 = spec.length edge
      · rw [dite_eq_left hlast] at hRight
        intro hHead
        apply hRight
        exact (c.mem_leftVertices_core spec _).mpr hHead
      · rw [dite_eq_right hlast] at hRight
        intro hHead
        apply hRight
        exact (c.mem_leftVertices_interior spec _ _).mpr
          ⟨hTailLeft, hHead⟩
    have hTailGlue : spec.core.tail edge = c.glue := by
      by_contra hTailNe
      exact (h.2 edge) (Or.inl
        ⟨hTailLeft, hTailNe, hHeadNotLeft⟩)
    rw [SubdivisionGraph.Spec.stepLeft, dite_eq_left hzero]
    simp [hTailGlue]
  · have hInteriorLeft :
        spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
      unfold SubdivisionGraph.Spec.stepLeft at hLeft
      rw [dite_eq_right hzero] at hLeft
      exact (c.mem_leftVertices_interior spec _ _).mp hLeft
    unfold SubdivisionGraph.Spec.stepRight at hRight
    by_cases hlast : offset.val + 1 = spec.length edge
    · rw [dite_eq_left hlast] at hRight
      exact False.elim (hRight
        ((c.mem_leftVertices_core spec _).mpr hInteriorLeft.2))
    · rw [dite_eq_right hlast] at hRight
      exact False.elim (hRight
        ((c.mem_leftVertices_interior spec _ _).mpr hInteriorLeft))

/-- The symmetric unit-step statement: a step cannot enter the named side
except through the embedded articulation. -/
theorem stepRight_eq_glue_of_mem_not_mem (h : c.Valid)
    (edge : Fin p) (offset : Fin (spec.length edge))
    (hRight : spec.stepRight edge offset ∈ leftVertices spec c)
    (hLeft : spec.stepLeft edge offset ∉ leftVertices spec c) :
    spec.stepRight edge offset = spec.coreVertex c.glue := by
  by_cases hlast : offset.val + 1 = spec.length edge
  · have hHeadLeft : spec.core.head edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepRight, dite_eq_left hlast] at hRight
      exact (c.mem_leftVertices_core spec _).mp hRight
    have hTailNotLeft : spec.core.tail edge ∉ c.left := by
      unfold SubdivisionGraph.Spec.stepLeft at hLeft
      by_cases hzero : offset.val = 0
      · rw [dite_eq_left hzero] at hLeft
        intro hTail
        apply hLeft
        exact (c.mem_leftVertices_core spec _).mpr hTail
      · rw [dite_eq_right hzero] at hLeft
        intro hTail
        apply hLeft
        exact (c.mem_leftVertices_interior spec _ _).mpr
          ⟨hTail, hHeadLeft⟩
    have hHeadGlue : spec.core.head edge = c.glue := by
      by_contra hHeadNe
      exact (h.2 edge) (Or.inr
        ⟨hHeadLeft, hHeadNe, hTailNotLeft⟩)
    rw [SubdivisionGraph.Spec.stepRight, dite_eq_left hlast]
    simp [hHeadGlue]
  · have hInteriorLeft :
        spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
      unfold SubdivisionGraph.Spec.stepRight at hRight
      rw [dite_eq_right hlast] at hRight
      exact (c.mem_leftVertices_interior spec _ _).mp hRight
    unfold SubdivisionGraph.Spec.stepLeft at hLeft
    by_cases hzero : offset.val = 0
    · rw [dite_eq_left hzero] at hLeft
      exact False.elim (hLeft
        ((c.mem_leftVertices_core spec _).mpr hInteriorLeft.1))
    · rw [dite_eq_right hzero] at hLeft
      exact False.elim (hLeft
        ((c.mem_leftVertices_interior spec _ _).mpr hInteriorLeft))

/-- Lift valid finite core data to a literal one-vertex cut of every positive
subdivision of that core. -/
noncomputable def toOneVertexCut (h : c.Valid) : OneVertexCut spec.graph where
  left := leftVertices spec c
  right := rightVertices spec c
  glue := spec.coreVertex c.glue
  glue_mem_left := (c.mem_leftVertices_core spec _).mpr h.1
  glue_mem_right := by simp [rightVertices]
  vertex_cover := by
    intro vertex
    by_cases hLeft : vertex ∈ leftVertices spec c
    · exact Or.inl hLeft
    · exact Or.inr ((c.mem_rightVertices_iff spec vertex).mpr (Or.inr hLeft))
  only_overlap := by
    intro vertex hLeft hRight
    rcases (c.mem_rightVertices_iff spec vertex).mp hRight with hGlue | hNotLeft
    · exact hGlue
    · exact False.elim (hNotLeft hLeft)
  no_cross := by
    intro a hALeft hANe b hBRight hBNe
    have hBNotLeft : b ∉ leftVertices spec c := by
      rcases (c.mem_rightVertices_iff spec b).mp hBRight with hGlue | hNotLeft
      · exact False.elim (hBNe hGlue)
      · exact hNotLeft
    apply Nat.eq_zero_of_not_pos
    intro hPositive
    obtain ⟨step, hStep⟩ :=
      (spec.num_edges_pos_iff a b).mp hPositive
    rcases step with ⟨edge, offset⟩
    simp only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] at hStep
    rcases hStep with hForward | hBackward
    · have hLeft : spec.stepLeft edge offset ∈ leftVertices spec c := by
        rw [hForward.1]
        exact hALeft
      have hRight : spec.stepRight edge offset ∉ leftVertices spec c := by
        intro hMember
        apply hBNotLeft
        rw [← hForward.2]
        exact hMember
      have hGlue := c.stepLeft_eq_glue_of_mem_not_mem spec h edge offset
        hLeft hRight
      exact hANe (hForward.1.symm.trans hGlue)
    · have hRight : spec.stepRight edge offset ∈ leftVertices spec c := by
        rw [hBackward.2]
        exact hALeft
      have hLeft : spec.stepLeft edge offset ∉ leftVertices spec c := by
        intro hMember
        apply hBNotLeft
        rw [← hBackward.1]
        exact hMember
      have hGlue := c.stepRight_eq_glue_of_mem_not_mem spec h edge offset
        hRight hLeft
      exact hANe (hBackward.2.symm.trans hGlue)

/-- Brill--Noether existence on a subdivided core is equivalent to existence
on the vertex wedge extracted from valid core-cut data. -/
@[simp] theorem BNExists_iff (h : c.Valid) (r d : ℤ) :
    BNExists spec.graph r d ↔
      BNExists
        (vertexWedge (c.toOneVertexCut spec h).leftGraph
          (c.toOneVertexCut spec h).rightGraph
          (c.toOneVertexCut spec h).leftGlue
          (c.toOneVertexCut spec h).rightGlue) r d :=
  (c.toOneVertexCut spec h).BNExists_iff r d

/-- Rank-one pencils on the two factors of a valid core cut glue to a pencil
on the full subdivision, with degrees adding. -/
theorem BNExists_rank_one_of_factors (h : c.Valid) (dLeft dRight : ℤ)
    (hLeft : BNExists (c.toOneVertexCut spec h).leftGraph 1 dLeft)
    (hRight : BNExists (c.toOneVertexCut spec h).rightGraph 1 dRight) :
    BNExists spec.graph 1 (dLeft + dRight) :=
  (c.toOneVertexCut spec h).BNExists_rank_one_of_factors dLeft dRight
    hLeft hRight

/-- An arbitrary-ASP transmission profile on the two induced factors of a
valid core cut transfers directly to the subdivided graph. -/
theorem transmissionExists_of_profile (h : c.Valid)
    (u : (c.toOneVertexCut spec h).leftGraph.V)
    (v : (c.toOneVertexCut spec h).rightGraph.V)
    (tau : AspPerm)
    (D : CFDiv (c.toOneVertexCut spec h).leftGraph)
    (E : CFDiv (c.toOneVertexCut spec h).rightGraph)
    (hProfile : WedgeTransmissionProfile
      (c.toOneVertexCut spec h).leftGraph
      (c.toOneVertexCut spec h).rightGraph
      (c.toOneVertexCut spec h).leftGlue
      (c.toOneVertexCut spec h).rightGlue D E u v tau) :
    TransmissionExists spec.graph u.val v.val tau :=
  (c.toOneVertexCut spec h).transmissionExists_of_profile u v tau D E hProfile

/-- A same-left arbitrary-ASP profile on the factors of a valid core cut
transfers to the full subdivision. -/
theorem transmissionExists_sameLeft_of_profile (h : c.Valid)
    (a b : (c.toOneVertexCut spec h).leftGraph.V)
    (tau : AspPerm)
    (D : CFDiv (c.toOneVertexCut spec h).leftGraph)
    (E : CFDiv (c.toOneVertexCut spec h).rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      (c.toOneVertexCut spec h).leftGraph
      (c.toOneVertexCut spec h).rightGraph
      (c.toOneVertexCut spec h).leftGlue
      (c.toOneVertexCut spec h).rightGlue D E a b tau) :
    TransmissionExists spec.graph a.val b.val tau :=
  (c.toOneVertexCut spec h).transmissionExists_sameLeft_of_profile
    a b tau D E hProfile

/-- Explicit subdivided-core divisor supplied by a same-left profile. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
    (h : c.Valid)
    (a b : (c.toOneVertexCut spec h).leftGraph.V)
    (tau : AspPerm)
    (D : CFDiv (c.toOneVertexCut spec h).leftGraph)
    (E : CFDiv (c.toOneVertexCut spec h).rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      (c.toOneVertexCut spec h).leftGraph
      (c.toOneVertexCut spec h).rightGraph
      (c.toOneVertexCut spec h).leftGlue
      (c.toOneVertexCut spec h).rightGlue D E a b tau) :
    SatisfiesTransmission spec.graph a.val b.val tau
      ((c.toOneVertexCut spec h).graphIso.mapDiv
        (wedgeAddDivisor
          (c.toOneVertexCut spec h).leftGraph
          (c.toOneVertexCut spec h).rightGraph
          (c.toOneVertexCut spec h).leftGlue
          (c.toOneVertexCut spec h).rightGlue D E)) :=
  (c.toOneVertexCut spec h).satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
      a b tau D E hProfile

/-- A same-right arbitrary-ASP profile on the factors of a valid core cut
transfers to the full subdivision. -/
theorem transmissionExists_sameRight_of_profile (h : c.Valid)
    (a b : (c.toOneVertexCut spec h).rightGraph.V)
    (tau : AspPerm)
    (D : CFDiv (c.toOneVertexCut spec h).leftGraph)
    (E : CFDiv (c.toOneVertexCut spec h).rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      (c.toOneVertexCut spec h).leftGraph
      (c.toOneVertexCut spec h).rightGraph
      (c.toOneVertexCut spec h).leftGlue
      (c.toOneVertexCut spec h).rightGlue D E a b tau) :
    TransmissionExists spec.graph a.val b.val tau :=
  (c.toOneVertexCut spec h).transmissionExists_sameRight_of_profile
    a b tau D E hProfile

/-- Explicit subdivided-core divisor supplied by a same-right profile. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
    (h : c.Valid)
    (a b : (c.toOneVertexCut spec h).rightGraph.V)
    (tau : AspPerm)
    (D : CFDiv (c.toOneVertexCut spec h).leftGraph)
    (E : CFDiv (c.toOneVertexCut spec h).rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      (c.toOneVertexCut spec h).leftGraph
      (c.toOneVertexCut spec h).rightGraph
      (c.toOneVertexCut spec h).leftGlue
      (c.toOneVertexCut spec h).rightGlue D E a b tau) :
    SatisfiesTransmission spec.graph a.val b.val tau
      ((c.toOneVertexCut spec h).graphIso.mapDiv
        (wedgeAddDivisor
          (c.toOneVertexCut spec h).leftGraph
          (c.toOneVertexCut spec h).rightGraph
          (c.toOneVertexCut spec h).leftGlue
          (c.toOneVertexCut spec h).rightGlue D E)) :=
  (c.toOneVertexCut spec h).satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
      a b tau D E hProfile

/-- Accepted finite core data immediately yields a checked cut of any
positive subdivision. -/
noncomputable def cutOfCheck (h : c.check = true) : OneVertexCut spec.graph :=
  c.toOneVertexCut spec (c.check_eq_true_iff.mp h)

/-- The generic core-cut lift can be fed straight into the existing
proof-carrying one-vertex-cut interface. -/
noncomputable def subdivisionCheckData : OneVertexCutCheck.Data spec.graph where
  left := leftVertices spec c
  right := rightVertices spec c
  glue := spec.coreVertex c.glue

@[simp] theorem subdivisionCheckData_check (h : c.Valid) :
    (c.subdivisionCheckData spec).check = true := by
  rw [OneVertexCutCheck.Data.check_eq_true_iff]
  let data : OneVertexCutCheck.Data spec.graph :=
    { left := leftVertices spec c
      right := rightVertices spec c
      glue := spec.coreVertex c.glue }
  change data.Valid
  exact ⟨(c.toOneVertexCut spec h).glue_mem_left,
    (c.toOneVertexCut spec h).glue_mem_right, by
    intro vertex
    exact (c.toOneVertexCut spec h).vertex_cover vertex, by
    intro vertex hLeft hRight
    exact (c.toOneVertexCut spec h).only_overlap vertex hLeft hRight, by
    intro a hALeft hANe b hBRight hBNe
    exact (c.toOneVertexCut spec h).no_cross a hALeft hANe b hBRight hBNe⟩

/-! ## Closed regression

The two core slots below meet at vertex `1`.  Their lengths are deliberately
different and greater than one, so the accepted lift exercises the rule that
every interior is assigned from both endpoints of its parent slot. -/

private def threeVertexPathCore : ExplicitPotential.Core 3 2 where
  tail
    | 0 => 0
    | 1 => 1
  head
    | 0 => 1
    | 1 => 2

private def threeVertexPathCut : Data threeVertexPathCore where
  glue := 1
  left := {0, 1}

private theorem threeVertexPathCut_check : threeVertexPathCut.check = true := by
  decide

private def threeVertexPathSpec : SubdivisionGraph.Spec 3 2 where
  core := threeVertexPathCore
  length edge := if edge = 0 then 2 else 3
  core_nonempty := by decide
  core_loopless := by decide
  length_pos := by
    intro edge
    by_cases h : edge = 0 <;> simp [h]

private theorem threeVertexPathSubdivision_check :
    (threeVertexPathCut.subdivisionCheckData threeVertexPathSpec).check = true :=
  threeVertexPathCut.subdivisionCheckData_check threeVertexPathSpec
    (threeVertexPathCut.check_eq_true_iff.mp threeVertexPathCut_check)

end Data

end CoreVertexCut

end Utilities.Certificate
