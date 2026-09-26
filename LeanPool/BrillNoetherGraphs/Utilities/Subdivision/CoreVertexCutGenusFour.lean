/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusFourVertexCut
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutTwoRegular
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SpanningTreeConnectivity

/-!
# Checked genus-four rank-one core cuts

A proof-free core articulation is sufficient for the genus-four critical
pencil when its factor genera are `(2,2)`, or `(3,1)` with the genus-one
side two-regular.  The checker and its soundness theorem are public and apply
uniformly to every positive subdivision.
-/

@[expose] public section

namespace Utilities.Certificate.CoreVertexCut.Data
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open ExplicitPotential
open Utilities.Certificate.CoreVertexCut
open Utilities.Certificate.CoreVertexCut.Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- The three finite factor alternatives consumed by the genus-four wedge
theorems.  The two-regular condition is required only on a genus-one side. -/
def GenusFourRankOneAlternatives (c : CoreVertexCut.Data core) : Prop :=
  (c.leftGenus = 2 ∧ c.rightGenus = 2) ∨
    (c.leftGenus = 3 ∧ c.RightTwoRegular ∧ c.rightGenus = 1) ∨
    (c.LeftTwoRegular ∧ c.leftGenus = 1 ∧ c.rightGenus = 3)

/-- Exact mathematical conditions for the genus-four cut argument. -/
def GenusFourRankOneConditions (c : CoreVertexCut.Data core) : Prop :=
  c.Valid ∧ core.Connected ∧ c.GenusFourRankOneAlternatives

/-- Kernel-cheap finite checker for the complete genus-four cut condition.
Connectivity is supplied by local rooted spanning-tree data rather than the
exponential all-cuts checker. -/
def genusFourRankOneCheck (c : CoreVertexCut.Data core)
    (tree : SpanningTreeConnectivity.CertificateData core) : Bool :=
  c.check && tree.check &&
    ((decide (c.leftGenus = 2) && decide (c.rightGenus = 2)) ||
      (decide (c.leftGenus = 3) && c.rightTwoRegularCheck &&
        decide (c.rightGenus = 1)) ||
      (c.leftTwoRegularCheck && decide (c.leftGenus = 1) &&
        decide (c.rightGenus = 3)))

/-- The executable checker implements the cut, spanning-tree, and factor
conditions exactly. -/
@[simp] theorem genusFourRankOneCheck_eq_true_iff
    (c : CoreVertexCut.Data core)
    (tree : SpanningTreeConnectivity.CertificateData core) :
    c.genusFourRankOneCheck tree = true ↔
      c.Valid ∧ tree.Valid ∧ c.GenusFourRankOneAlternatives := by
  simp only [genusFourRankOneCheck, GenusFourRankOneAlternatives,
    Bool.and_eq_true, Bool.or_eq_true, check_eq_true_iff,
    SpanningTreeConnectivity.CertificateData.check_eq_true_iff,
    leftTwoRegularCheck_eq_true_iff, rightTwoRegularCheck_eq_true_iff,
    decide_eq_true_eq]
  tauto

/-- Accepted cheap checker data imply the mathematical conditions used by
the subdivision theorem. -/
theorem genusFourRankOneConditions_of_check
    (c : CoreVertexCut.Data core)
    (tree : SpanningTreeConnectivity.CertificateData core)
    (hCheck : c.genusFourRankOneCheck tree = true) :
    c.GenusFourRankOneConditions := by
  obtain ⟨hCut, hTree, hAlternatives⟩ :=
    (c.genusFourRankOneCheck_eq_true_iff tree).mp hCheck
  exact ⟨hCut, tree.coreConnected_of_valid hTree, hAlternatives⟩

variable (spec : SubdivisionGraph.Spec n p)
variable (c : CoreVertexCut.Data spec.core)

/-- Accepted genus-four cut data makes every positive subdivision connected. -/
theorem graph_connected_of_genusFourRankOneConditions
    (h : c.GenusFourRankOneConditions) :
    graphConnected spec.graph :=
  spec.graph_connected_of_coreConnected h.2.1

/-- The finite factor alternatives force ambient genus four, independently of
the subdivision lengths. -/
theorem graph_genus_eq_four_of_genusFourRankOneConditions
    (h : c.GenusFourRankOneConditions) :
    genus spec.graph = 4 := by
  have hSum := c.leftGenus_add_rightGenus_eq_graph_genus spec h.1
  rcases h.2.2 with hTwoTwo | hThreeOne | hOneThree
  · omega
  · omega
  · omega

/-- A checked `(2,2)` or rigid `(3,1)` core cut supplies the critical
degree-three rank-one divisor on every positive subdivision. -/
theorem bnExists_one_three_of_genusFourRankOneConditions
    (h : c.GenusFourRankOneConditions) :
    BNExists spec.graph 1 3 := by
  let cut := c.toOneVertexCut spec h.1
  have hConnected : graphConnected spec.graph :=
    c.graph_connected_of_genusFourRankOneConditions spec h
  rcases h.2.2 with hTwoTwo | hThreeOne | hOneThree
  · have hLeftGenus : genus cut.leftGraph = 2 := by
      dsimp [cut]
      rw [c.leftGraph_genus spec h.1, hTwoTwo.1]
    have hRightGenus : genus cut.rightGraph = 2 := by
      dsimp [cut]
      rw [c.rightGraph_genus spec h.1, hTwoTwo.2]
    exact cut.BNExists_rankOneDegreeThree_of_genus_two_two
      hConnected hLeftGenus hRightGenus
  · have hLeftGenus : genus cut.leftGraph = 3 := by
      dsimp [cut]
      rw [c.leftGraph_genus spec h.1, hThreeOne.1]
    have hRightRigid : PointedGenusOneRigid cut.rightGraph cut.rightGlue := by
      dsimp [cut]
      exact c.rightPointedGenusOneRigid spec
        ⟨h.1, h.2.1, hThreeOne.2.1, hThreeOne.2.2⟩
    exact cut.BNExists_rankOneDegreeThree_of_left_three_right_rigid_one
      hConnected hLeftGenus hRightRigid
  · have hLeftRigid : PointedGenusOneRigid cut.leftGraph cut.leftGlue := by
      dsimp [cut]
      exact c.leftPointedGenusOneRigid spec
        ⟨h.1, h.2.1, hOneThree.1, hOneThree.2.1⟩
    have hRightGenus : genus cut.rightGraph = 3 := by
      dsimp [cut]
      rw [c.rightGraph_genus spec h.1, hOneThree.2.2]
    exact cut.BNExists_rankOneDegreeThree_of_left_rigid_one_right_three
      hConnected hLeftRigid hRightGenus

/-- Checker-facing form of the critical genus-four conclusion. -/
theorem bnExists_one_three_of_genusFourRankOneCheck
    (tree : SpanningTreeConnectivity.CertificateData spec.core)
    (hCheck : c.genusFourRankOneCheck tree = true) :
    BNExists spec.graph 1 3 :=
  c.bnExists_one_three_of_genusFourRankOneConditions spec
    (c.genusFourRankOneConditions_of_check tree hCheck)


end Utilities.Certificate.CoreVertexCut.Data
