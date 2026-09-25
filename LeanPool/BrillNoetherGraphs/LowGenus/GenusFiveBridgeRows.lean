/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicCoverage
public import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.GenusFiveVertexCut
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutGenus
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateCoreVertexCut

/-!
# Articulation data for the four genus-five cubic bridge rows

All four exceptional rows in the public cubic atlas have the same labelled
genus-two lobe on vertices `{0,1,2}`, attached to the complementary
genus-three side at vertex `0`.  The occurrence-level core cut checker and
the factor-genus calculator verify this finite structural data directly.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFiveBridgeRows

open Utilities
open Utilities.Certificate
open Utilities.Certificate.CoreVertexCut
open Utilities.Certificate.CoreVertexCut.Data
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.DegenerateCoreVertexCut
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFiveCubicCoverage
open AtanasovRanganathan.GenusFiveCubicAtlas

/-- The root-double bridge cut, with gluing vertex zero and left vertex set `{0, 1, 2}`. -/
def rootDoubleCut : Data rootDoubleCore where
  glue := 0
  left := {0, 1, 2}

/-- The one-chord bridge cut, with gluing vertex zero and left vertex set `{0, 1, 2}`. -/
def oneChordCut : Data oneChordCore where
  glue := 0
  left := {0, 1, 2}

/-- The square bridge cut, with gluing vertex zero and left vertex set `{0, 1, 2}`. -/
def squareCut : Data squareCore where
  glue := 0
  left := {0, 1, 2}

/-- The double-matching bridge cut, with gluing vertex zero and left vertex set `{0, 1, 2}`. -/
def doubleMatchingCut : Data doubleMatchingCore where
  glue := 0
  left := {0, 1, 2}

theorem rootDoubleCut_valid : rootDoubleCut.Valid :=
  rootDoubleCut.check_eq_true_iff.mp (by decide)
theorem oneChordCut_valid : oneChordCut.Valid :=
  oneChordCut.check_eq_true_iff.mp (by decide)
theorem squareCut_valid : squareCut.Valid :=
  squareCut.check_eq_true_iff.mp (by decide)
theorem doubleMatchingCut_valid : doubleMatchingCut.Valid :=
  doubleMatchingCut.check_eq_true_iff.mp (by decide)

theorem rootDoubleCut_leftGenus : rootDoubleCut.leftGenus = 2 := by decide
theorem oneChordCut_leftGenus : oneChordCut.leftGenus = 2 := by decide
theorem squareCut_leftGenus : squareCut.leftGenus = 2 := by decide
theorem doubleMatchingCut_leftGenus : doubleMatchingCut.leftGenus = 2 := by decide

theorem rootDoubleCut_rightGenus : rootDoubleCut.rightGenus = 3 := by decide
theorem oneChordCut_rightGenus : oneChordCut.rightGenus = 3 := by decide
theorem squareCut_rightGenus : squareCut.rightGenus = 3 := by decide
theorem doubleMatchingCut_rightGenus : doubleMatchingCut.rightGenus = 3 := by decide

private theorem faceSpec_repIsContraction
    {n p : ℕ} (core : ExplicitPotential.Core n p) (hn : 0 < n)
    (length : Fin p → ℕ)
    (hForest : IsForest core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy core (zeroSlots length)) :
    (faceSpec core hn length hForest hNotLoopy).RepIsContraction := by
  intro u v hRep
  exact (compFold_iff core (zeroSlots length) u v).mp hRep

/-- A checked `(2,3)` articulation on a genus-five core supplies a
degree-four pencil on every nonloopy forest face of that core. -/
theorem bnExists_face_of_two_three_cut
    (genusFour : GenusFourRankOneExistence)
    {n p : ℕ} (core : ExplicitPotential.Core n p) (hn : 0 < n)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (hConnected : core.Connected)
    (cut : CoreVertexCut.Data core) (hValid : cut.Valid)
    (hLeft : cut.leftGenus = 2) (hRight : cut.rightGenus = 3)
    (length : Fin p → ℕ)
    (hForest : IsForest core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy core (zeroSlots length)) :
    BNExists (faceSpec core hn length hForest hNotLoopy).graph 1 4 := by
  let d := faceSpec core hn length hForest hNotLoopy
  have hRep : d.RepIsContraction :=
    faceSpec_repIsContraction core hn length hForest hNotLoopy
  let transported := contractedCut d cut
  have hTransportedValid : transported.Valid :=
    contractedCut_valid d cut hValid hRep
  have hTransportedConnected : d.contractedSpec.core.Connected :=
    d.canonicalContraction.target_core_connected hConnected
  let graphCut := transported.toOneVertexCut d.contractedSpec hTransportedValid
  have hContractedConnected : graphConnected d.contractedSpec.graph :=
    d.contractedSpec.graph_connected_of_coreConnected hTransportedConnected
  have hFaceGenus : genus d.graph = 5 := by
    rw [d.genus_graph]
    have hSum := cut.leftGenus_add_rightGenus hValid hLoopless
    rw [hLeft, hRight] at hSum
    omega
  have hContractedGenus : genus d.contractedSpec.graph = 5 := by
    have hEq := d.canonicalContraction.laplacianEquiv.genus_eq
    rw [hFaceGenus] at hEq
    exact hEq.symm
  have hLeftGraph : genus graphCut.leftGraph = 2 := by
    dsimp only [graphCut]
    rw [transported.leftGraph_genus d.contractedSpec hTransportedValid]
    exact (contractedCut_leftGenus d cut hValid hRep hLoopless).trans hLeft
  have hRightGraph : genus graphCut.rightGraph = 3 := by
    dsimp only [graphCut]
    rw [transported.rightGraph_genus d.contractedSpec hTransportedValid]
    exact (contractedCut_rightGenus d cut hValid hRep hLoopless).trans hRight
  have hContracted : BNExists d.contractedSpec.graph 1 4 :=
    Utilities.BNExists_one_four_of_positiveGenus_oneVertexCut genusFour
      d.contractedSpec.graph hContractedConnected hContractedGenus graphCut
      (by rw [hLeftGraph]; norm_num) (by rw [hRightGraph]; norm_num)
  exact (d.canonicalContraction.laplacianEquiv.bnExists_iff 1 4).mp hContracted

theorem rootDouble_closed (genusFour : GenusFourRankOneExistence) :
    ClosedSubdivisionDharConstruction rootDoubleCore (by norm_num) := by
  intro length hForest hNotLoopy
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (bnExists_face_of_two_three_cut genusFour rootDoubleCore (by norm_num)
      rootDouble.loopless rootDouble.connected rootDoubleCut rootDoubleCut_valid
      rootDoubleCut_leftGenus rootDoubleCut_rightGenus length hForest hNotLoopy)

theorem oneChord_closed (genusFour : GenusFourRankOneExistence) :
    ClosedSubdivisionDharConstruction oneChordCore (by norm_num) := by
  intro length hForest hNotLoopy
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (bnExists_face_of_two_three_cut genusFour oneChordCore (by norm_num)
      oneChord.loopless oneChord.connected oneChordCut oneChordCut_valid
      oneChordCut_leftGenus oneChordCut_rightGenus length hForest hNotLoopy)

theorem square_closed (genusFour : GenusFourRankOneExistence) :
    ClosedSubdivisionDharConstruction squareCore (by norm_num) := by
  intro length hForest hNotLoopy
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (bnExists_face_of_two_three_cut genusFour squareCore (by norm_num)
      square.loopless square.connected squareCut squareCut_valid
      squareCut_leftGenus squareCut_rightGenus length hForest hNotLoopy)

theorem doubleMatching_closed (genusFour : GenusFourRankOneExistence) :
    ClosedSubdivisionDharConstruction doubleMatchingCore (by norm_num) := by
  intro length hForest hNotLoopy
  exact DegreeFourDharPencil.nonempty_ofBNExists
    (bnExists_face_of_two_three_cut genusFour doubleMatchingCore (by norm_num)
      doubleMatching.loopless doubleMatching.connected doubleMatchingCut
      doubleMatchingCut_valid doubleMatchingCut_leftGenus
      doubleMatchingCut_rightGenus length hForest hNotLoopy)

/-- The four bridge rows are all closed structurally by the same checked
`(2,3)` articulation. -/
theorem bridgeAtlasClosedCoverage
    (genusFour : GenusFourRankOneExistence) : BridgeAtlasClosedCoverage := by
  intro row hRow
  simp [bridgeAtlas] at hRow
  rcases hRow with rfl | rfl | rfl | rfl
  · exact rootDouble_closed genusFour
  · exact oneChord_closed genusFour
  · exact square_closed genusFour
  · exact doubleMatching_closed genusFour

end AtanasovRanganathan.GenusFiveBridgeRows
