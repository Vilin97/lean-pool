/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateCoreVertexCut

/-!
# Closed genus-four row 098 from its separating vertex

Row 098 is the unique bridge-bearing member of the six loopless cubic
genus-four cores.  Removing vertex `1` separates two genus-two lobes.  The
checked core cut below is independent of edge lengths, and the public
degenerate-cut theorem shows that it survives every nonloopy forest face.

This gives a short structural proof on the whole closed orthant; the generated
`g4row098.rpf` cut-vertex certificate is therefore no longer load-bearing.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFourRow098Closed

open Utilities
open Utilities.Certificate
open Utilities.Certificate.CoreVertexCut
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.DegenerateSpec
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas

/-- The two genus-two lobes of row 098 meet at vertex `1`. -/
def cut : CoreVertexCut.Data row098Core where
  glue := 1
  left := {0, 1, 4, 5}

theorem cut_valid : cut.Valid :=
  cut.check_eq_true_iff.mp (by decide)

theorem cut_leftGenus : cut.leftGenus = 2 := by decide
theorem cut_rightGenus : cut.rightGenus = 2 := by decide

private theorem faceSpec_repIsContraction
    (length : Fin 9 → ℕ)
    (hForest : IsForest row098Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row098Core (zeroSlots length)) :
    (faceSpec row098Core (by norm_num) length hForest hNotLoopy).RepIsContraction := by
  intro u v hRep
  exact (compFold_iff row098Core (zeroSlots length) u v).mp hRep

/-- Every subdivision and every equal-genus contraction of row 098 carries a
degree-three rank-one divisor. -/
theorem bnExists_closed
    (length : Fin 9 → ℕ)
    (hForest : IsForest row098Core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row098Core (zeroSlots length)) :
    BNExists (faceSpec row098Core (by norm_num) length hForest hNotLoopy).graph 1 3 :=
  DegenerateCoreVertexCut.bnExists_one_three_of_two_two
    (faceSpec row098Core (by norm_num) length hForest hNotLoopy) cut
    (faceSpec_repIsContraction length hForest hNotLoopy)
    row098.loopless cut_valid row098.connected cut_leftGenus cut_rightGenus

end AtanasovRanganathan.GenusFourRow098Closed
