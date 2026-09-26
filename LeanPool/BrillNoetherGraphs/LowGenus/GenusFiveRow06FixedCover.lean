/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverBase
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverCells0
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverCells1
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverCells2
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverCells3
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverCells4
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06Symmetry
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverReceipts

/-! **Independent generated check.** This module provides an additional generated proof of row 06
and is not imported by the main `LowGenus` root.

Generated exact replay of the fixed AR row-06 divisor on a
fundamental domain for the core's slot-level symmetry group.

The external discovery data are untrusted: `cells_check` and
`tree_check` replay every arithmetic obligation in the kernel, and the
chamber is discharged by the generated coverage theorem, so the
conclusion is the row on the whole closed orthant. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06FixedCover

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow06CoverBase
open GenusFiveRow06Symmetry (Chamber chamber_covers)

/-- The 483 row-06 closed-cover cells in global index order, obtained by concatenating the five
certificate blocks. -/
def cells : List (CoordinateCell row06Core) :=
  GenusFiveRow06CoverCells0.chunk ++ GenusFiveRow06CoverCells1.chunk ++
    GenusFiveRow06CoverCells2.chunk ++ GenusFiveRow06CoverCells3.chunk ++
    GenusFiveRow06CoverCells4.chunk

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, List.all_append, GenusFiveRow06CoverCells0.chunk_check,
    GenusFiveRow06CoverCells1.chunk_check, GenusFiveRow06CoverCells2.chunk_check,
    GenusFiveRow06CoverCells3.chunk_check, GenusFiveRow06CoverCells4.chunk_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.CertificateData.checkClosed_eq_true_iff _ _).mp hChecks

/-- The twelve root rows of the closed orthant followed by the six
chamber inequalities cutting the fundamental domain. -/
def base : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0,
  0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff
  [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0,
  0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, -1,
  1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The 37 homogeneous affine forms whose signs determine branches of the row-06 decision tree;
coefficients are indexed by the twelve edge lengths. -/
def splitForms : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0], aff [0, 0,
  0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0,
  0, -1, 0, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1,
  -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0,
  0, -1, 2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0,
  0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
  aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0], aff
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0], aff [0,
  0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1], aff [0, 0, 0,
  0, 0, 1, 0, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0,
  2, 0, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0,
  0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0,
  0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, -1, 0, 0, 1,
  0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 1,
  0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0,
  0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0]]

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0] := by rfl

theorem splitForm14 : splitForms.getD 14 0 = aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm15 : splitForms.getD 15 0 = aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1] := by rfl

theorem splitForm17 : splitForms.getD 17 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0] := by rfl

theorem splitForm18 : splitForms.getD 18 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0] := by rfl

theorem splitForm20 : splitForms.getD 20 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0] := by rfl

theorem splitForm21 : splitForms.getD 21 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0] := by rfl

theorem splitForm22 : splitForms.getD 22 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1] := by rfl

theorem splitForm23 : splitForms.getD 23 0 = aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0] := by rfl

theorem splitForm24 : splitForms.getD 24 0 = aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm25 : splitForms.getD 25 0 = aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm28 : splitForms.getD 28 0 = aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm29 : splitForms.getD 29 0 = aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 0, 0, 0, 0, 2, -1, 0, -2, 0, 0, 0, 0] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm32 : splitForms.getD 32 0 = aff [0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 0, 0] := by rfl

theorem splitForm33 : splitForms.getD 33 0 = aff [0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 1, 0, 0] := by rfl

theorem splitForm34 : splitForms.getD 34 0 = aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0] := by rfl

theorem splitForm35 : splitForms.getD 35 0 = aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0] := by rfl

theorem splitForm36 : splitForms.getD 36 0 = aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0] := by rfl

/-- Subtree splitting on `length[2] - length[3]` in the row-06 symmetry chamber, with leaves
selecting cells 0, 1, 2, 3, 4, 5 and Farkas receipts excluding inconsistent sign branches. -/
def treePart0 : CompactCellTree :=
  .split 4
    (.cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17])
    (.split 14
        (.cell 1 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36])
        (.split 15
            (.cell 2 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54])
            (.split 27
                (.cell 3 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72,
                  73, 74])
                (.split 28
                    (.cell 4 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91,
                      92, 93, 94])
                    (.split 29
                        (.cell 5 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
                          109, 110, 111, 112, 113, 114])
                        (.absurd 115))))))

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 0, 6, 7, 8, 9, 10 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart1 : CompactCellTree :=
  .split 5
    (.cell 0 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 116, 33, 34, 35, 117])
    (.split 6
        (.cell 6 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 118, 51, 52, 53, 50])
        (.split 7
            (.cell 6 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 119, 71, 72, 73, 120])
            (.split 8
                (.cell 7 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 121, 91, 92, 93, 90,
                  122, 123])
                (.split 30
                    (.cell 8 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 124, 111,
                      112, 113, 110, 125, 126])
                    (.split 31
                        (.cell 9 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                          140, 141, 142, 143, 144, 145])
                        (.split 32
                            (.cell 10 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157,
                              158, 159, 160, 161, 162, 163, 164, 165])
                            (.absurd 166)))))))

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 167 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart2 : CompactCellTree :=
  .absurd 167

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 11, 12, 13, 14, 15 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart3 : CompactCellTree :=
  .split 14
    (.cell 11 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 168, 71, 72, 73, 169])
    (.split 15
        (.cell 12 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 91, 92, 93, 170])
        (.split 27
            (.cell 13 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 171, 172, 110,
              111, 112, 113, 173])
            (.split 28
                (.cell 14 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174,
                  175, 145, 141, 142, 143, 176])
                (.split 29
                    (.cell 15 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
                      177, 178, 165, 160, 161, 162, 163])
                    (.absurd 179)))))

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 180 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart4 : CompactCellTree :=
  .absurd 180

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 16, 17, 18, 19, 20 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart5 : CompactCellTree :=
  .split 14
    (.cell 16 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 111, 112, 113,
      108, 125, 126])
    (.split 15
        (.cell 17 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 141, 142,
          143, 182, 183, 184])
        (.split 27
            (.cell 18 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185, 186,
              165, 160, 161, 162, 187, 188, 189])
            (.split 28
                (.cell 19 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 206, 207, 208, 209, 210, 211])
                (.split 29
                    (.cell 20 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      225, 226, 227, 228, 229, 230, 231, 232, 233])
                    (.absurd 234)))))

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 21, 22, 23, 24, 25, 26, 27, 28, 29, 30 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart6 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 141,
          142, 143, 236, 183, 184])
        (.split 15
            (.cell 22 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 160,
              161, 162, 237, 188, 189])
            (.split 27
                (.cell 23 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 206, 207, 208, 238, 210, 211])
                (.split 28
                    (.cell 24 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 227, 228, 229, 230, 241, 232, 233])
                    (.split 29
                        (.cell 25 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                          255, 256, 257, 258, 259, 260, 261, 262, 263])
                        (.absurd 264))))))
    (.split 32
        (.split 14
            (.cell 26 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265,
              160, 161, 162, 163, 164, 177])
            (.split 15
                (.cell 27 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205,
                  206, 207, 208, 266, 267, 268])
                (.split 27
                    (.cell 28 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 227, 228, 229, 230, 269, 270, 271])
                    (.split 28
                        (.cell 29 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                          272, 273, 257, 258, 259, 260, 274, 275, 276])
                        (.split 29
                            (.cell 30 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 290, 291, 292, 293, 294, 295, 296, 297, 298])
                            (.absurd 299))))))
        (.absurd 300))

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[8] + length[9]` in the row-06 symmetry chamber, with
leaves selecting cells 0, 31, 32, 33, 34, 35 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart7 : CompactCellTree :=
  .split 9
    (.cell 0 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 116, 33, 301, 35, 36])
    (.split 10
        (.cell 31 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 118, 51, 50, 53, 54])
        (.split 11
            (.cell 31 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 119, 71, 302, 73, 74])
            (.split 12
                (.cell 32 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 121, 91, 90, 303,
                  304, 93, 94])
                (.split 13
                    (.cell 33 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 124,
                      111, 110, 305, 306, 113, 114])
                    (.split 33
                        (.cell 34 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                          140, 141, 145, 307, 143, 308])
                        (.split 16
                            (.cell 35 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157,
                              158, 159, 160, 309, 163, 165, 162, 310])
                            (.absurd 311)))))))

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 312 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart8 : CompactCellTree :=
  .absurd 312

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 36, 37, 38, 39, 40 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart9 : CompactCellTree :=
  .split 14
    (.cell 36 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 168, 71, 169, 73, 74])
    (.split 15
        (.cell 37 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 91, 170, 93, 94])
        (.split 27
            (.cell 38 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 171, 172, 110,
              111, 173, 113, 114])
            (.split 28
                (.cell 39 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174,
                  175, 145, 141, 176, 143, 308])
                (.split 29
                    (.cell 40 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
                      177, 178, 165, 160, 163, 162, 310])
                    (.absurd 179)))))

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
      1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 313 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart10 : CompactCellTree :=
  .absurd 313

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
      1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 41, 42, 43, 44, 45 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart11 : CompactCellTree :=
  .split 14
    (.cell 41 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 111, 108, 305,
      306, 113, 114])
    (.split 15
        (.cell 42 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 141, 182,
          314, 315, 143, 308])
        (.split 27
            (.cell 43 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185, 186,
              165, 160, 187, 316, 317, 162, 310])
            (.split 28
                (.cell 44 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 206, 209, 318, 319, 208, 320])
                (.split 29
                    (.cell 45 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      225, 226, 227, 228, 231, 321, 322, 230, 323])
                    (.absurd 234)))))

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
      1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[8] - 2 * length[9] - length[10]` in the row-06 symmetry
chamber, with leaves selecting cells 46, 47, 48, 49, 50, 51, 52, 53, 54 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart12 : CompactCellTree :=
  .split 13
    (.split 14
        (.cell 46 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 141,
          236, 314, 315, 143, 308])
        (.split 15
            (.cell 47 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 160,
              237, 316, 317, 162, 310])
            (.split 27
                (.cell 48 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 206, 238, 318, 319, 208, 320])
                (.split 28
                    (.cell 49 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 227, 228, 241, 321, 322, 230, 323])
                    (.split 29
                        (.cell 50 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                          255, 256, 257, 258, 261, 324, 325, 260, 326])
                        (.absurd 264))))))
    (.split 14
        (.absurd 327)
        (.split 15
            (.split 16
                (.cell 51 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 328,
                  206, 329, 266, 205, 208, 320])
                (.absurd 330))
            (.split 27
                (.split 16
                    (.cell 52 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 225, 228, 331, 269, 227, 230, 323])
                    (.absurd 332))
                (.split 28
                    (.split 16
                        (.cell 53 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                          272, 273, 255, 258, 333, 274, 257, 260, 326])
                        (.absurd 334))
                    (.split 29
                        (.split 16
                            (.cell 54 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 335, 291, 290, 293, 336, 296, 292, 295, 337])
                            (.absurd 338))
                        (.absurd 264))))))

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
      1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 339 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart13 : CompactCellTree :=
  .absurd 339

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 31, 55, 56, 57, 58, 59 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart14 : CompactCellTree :=
  .split 5
    (.cell 31 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 119, 71, 169, 73, 340])
    (.split 6
        (.cell 55 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 121, 91, 170, 93, 90])
        (.split 7
            (.cell 55 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 124, 111, 173,
              113, 341])
            (.split 8
                (.cell 56 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140,
                  141, 176, 143, 145, 183, 184])
                (.split 30
                    (.cell 57 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
                      159, 160, 163, 162, 165, 188, 189])
                    (.split 31
                        (.cell 58 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                          342, 206, 266, 208, 343, 205])
                        (.split 32
                            (.cell 59 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                              224, 344, 228, 269, 230, 231, 345, 227])
                            (.absurd 346)))))))

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 347 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart15 : CompactCellTree :=
  .absurd 347

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 32, 60, 61, 62, 63, 64 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart16 : CompactCellTree :=
  .split 5
    (.cell 32 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 124, 111, 108, 305, 306,
      113, 348])
    (.split 6
        (.cell 60 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 182,
          314, 315, 143, 145])
        (.split 7
            (.cell 60 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
              187, 316, 317, 162, 349])
            (.split 8
                (.cell 61 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 342,
                  206, 209, 318, 319, 208, 205, 210, 211])
                (.split 30
                    (.cell 62 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      344, 228, 231, 321, 322, 230, 227, 232, 233])
                    (.split 31
                        (.cell 63 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                          350, 258, 351, 324, 325, 260, 352, 257])
                        (.split 32
                            (.cell 64 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 353, 293, 354, 355, 356, 295, 298, 357, 292])
                            (.absurd 358)))))))

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 359 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart17 : CompactCellTree :=
  .absurd 359

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0,
      -2, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[8] - 2 * length[9] - length[10]` in the row-06 symmetry
chamber, with leaves selecting cells 65, 66, 67 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart18 : CompactCellTree :=
  .split 13
    (.cell 65 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 165, 316,
      317, 162, 177])
    (.split 33
        (.cell 66 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 342, 206, 205,
          360, 208, 268])
        (.split 16
            (.cell 67 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 344, 228,
              361, 269, 227, 230, 271])
            (.absurd 362)))

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0,
      -2, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + 2 * length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 68, 69, 70, 71, 72, 73, 74, 75 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart19 : CompactCellTree :=
  .split 7
    (.absurd 363)
    (.split 13
        (.split 8
            (.cell 68 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 344, 228,
              225, 321, 322, 230, 227, 232, 233])
            (.split 30
                (.cell 69 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 350,
                  258, 364, 324, 325, 260, 257, 262, 263])
                (.split 31
                    (.cell 70 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      353, 293, 365, 355, 356, 295, 366, 292])
                    (.split 32
                        (.cell 71 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                          380, 381, 382, 383, 384, 385, 386, 387, 388])
                        (.absurd 389)))))
        (.split 33
            (.absurd 390)
            (.split 16
                (.split 8
                    (.cell 72 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      353, 293, 391, 296, 290, 295, 292, 392, 393])
                    (.split 30
                        (.cell 73 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                          380, 381, 394, 395, 396, 385, 388, 397, 398])
                        (.split 31
                            (.cell 74 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                              411, 412, 413, 414, 415, 416, 417, 418, 419])
                            (.split 32
                                (.cell 75 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430,
                                  431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441])
                                (.absurd 442)))))
                (.absurd 443))))

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0,
      -2, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 339 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart20 : CompactCellTree :=
  .absurd 339

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 444 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart21 : CompactCellTree :=
  .absurd 444

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 76, 77, 78, 79, 80 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart22 : CompactCellTree :=
  .split 14
    (.cell 76 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 111, 173, 113,
      108])
    (.split 15
        (.cell 77 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 141, 176,
          143, 182])
        (.split 27
            (.cell 78 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185, 186,
              165, 160, 163, 162, 187])
            (.split 28
                (.cell 79 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 206, 266, 208, 209])
                (.split 29
                    (.cell 80 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      225, 226, 227, 228, 269, 230, 231])
                    (.absurd 234)))))

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 445 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart23 : CompactCellTree :=
  .absurd 445

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 81, 82, 83, 84, 85 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart24 : CompactCellTree :=
  .split 14
    (.cell 81 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 160, 163,
      162, 177, 188, 189])
    (.split 15
        (.cell 82 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206, 266,
          208, 268, 210, 211])
        (.split 27
            (.cell 83 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240,
              227, 228, 269, 230, 271, 232, 233])
            (.split 28
                (.cell 84 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 258, 274, 260, 276, 262, 263])
                (.split 29
                    (.cell 85 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      290, 291, 292, 293, 296, 295, 298, 392, 393])
                    (.absurd 299)))))

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 86, 87, 88, 89, 90, 91, 92, 93, 94, 95 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart25 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 86 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 206,
          266, 208, 328, 210, 211])
        (.split 15
            (.cell 87 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228,
              269, 230, 447, 232, 233])
            (.split 27
                (.cell 88 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 258, 274, 260, 448, 262, 263])
                (.split 28
                    (.cell 89 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 293, 296, 295, 451, 392, 393])
                    (.split 29
                        (.cell 90 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                          452, 453, 388, 381, 395, 385, 454, 397, 398])
                        (.absurd 455))))))
    (.split 32
        (.split 14
            (.cell 91 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456,
              228, 269, 230, 231, 345, 225])
            (.split 15
                (.cell 92 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257,
                  258, 274, 260, 351, 457, 364])
                (.split 27
                    (.cell 93 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 293, 296, 295, 354, 458, 365])
                    (.split 28
                        (.cell 94 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                          459, 460, 388, 381, 395, 385, 461, 462, 382])
                        (.split 29
                            (.cell 95 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                              411, 463, 464, 419, 413, 415, 417, 465, 466, 467])
                            (.absurd 468))))))
        (.absurd 469))

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 347 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart26 : CompactCellTree :=
  .absurd 347

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 359 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart27 : CompactCellTree :=
  .absurd 359

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 96, 97, 98, 99, 100 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart28 : CompactCellTree :=
  .split 14
    (.cell 96 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 160, 187,
      316, 317, 162, 177])
    (.split 15
        (.cell 97 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209,
          318, 319, 208, 268])
        (.split 27
            (.cell 98 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240,
              227, 228, 231, 321, 322, 230, 271])
            (.split 28
                (.cell 99 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 258, 351, 324, 325, 260, 276])
                (.split 29
                    (.cell 100 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      290, 291, 292, 293, 354, 355, 356, 295, 298])
                    (.absurd 299)))))

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 363 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart29 : CompactCellTree :=
  .absurd 363

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 101, 102, 103, 104, 105 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart30 : CompactCellTree :=
  .split 14
    (.cell 101 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 228,
      231, 321, 322, 230, 225, 232, 233])
    (.split 15
        (.cell 102 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 258, 351,
          324, 325, 260, 364, 262, 263])
        (.split 27
            (.cell 103 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              292, 293, 354, 355, 356, 295, 365, 392, 393])
            (.split 28
                (.cell 104 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 381, 461, 383, 384, 385, 382, 397, 398])
                (.split 29
                    (.cell 105 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      463, 464, 419, 413, 465, 470, 471, 417, 467, 472, 473])
                    (.absurd 468)))))

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 106, 107, 108, 109, 110, 111, 112, 113, 114, 115 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart31 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 106 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474, 258,
          351, 324, 325, 260, 255, 262, 263])
        (.split 15
            (.cell 107 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 293,
              354, 355, 356, 295, 335, 392, 393])
            (.split 27
                (.cell 108 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 381, 461, 383, 384, 385, 475, 397, 398])
                (.split 28
                    (.cell 109 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 419, 413, 465, 470, 471, 417, 478, 472, 473])
                    (.split 29
                        (.cell 110 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 479, 480, 441, 434, 481, 482, 483, 438, 484, 485, 486])
                        (.absurd 487))))))
    (.split 32
        (.split 14
            (.cell 111 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 488,
              293, 354, 355, 356, 295, 298, 357, 290])
            (.split 15
                (.cell 112 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 388,
                  381, 461, 383, 384, 385, 386, 489, 396])
                (.split 27
                    (.cell 113 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 419, 413, 465, 470, 471, 417, 490, 491, 416])
                    (.split 28
                        (.cell 114 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 492, 493, 441, 434, 481, 482, 483, 438, 439, 494, 437])
                        (.split 29
                            (.cell 115 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                              507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518])
                            (.absurd 519))))))
        (.absurd 520))

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 521 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart32 : CompactCellTree :=
  .absurd 521

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 116, 117, 118, 119, 120 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart33 : CompactCellTree :=
  .split 14
    (.cell 116 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 206,
      238, 318, 319, 208, 328])
    (.split 15
        (.cell 117 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 241,
          321, 322, 230, 447])
        (.split 27
            (.cell 118 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273,
              257, 258, 261, 324, 325, 260, 448])
            (.split 28
                (.cell 119 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 293, 522, 355, 356, 295, 451])
                (.split 29
                    (.cell 120 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      452, 453, 388, 381, 523, 383, 384, 385, 454])
                    (.absurd 455)))))

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 524 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart34 : CompactCellTree :=
  .absurd 524

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 525 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart35 : CompactCellTree :=
  .absurd 525

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 2,
      -2, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - length[5] - 2 * length[7]` in the row-06 symmetry chamber,
with leaves selecting cells 121, 122, 123 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart36 : CompactCellTree :=
  .split 8
    (.cell 121 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 293, 522,
      355, 356, 295, 292, 392, 393])
    (.split 30
        (.cell 122 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 396, 381, 523,
          383, 384, 385, 388, 397, 398])
        (.split 32
            (.cell 123 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 416, 413,
              526, 470, 471, 417, 527, 528, 419])
            (.absurd 529)))

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells
      (((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 2,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - 2 * length[2] + length[3]` in the row-06 symmetry
chamber, with leaves selecting cells 124, 125, 126, 127, 128, 129, 130, 131, 132 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart37 : CompactCellTree :=
  .split 27
    (.split 8
        (.cell 124 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459, 460, 452,
          381, 523, 383, 384, 385, 388, 397, 398])
        (.split 30
            (.cell 125 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476, 477,
              530, 413, 526, 470, 471, 417, 419, 472, 473])
            (.split 32
                (.cell 126 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 492,
                  493, 531, 434, 532, 482, 483, 438, 533, 534, 441])
                (.absurd 535))))
    (.split 28
        (.split 8
            (.cell 127 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476, 477,
              463, 413, 526, 470, 471, 417, 419, 472, 473])
            (.split 30
                (.cell 128 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 492,
                  493, 536, 434, 532, 482, 483, 438, 441, 485, 486])
                (.split 32
                    (.cell 129 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507,
                      537, 538, 539, 511, 540, 513, 514, 515, 541, 542, 510])
                    (.absurd 543))))
        (.split 29
            (.split 8
                (.cell 130 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 536,
                  480, 479, 434, 532, 482, 483, 438, 441, 485, 486])
                (.split 30
                    (.cell 131 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507,
                      539, 509, 544, 511, 540, 513, 514, 515, 510, 545, 546])
                    (.split 32
                        (.cell 132 [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558,
                          559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570])
                        (.absurd 571))))
            (.absurd 468)))

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells
      (((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 521 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart38 : CompactCellTree :=
  .absurd 521

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 133, 134, 135, 136, 137 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart39 : CompactCellTree :=
  .split 14
    (.cell 133 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 228,
      331, 269, 447, 230, 225])
    (.split 15
        (.cell 134 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 258, 333,
          274, 448, 260, 364])
        (.split 27
            (.cell 135 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              292, 293, 336, 296, 451, 295, 365])
            (.split 28
                (.cell 136 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 381, 572, 395, 454, 385, 382])
                (.split 29
                    (.cell 137 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      463, 464, 419, 413, 573, 415, 527, 417, 467])
                    (.absurd 468)))))

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 574 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart40 : CompactCellTree :=
  .absurd 574

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 575 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart41 : CompactCellTree :=
  .absurd 575

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells
      (((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - length[5] - 2 * length[7]` in the row-06 symmetry chamber,
with leaves selecting cells 138, 139, 140 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart42 : CompactCellTree :=
  .split 8
    (.cell 138 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 452, 381, 572,
      395, 454, 385, 388, 397, 398])
    (.split 30
        (.cell 139 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 530, 413, 573,
          415, 527, 417, 419, 472, 473])
        (.split 32
            (.cell 140 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 531, 434,
              576, 436, 533, 438, 577, 534, 441])
            (.absurd 535)))

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells
      ((((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 2,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - 2 * length[2] + length[3]` in the row-06 symmetry
chamber, with leaves selecting cells 141, 142, 143, 144, 145, 146, 147, 148, 149 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart43 : CompactCellTree :=
  .split 27
    (.split 8
        (.cell 141 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476, 477, 463,
          413, 573, 415, 527, 417, 419, 472, 473])
        (.split 30
            (.cell 142 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 492, 493,
              536, 434, 576, 436, 533, 438, 441, 485, 486])
            (.split 32
                (.cell 143 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 537,
                  538, 539, 511, 578, 579, 541, 515, 580, 542, 510])
                (.absurd 543))))
    (.split 28
        (.split 8
            (.cell 144 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 492, 493,
              479, 434, 576, 436, 533, 438, 441, 485, 486])
            (.split 30
                (.cell 145 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 537,
                  538, 544, 511, 578, 579, 541, 515, 510, 545, 546])
                (.split 32
                    (.cell 146 [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559,
                      581, 582, 562, 563, 583, 584, 568, 567, 585, 569, 570])
                    (.absurd 571))))
        (.split 29
            (.split 8
                (.cell 147 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 544,
                  509, 508, 511, 578, 579, 541, 515, 510, 545, 546])
                (.split 30
                    (.cell 148 [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559,
                      562, 561, 586, 563, 583, 584, 568, 567, 570, 587, 588])
                    (.split 32
                        (.cell 149 [589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600,
                          601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612])
                        (.absurd 613))))
            (.absurd 487)))

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells
      ((((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 614 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart44 : CompactCellTree :=
  .absurd 614

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[8] - 2 * length[9]` in the row-06 symmetry chamber, with leaves
selecting cells 0, 150, 151, 152, 153, 154 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart45 : CompactCellTree :=
  .split 17
    (.cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 17, 615, 14, 16, 15])
    (.split 18
        (.cell 150 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 36, 31, 33, 35, 34])
        (.split 19
            (.cell 150 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 616, 617, 53, 52])
            (.split 20
                (.cell 151 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 74, 70, 618, 619,
                  620, 73, 72])
                (.split 21
                    (.cell 152 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 90, 621,
                      304, 622, 93, 92])
                    (.split 34
                        (.cell 153 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
                          114, 110, 623, 624, 113, 112])
                        (.split 22
                            (.cell 154 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
                              139, 308, 625, 626, 145, 627, 143, 142])
                            (.absurd 628)))))))

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++
      [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 629 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart46 : CompactCellTree :=
  .absurd 629

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 155, 156, 157, 158, 159 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart47 : CompactCellTree :=
  .split 14
    (.cell 155 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 630, 631, 51, 53, 52])
    (.split 15
        (.cell 156 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 632, 71, 73, 72])
        (.split 27
            (.cell 157 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 633, 91,
              93, 92])
            (.split 28
                (.cell 158 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 171, 172,
                  110, 634, 111, 113, 112])
                (.split 29
                    (.cell 159 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                      236, 635, 145, 625, 141, 143, 142])
                    (.absurd 636)))))

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 637 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart48 : CompactCellTree :=
  .absurd 637

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 160, 161, 162, 163, 164 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart49 : CompactCellTree :=
  .split 14
    (.cell 160 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 638, 639, 621, 304, 640,
      93, 92])
    (.split 15
        (.cell 161 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 641, 642, 306,
          643, 113, 112])
        (.split 27
            (.cell 162 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174, 175,
              145, 644, 645, 315, 646, 143, 142])
            (.split 28
                (.cell 163 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 647, 648, 317, 649, 162, 161])
                (.split 29
                    (.cell 164 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      328, 650, 205, 651, 652, 319, 653, 208, 207])
                    (.absurd 654)))))

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[8] + 2 * length[9] - length[10]` in the row-06 symmetry
chamber, with leaves selecting cells 165, 166, 167, 168, 169, 170, 171, 172, 173, 174 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart50 : CompactCellTree :=
  .split 21
    (.split 14
        (.cell 165 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 108, 642,
          306, 655, 113, 112])
        (.split 15
            (.cell 166 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 182,
              645, 315, 656, 143, 142])
            (.split 27
                (.cell 167 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 187, 648, 317, 657, 162, 161])
                (.split 28
                    (.cell 168 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 204, 205, 209, 652, 319, 658, 208, 207])
                    (.split 29
                        (.cell 169 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 225, 226, 227, 231, 659, 322, 660, 230, 229])
                        (.absurd 234))))))
    (.split 22
        (.split 14
            (.cell 170 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235,
              625, 626, 236, 627, 143, 142])
            (.split 15
                (.cell 171 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165,
                  661, 662, 237, 663, 162, 161])
                (.split 27
                    (.cell 172 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 204, 205, 664, 665, 238, 666, 208, 207])
                    (.split 28
                        (.cell 173 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 239, 240, 227, 667, 668, 241, 669, 230, 229])
                        (.split 29
                            (.cell 174 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                              254, 255, 256, 257, 670, 671, 261, 672, 260, 259])
                            (.absurd 264))))))
        (.absurd 673))

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 629 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart51 : CompactCellTree :=
  .absurd 629

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0,
      0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 150, 175, 176, 177, 178, 179 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart52 : CompactCellTree :=
  .split 5
    (.cell 150 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 631, 51, 53, 674])
    (.split 6
        (.cell 175 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 74, 632, 71, 73, 70])
        (.split 7
            (.cell 175 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 633, 91, 93, 675])
            (.split 8
                (.cell 176 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 114, 634,
                  111, 113, 110, 125, 126])
                (.split 30
                    (.cell 177 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                      308, 625, 141, 143, 145, 183, 184])
                    (.split 31
                        (.cell 178 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157,
                          158, 310, 661, 160, 162, 676, 165])
                        (.split 32
                            (.cell 179 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                              202, 320, 664, 206, 208, 651, 677, 205])
                            (.absurd 678)))))))

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 637 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart53 : CompactCellTree :=
  .absurd 637

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 151, 180, 181, 182, 183, 184 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart54 : CompactCellTree :=
  .split 5
    (.cell 151 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 639, 621, 304, 640, 93,
      679])
    (.split 6
        (.cell 180 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 114, 641, 642, 306,
          643, 113, 110])
        (.split 7
            (.cell 180 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 308, 644,
              645, 315, 646, 143, 680])
            (.split 8
                (.cell 181 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 310,
                  647, 648, 317, 649, 162, 165, 188, 189])
                (.split 30
                    (.cell 182 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      320, 651, 652, 319, 653, 208, 205, 210, 211])
                    (.split 31
                        (.cell 183 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 323, 681, 659, 322, 682, 230, 683, 227])
                        (.split 32
                            (.cell 184 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                              254, 326, 684, 685, 325, 686, 260, 261, 687, 257])
                            (.absurd 688)))))))

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 152, 185, 186, 187, 188, 189 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart55 : CompactCellTree :=
  .split 5
    (.cell 152 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 114, 108, 642, 306,
      655, 113, 348])
    (.split 6
        (.cell 185 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 308, 182, 645,
          315, 656, 143, 145])
        (.split 7
            (.cell 185 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 310, 187,
              648, 317, 657, 162, 349])
            (.split 8
                (.cell 186 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 320,
                  209, 652, 319, 658, 208, 205, 210, 211])
                (.split 30
                    (.cell 187 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      323, 231, 659, 322, 660, 230, 227, 232, 233])
                    (.split 31
                        (.cell 188 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                          254, 326, 351, 685, 325, 689, 260, 352, 257])
                        (.split 32
                            (.cell 189 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 337, 354, 690, 356, 691, 295, 298, 357, 292])
                            (.absurd 692)))))))

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] + length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 190, 191, 192, 193, 194 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart56 : CompactCellTree :=
  .split 5
    (.absurd 693)
    (.split 34
        (.absurd 694)
        (.split 22
            (.split 6
                (.cell 190 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 320,
                  664, 665, 328, 666, 208, 205])
                (.split 7
                    (.cell 190 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      323, 667, 668, 447, 669, 230, 695])
                    (.split 8
                        (.cell 191 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                          254, 326, 670, 671, 448, 672, 260, 257, 262, 263])
                        (.split 30
                            (.cell 192 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 337, 696, 697, 451, 698, 295, 292, 392, 393])
                            (.split 31
                                (.cell 193 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377,
                                  378, 379, 699, 700, 701, 454, 702, 385, 703, 388])
                                (.split 32
                                    (.cell 194 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408,
                                      409, 410, 411, 704, 705, 706, 527, 707, 417, 467, 708, 419])
                                    (.absurd 709)))))))
            (.absurd 710)))

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 629 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart57 : CompactCellTree :=
  .absurd 629

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells
      (((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0,
      0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 711 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart58 : CompactCellTree :=
  .absurd 711

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 195, 196, 197, 198, 199 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart59 : CompactCellTree :=
  .split 14
    (.cell 195 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 638, 633, 91, 93, 639])
    (.split 15
        (.cell 196 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 634, 111, 113,
          641])
        (.split 27
            (.cell 197 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174, 175,
              145, 625, 141, 143, 644])
            (.split 28
                (.cell 198 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 661, 160, 162, 647])
                (.split 29
                    (.cell 199 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      328, 650, 205, 664, 206, 208, 651])
                    (.absurd 654)))))

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1,
      0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 712 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart60 : CompactCellTree :=
  .absurd 712

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1,
      0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 200, 201, 202, 203, 204 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart61 : CompactCellTree :=
  .split 14
    (.cell 200 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 625,
      141, 143, 236, 183, 184])
    (.split 15
        (.cell 201 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 661, 160,
          162, 237, 188, 189])
        (.split 27
            (.cell 202 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
              205, 664, 206, 208, 238, 210, 211])
            (.split 28
                (.cell 203 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 667, 228, 230, 241, 232, 233])
                (.split 29
                    (.cell 204 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      255, 256, 257, 670, 258, 260, 261, 262, 263])
                    (.absurd 264)))))

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0,
      1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 205, 206, 207, 208, 209, 210, 211, 212, 213, 214 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart62 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 205 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 661,
          160, 162, 177, 188, 189])
        (.split 15
            (.cell 206 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 664,
              206, 208, 268, 210, 211])
            (.split 27
                (.cell 207 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 667, 228, 230, 271, 232, 233])
                (.split 28
                    (.cell 208 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      272, 273, 257, 670, 258, 260, 276, 262, 263])
                    (.split 29
                        (.cell 209 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                          289, 290, 291, 292, 696, 293, 295, 298, 392, 393])
                        (.absurd 299))))))
    (.split 32
        (.split 14
            (.cell 210 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446,
              664, 206, 208, 651, 677, 328])
            (.split 15
                (.cell 211 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227,
                  667, 228, 230, 681, 713, 447])
                (.split 27
                    (.cell 212 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      272, 273, 257, 670, 258, 260, 684, 714, 448])
                    (.split 28
                        (.cell 213 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                          289, 449, 450, 292, 696, 293, 295, 715, 716, 451])
                        (.split 29
                            (.cell 214 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                              379, 452, 453, 388, 700, 381, 385, 717, 718, 454])
                            (.absurd 455))))))
        (.absurd 719))

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0,
      1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 637 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart63 : CompactCellTree :=
  .absurd 637

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 720 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart64 : CompactCellTree :=
  .absurd 720

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 215, 216, 217, 218, 219 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart65 : CompactCellTree :=
  .split 14
    (.cell 215 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 644,
      645, 315, 646, 143, 236])
    (.split 15
        (.cell 216 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 647, 648,
          317, 649, 162, 237])
        (.split 27
            (.cell 217 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
              205, 651, 652, 319, 653, 208, 238])
            (.split 28
                (.cell 218 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 681, 659, 322, 682, 230, 241])
                (.split 29
                    (.cell 219 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      255, 256, 257, 684, 685, 325, 686, 260, 261])
                    (.absurd 264)))))

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 721 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart66 : CompactCellTree :=
  .absurd 721

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 220, 221, 222, 223, 224 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart67 : CompactCellTree :=
  .split 14
    (.cell 220 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 651,
      652, 319, 653, 208, 328, 210, 211])
    (.split 15
        (.cell 221 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 681, 659,
          322, 682, 230, 447, 232, 233])
        (.split 27
            (.cell 222 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273,
              257, 684, 685, 325, 686, 260, 448, 262, 263])
            (.split 28
                (.cell 223 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 715, 690, 356, 722, 295, 451, 392, 393])
                (.split 29
                    (.cell 224 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      452, 453, 388, 717, 723, 384, 724, 385, 454, 397, 398])
                    (.absurd 455)))))

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 225, 226, 227, 228, 229, 230, 231, 232, 233, 234 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart68 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 225 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 681,
          659, 322, 682, 230, 225, 232, 233])
        (.split 15
            (.cell 226 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 684,
              685, 325, 686, 260, 364, 262, 263])
            (.split 27
                (.cell 227 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 715, 690, 356, 722, 295, 365, 392, 393])
                (.split 28
                    (.cell 228 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 388, 717, 723, 384, 724, 385, 382, 397, 398])
                    (.split 29
                        (.cell 229 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 463, 464, 419, 725, 726, 471, 727, 417, 467, 472, 473])
                        (.absurd 468))))))
    (.split 32
        (.split 14
            (.cell 230 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474,
              684, 685, 325, 686, 260, 261, 687, 255])
            (.split 15
                (.cell 231 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292,
                  715, 690, 356, 722, 295, 522, 728, 335])
                (.split 27
                    (.cell 232 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 388, 717, 723, 384, 724, 385, 523, 729, 475])
                    (.split 28
                        (.cell 233 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 476, 477, 419, 725, 726, 471, 727, 417, 526, 730, 478])
                        (.split 29
                            (.cell 234 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                              432, 479, 480, 441, 731, 732, 483, 733, 438, 532, 734, 484])
                            (.absurd 487))))))
        (.absurd 735))

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 693 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart69 : CompactCellTree :=
  .absurd 693

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 235, 236, 237, 238, 239 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart70 : CompactCellTree :=
  .split 14
    (.cell 235 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 187,
      648, 317, 657, 162, 177])
    (.split 15
        (.cell 236 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 209, 652,
          319, 658, 208, 268])
        (.split 27
            (.cell 237 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240,
              227, 231, 659, 322, 660, 230, 271])
            (.split 28
                (.cell 238 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 351, 685, 325, 689, 260, 276])
                (.split 29
                    (.cell 239 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      290, 291, 292, 354, 690, 356, 691, 295, 298])
                    (.absurd 299)))))

theorem treePart70_check :
    treePart70.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 736 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart71 : CompactCellTree :=
  .absurd 736

theorem treePart71_check :
    treePart71.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 240, 241, 242, 243, 244 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart72 : CompactCellTree :=
  .split 14
    (.cell 240 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 231,
      659, 322, 660, 230, 225, 232, 233])
    (.split 15
        (.cell 241 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 351, 685,
          325, 689, 260, 364, 262, 263])
        (.split 27
            (.cell 242 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              292, 354, 690, 356, 691, 295, 365, 392, 393])
            (.split 28
                (.cell 243 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 461, 723, 384, 737, 385, 382, 397, 398])
                (.split 29
                    (.cell 244 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      463, 464, 419, 465, 726, 471, 738, 417, 467, 472, 473])
                    (.absurd 468)))))

theorem treePart72_check :
    treePart72.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[5] - 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 245, 246, 247, 248, 249, 250, 251, 252, 253 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart73 : CompactCellTree :=
  .split 30
    (.split 14
        (.cell 245 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474, 351,
          685, 325, 689, 260, 255, 262, 263])
        (.split 15
            (.cell 246 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 354,
              690, 356, 691, 295, 335, 392, 393])
            (.split 27
                (.cell 247 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 461, 723, 384, 737, 385, 475, 397, 398])
                (.split 28
                    (.cell 248 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 419, 465, 726, 471, 738, 417, 478, 472, 473])
                    (.split 29
                        (.cell 249 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 479, 480, 441, 481, 732, 483, 739, 438, 484, 485, 486])
                        (.absurd 487))))))
    (.split 14
        (.absurd 740)
        (.split 15
            (.split 32
                (.cell 250 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 452,
                  461, 723, 384, 737, 385, 386, 489, 388])
                (.absurd 741))
            (.split 27
                (.split 32
                    (.cell 251 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 463, 465, 726, 471, 738, 417, 490, 491, 419])
                    (.absurd 742))
                (.split 28
                    (.split 32
                        (.cell 252 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 492, 493, 479, 481, 732, 483, 739, 438, 439, 494, 441])
                        (.absurd 743))
                    (.split 29
                        (.split 32
                            (.cell 253 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                              507, 544, 509, 508, 512, 744, 514, 745, 515, 516, 517, 510])
                            (.absurd 746))
                        (.absurd 487))))))

theorem treePart73_check :
    treePart73.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 693 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart74 : CompactCellTree :=
  .absurd 693

theorem treePart74_check :
    treePart74.check splitForms farkasReceipts cells
      ((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, -2, 0, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[8] - length[9] + length[11]` in the row-06 symmetry
chamber, with leaves selecting cells 254, 255, 256, 257, 258 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart75 : CompactCellTree :=
  .split 22
    (.split 14
        (.cell 254 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 664,
          665, 328, 666, 208, 268])
        (.split 15
            (.cell 255 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 667,
              668, 447, 669, 230, 271])
            (.split 27
                (.cell 256 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 670, 671, 448, 672, 260, 276])
                (.split 28
                    (.cell 257 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 696, 697, 451, 698, 295, 298])
                    (.split 29
                        (.cell 258 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                          379, 452, 453, 388, 700, 701, 454, 702, 385, 386])
                        (.absurd 455))))))
    (.absurd 747)

theorem treePart75_check :
    treePart75.check splitForms farkasReceipts cells
      (((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -1, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 736 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart76 : CompactCellTree :=
  .absurd 736

theorem treePart76_check :
    treePart76.check splitForms farkasReceipts cells
      ((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, 0, 0, 2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 259, 260, 261, 262, 263 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart77 : CompactCellTree :=
  .split 14
    (.cell 259 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474, 670,
      671, 364, 672, 260, 255, 262, 263])
    (.split 15
        (.cell 260 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 696, 697,
          365, 698, 295, 335, 392, 393])
        (.split 27
            (.cell 261 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459, 460,
              388, 700, 701, 382, 702, 385, 475, 397, 398])
            (.split 28
                (.cell 262 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476,
                  477, 419, 705, 706, 467, 707, 417, 478, 472, 473])
                (.split 29
                    (.cell 263 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      479, 480, 441, 748, 749, 577, 750, 438, 484, 485, 486])
                    (.absurd 487)))))

theorem treePart77_check :
    treePart77.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 264, 265, 266, 267, 268, 269, 270, 271 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart78 : CompactCellTree :=
  .split 14
    (.absurd 740)
    (.split 15
        (.split 30
            (.cell 264 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 452, 700,
              701, 382, 702, 385, 388, 397, 398])
            (.split 32
                (.cell 265 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 530,
                  705, 706, 467, 707, 417, 490, 528, 419])
                (.absurd 751)))
        (.split 27
            (.split 30
                (.cell 266 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476,
                  477, 463, 705, 706, 467, 707, 417, 419, 472, 473])
                (.split 32
                    (.cell 267 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      492, 493, 536, 748, 749, 577, 750, 438, 439, 534, 441])
                    (.absurd 752)))
            (.split 28
                (.split 30
                    (.cell 268 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      492, 493, 479, 748, 749, 577, 750, 438, 441, 485, 486])
                    (.split 32
                        (.cell 269 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                          507, 537, 538, 544, 753, 754, 580, 755, 515, 516, 542, 510])
                        (.absurd 756)))
                (.split 29
                    (.split 30
                        (.cell 270 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                          507, 544, 509, 508, 753, 754, 580, 755, 515, 510, 545, 546])
                        (.split 32
                            (.cell 271 [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558,
                              559, 562, 561, 586, 757, 758, 585, 759, 567, 760, 569, 570])
                            (.absurd 761)))
                    (.absurd 487)))))

theorem treePart78_check :
    treePart78.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, -1, 0, -2, 0, 0,
      0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 762 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart79 : CompactCellTree :=
  .absurd 762

theorem treePart79_check :
    treePart79.check splitForms farkasReceipts cells
      (((((((((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      -1, 0, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 0, 272, 273, 274, 275 and Farkas receipts excluding inconsistent sign branches. -/
def treePart80 : CompactCellTree :=
  .split 23
    (.cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 17, 14, 15, 763, 16])
    (.split 24
        (.cell 272 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 36, 33, 34, 31, 35])
        (.split 25
            (.cell 272 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 51, 52, 764, 765])
            (.split 26
                (.cell 273 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 74, 71, 72, 766,
                  767, 70, 768])
                (.split 35
                    (.cell 274 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 91, 92,
                      123, 769, 90, 770])
                    (.split 36
                        (.cell 275 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107,
                          114, 111, 112, 771, 634, 110, 772])
                        (.absurd 773))))))

theorem treePart80_check :
    treePart80.check splitForms farkasReceipts cells
      ((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]]) ++
      [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 774 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart81 : CompactCellTree :=
  .absurd 774

theorem treePart81_check :
    treePart81.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 276, 277, 278, 279, 280 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart82 : CompactCellTree :=
  .split 14
    (.cell 276 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 630, 51, 52, 631, 53])
    (.split 15
        (.cell 277 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 71, 72, 632, 73])
        (.split 27
            (.cell 278 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92,
              633, 93])
            (.split 28
                (.cell 279 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 171, 172,
                  110, 111, 112, 634, 113])
                (.split 29
                    (.cell 280 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                      236, 635, 145, 141, 142, 625, 143])
                    (.absurd 636)))))

theorem treePart82_check :
    treePart82.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 775 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart83 : CompactCellTree :=
  .absurd 775

theorem treePart83_check :
    treePart83.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 281, 282, 283, 284, 285 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart84 : CompactCellTree :=
  .split 14
    (.cell 281 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 638, 91, 92, 123, 769, 639,
      776])
    (.split 15
        (.cell 282 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 111, 112, 126,
          777, 641, 778])
        (.split 27
            (.cell 283 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174, 175,
              145, 141, 142, 184, 779, 644, 780])
            (.split 28
                (.cell 284 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 160, 161, 189, 781, 647, 782])
                (.split 29
                    (.cell 285 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      328, 650, 205, 206, 207, 211, 783, 651, 784])
                    (.absurd 654)))))

theorem treePart84_check :
    treePart84.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 286, 287, 288, 289, 290, 291, 292, 293, 294, 295 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart85 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 286 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 111, 112,
          126, 777, 108, 785])
        (.split 15
            (.cell 287 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 141,
              142, 184, 779, 182, 786])
            (.split 27
                (.cell 288 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 160, 161, 189, 781, 187, 787])
                (.split 28
                    (.cell 289 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 204, 205, 206, 207, 211, 783, 209, 788])
                    (.split 29
                        (.cell 290 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 225, 226, 227, 228, 229, 233, 789, 231, 790])
                        (.absurd 234))))))
    (.split 36
        (.split 14
            (.cell 291 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235,
              141, 142, 791, 625, 236, 792])
            (.split 15
                (.cell 292 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165,
                  160, 161, 793, 661, 237, 794])
                (.split 27
                    (.cell 293 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 204, 205, 206, 207, 795, 664, 238, 796])
                    (.split 28
                        (.cell 294 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 239, 240, 227, 228, 229, 797, 667, 241, 798])
                        (.split 29
                            (.cell 295 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                              254, 255, 256, 257, 258, 259, 799, 670, 261, 800])
                            (.absurd 264))))))
        (.absurd 773))

theorem treePart85_check :
    treePart85.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0]])
      ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 801 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart86 : CompactCellTree :=
  .absurd 801

theorem treePart86_check :
    treePart86.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 1, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 31, 296, 297, 298, 299 and Farkas receipts excluding inconsistent sign branches. -/
def treePart87 : CompactCellTree :=
  .split 23
    (.cell 31 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 51, 631, 802, 53])
    (.split 24
        (.cell 296 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 74, 71, 632, 70, 73])
        (.split 25
            (.cell 296 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 91, 633, 803, 804])
            (.split 26
                (.cell 297 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 114, 111,
                  634, 126, 777, 110, 805])
                (.split 35
                    (.cell 298 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                      308, 141, 625, 184, 779, 145, 806])
                    (.split 36
                        (.cell 299 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157,
                          158, 310, 160, 661, 807, 647, 165, 808])
                        (.absurd 809))))))

theorem treePart87_check :
    treePart87.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 810 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart88 : CompactCellTree :=
  .absurd 810

theorem treePart88_check :
    treePart88.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 32, 300, 301, 302, 303 and Farkas receipts excluding inconsistent sign branches. -/
def treePart89 : CompactCellTree :=
  .split 23
    (.cell 32 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 91, 639, 303, 304, 811, 93])
    (.split 24
        (.cell 300 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 114, 111, 641, 305,
          306, 110, 113])
        (.split 25
            (.cell 300 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 308, 141,
              644, 314, 315, 812, 813])
            (.split 26
                (.cell 301 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 310,
                  160, 647, 316, 317, 189, 781, 165, 814])
                (.split 35
                    (.cell 302 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      320, 206, 651, 318, 319, 211, 783, 205, 815])
                    (.split 36
                        (.cell 303 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 323, 228, 681, 321, 322, 816, 241, 227, 817])
                        (.absurd 818))))))

theorem treePart89_check :
    treePart89.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 304, 305, 306, 307, 308, 309, 310, 311 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart90 : CompactCellTree :=
  .split 23
    (.absurd 819)
    (.split 13
        (.split 24
            (.cell 304 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 308, 141,
              236, 314, 315, 145, 143])
            (.split 25
                (.cell 304 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 310,
                  160, 237, 316, 317, 820, 821])
                (.split 26
                    (.cell 305 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      320, 206, 238, 318, 319, 211, 783, 205, 822])
                    (.split 35
                        (.cell 306 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 323, 228, 241, 321, 322, 233, 789, 227, 823])
                        (.split 36
                            (.cell 307 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                              254, 326, 258, 261, 324, 325, 824, 276, 257, 825])
                            (.absurd 826))))))
        (.split 33
            (.absurd 827)
            (.split 16
                (.split 24
                    (.cell 308 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      320, 206, 329, 664, 328, 205, 208])
                    (.split 25
                        (.cell 308 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
                          224, 323, 228, 331, 667, 447, 828, 829])
                        (.split 26
                            (.cell 309 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                              254, 326, 258, 333, 670, 448, 263, 830, 257, 831])
                            (.split 35
                                (.cell 310 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287,
                                  288, 289, 337, 293, 336, 696, 451, 393, 832, 292, 833])
                                (.split 36
                                    (.cell 311 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376,
                                      377, 378, 379, 699, 381, 572, 700, 454, 834, 382, 388, 835])
                                    (.absurd 836))))))
                (.absurd 311))))

theorem treePart90_check :
    treePart90.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 801 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart91 : CompactCellTree :=
  .absurd 801

theorem treePart91_check :
    treePart91.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 837 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart92 : CompactCellTree :=
  .absurd 837

theorem treePart92_check :
    treePart92.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true
      := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 312, 313, 314, 315, 316 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart93 : CompactCellTree :=
  .split 14
    (.cell 312 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 638, 91, 633, 639, 93])
    (.split 15
        (.cell 313 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 111, 634, 641,
          113])
        (.split 27
            (.cell 314 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174, 175,
              145, 141, 625, 644, 143])
            (.split 28
                (.cell 315 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185,
                  186, 165, 160, 661, 647, 162])
                (.split 29
                    (.cell 316 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      328, 650, 205, 206, 664, 651, 208])
                    (.absurd 654)))))

theorem treePart93_check :
    treePart93.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2,
      0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 838 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart94 : CompactCellTree :=
  .absurd 838

theorem treePart94_check :
    treePart94.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0,
      -2, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 317, 318, 319, 320, 321 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart95 : CompactCellTree :=
  .split 14
    (.cell 317 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 141,
      625, 184, 779, 236, 839])
    (.split 15
        (.cell 318 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 160, 661,
          189, 781, 237, 840])
        (.split 27
            (.cell 319 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
              205, 206, 664, 211, 783, 238, 841])
            (.split 28
                (.cell 320 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 228, 667, 233, 789, 241, 842])
                (.split 29
                    (.cell 321 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      255, 256, 257, 258, 670, 263, 830, 261, 843])
                    (.absurd 264)))))

theorem treePart95_check :
    treePart95.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0,
      -2, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0,
      0, -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 322, 323, 324, 325, 326, 327, 328, 329, 330, 331 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart96 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 322 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 160,
          661, 189, 781, 177, 844])
        (.split 15
            (.cell 323 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206,
              664, 211, 783, 268, 845])
            (.split 27
                (.cell 324 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 228, 667, 233, 789, 271, 846])
                (.split 28
                    (.cell 325 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      272, 273, 257, 258, 670, 263, 830, 276, 847])
                    (.split 29
                        (.cell 326 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                          289, 290, 291, 292, 293, 696, 393, 832, 298, 848])
                        (.absurd 299))))))
    (.split 36
        (.split 14
            (.cell 327 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446,
              206, 664, 849, 651, 328, 850])
            (.split 15
                (.cell 328 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227,
                  228, 667, 851, 681, 447, 852])
                (.split 27
                    (.cell 329 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      272, 273, 257, 258, 670, 853, 684, 448, 854])
                    (.split 28
                        (.cell 330 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                          289, 449, 450, 292, 293, 696, 855, 715, 451, 856])
                        (.split 29
                            (.cell 331 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                              379, 452, 453, 388, 381, 700, 857, 717, 454, 858])
                            (.absurd 455))))))
        (.absurd 809))

theorem treePart96_check :
    treePart96.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0,
      -2, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 810 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart97 : CompactCellTree :=
  .absurd 810

theorem treePart97_check :
    treePart97.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 819 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart98 : CompactCellTree :=
  .absurd 819

theorem treePart98_check :
    treePart98.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 332, 333, 334, 335, 336 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart99 : CompactCellTree :=
  .split 14
    (.cell 332 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 141,
      644, 314, 315, 236, 143])
    (.split 15
        (.cell 333 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 160, 647,
          316, 317, 237, 162])
        (.split 27
            (.cell 334 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
              205, 206, 651, 318, 319, 238, 208])
            (.split 28
                (.cell 335 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 228, 681, 321, 322, 241, 230])
                (.split 29
                    (.cell 336 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      255, 256, 257, 258, 684, 324, 325, 261, 260])
                    (.absurd 264)))))

theorem treePart99_check :
    treePart99.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 859 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart100 : CompactCellTree :=
  .absurd 859

theorem treePart100_check :
    treePart100.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 337, 338, 339, 340, 341 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart101 : CompactCellTree :=
  .split 14
    (.cell 337 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 206,
      651, 318, 319, 211, 783, 328, 860])
    (.split 15
        (.cell 338 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 681,
          321, 322, 233, 789, 447, 861])
        (.split 27
            (.cell 339 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273,
              257, 258, 684, 324, 325, 263, 830, 448, 862])
            (.split 28
                (.cell 340 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 293, 715, 355, 356, 393, 832, 451, 863])
                (.split 29
                    (.cell 341 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      452, 453, 388, 381, 717, 383, 384, 398, 864, 454, 865])
                    (.absurd 455)))))

theorem treePart101_check :
    treePart101.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 342, 343, 344, 345, 346, 347, 348, 349, 350 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart102 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 342 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 228,
          681, 321, 322, 233, 789, 225, 866])
        (.split 15
            (.cell 343 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 258,
              684, 324, 325, 263, 830, 364, 867])
            (.split 27
                (.cell 344 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 293, 715, 355, 356, 393, 832, 365, 868])
                (.split 28
                    (.cell 345 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 388, 381, 717, 383, 384, 398, 864, 382, 869])
                    (.split 29
                        (.cell 346 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 463, 464, 419, 413, 725, 470, 471, 473, 870, 467, 871])
                        (.absurd 468))))))
    (.split 14
        (.absurd 574)
        (.split 15
            (.split 36
                (.cell 347 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290,
                  293, 715, 355, 356, 872, 522, 292, 873])
                (.absurd 874))
            (.split 27
                (.split 36
                    (.cell 348 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 452, 381, 717, 383, 384, 875, 523, 388, 876])
                    (.absurd 877))
                (.split 28
                    (.split 36
                        (.cell 349 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 476, 477, 463, 413, 725, 470, 471, 878, 526, 419, 879])
                        (.absurd 880))
                    (.split 29
                        (.split 36
                            (.cell 350 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                              432, 536, 480, 479, 434, 731, 482, 483, 881, 532, 441, 882])
                            (.absurd 883))
                        (.absurd 468))))))

theorem treePart102_check :
    treePart102.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 884 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart103 : CompactCellTree :=
  .absurd 884

theorem treePart103_check :
    treePart103.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 351, 352, 353, 354, 355 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart104 : CompactCellTree :=
  .split 14
    (.cell 351 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 160,
      187, 316, 317, 177, 162])
    (.split 15
        (.cell 352 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209,
          318, 319, 268, 208])
        (.split 27
            (.cell 353 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240,
              227, 228, 231, 321, 322, 271, 230])
            (.split 28
                (.cell 354 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 258, 351, 324, 325, 276, 260])
                (.split 29
                    (.cell 355 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      290, 291, 292, 293, 354, 355, 356, 298, 295])
                    (.absurd 299)))))

theorem treePart104_check :
    treePart104.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 885 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart105 : CompactCellTree :=
  .absurd 885

theorem treePart105_check :
    treePart105.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 356, 357, 358, 359, 360 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart106 : CompactCellTree :=
  .split 14
    (.cell 356 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 228,
      231, 321, 322, 233, 789, 225, 886])
    (.split 15
        (.cell 357 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 258, 351,
          324, 325, 263, 830, 364, 887])
        (.split 27
            (.cell 358 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              292, 293, 354, 355, 356, 393, 832, 365, 888])
            (.split 28
                (.cell 359 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 381, 461, 383, 384, 398, 864, 382, 889])
                (.split 29
                    (.cell 360 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      463, 464, 419, 413, 465, 470, 471, 473, 870, 467, 890])
                    (.absurd 468)))))

theorem treePart106_check :
    treePart106.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 361, 362, 363, 364, 365, 366, 367, 368, 369, 370 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart107 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 361 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474, 258,
          351, 324, 325, 263, 830, 255, 891])
        (.split 15
            (.cell 362 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 293,
              354, 355, 356, 393, 832, 335, 892])
            (.split 27
                (.cell 363 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 388, 381, 461, 383, 384, 398, 864, 475, 893])
                (.split 28
                    (.cell 364 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 419, 413, 465, 470, 471, 473, 870, 478, 894])
                    (.split 29
                        (.cell 365 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 479, 480, 441, 434, 481, 482, 483, 486, 895, 484, 896])
                        (.absurd 487))))))
    (.split 36
        (.split 14
            (.cell 366 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 488,
              293, 354, 355, 356, 897, 298, 290, 898])
            (.split 15
                (.cell 367 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 388,
                  381, 461, 383, 384, 899, 386, 396, 900])
                (.split 27
                    (.cell 368 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 419, 413, 465, 470, 471, 901, 490, 416, 902])
                    (.split 28
                        (.cell 369 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 492, 493, 441, 434, 481, 482, 483, 903, 439, 437, 904])
                        (.split 29
                            (.cell 370 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                              507, 508, 509, 510, 511, 512, 513, 514, 905, 516, 518, 906])
                            (.absurd 519))))))
        (.absurd 826))

theorem treePart107_check :
    treePart107.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 2, -2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 884 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart108 : CompactCellTree :=
  .absurd 884

theorem treePart108_check :
    treePart108.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[8] + 2 * length[9] + length[11]` in the row-06 symmetry
chamber, with leaves selecting cells 371, 372, 373, 374, 375 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart109 : CompactCellTree :=
  .split 16
    (.split 14
        (.cell 371 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 206,
          907, 664, 328, 268, 208])
        (.split 15
            (.cell 372 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228,
              908, 667, 447, 271, 230])
            (.split 27
                (.cell 373 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 258, 909, 670, 448, 276, 260])
                (.split 28
                    (.cell 374 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 293, 910, 696, 451, 298, 295])
                    (.split 29
                        (.cell 375 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                          379, 452, 453, 388, 381, 911, 700, 454, 386, 385])
                        (.absurd 455))))))
    (.absurd 912)

theorem treePart109_check :
    treePart109.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 885 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart110 : CompactCellTree :=
  .absurd 885

theorem treePart110_check :
    treePart110.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 376, 377, 378, 379, 380 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart111 : CompactCellTree :=
  .split 14
    (.cell 376 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 474, 258,
      909, 670, 364, 263, 830, 255, 913])
    (.split 15
        (.cell 377 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 292, 293, 910,
          696, 365, 393, 832, 335, 914])
        (.split 27
            (.cell 378 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459, 460,
              388, 381, 911, 700, 382, 398, 864, 475, 915])
            (.split 28
                (.cell 379 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476,
                  477, 419, 413, 916, 705, 467, 473, 870, 478, 917])
                (.split 29
                    (.cell 380 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      479, 480, 441, 434, 918, 748, 577, 486, 895, 484, 919])
                    (.absurd 487)))))

theorem treePart111_check :
    treePart111.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 381, 382, 383, 384, 385, 386, 387, 388 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart112 : CompactCellTree :=
  .split 14
    (.absurd 740)
    (.split 15
        (.split 35
            (.cell 381 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 452, 381,
              911, 700, 382, 398, 864, 388, 920])
            (.split 36
                (.cell 382 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 530,
                  413, 916, 705, 467, 921, 490, 419, 902])
                (.absurd 922)))
        (.split 27
            (.split 35
                (.cell 383 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 476,
                  477, 463, 413, 916, 705, 467, 473, 870, 419, 923])
                (.split 36
                    (.cell 384 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      492, 493, 536, 434, 918, 748, 577, 924, 439, 441, 904])
                    (.absurd 925)))
            (.split 28
                (.split 35
                    (.cell 385 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432,
                      492, 493, 479, 434, 918, 748, 577, 486, 895, 441, 926])
                    (.split 36
                        (.cell 386 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                          507, 537, 538, 544, 511, 927, 753, 580, 928, 516, 510, 906])
                        (.absurd 929)))
                (.split 29
                    (.split 35
                        (.cell 387 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                          507, 544, 509, 508, 511, 927, 753, 580, 546, 930, 510, 931])
                        (.split 36
                            (.cell 388 [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558,
                              559, 562, 561, 586, 563, 932, 757, 585, 933, 760, 570, 934])
                            (.absurd 935)))
                    (.absurd 487)))))

theorem treePart112_check :
    treePart112.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])])
      ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 2, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0,
      0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 936 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart113 : CompactCellTree :=
  .absurd 936

theorem treePart113_check :
    treePart113.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 937 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart114 : CompactCellTree :=
  .absurd 937

theorem treePart114_check :
    treePart114.check splitForms farkasReceipts cells
      ((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 150, 389, 390, 391, 392 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart115 : CompactCellTree :=
  .split 23
    (.cell 150 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 34, 116, 33, 938, 35])
    (.split 24
        (.cell 389 [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 118, 51, 50, 53])
        (.split 25
            (.cell 389 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 72, 119, 71, 939, 940])
            (.split 26
                (.cell 390 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 92, 121, 91, 123,
                  769, 90, 941])
                (.split 35
                    (.cell 391 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 112,
                      124, 111, 126, 777, 110, 942])
                    (.split 36
                        (.cell 392 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
                          139, 142, 140, 141, 943, 176, 145, 944])
                        (.absurd 945))))))

theorem treePart115_check :
    treePart115.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 946 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart116 : CompactCellTree :=
  .absurd 946

theorem treePart116_check :
    treePart116.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[4] - 2 * length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 151, 393, 394, 395, 396 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart117 : CompactCellTree :=
  .split 23
    (.cell 151 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 72, 169, 618, 619, 947, 948,
      73])
    (.split 24
        (.cell 393 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 92, 170, 621, 304, 949, 90,
          93])
        (.split 25
            (.cell 393 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 112, 173, 642,
              306, 950, 951, 952])
            (.split 26
                (.cell 394 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 142,
                  176, 645, 315, 953, 184, 779, 145, 954])
                (.split 35
                    (.cell 395 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
                      161, 163, 648, 317, 955, 189, 781, 165, 956])
                    (.split 36
                        (.cell 396 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                          202, 207, 266, 652, 319, 957, 958, 209, 205, 959])
                        (.absurd 960))))))

theorem treePart117_check :
    treePart117.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 961 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart118 : CompactCellTree :=
  .absurd 961

theorem treePart118_check :
    treePart118.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[8] + 2 * length[9] - length[10]` in the row-06 symmetry
chamber, with leaves selecting cells 397, 398, 399 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart119 : CompactCellTree :=
  .split 21
    (.cell 397 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 112, 110, 642, 306,
      962, 108, 113])
    (.split 34
        (.cell 398 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 142, 145, 963,
          964, 182, 143])
        (.split 22
            (.cell 399 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 161, 159,
              965, 165, 966, 187, 162])
            (.absurd 967)))

theorem treePart119_check :
    treePart119.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - 2 * length[7]` in the row-06 symmetry chamber, with
leaves selecting cells 400, 401, 402, 403, 404, 405, 406, 407 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart120 : CompactCellTree :=
  .split 25
    (.absurd 968)
    (.split 26
        (.split 21
            (.cell 400 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 161, 165,
              648, 317, 969, 189, 781, 177, 970])
            (.split 34
                (.cell 401 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 207,
                  205, 971, 972, 211, 783, 268, 973])
                (.split 22
                    (.cell 402 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      229, 344, 974, 227, 975, 233, 789, 271, 976])
                    (.absurd 977))))
        (.split 35
            (.split 21
                (.cell 403 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 207,
                  205, 652, 319, 978, 211, 783, 328, 979])
                (.split 34
                    (.cell 404 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      229, 227, 980, 975, 233, 789, 447, 981])
                    (.split 22
                        (.cell 405 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                          254, 259, 350, 982, 257, 983, 263, 830, 448, 984])
                        (.absurd 985))))
            (.split 21
                (.split 36
                    (.cell 406 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      229, 225, 659, 322, 986, 987, 231, 227, 988])
                    (.absurd 989))
                (.split 34
                    (.absurd 990)
                    (.split 22
                        (.split 36
                            (.cell 407 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 294, 353, 991, 290, 992, 993, 354, 292, 994])
                            (.absurd 995))
                        (.absurd 985))))))

theorem treePart120_check :
    treePart120.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [aff [0, 0, 0, 1,
      -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 937 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart121 : CompactCellTree :=
  .absurd 937

theorem treePart121_check :
    treePart121.check splitForms farkasReceipts cells
      ((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, -2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 996 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart122 : CompactCellTree :=
  .absurd 996

theorem treePart122_check :
    treePart122.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 408, 409, 410, 411, 412 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart123 : CompactCellTree :=
  .split 14
    (.cell 408 [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 168, 119, 71, 169, 73])
    (.split 15
        (.cell 409 [75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 90, 121, 91, 170, 93])
        (.split 27
            (.cell 410 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 171, 172, 110,
              124, 111, 173, 113])
            (.split 28
                (.cell 411 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 174,
                  175, 145, 140, 141, 176, 143])
                (.split 29
                    (.cell 412 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
                      177, 178, 165, 159, 160, 163, 162])
                    (.absurd 179)))))

theorem treePart123_check :
    treePart123.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 997 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart124 : CompactCellTree :=
  .absurd 997

theorem treePart124_check :
    treePart124.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 413, 414, 415, 416, 417 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart125 : CompactCellTree :=
  .split 14
    (.cell 413 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 124, 111,
      126, 777, 108, 998])
    (.split 15
        (.cell 414 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 140, 141,
          184, 779, 182, 999])
        (.split 27
            (.cell 415 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185, 186,
              165, 159, 160, 189, 781, 187, 1000])
            (.split 28
                (.cell 416 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 342, 206, 211, 783, 209, 1001])
                (.split 29
                    (.cell 417 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      225, 226, 227, 344, 228, 233, 789, 231, 1002])
                    (.absurd 234)))))

theorem treePart125_check :
    treePart125.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 418, 419, 420, 421, 422, 423, 424, 425, 426, 427 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart126 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 418 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 140,
          141, 184, 779, 236, 1003])
        (.split 15
            (.cell 419 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 159,
              160, 189, 781, 237, 1004])
            (.split 27
                (.cell 420 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 342, 206, 211, 783, 238, 1005])
                (.split 28
                    (.cell 421 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 227, 344, 228, 233, 789, 241, 1006])
                    (.split 29
                        (.cell 422 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                          254, 255, 256, 257, 350, 258, 263, 830, 261, 1007])
                        (.absurd 264))))))
    (.split 36
        (.split 14
            (.cell 423 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265,
              159, 160, 1008, 163, 177, 1009])
            (.split 15
                (.cell 424 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205,
                  342, 206, 1010, 266, 268, 1011])
                (.split 27
                    (.cell 425 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      239, 240, 227, 344, 228, 1012, 269, 271, 1013])
                    (.split 28
                        (.cell 426 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
                          254, 272, 273, 257, 350, 258, 1014, 274, 276, 1015])
                        (.split 29
                            (.cell 427 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288,
                              289, 290, 291, 292, 353, 293, 1016, 296, 298, 1017])
                            (.absurd 299))))))
        (.absurd 945))

theorem treePart126_check :
    treePart126.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 946 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart127 : CompactCellTree :=
  .absurd 946

theorem treePart127_check :
    treePart127.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -2, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 961 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart128 : CompactCellTree :=
  .absurd 961

theorem treePart128_check :
    treePart128.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 428, 429, 430, 431, 432 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart129 : CompactCellTree :=
  .split 14
    (.cell 428 [95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 181, 173, 642,
      306, 950, 108, 113])
    (.split 15
        (.cell 429 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 176, 645,
          315, 953, 182, 143])
        (.split 27
            (.cell 430 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 185, 186,
              165, 163, 648, 317, 955, 187, 162])
            (.split 28
                (.cell 431 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203,
                  204, 205, 266, 652, 319, 957, 209, 208])
                (.split 29
                    (.cell 432 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
                      225, 226, 227, 269, 659, 322, 1018, 231, 230])
                    (.absurd 234)))))

theorem treePart129_check :
    treePart129.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 968 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart130 : CompactCellTree :=
  .absurd 968

theorem treePart130_check :
    treePart130.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0,
      0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 433, 434, 435, 436, 437 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart131 : CompactCellTree :=
  .split 14
    (.cell 433 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 265, 163,
      648, 317, 955, 189, 781, 177, 970])
    (.split 15
        (.cell 434 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 266, 652,
          319, 957, 211, 783, 268, 973])
        (.split 27
            (.cell 435 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240,
              227, 269, 659, 322, 1018, 233, 789, 271, 976])
            (.split 28
                (.cell 436 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 274, 685, 325, 1019, 263, 830, 276, 1020])
                (.split 29
                    (.cell 437 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      290, 291, 292, 296, 690, 356, 1021, 393, 832, 298, 1022])
                    (.absurd 299)))))

theorem treePart131_check :
    treePart131.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 438, 439, 440, 441, 442, 443, 444, 445, 446, 447 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart132 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 438 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 266,
          652, 319, 957, 211, 783, 328, 979])
        (.split 15
            (.cell 439 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 269,
              659, 322, 1018, 233, 789, 447, 981])
            (.split 27
                (.cell 440 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272,
                  273, 257, 274, 685, 325, 1019, 263, 830, 448, 984])
                (.split 28
                    (.cell 441 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 296, 690, 356, 1021, 393, 832, 451, 1023])
                    (.split 29
                        (.cell 442 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                          379, 452, 453, 388, 395, 723, 384, 1024, 398, 864, 454, 1025])
                        (.absurd 455))))))
    (.split 36
        (.split 14
            (.cell 443 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456,
              269, 659, 322, 1018, 987, 231, 225, 988])
            (.split 15
                (.cell 444 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257,
                  274, 685, 325, 1019, 1026, 351, 364, 1027])
                (.split 27
                    (.cell 445 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
                      449, 450, 292, 296, 690, 356, 1021, 993, 354, 365, 994])
                    (.split 28
                        (.cell 446 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378,
                          379, 459, 460, 388, 395, 723, 384, 1024, 1028, 461, 382, 1029])
                        (.split 29
                            (.cell 447 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                              411, 463, 464, 419, 415, 726, 471, 1030, 1031, 465, 467, 1032])
                            (.absurd 468))))))
        (.absurd 960))

theorem treePart132_check :
    treePart132.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, -2, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 819 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart133 : CompactCellTree :=
  .absurd 819

theorem treePart133_check :
    treePart133.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 448, 449, 450, 451, 452 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart134 : CompactCellTree :=
  .split 14
    (.cell 448 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 235, 644,
      645, 315, 1033, 236, 143])
    (.split 15
        (.cell 449 [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 165, 647, 648,
          317, 1034, 237, 162])
        (.split 27
            (.cell 450 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
              205, 651, 652, 319, 1035, 238, 208])
            (.split 28
                (.cell 451 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239,
                  240, 227, 681, 659, 322, 1036, 241, 230])
                (.split 29
                    (.cell 452 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
                      255, 256, 257, 684, 685, 325, 1037, 261, 260])
                    (.absurd 264)))))

theorem treePart134_check :
    treePart134.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 859 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart135 : CompactCellTree :=
  .absurd 859

theorem treePart135_check :
    treePart135.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 453, 454, 455, 456, 457 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart136 : CompactCellTree :=
  .split 14
    (.cell 453 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 651,
      652, 319, 1035, 211, 783, 328, 860])
    (.split 15
        (.cell 454 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 681, 659,
          322, 1036, 233, 789, 447, 861])
        (.split 27
            (.cell 455 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273,
              257, 684, 685, 325, 1037, 263, 830, 448, 862])
            (.split 28
                (.cell 456 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 715, 690, 356, 1038, 393, 832, 451, 863])
                (.split 29
                    (.cell 457 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      452, 453, 388, 717, 723, 384, 1039, 398, 864, 454, 865])
                    (.absurd 455)))))

theorem treePart136_check :
    treePart136.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      -2, -1, 0, 1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- 2 * length[4] - length[5] + 2 * length[7]` in the row-06 symmetry
chamber, with leaves selecting cells 458, 459, 460, 461, 462, 463, 464, 465, 466 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart137 : CompactCellTree :=
  .split 35
    (.split 14
        (.cell 458 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 456, 681,
          659, 322, 1036, 233, 789, 225, 866])
        (.split 15
            (.cell 459 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 257, 684,
              685, 325, 1037, 263, 830, 364, 867])
            (.split 27
                (.cell 460 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 715, 690, 356, 1038, 393, 832, 365, 868])
                (.split 28
                    (.cell 461 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 388, 717, 723, 384, 1039, 398, 864, 382, 869])
                    (.split 29
                        (.cell 462 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 463, 464, 419, 725, 726, 471, 1040, 473, 870, 467, 871])
                        (.absurd 468))))))
    (.split 14
        (.absurd 1041)
        (.split 15
            (.split 36
                (.cell 463 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290,
                  715, 690, 356, 1038, 872, 522, 292, 873])
                (.absurd 1042))
            (.split 27
                (.split 36
                    (.cell 464 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      459, 460, 452, 717, 723, 384, 1039, 875, 523, 388, 876])
                    (.absurd 877))
                (.split 28
                    (.split 36
                        (.cell 465 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410,
                          411, 476, 477, 463, 725, 726, 471, 1040, 878, 526, 419, 879])
                        (.absurd 880))
                    (.split 29
                        (.split 36
                            (.cell 466 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                              432, 536, 480, 479, 731, 732, 483, 1043, 881, 532, 441, 882])
                            (.absurd 883))
                        (.absurd 468))))))

theorem treePart137_check :
    treePart137.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, -2, 2, -1, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0,
      0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 819 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart138 : CompactCellTree :=
  .absurd 819

theorem treePart138_check :
    treePart138.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++ [aff [0, 0, 0, 0,
      0, 1, 0, 0, -2, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 721 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart139 : CompactCellTree :=
  .absurd 721

theorem treePart139_check :
    treePart139.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 467, 468, 469, 470 and Farkas receipts excluding inconsistent sign branches. -/
def treePart140 : CompactCellTree :=
  .split 24
    (.cell 467 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 328, 342, 1044,
      238, 972, 205, 208])
    (.split 25
        (.cell 467 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 447, 344,
          1045, 241, 975, 828, 829])
        (.split 26
            (.cell 468 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 448, 350,
              1046, 261, 983, 263, 830, 257, 831])
            (.split 35
                (.cell 469 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 451,
                  353, 1047, 522, 992, 393, 832, 292, 833])
                (.split 36
                    (.cell 470 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      454, 380, 1048, 523, 1049, 834, 382, 388, 835])
                    (.absurd 1050)))))

theorem treePart140_check :
    treePart140.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `2 * length[4] - length[7]` in the row-06 symmetry chamber, with leaves
selecting cells 471, 472, 473, 474 and Farkas receipts excluding inconsistent sign branches. -/
def treePart141 : CompactCellTree :=
  .split 24
    (.cell 471 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 239, 240, 225,
      344, 1045, 241, 975, 227, 230])
    (.split 25
        (.cell 471 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273, 364,
          350, 1046, 261, 983, 1051, 1052])
        (.split 26
            (.cell 472 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              365, 353, 1047, 522, 992, 393, 832, 292, 1053])
            (.split 35
                (.cell 473 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 382, 380, 1048, 523, 1049, 398, 864, 388, 920])
                (.split 36
                    (.cell 474 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 467, 412, 1054, 526, 1055, 921, 478, 419, 1056])
                    (.absurd 1057)))))

theorem treePart141_check :
    treePart141.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0,
      -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - 2 * length[2] + 2 * length[3]` in the row-06 symmetry
chamber, with leaves selecting cells 475, 476, 477, 478, 479, 480, 481, 482 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart142 : CompactCellTree :=
  .split 28
    (.split 24
        (.cell 475 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273, 255,
          350, 1046, 261, 983, 257, 260])
        (.split 25
            (.cell 475 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449, 450,
              335, 353, 1047, 522, 992, 1058, 1059])
            (.split 26
                (.cell 476 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 459,
                  460, 475, 380, 1048, 523, 1049, 398, 864, 388, 1060])
                (.split 35
                    (.cell 477 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      476, 477, 478, 412, 1054, 526, 1055, 473, 870, 419, 923])
                    (.split 36
                        (.cell 478 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 492, 493, 484, 433, 1061, 532, 1062, 924, 437, 441, 1063])
                        (.absurd 925))))))
    (.split 29
        (.split 24
            (.cell 479 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 335, 291,
              290, 353, 1047, 522, 992, 292, 295])
            (.split 25
                (.cell 479 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 475,
                  453, 396, 380, 1048, 523, 1049, 1064, 1065])
                (.split 26
                    (.cell 480 [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
                      478, 464, 416, 412, 1054, 526, 1055, 473, 870, 419, 1066])
                    (.split 35
                        (.cell 481 [420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
                          432, 484, 480, 437, 433, 1061, 532, 1062, 486, 895, 441, 926])
                        (.split 36
                            (.cell 482 [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506,
                              507, 1067, 509, 518, 1068, 1069, 540, 1070, 928, 1071, 510, 1072])
                            (.absurd 929))))))
        (.absurd 264))

theorem treePart142_check :
    treePart142.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1073 to exclude the accumulated affine constraints
in this row-06 branch. -/
def treePart143 : CompactCellTree :=
  .absurd 1073

theorem treePart143_check :
    treePart143.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 0, 1])]) = true := by
  decide +kernel

/-- A branch of the final row-06 cover assembly, starting at split form 2
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch0 : CompactCellTree :=
  .split 2
    (.split 3
      treePart0
      (.split 4
        treePart1
        (.split 5
          treePart2
          (.split 6
            treePart3
            (.split 7
              treePart4
              (.split 8
                treePart5
                treePart6))))))
    (.split 3
      (.split 4
        treePart7
        (.split 9
          treePart8
          (.split 10
            treePart9
            (.split 11
              treePart10
              (.split 12
                treePart11
                treePart12)))))
      (.split 4
        (.split 9
          treePart13
          (.split 10
            treePart14
            (.split 11
              treePart15
              (.split 12
                treePart16
                (.split 5
                  treePart17
                  (.split 6
                    treePart18
                    treePart19))))))
        (.split 9
          treePart20
          (.split 10
            (.split 5
              treePart21
              (.split 6
                treePart22
                (.split 7
                  treePart23
                  (.split 8
                    treePart24
                    treePart25))))
            (.split 11
              treePart26
              (.split 12
                (.split 5
                  treePart27
                  (.split 6
                    treePart28
                    (.split 7
                      treePart29
                      (.split 8
                        treePart30
                        treePart31))))
                (.split 13
                  (.split 5
                    treePart32
                    (.split 6
                      treePart33
                      (.split 7
                        treePart34
                        (.split 14
                          treePart35
                          (.split 15
                            treePart36
                            treePart37)))))
                  (.split 5
                    treePart38
                    (.split 16
                      (.split 6
                        treePart39
                        (.split 7
                          treePart40
                          (.split 14
                            treePart41
                            (.split 15
                              treePart42
                              treePart43))))
                      treePart44)))))))))

theorem treeAssemblyBranch0_check :
    treeAssemblyBranch0.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0,
        0, 1, -1, 0, 0]]) = true := by
  simp only [treeAssemblyBranch0, CompactCellTree.check_split, Bool.and_true, splitForm2,
    splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9,
    splitForm10, splitForm11, splitForm12, splitForm13, splitForm14, splitForm15, splitForm16,
    treePart0_check, treePart1_check, treePart10_check, treePart11_check, treePart12_check,
    treePart13_check, treePart14_check, treePart15_check, treePart16_check, treePart17_check,
    treePart18_check, treePart19_check, treePart2_check, treePart20_check, treePart21_check,
    treePart22_check, treePart23_check, treePart24_check, treePart25_check, treePart26_check,
    treePart27_check, treePart28_check, treePart29_check, treePart3_check, treePart30_check,
    treePart31_check, treePart32_check, treePart33_check, treePart34_check, treePart35_check,
    treePart36_check, treePart37_check, treePart38_check, treePart39_check, treePart4_check,
    treePart40_check, treePart41_check, treePart42_check, treePart43_check, treePart44_check,
    treePart5_check, treePart6_check, treePart7_check, treePart8_check, treePart9_check]

/-- A branch of the final row-06 cover assembly, starting at split form 3
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch1 : CompactCellTree :=
  .split 3
    (.split 4
      treePart45
      (.split 17
        treePart46
        (.split 18
          treePart47
          (.split 19
            treePart48
            (.split 20
              treePart49
              treePart50)))))
    (.split 4
      (.split 17
        treePart51
        (.split 18
          treePart52
          (.split 19
            treePart53
            (.split 20
              treePart54
              (.split 21
                treePart55
                treePart56)))))
      (.split 17
        treePart57
        (.split 18
          (.split 5
            treePart58
            (.split 6
              treePart59
              (.split 7
                treePart60
                (.split 8
                  treePart61
                  treePart62))))
          (.split 19
            treePart63
            (.split 20
              (.split 5
                treePart64
                (.split 6
                  treePart65
                  (.split 7
                    treePart66
                    (.split 8
                      treePart67
                      treePart68))))
              (.split 21
                (.split 5
                  treePart69
                  (.split 6
                    treePart70
                    (.split 7
                      treePart71
                      (.split 8
                        treePart72
                        treePart73))))
                (.split 5
                  treePart74
                  (.split 6
                    treePart75
                    (.split 7
                      treePart76
                      (.split 22
                        (.split 8
                          treePart77
                          treePart78)
                        treePart79))))))))))

theorem treeAssemblyBranch1_check :
    treeAssemblyBranch1.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) = true := by
  simp only [treeAssemblyBranch1, CompactCellTree.check_split, Bool.and_true, splitForm3,
    splitForm4, splitForm5, splitForm6, splitForm7, splitForm8, splitForm17, splitForm18,
    splitForm19, splitForm20, splitForm21, splitForm22, treePart45_check, treePart46_check,
    treePart47_check, treePart48_check, treePart49_check, treePart50_check, treePart51_check,
    treePart52_check, treePart53_check, treePart54_check, treePart55_check, treePart56_check,
    treePart57_check, treePart58_check, treePart59_check, treePart60_check, treePart61_check,
    treePart62_check, treePart63_check, treePart64_check, treePart65_check, treePart66_check,
    treePart67_check, treePart68_check, treePart69_check, treePart70_check, treePart71_check,
    treePart72_check, treePart73_check, treePart74_check, treePart75_check, treePart76_check,
    treePart77_check, treePart78_check, treePart79_check]

/-- A branch of the final row-06 cover assembly, starting at split form 1
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch2 : CompactCellTree :=
  .split 1
    treeAssemblyBranch0
    treeAssemblyBranch1

theorem treeAssemblyBranch2_check :
    treeAssemblyBranch2.check splitForms farkasReceipts cells
      (base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch2, CompactCellTree.check_split, Bool.and_true, splitForm1,
    treeAssemblyBranch0_check, treeAssemblyBranch1_check]

/-- A branch of the final row-06 cover assembly, starting at split form 1
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch3 : CompactCellTree :=
  .split 1
    (.split 2
      (.split 4
        treePart80
        (.split 23
          treePart81
          (.split 24
            treePart82
            (.split 25
              treePart83
              (.split 26
                treePart84
                treePart85)))))
      (.split 4
        (.split 9
          treePart86
          (.split 10
            treePart87
            (.split 11
              treePart88
              (.split 12
                treePart89
                treePart90))))
        (.split 9
          treePart91
          (.split 10
            (.split 23
              treePart92
              (.split 24
                treePart93
                (.split 25
                  treePart94
                  (.split 26
                    treePart95
                    treePart96))))
            (.split 11
              treePart97
              (.split 12
                (.split 23
                  treePart98
                  (.split 24
                    treePart99
                    (.split 25
                      treePart100
                      (.split 26
                        treePart101
                        treePart102))))
                (.split 13
                  (.split 23
                    treePart103
                    (.split 24
                      treePart104
                      (.split 25
                        treePart105
                        (.split 26
                          treePart106
                          treePart107))))
                  (.split 23
                    treePart108
                    (.split 24
                      treePart109
                      (.split 25
                        treePart110
                        (.split 16
                          (.split 26
                            treePart111
                            treePart112)
                          treePart113)))))))))))
    (.split 4
      (.split 17
        treePart114
        (.split 18
          treePart115
          (.split 19
            treePart116
            (.split 20
              treePart117
              (.split 23
                treePart118
                (.split 24
                  treePart119
                  treePart120))))))
      (.split 17
        treePart121
        (.split 18
          (.split 23
            treePart122
            (.split 24
              treePart123
              (.split 25
                treePart124
                (.split 26
                  treePart125
                  treePart126))))
          (.split 19
            treePart127
            (.split 20
              (.split 23
                treePart128
                (.split 24
                  treePart129
                  (.split 25
                    treePart130
                    (.split 26
                      treePart131
                      treePart132))))
              (.split 21
                (.split 23
                  treePart133
                  (.split 24
                    treePart134
                    (.split 25
                      treePart135
                      (.split 26
                        treePart136
                        treePart137))))
                (.split 23
                  treePart138
                  (.split 22
                    (.split 14
                      treePart139
                      (.split 15
                        treePart140
                        (.split 27
                          treePart141
                          treePart142)))
                    treePart143))))))))

theorem treeAssemblyBranch3_check :
    treeAssemblyBranch3.check splitForms farkasReceipts cells
      (base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0])]) = true :=
        by
  simp only [treeAssemblyBranch3, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm2, splitForm4, splitForm9, splitForm10, splitForm11, splitForm12, splitForm13,
    splitForm14, splitForm15, splitForm16, splitForm17, splitForm18, splitForm19, splitForm20,
    splitForm21, splitForm22, splitForm23, splitForm24, splitForm25, splitForm26, splitForm27,
    treePart100_check, treePart101_check, treePart102_check, treePart103_check,
    treePart104_check, treePart105_check, treePart106_check, treePart107_check,
    treePart108_check, treePart109_check, treePart110_check, treePart111_check,
    treePart112_check, treePart113_check, treePart114_check, treePart115_check,
    treePart116_check, treePart117_check, treePart118_check, treePart119_check,
    treePart120_check, treePart121_check, treePart122_check, treePart123_check,
    treePart124_check, treePart125_check, treePart126_check, treePart127_check,
    treePart128_check, treePart129_check, treePart130_check, treePart131_check,
    treePart132_check, treePart133_check, treePart134_check, treePart135_check,
    treePart136_check, treePart137_check, treePart138_check, treePart139_check,
    treePart140_check, treePart141_check, treePart142_check, treePart143_check,
    treePart80_check, treePart81_check, treePart82_check, treePart83_check, treePart84_check,
    treePart85_check, treePart86_check, treePart87_check, treePart88_check, treePart89_check,
    treePart90_check, treePart91_check, treePart92_check, treePart93_check, treePart94_check,
    treePart95_check, treePart96_check, treePart97_check, treePart98_check, treePart99_check]

/-- The complete compact decision tree for row 06 on the symmetry chamber, assembling 144
subtrees whose cell and Farkas certificates are replayed by the cover checker. -/
def tree : CompactCellTree :=
  .split 0
    treeAssemblyBranch2
    treeAssemblyBranch3

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0,
    treeAssemblyBranch2_check, treeAssemblyBranch3_check]

/-- On the chamber the eighteen active rows all hold: the first twelve
because lengths are natural numbers, the last six by definition of the
fundamental domain. -/
theorem base_holds (length : Fin 12 → ℕ) (hChamber : Chamber length) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  obtain ⟨⟨q0, q1, q2⟩, r0, r1, r2⟩ := hChamber
  intro form hForm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hForm
  rcases hForm with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp [aff,
    _root_.Utilities.Certificate.AffineCover.AffineForm.Holds,
    _root_.Utilities.Certificate.AffineCover.AffineForm.eval,
    lengthPoint, Fin.sum_univ_succ]
  all_goals omega

/-- Connectivity of the core, checked here so that the generated
modules stay self-contained. -/
theorem rowConnected : row06Core.Connected :=
  (row06Core.connectedCheck_eq_true_iff).mp (by decide +kernel)

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row06Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row06Core (by norm_num) Chamber
    (fun length _ _ => chamber_covers length)
    (fun length forest notLoopy hChamber =>
      chamberPencil_of_compactCellTree (by norm_num) rowConnected
        cells base splitForms farkasReceipts tree cells_valid tree_check
        length forest notLoopy (base_holds length hChamber))

end AtanasovRanganathan.GenusFiveRow06FixedCover
