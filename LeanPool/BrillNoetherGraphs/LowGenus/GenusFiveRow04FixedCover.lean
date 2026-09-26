/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverBase
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverCells0
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverCells1
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04Symmetry
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverReceipts

/-! **Independent generated check.** This module provides an additional generated proof of row 04
and is not imported by the main `LowGenus` root.

Generated exact replay of the fixed AR row-04 divisor on a
fundamental domain for the core's slot-level symmetry group.

The external discovery data are untrusted: `cells_check` and
`tree_check` replay every arithmetic obligation in the kernel, and the
chamber is discharged by the generated coverage theorem, so the
conclusion is the row on the whole closed orthant. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04FixedCover

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow04CoverBase
open GenusFiveRow04Symmetry (Chamber chamber_covers)

/-- The 195 row-04 closed-cover cells in global index order, obtained by concatenating the two
certificate blocks. -/
def cells : List (CoordinateCell row04Core) :=
  GenusFiveRow04CoverCells0.chunk ++ GenusFiveRow04CoverCells1.chunk

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, List.all_append, GenusFiveRow04CoverCells0.chunk_check,
    GenusFiveRow04CoverCells1.chunk_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.Certificate.checkClosed_eq_true_iff _ _).mp hChecks

/-- The twelve root rows of the closed orthant followed by the six
chamber inequalities cutting the fundamental domain. -/
def base : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0,
  0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff
  [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0,
  0, 0, 1, 0, 0, 0, 0, 0, -1]]

/-- The 32 homogeneous affine forms whose signs determine branches of the row-04 decision tree;
coefficients are indexed by the twelve edge lengths. -/
def splitForms : List (ExplicitPotential.AffineForm 12) :=
  [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1],
  aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff
  [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0,
  -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 1,
  0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0,
  0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0,
  -1, -1, 0, -1, 1, 0, 1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0,
  -1, -1, 0, 0, 1, 0, 1], aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -2, 0, 0,
  1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0,
  0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0,
  0, -1, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, -1, -1, 0, -1, 0, 0,
  0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0,
  0, 1, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0,
  -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0,
  1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1]]

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1] := by rfl

theorem splitForm14 :
    splitForms.getD 14 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1] := by rfl

theorem splitForm15 :
    splitForms.getD 15 0 = aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1] := by rfl

theorem splitForm17 :
    splitForms.getD 17 0 = aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm18 :
    splitForms.getD 18 0 = aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm20 :
    splitForms.getD 20 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1] := by rfl

theorem splitForm21 :
    splitForms.getD 21 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1] := by rfl

theorem splitForm22 : splitForms.getD 22 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1] := by rfl

theorem splitForm23 : splitForms.getD 23 0 = aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm24 :
    splitForms.getD 24 0 = aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm25 :
    splitForms.getD 25 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1] := by rfl

theorem splitForm28 : splitForms.getD 28 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1] := by rfl

theorem splitForm29 :
    splitForms.getD 29 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1] := by rfl

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 0, 1, 2, 3 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart0 : CompactCellTree :=
  .split 3
    (.cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21])
    (.split 16
        (.cell 1 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
          42, 43, 44])
        (.split 27
            (.cell 2 [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
              64, 65, 66, 67])
            (.split 29
                (.cell 3 [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
                  86, 87, 88, 89, 90])
                (.absurd 91))))

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[3] - length[5] + length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 4, 5, 6 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart1 : CompactCellTree :=
  .split 8
    (.cell 4 [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 92, 60, 61, 62, 93, 67, 94,
      95, 96])
    (.split 9
        (.cell 5 [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 89, 83, 84, 85, 90, 97,
          98, 99, 100])
        (.split 15
            (.cell 6 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
              116, 117, 118, 119, 120, 121, 122, 123])
            (.absurd 124)))

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[3] - length[5] + length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 7, 8, 9, 10, 11, 12, 13, 14, 15 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart2 : CompactCellTree :=
  .split 8
    (.split 16
        (.cell 7 [68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 89, 83, 84, 85, 98, 88,
          97, 125, 126, 90])
        (.split 27
            (.cell 8 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
              116, 117, 118, 127, 128, 129, 130, 131, 121])
            (.split 29
                (.cell 9 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                  146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
                (.absurd 156))))
    (.split 9
        (.split 16
            (.cell 10 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
              116, 117, 118, 120, 129, 127, 130, 131, 121])
            (.split 27
                (.cell 11 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                  146, 147, 148, 149, 157, 152, 150, 158, 159, 155])
                (.split 29
                    (.cell 12 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
                      173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
                    (.absurd 184))))
        (.split 15
            (.split 16
                (.cell 13 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                  146, 147, 148, 149, 185, 157, 153, 158, 159, 155])
                (.split 27
                    (.cell 14 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172,
                      173, 174, 175, 176, 177, 186, 178, 187, 188, 189, 183])
                    (.split 29
                        (.cell 15 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                          203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213])
                        (.absurd 214))))
            (.absurd 124)))

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells
      ((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]])
      ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 215 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart3 : CompactCellTree :=
  .absurd 215

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 0, 16, 17, 18, 19, 20, 21, 22 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart4 : CompactCellTree :=
  .split 17
    (.cell 16 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 154, 216, 217, 147, 148,
      149, 218, 155, 151, 219])
    (.split 18
        (.cell 0 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 220, 175,
          176, 177, 221, 222, 223, 224])
        (.split 8
            (.split 10
                (.cell 17 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238,
                  239, 240, 241, 242, 243, 244, 245])
                (.split 23
                    (.cell 18 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      259, 260, 261, 262, 263, 264, 265, 266, 267, 268])
                    (.absurd 269)))
            (.split 7
                (.cell 19 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238,
                  240, 270, 241, 242, 243, 271, 239, 244, 245])
                (.split 9
                    (.cell 20 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      272, 273, 259, 261, 262, 263, 264, 267, 268])
                    (.split 19
                        (.split 30
                            (.cell 21 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                              286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297])
                            (.split 15
                                (.cell 22 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308,
                                  309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321])
                                (.absurd 322)))
                        (.absurd 323))))))

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 0, 16, 19, 23, 24 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart5 : CompactCellTree :=
  .split 10
    (.cell 19 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 150, 153, 217, 147,
      148, 149, 324, 155, 151, 219])
    (.split 17
        (.cell 16 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 182, 325, 222, 175,
          176, 177, 326, 183, 223, 224])
        (.split 18
            (.cell 0 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 327,
              205, 206, 207, 328, 329, 330, 331])
            (.split 23
                (.split 24
                    (.cell 23 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 332,
                      333, 273, 261, 262, 263, 264, 334, 265, 335, 267, 268])
                    (.cell 24 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 272,
                      335, 273, 261, 262, 263, 264, 334, 265, 267, 268]))
                (.absurd 336))))

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells
      (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])])
      = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 215 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart6 : CompactCellTree :=
  .absurd 215

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 25, 26, 27, 28, 29, 30 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart7 : CompactCellTree :=
  .split 17
    (.absurd 337)
    (.split 18
        (.absurd 338)
        (.split 10
            (.split 16
                (.cell 25 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  260, 339, 262, 263, 264, 340, 335, 341, 342, 273])
                (.split 27
                    (.cell 26 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366])
                    (.split 29
                        (.cell 27 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          295, 367, 368, 290, 291, 292, 369, 370, 289, 296, 294])
                        (.absurd 371))))
            (.split 23
                (.split 16
                    (.cell 28 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 357, 358, 359, 360, 361, 362, 372, 373, 364, 365, 366])
                    (.split 27
                        (.cell 29 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          295, 367, 368, 290, 291, 292, 369, 374, 375, 376, 377, 294])
                        (.split 29
                            (.cell 30 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 378, 379, 380, 314, 315, 316, 381, 382, 383, 384, 320, 319])
                            (.absurd 385))))
                (.absurd 269))))

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 31, 32, 33 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart8 : CompactCellTree :=
  .split 10
    (.absurd 217)
    (.split 17
        (.absurd 386)
        (.split 18
            (.absurd 387)
            (.split 23
                (.split 24
                    (.split 16
                        (.cell 31 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 367,
                          388, 389, 295, 290, 291, 292, 369, 374, 375, 376, 377, 294])
                        (.split 27
                            (.cell 32 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              379, 390, 391, 378, 314, 315, 316, 381, 382, 383, 392, 393, 319])
                            (.split 29
                                (.cell 33 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417,
                                  418])
                                (.absurd 419))))
                    (.absurd 420))
                (.absurd 421))))

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 34, 35, 36, 37, 38, 39 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart9 : CompactCellTree :=
  .split 17
    (.absurd 422)
    (.split 18
        (.absurd 423)
        (.split 10
            (.split 16
                (.cell 34 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  339, 335, 262, 263, 264, 341, 342, 273])
                (.split 27
                    (.cell 35 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 358, 363, 359, 360, 361, 364, 365, 366])
                    (.split 29
                        (.cell 36 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          295, 368, 370, 290, 291, 292, 289, 296, 294])
                        (.absurd 371))))
            (.split 23
                (.split 16
                    (.cell 37 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      358, 357, 356, 359, 360, 361, 372, 424, 364, 365, 366])
                    (.split 27
                        (.cell 38 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          368, 367, 295, 290, 291, 292, 374, 425, 376, 377, 294])
                        (.split 29
                            (.cell 39 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 380, 379, 378, 314, 315, 316, 382, 426, 384, 320, 319])
                            (.absurd 385))))
                (.absurd 269))))

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells
      ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[9] + length[11]` in the row-04
symmetry chamber, with leaves selecting cells 40, 41, 42 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart10 : CompactCellTree :=
  .split 16
    (.cell 40 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 212, 211, 427, 428,
      205, 206, 207, 429, 430, 213])
    (.split 27
        (.cell 41 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 431, 432, 433,
          238, 241, 242, 243, 434, 435, 240])
        (.split 29
            (.cell 42 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 272, 436,
              339, 261, 262, 263, 264, 335, 267, 273])
            (.absurd 437)))

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 43, 44, 45, 46, 47, 48 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart11 : CompactCellTree :=
  .split 17
    (.absurd 386)
    (.split 18
        (.absurd 387)
        (.split 19
            (.split 16
                (.split 30
                    (.cell 43 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                      287, 368, 438, 290, 291, 292, 293, 294, 295, 376, 377, 289])
                    (.split 15
                        (.cell 44 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                          311, 380, 439, 314, 315, 316, 317, 440, 319, 392, 393, 313])
                        (.absurd 441)))
                (.split 27
                    (.split 30
                        (.cell 45 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                          311, 380, 439, 314, 315, 316, 442, 319, 378, 392, 393, 384])
                        (.split 15
                            (.cell 46 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                              443, 444, 445, 446, 410, 411, 412, 447, 448, 418, 449, 450, 451])
                            (.absurd 452)))
                    (.split 30
                        (.split 29
                            (.cell 47 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                              443, 444, 445, 446, 410, 411, 412, 453, 416, 409, 451, 417, 418])
                            (.absurd 454))
                        (.split 15
                            (.split 29
                                (.cell 48 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465,
                                  466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478,
                                  479])
                                (.absurd 480))
                            (.absurd 452)))))
            (.absurd 481)))

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation
      (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 17, 34, 35, 36 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart12 : CompactCellTree :=
  .split 3
    (.cell 17 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 127, 128, 120, 116,
      117, 118, 121, 123])
    (.split 16
        (.cell 34 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 150, 151, 157,
          147, 148, 149, 158, 159, 155])
        (.split 27
            (.cell 35 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 180, 223,
              178, 175, 176, 177, 188, 189, 183])
            (.split 29
                (.cell 36 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 428,
                  330, 209, 205, 206, 207, 211, 210, 213])
                (.absurd 214))))

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[2] + length[3] + length[5] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 18, 23, 31, 32, 33, 37, 38, 39 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart13 : CompactCellTree :=
  .split 6
    (.split 3
        (.split 23
            (.cell 18 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 223, 187,
              180, 175, 176, 177, 482, 483, 181, 224])
            (.absurd 484))
        (.split 23
            (.split 16
                (.cell 37 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 330,
                  210, 428, 205, 206, 207, 485, 486, 429, 430, 213])
                (.split 27
                    (.cell 38 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237,
                      244, 270, 238, 241, 242, 243, 487, 488, 434, 435, 240])
                    (.split 29
                        (.cell 39 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                          267, 260, 261, 262, 263, 264, 265, 489, 335, 339, 273])
                        (.absurd 437))))
            (.absurd 484)))
    (.split 3
        (.split 23
            (.split 24
                (.cell 23 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 210, 490,
                  213, 428, 205, 206, 207, 330, 485, 486, 427, 331])
                (.absurd 491))
            (.absurd 492))
        (.split 23
            (.split 24
                (.split 16
                    (.cell 31 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 270,
                      493, 239, 238, 241, 242, 243, 244, 487, 488, 434, 435, 240])
                    (.split 27
                        (.cell 32 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 260,
                          333, 259, 261, 262, 263, 264, 267, 265, 489, 341, 342, 273])
                        (.split 29
                            (.cell 33 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354,
                              357, 494, 495, 356, 359, 360, 361, 496, 372, 497, 498, 358, 366])
                            (.absurd 499))))
                (.absurd 491))
            (.absurd 492)))

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0,
      -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 19, 49, 50, 51, 52 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart14 : CompactCellTree :=
  .split 3
    (.split 7
        (.cell 19 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 150, 155, 500,
          147, 148, 149, 501, 151, 153, 219])
        (.split 19
            (.cell 49 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 174, 223,
              183, 175, 176, 177, 178, 180, 187, 224])
            (.absurd 502)))
    (.split 7
        (.absurd 503)
        (.split 19
            (.split 16
                (.cell 50 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 204,
                  330, 211, 205, 206, 207, 209, 428, 429, 430, 213])
                (.split 27
                    (.cell 51 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237,
                      504, 244, 432, 241, 242, 243, 505, 238, 434, 435, 240])
                    (.split 29
                        (.cell 52 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                          506, 267, 436, 262, 263, 264, 507, 261, 335, 260, 273])
                        (.absurd 437))))
            (.absurd 502)))

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff
      [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 19, 22, 44, 46, 48 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart15 : CompactCellTree :=
  .split 3
    (.split 7
        (.cell 19 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 150, 155, 500,
          147, 148, 149, 217, 151, 153, 219])
        (.split 19
            (.split 15
                (.cell 22 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 204,
                  330, 211, 205, 206, 207, 208, 209, 213, 210, 331])
                (.absurd 508))
            (.absurd 502)))
    (.split 7
        (.absurd 509)
        (.split 19
            (.split 15
                (.split 16
                    (.cell 44 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237,
                      504, 244, 432, 241, 242, 243, 510, 505, 239, 434, 435, 240])
                    (.split 27
                        (.cell 46 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                          506, 267, 436, 262, 263, 264, 511, 507, 259, 341, 342, 273])
                        (.split 29
                            (.cell 48 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354,
                              355, 512, 496, 513, 359, 360, 361, 514, 515, 495, 498, 357, 366])
                            (.absurd 499))))
                (.absurd 508))
            (.absurd 502)))

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Leaf selecting row-04 cell 0, with 22 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart16 : CompactCellTree :=
  .cell 0 [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 64, 516, 61, 62, 63, 92, 67, 96]

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 517 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart17 : CompactCellTree :=
  .absurd 517

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[10] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 0, 53, 54, 55, 56, 57, 58, 59 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart18 : CompactCellTree :=
  .split 20
    (.cell 53 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185, 518, 519,
      154, 520, 146, 155, 521])
    (.split 21
        (.cell 0 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 186, 522,
          176, 177, 221, 174, 523, 224])
        (.split 16
            (.split 22
                (.cell 54 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 243, 240, 239, 525, 504])
                (.split 26
                    (.cell 55 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 341, 260, 259, 264, 527, 506, 528, 529])
                    (.absurd 530)))
            (.split 27
                (.cell 56 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 239, 240, 431, 243, 525, 504])
                (.split 31
                    (.split 14
                        (.cell 57 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 364, 361, 357, 366, 532, 512, 533, 534])
                        (.split 28
                            (.cell 58 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                              286, 535, 536, 537, 290, 294, 292, 538, 287, 376, 438, 293])
                            (.absurd 539)))
                    (.split 14
                        (.cell 57 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 364, 361, 357, 366, 532, 512, 540, 541])
                        (.split 28
                            (.split 29
                                (.cell 59 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308,
                                  309, 310, 542, 317, 543, 314, 384, 316, 544, 311, 545, 546, 319])
                                (.absurd 547))
                            (.absurd 548)))))))

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 0, 53, 57, 60 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart19 : CompactCellTree :=
  .split 22
    (.cell 57 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185, 158, 149,
      518, 153, 520, 146, 155, 549])
    (.split 20
        (.cell 53 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 186, 523,
          550, 182, 221, 174, 183, 551])
        (.split 21
            (.cell 0 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 208,
              552, 206, 207, 328, 204, 553, 331])
            (.split 25
                (.cell 60 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 554, 555, 240, 525, 504, 556, 557, 558])
                (.absurd 559))))

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])])
      = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 0, 57, 60, 61 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart20 : CompactCellTree :=
  .split 13
    (.split 3
        (.cell 0 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 119, 560,
          117, 118, 561, 115, 121, 123])
        (.split 22
            (.cell 57 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185,
              158, 149, 157, 151, 520, 146, 155, 562])
            (.split 26
                (.cell 61 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                  186, 188, 177, 178, 223, 221, 174, 563, 564, 565])
                (.absurd 566))))
    (.split 3
        (.cell 0 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 119, 560,
          117, 118, 561, 115, 121, 123])
        (.split 22
            (.cell 57 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185,
              158, 149, 518, 151, 520, 146, 155, 562])
            (.split 25
                (.cell 60 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                  186, 188, 567, 223, 568, 221, 174, 563, 564, 565])
                (.absurd 492))))

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0,
      0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[9] + length[11]` in the row-04
symmetry chamber, with leaves selecting cells 0, 54, 55, 59, 62 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart21 : CompactCellTree :=
  .split 16
    (.split 3
        (.cell 0 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 119, 560,
          117, 118, 561, 115, 121, 123])
        (.split 22
            (.cell 54 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185,
              158, 149, 155, 157, 520, 146])
            (.split 26
                (.cell 55 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                  186, 188, 223, 178, 177, 221, 174, 563, 569])
                (.absurd 566))))
    (.split 3
        (.cell 0 [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 119, 560,
          117, 118, 561, 115, 121, 123])
        (.split 27
            (.split 28
                (.cell 62 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                  186, 178, 175, 183, 177, 221, 174, 188, 181])
                (.absurd 570))
            (.split 28
                (.split 29
                    (.cell 59 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 208, 209, 205, 211, 207, 328, 204, 427, 571, 213])
                    (.absurd 572))
                (.absurd 570))))

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 573 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart22 : CompactCellTree :=
  .absurd 573

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, 0, 0,
      0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 574 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart23 : CompactCellTree :=
  .absurd 574

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[10] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 4, 63, 64, 65, 66, 67, 68, 69, 70, 71 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart24 : CompactCellTree :=
  .split 20
    (.cell 63 [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 185, 518, 519,
      154, 150, 157, 575, 155, 521])
    (.split 21
        (.cell 4 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 186, 522,
          176, 177, 180, 178, 576, 523, 224])
        (.split 13
            (.split 14
                (.split 22
                    (.cell 64 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 341, 264, 259, 335, 261, 507, 577, 273, 578])
                    (.split 26
                        (.cell 65 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 364, 361, 495, 363, 356, 515, 579, 580, 581, 582])
                        (.absurd 583)))
                (.split 22
                    (.split 16
                        (.cell 66 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 364, 361, 498, 366, 356, 515, 579])
                        (.split 27
                            (.cell 67 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                              286, 535, 536, 376, 438, 294, 293, 292, 295, 584, 585])
                            (.split 28
                                (.split 31
                                    (.cell 68 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403,
                                      404, 405, 443, 586, 447, 446, 410, 587, 412, 409, 588, 589,
                                      449, 418, 453])
                                    (.split 29
                                        (.cell 69 [455, 456, 457, 458, 459, 460, 461, 462, 463,
                                          464, 465, 466, 467, 590, 474, 470, 471, 591, 473, 592,
                                          593, 594, 595, 596, 479])
                                        (.absurd 597)))
                                (.absurd 598))))
                    (.split 26
                        (.cell 70 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 364, 495, 599, 361, 356, 515, 579, 580, 366])
                        (.absurd 600))))
            (.split 22
                (.cell 64 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 243, 558, 239, 238, 505, 601, 240, 602])
                (.split 25
                    (.cell 71 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 341, 603, 332, 273, 261, 507, 577, 528, 604, 605])
                    (.absurd 606)))))

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 607 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart25 : CompactCellTree :=
  .absurd 607

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 5, 72, 73, 74, 75, 76, 77, 78, 79 and
Farkas receipts excluding inconsistent sign branches. -/
def treePart26 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 72 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 208, 553,
          608, 212, 210, 609, 428, 213, 610])
        (.split 21
            (.cell 5 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524, 510,
              611, 242, 243, 270, 601, 238, 558, 245])
            (.split 16
                (.split 22
                    (.cell 73 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      531, 514, 364, 361, 366, 498, 357, 579, 356])
                    (.split 26
                        (.cell 74 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          535, 536, 376, 612, 438, 292, 367, 585, 295, 613, 614])
                        (.absurd 615)))
                (.split 14
                    (.cell 75 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      531, 514, 364, 361, 513, 366, 357, 579, 356, 498, 541])
                    (.split 27
                        (.cell 76 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          535, 536, 376, 438, 294, 293, 292, 367, 585, 295])
                        (.split 28
                            (.split 31
                                (.cell 77 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 586, 447, 616, 410, 416, 412, 406, 589, 409, 449, 418,
                                  453])
                                (.split 29
                                    (.cell 78 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464,
                                      465, 466, 467, 590, 474, 617, 471, 618, 473, 619, 594, 592,
                                      620, 596, 479])
                                    (.absurd 597)))
                            (.absurd 598)))))))
    (.split 22
        (.cell 75 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 208, 429,
          207, 553, 211, 210, 609, 428, 213, 621])
        (.split 20
            (.cell 72 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524, 510,
              558, 622, 431, 270, 601, 238, 240, 623])
            (.split 21
                (.cell 5 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 526,
                  511, 624, 263, 264, 260, 577, 261, 605, 268])
                (.split 25
                    (.cell 79 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      531, 514, 364, 625, 599, 366, 357, 579, 356, 580, 626, 541])
                    (.absurd 627)))))

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 628 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart27 : CompactCellTree :=
  .absurd 628

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 6, 80, 81, 82, 83, 84, 85, 86, 87 and
Farkas receipts excluding inconsistent sign branches. -/
def treePart28 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 80 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524, 510, 558,
          622, 431, 504, 270, 433, 240, 623])
        (.split 21
            (.cell 6 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 526, 511,
              624, 263, 264, 506, 629, 339, 605, 268])
            (.split 16
                (.split 22
                    (.cell 81 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                      535, 536, 376, 292, 294, 289, 287, 367, 368])
                    (.split 26
                        (.cell 82 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                          542, 317, 392, 630, 313, 316, 311, 379, 380, 631, 632])
                        (.absurd 633)))
                (.split 14
                    (.cell 83 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                      535, 536, 376, 292, 288, 294, 287, 367, 368, 289, 634])
                    (.split 27
                        (.cell 84 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                          542, 317, 392, 313, 319, 442, 316, 311, 379, 380])
                        (.split 28
                            (.split 31
                                (.cell 85 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465,
                                  466, 467, 590, 474, 635, 471, 476, 473, 468, 619, 469, 636, 479,
                                  637])
                                (.split 29
                                    (.cell 86 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647,
                                      648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659,
                                      660, 661, 662])
                                    (.absurd 663)))
                            (.absurd 664)))))))
    (.split 22
        (.cell 83 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524, 510, 434,
          243, 558, 239, 504, 270, 433, 240, 602])
        (.split 20
            (.cell 80 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 526, 511,
              605, 665, 272, 506, 666, 339, 273, 667])
            (.split 21
                (.cell 6 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 531,
                  514, 668, 360, 361, 512, 669, 358, 541, 670])
                (.split 25
                    (.cell 87 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                      535, 536, 376, 671, 672, 294, 287, 367, 368, 613, 673, 634])
                    (.absurd 674)))))

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 675 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart29 : CompactCellTree :=
  .absurd 675

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 676 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart30 : CompactCellTree :=
  .absurd 676

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 66, 70, 73, 74, 81, 82 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart31 : CompactCellTree :=
  .split 22
    (.split 8
        (.cell 66 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 186, 188,
          177, 181, 187, 180, 183, 576])
        (.split 9
            (.cell 73 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 208,
              429, 207, 427, 210, 213, 609, 428])
            (.split 15
                (.cell 81 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 243, 433, 270, 504, 239, 240])
                (.absurd 677))))
    (.split 26
        (.split 8
            (.cell 70 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 208,
              429, 330, 210, 207, 428, 213, 609, 678, 559])
            (.split 9
                (.cell 74 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 434, 244, 270, 243, 240, 601, 238, 556, 679])
                (.split 15
                    (.cell 82 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 341, 267, 260, 264, 506, 335, 273, 528, 680])
                    (.absurd 681))))
        (.absurd 682))

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[8] + length[9] + length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 69, 78, 86, 88, 89, 90 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart32 : CompactCellTree :=
  .split 27
    (.split 14
        (.absurd 683)
        (.split 28
            (.split 8
                (.cell 88 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 524,
                  510, 270, 241, 239, 243, 238, 240, 601, 434, 433])
                (.split 9
                    (.cell 89 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 260, 262, 259, 264, 273, 577, 261, 341, 339])
                    (.split 15
                        (.cell 90 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 357, 359, 495, 361, 512, 498, 366, 364, 358])
                        (.absurd 684))))
            (.absurd 685)))
    (.split 14
        (.absurd 686)
        (.split 28
            (.split 29
                (.split 8
                    (.cell 69 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      526, 511, 687, 262, 259, 264, 261, 273, 577, 339, 688, 335])
                    (.split 9
                        (.cell 78 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                          531, 514, 689, 359, 495, 361, 366, 579, 356, 358, 690, 363])
                        (.split 15
                            (.cell 86 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                              286, 535, 536, 691, 290, 288, 292, 287, 289, 294, 368, 692, 370])
                            (.absurd 693))))
                (.absurd 694))
            (.absurd 695)))

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0,
      0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1,
      -1, 0, 0, 1, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 71, 79, 87 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart33 : CompactCellTree :=
  .split 3
    (.absurd 696)
    (.split 22
        (.absurd 697)
        (.split 25
            (.split 8
                (.cell 71 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                  186, 188, 567, 223, 181, 180, 183, 576, 563, 564, 698])
                (.split 9
                    (.cell 79 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202,
                      203, 208, 429, 699, 330, 427, 213, 609, 428, 678, 700, 701])
                    (.split 15
                        (.cell 87 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237,
                          524, 510, 434, 554, 244, 433, 504, 239, 240, 556, 702, 703])
                        (.absurd 677))))
            (.absurd 704)))

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
      [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 36 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart34 : CompactCellTree :=
  .absurd 36

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells
      (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 705 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart35 : CompactCellTree :=
  .absurd 705

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells
      ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 706 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart36 : CompactCellTree :=
  .absurd 706

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, -1, 0,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 707 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart37 : CompactCellTree :=
  .absurd 707

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 708 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart38 : CompactCellTree :=
  .absurd 708

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[10] - length[11]` in the row-04 symmetry chamber,
with leaves selecting cells 17, 91, 92, 93, 94, 95, 96, 97, 98, 99 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart39 : CompactCellTree :=
  .split 12
    (.absurd 709)
    (.split 20
        (.cell 91 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 438, 370,
          634, 710, 293, 294, 711])
        (.split 21
            (.cell 17 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378, 439,
              712, 713, 315, 316, 714, 321])
            (.split 22
                (.split 16
                    (.cell 92 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 470, 715, 636, 473, 476, 479])
                    (.split 14
                        (.cell 93 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650,
                          716, 717, 718, 719, 656, 720, 662, 655, 721])
                        (.split 27
                            (.cell 94 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 735, 736, 737, 738, 739, 740, 741, 742])
                            (.split 28
                                (.split 31
                                    (.cell 95 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752,
                                      753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764,
                                      765])
                                    (.split 29
                                        (.cell 96 [766, 767, 768, 769, 770, 771, 772, 773, 774,
                                          775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785,
                                          786, 787, 788])
                                        (.absurd 789)))
                                (.absurd 790)))))
                (.split 26
                    (.split 13
                        (.cell 97 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650,
                          716, 717, 718, 719, 662, 791, 656, 792, 793])
                        (.split 25
                            (.cell 98 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 735, 736, 737, 738, 794, 795, 740, 796, 797, 798])
                            (.cell 99 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 735, 736, 737, 738, 740, 798, 741, 796, 797])))
                    (.absurd 799)))))

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0,
      0, 1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 800 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart40 : CompactCellTree :=
  .absurd 800

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] - length[10] - length[11]` in the row-04 symmetry chamber,
with leaves selecting cells 20, 100, 101, 102, 103, 104, 105, 106, 107, 108 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart41 : CompactCellTree :=
  .split 12
    (.absurd 801)
    (.split 20
        (.cell 100 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 444, 451, 802,
          409, 803, 804, 453, 418, 805])
        (.split 21
            (.cell 20 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 477,
              715, 592, 806, 472, 473, 807, 808])
            (.split 22
                (.split 14
                    (.cell 101 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734,
                      809, 810, 737, 735, 738, 742, 811, 740, 812, 813])
                    (.split 16
                        (.cell 102 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                          826, 827, 828, 829, 830, 831, 832, 833, 834])
                        (.split 27
                            (.cell 103 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754,
                              755, 835, 836, 758, 756, 763, 837, 764, 765, 762])
                            (.split 28
                                (.split 31
                                    (.cell 104 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847,
                                      848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859,
                                      860, 861])
                                    (.split 29
                                        (.cell 105 [862, 863, 864, 865, 866, 867, 868, 869, 870,
                                          871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881,
                                          882, 883, 884, 885])
                                        (.absurd 886)))
                                (.absurd 887)))))
                (.split 26
                    (.split 13
                        (.cell 106 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                          826, 827, 828, 829, 830, 831, 834, 888, 832, 889, 890])
                        (.split 25
                            (.cell 107 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754,
                              755, 835, 836, 758, 756, 763, 891, 892, 764, 893, 894, 895])
                            (.cell 108 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754,
                              755, 835, 836, 758, 756, 763, 764, 895, 765, 893, 894])))
                    (.absurd 896)))))

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 897 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart42 : CompactCellTree :=
  .absurd 897

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells
      ((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1,
      -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 898 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart43 : CompactCellTree :=
  .absurd 898

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells
      (((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 899 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart44 : CompactCellTree :=
  .absurd 899

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells
      ((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 109, 110, 111, 112 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart45 : CompactCellTree :=
  .split 22
    (.split 30
        (.cell 109 [766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 900, 781, 901,
          902, 785, 903, 904, 905, 788, 779, 906, 907])
        (.split 15
            (.cell 110 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 908, 853,
              909, 859, 858, 910, 911, 912, 913, 914, 915, 916])
            (.absurd 917)))
    (.split 26
        (.split 30
            (.cell 111 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 908, 853,
              909, 859, 858, 910, 911, 851, 860, 854, 918, 916, 919])
            (.split 15
                (.cell 112 [862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 920,
                  877, 921, 922, 882, 923, 924, 925, 926, 885, 927, 928, 929])
                (.absurd 930)))
        (.absurd 931))

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells
      ((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[9] + length[11]` in the row-04
symmetry chamber, with leaves selecting cells 113, 114, 115, 116, 117, 118, 119, 120 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart46 : CompactCellTree :=
  .split 16
    (.split 30
        (.cell 113 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 908, 853, 909,
          859, 858, 915, 932, 851, 860, 854])
        (.split 15
            (.cell 114 [862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 920, 877,
              921, 922, 882, 933, 934, 925, 926, 885])
            (.absurd 930)))
    (.split 27
        (.split 30
            (.cell 115 [862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 920, 877,
              921, 922, 933, 935, 936, 882, 875, 885, 878])
            (.split 15
                (.cell 116 [937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950,
                  951, 952, 953, 954, 955, 956, 957, 958, 959, 960])
                (.absurd 961)))
        (.split 28
            (.split 30
                (.split 31
                    (.cell 117 [962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974,
                      975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987])
                    (.split 29
                        (.cell 118 [988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999,
                          1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011,
                          1012, 1013])
                        (.absurd 1014)))
                (.split 15
                    (.split 31
                        (.cell 119 [988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999,
                          1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1015, 1016, 1017, 1018,
                          1013, 1019])
                        (.split 29
                            (.cell 120 [1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029,
                              1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040,
                              1041, 1042, 1043, 1044, 1045])
                            (.absurd 1046)))
                    (.absurd 1047)))
            (.absurd 1048)))

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells
      (((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[10] + length[11]` in the row-04
symmetry chamber, with leaves selecting cells 121, 122 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart47 : CompactCellTree :=
  .split 26
    (.split 30
        (.cell 121 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 908, 853, 909,
          859, 910, 1049, 858, 851, 860, 854, 918, 932])
        (.split 15
            (.cell 122 [862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 920, 877,
              921, 922, 923, 1050, 882, 925, 926, 885, 927, 934])
            (.absurd 930)))
    (.absurd 931)

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
      (((((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0,
      -1, -1, 0, -1, 1, 0, 1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0,
      -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 123, 124 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart48 : CompactCellTree :=
  .split 22
    (.absurd 813)
    (.split 25
        (.split 30
            (.cell 123 [766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 1051, 781,
              901, 902, 1052, 1053, 906, 905, 788, 779, 1054, 1055, 1056])
            (.split 15
                (.cell 124 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 908,
                  853, 909, 859, 1057, 1058, 915, 912, 1059, 860, 918, 1060, 1061])
                (.absurd 917)))
        (.absurd 1062))

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells
      (((((((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
      -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -2, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 322 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart49 : CompactCellTree :=
  .absurd 322

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells
      (((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0,
      0, 0, 0, 1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[3] - length[5] + length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 18, 125, 126, 127, 128, 129, 130, 131, 132, 133 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart50 : CompactCellTree :=
  .split 23
    (.split 12
        (.absurd 709)
        (.split 20
            (.cell 125 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 1063, 368,
              295, 634, 710, 293, 374, 438, 294, 711])
            (.split 21
                (.cell 18 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 1064,
                  380, 378, 713, 315, 316, 382, 439, 714, 321])
                (.split 22
                    (.split 16
                        (.cell 126 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466,
                          467, 1065, 469, 592, 636, 473, 476, 479, 1066, 470])
                        (.split 14
                            (.cell 127 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                              650, 1067, 659, 716, 719, 656, 720, 662, 1068, 717, 655, 721])
                            (.split 27
                                (.cell 128 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                                  733, 734, 1069, 1070, 735, 738, 739, 740, 741, 742, 1071, 736])
                                (.split 28
                                    (.split 31
                                        (.cell 129 [743, 744, 745, 746, 747, 748, 749, 750, 751,
                                          752, 753, 754, 755, 1072, 1073, 756, 759, 760, 761, 762,
                                          1074, 757, 763, 764, 765])
                                        (.split 29
                                            (.cell 130 [766, 767, 768, 769, 770, 771, 772, 773,
                                              774, 775, 776, 777, 778, 1075, 1076, 779, 782, 783,
                                              784, 785, 1077, 780, 786, 787, 788])
                                            (.absurd 1078)))
                                    (.absurd 1079)))))
                    (.split 26
                        (.split 13
                            (.cell 131 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                              650, 1067, 659, 716, 719, 662, 791, 656, 1068, 717, 792, 793])
                            (.split 25
                                (.cell 132 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                                  733, 734, 1069, 1070, 735, 738, 794, 795, 740, 1071, 736, 796,
                                  797, 798])
                                (.cell 133 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                                  733, 734, 1069, 1070, 735, 738, 740, 798, 741, 1071, 736, 796,
                                  797])))
                        (.absurd 799))))))
    (.absurd 269)

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 217 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart51 : CompactCellTree :=
  .absurd 217

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1080 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart52 : CompactCellTree :=
  .absurd 1080

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1081 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart53 : CompactCellTree :=
  .absurd 1081

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0,
      -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1082 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart54 : CompactCellTree :=
  .absurd 1082

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff
      [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 23, 134, 135, 136, 137, 138, 139, 140, 141
and Farkas receipts excluding inconsistent sign branches. -/
def treePart55 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 134 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 1083, 407, 1084,
          409, 803, 804, 453, 1085, 414, 446, 418, 805])
        (.split 21
            (.cell 23 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 1086, 1087,
              1088, 592, 806, 472, 473, 1065, 1066, 470, 807, 808])
            (.split 16
                (.split 22
                    (.cell 135 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 1089,
                      1090, 1091, 735, 738, 742, 740, 812, 1069, 1071, 736])
                    (.split 26
                        (.cell 136 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                          1092, 1093, 1094, 830, 831, 1095, 833, 832, 1096, 1097, 1098, 889, 1099])
                        (.absurd 1100)))
                (.split 14
                    (.cell 137 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 1089,
                      1090, 1091, 735, 738, 742, 1101, 740, 1069, 1071, 736, 812, 813])
                    (.split 27
                        (.cell 138 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                          1092, 1093, 1094, 830, 831, 833, 834, 1102, 832, 1096, 1097, 1098])
                        (.split 28
                            (.split 31
                                (.cell 139 [766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776,
                                  777, 1103, 1104, 1105, 779, 1106, 783, 906, 785, 1075, 1077, 780,
                                  902, 788, 1107])
                                (.split 29
                                    (.cell 140 [838, 839, 840, 841, 842, 843, 844, 845, 846, 847,
                                      848, 849, 1108, 1109, 1110, 854, 1111, 856, 915, 858, 1112,
                                      1113, 1114, 1115, 1116, 860])
                                    (.absurd 1117)))
                            (.absurd 1118)))))))
    (.split 22
        (.cell 137 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 1083, 407, 1084,
          409, 449, 412, 803, 416, 1085, 414, 446, 418, 1119])
        (.split 20
            (.cell 134 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 1086, 1087,
              1088, 592, 807, 1120, 637, 1065, 1066, 470, 479, 1121])
            (.split 21
                (.cell 23 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 1122, 1123,
                  1124, 716, 1125, 1126, 656, 1067, 1068, 717, 721, 1127])
                (.split 25
                    (.cell 141 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 1089,
                      1090, 1091, 735, 738, 794, 795, 740, 1069, 1071, 736, 796, 1128, 813])
                    (.absurd 1129)))))

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1130 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart56 : CompactCellTree :=
  .absurd 1130

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0,
      0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1131 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart57 : CompactCellTree :=
  .absurd 1131

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart58 : CompactCellTree :=
  .absurd 82

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1132 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart59 : CompactCellTree :=
  .absurd 1132

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 337 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart60 : CompactCellTree :=
  .absurd 337

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1133 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart61 : CompactCellTree :=
  .absurd 1133

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1134 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart62 : CompactCellTree :=
  .absurd 1134

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 142, 143, 144, 145 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart63 : CompactCellTree :=
  .split 10
    (.split 22
        (.cell 142 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378, 313, 630,
          392, 316, 1135, 320, 1136, 384, 319, 1137])
        (.split 26
            (.cell 143 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409, 1084,
              1138, 449, 412, 588, 417, 1139, 451, 1140, 1141, 1142])
            (.absurd 1143)))
    (.split 23
        (.split 22
            (.cell 144 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409, 1084,
              1138, 449, 412, 588, 417, 1139, 414, 1144, 418, 1141])
            (.split 26
                (.cell 145 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 592,
                  1088, 1145, 636, 473, 593, 478, 1146, 1066, 1147, 1148, 1149, 1150])
                (.absurd 1151)))
        (.absurd 1152))

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 93, 127, 146, 147 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart64 : CompactCellTree :=
  .split 10
    (.split 22
        (.cell 93 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409, 451, 416,
          449, 412, 588, 417, 418, 1141])
        (.split 26
            (.cell 146 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 592, 477,
              618, 636, 473, 593, 478, 1148, 1149, 1150])
            (.absurd 1153)))
    (.split 23
        (.split 22
            (.cell 127 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 477, 1145,
              592, 636, 473, 593, 478, 1066, 1154, 479, 1149])
            (.split 26
                (.cell 147 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 1155,
                  1156, 716, 719, 656, 1157, 1158, 1068, 1159, 792, 1160, 1161])
                (.absurd 1162)))
        (.absurd 1163))

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] + length[2] - length[3] - length[5] + length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 101, 109, 110, 111, 112, 148 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart65 : CompactCellTree :=
  .split 9
    (.split 22
        (.cell 101 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 444, 416,
          1164, 409, 449, 412, 588, 417, 418, 1141])
        (.split 26
            (.cell 148 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 618,
              477, 592, 636, 473, 593, 478, 1148, 1149, 1150])
            (.absurd 1165)))
    (.split 19
        (.split 22
            (.split 30
                (.cell 109 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 1166,
                  1167, 655, 719, 656, 1157, 1158, 657, 662, 716, 793, 1160])
                (.split 15
                    (.cell 110 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734,
                      1168, 1169, 739, 738, 742, 1170, 1171, 1172, 1173, 1174, 798, 1175])
                    (.absurd 1176)))
            (.split 26
                (.split 30
                    (.cell 111 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734,
                      1168, 1177, 739, 738, 742, 1170, 1171, 809, 740, 735, 796, 1175, 1178])
                    (.split 15
                        (.cell 112 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                          826, 1179, 1180, 1181, 831, 832, 1182, 1183, 1184, 1185, 834, 889, 1186,
                          1187])
                        (.absurd 1188)))
                (.absurd 1189)))
        (.absurd 1190))

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells
      ((((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 137, 149 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart66 : CompactCellTree :=
  .split 10
    (.absurd 329)
    (.split 17
        (.absurd 1191)
        (.split 18
            (.absurd 1192)
            (.split 23
                (.split 24
                    (.split 22
                        (.cell 137 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          1193, 407, 416, 409, 449, 412, 588, 417, 1194, 414, 451, 418, 1141])
                        (.split 26
                            (.cell 149 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466,
                              1195, 1087, 618, 592, 636, 473, 593, 478, 1196, 1066, 477, 1148,
                              1149, 1150])
                            (.absurd 1197)))
                    (.absurd 1198))
                (.absurd 1199))))

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart67 : CompactCellTree :=
  .absurd 82

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1132 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart68 : CompactCellTree :=
  .absurd 1132

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1200 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart69 : CompactCellTree :=
  .absurd 1200

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1201 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart70 : CompactCellTree :=
  .absurd 1201

theorem treePart70_check :
    treePart70.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 60, 98, 107, 123, 124, 132, 150, 151 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart71 : CompactCellTree :=
  .split 17
    (.cell 150 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 512, 1202, 1203, 364,
      625, 496, 1204, 1205, 366, 580, 1206, 1207])
    (.split 18
        (.cell 60 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 535, 1208, 376,
          671, 296, 1209, 538, 1210, 613, 1211, 1212])
        (.split 8
            (.split 10
                (.cell 98 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  416, 418, 449, 1213, 417, 1214, 1140, 1141, 1142])
                (.split 23
                    (.cell 132 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      618, 470, 592, 636, 1215, 478, 1216, 1066, 1217, 1148, 1149, 1150])
                    (.absurd 1218)))
            (.split 7
                (.cell 151 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  418, 446, 449, 1213, 417, 1214, 1219, 416, 1140, 1141, 1142])
                (.split 9
                    (.cell 107 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      468, 479, 618, 592, 636, 1215, 478, 1216, 1148, 1149, 1150])
                    (.split 19
                        (.split 30
                            (.cell 123 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 1168, 1220, 812, 738, 794, 1171, 1221, 809, 740, 735, 796, 1175,
                              1178])
                            (.split 15
                                (.cell 124 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824,
                                  825, 826, 1179, 1222, 833, 831, 1223, 1183, 1224, 1184, 1225,
                                  834, 889, 1186, 1187])
                                (.absurd 1226)))
                        (.absurd 1227))))))

theorem treePart71_check :
    treePart71.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 60, 141, 150, 151, 152 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart72 : CompactCellTree :=
  .split 10
    (.cell 151 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 498, 1203,
      364, 625, 496, 1204, 1228, 366, 580, 1206, 1207])
    (.split 17
        (.cell 150 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210,
          376, 671, 296, 1209, 1230, 294, 613, 1211, 1212])
        (.split 18
            (.cell 60 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
              392, 1232, 320, 1233, 544, 1234, 631, 1137, 1235])
            (.split 23
                (.split 24
                    (.cell 141 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 1236,
                      1087, 479, 592, 636, 1215, 478, 1216, 1237, 1066, 476, 1148, 1149, 1150])
                    (.cell 152 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 468,
                      476, 479, 592, 636, 1215, 478, 1216, 1237, 1066, 1148, 1149, 1150]))
                (.absurd 1238))))

theorem treePart72_check :
    treePart72.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1239 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart73 : CompactCellTree :=
  .absurd 1239

theorem treePart73_check :
    treePart73.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart74 : CompactCellTree :=
  .absurd 82

theorem treePart74_check :
    treePart74.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1240 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart75 : CompactCellTree :=
  .absurd 1240

theorem treePart75_check :
    treePart75.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 386 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart76 : CompactCellTree :=
  .absurd 386

theorem treePart76_check :
    treePart76.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0,
      0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 54, 92, 102, 113, 114, 126, 153, 154 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart77 : CompactCellTree :=
  .split 17
    (.cell 153 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 506, 1241, 800, 341,
      264, 436, 507, 1242, 273])
    (.split 18
        (.cell 54 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 531, 1243, 364,
          361, 513, 515, 532, 1203])
        (.split 8
            (.split 10
                (.cell 92 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378,
                  384, 319, 392, 316, 440, 1135])
                (.split 23
                    (.cell 126 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443,
                      451, 802, 409, 449, 412, 448, 588, 414, 1244])
                    (.absurd 1245)))
            (.split 7
                (.cell 154 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378,
                  319, 712, 392, 316, 440, 1135, 1234, 384])
                (.split 9
                    (.cell 102 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443,
                      444, 418, 451, 409, 449, 412, 448, 588])
                    (.split 30
                        (.split 19
                            (.cell 113 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                              650, 652, 1246, 662, 719, 656, 1247, 1157, 657, 793, 716])
                            (.absurd 1248))
                        (.split 19
                            (.split 15
                                (.cell 114 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                                  733, 734, 1168, 1249, 812, 738, 742, 1250, 1170, 1172, 1251, 740])
                                (.absurd 1252))
                            (.absurd 1253)))))))

theorem treePart77_check :
    treePart77.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[3] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 54, 135, 153, 154, 155 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart78 : CompactCellTree :=
  .split 10
    (.cell 154 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261, 335, 800,
      341, 264, 436, 507, 1254, 273])
    (.split 17
        (.cell 153 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 512, 1202, 1203,
          364, 361, 513, 515, 1205, 366])
        (.split 18
            (.cell 54 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 535, 1208,
              376, 292, 612, 584, 538, 1210])
            (.split 23
                (.split 24
                    (.cell 135 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 1255,
                      407, 418, 409, 449, 412, 448, 588, 1193, 414, 416])
                    (.cell 155 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 444,
                      416, 418, 409, 449, 412, 448, 588, 1193, 414]))
                (.absurd 1256))))

theorem treePart78_check :
    treePart78.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1,
      0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1201 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart79 : CompactCellTree :=
  .absurd 1201

theorem treePart79_check :
    treePart79.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[2] + length[3] + length[5] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 55, 136, 156, 157, 158, 159 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart80 : CompactCellTree :=
  .split 6
    (.split 17
        (.cell 156 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210,
          376, 296, 584, 292, 1230, 294, 613, 1257])
        (.split 18
            (.cell 55 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
              392, 320, 1135, 316, 544, 1234, 631, 1258])
            (.split 10
                (.cell 157 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  446, 1084, 449, 417, 588, 412, 1259, 418, 1140, 1260])
                (.split 23
                    (.cell 158 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 470, 1088, 636, 478, 593, 473, 1261, 1066, 1262, 1148, 1263])
                    (.absurd 1264)))))
    (.split 10
        (.cell 157 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 438,
          1210, 376, 296, 584, 292, 1265, 294, 613, 1257])
        (.split 17
            (.cell 156 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 311, 1266,
              1234, 392, 320, 1135, 316, 1267, 319, 631, 1258])
            (.split 18
                (.cell 55 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 586,
                  1268, 449, 417, 588, 412, 1269, 1219, 1140, 1260])
                (.split 23
                    (.split 24
                        (.cell 136 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          717, 1123, 1270, 716, 719, 1158, 1157, 656, 1271, 1068, 1272, 792, 1273])
                        (.cell 159 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          657, 1272, 662, 716, 719, 1158, 1157, 656, 1271, 1068, 792, 1273]))
                    (.absurd 1264)))))

theorem treePart80_check :
    treePart80.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[3] - length[5] + length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 55, 97, 106, 121, 122, 131, 156 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart81 : CompactCellTree :=
  .split 8
    (.split 17
        (.cell 156 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210,
          376, 296, 584, 292, 1230, 294, 613, 1257])
        (.split 18
            (.cell 55 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
              392, 320, 1135, 316, 544, 1234, 631, 1258])
            (.split 10
                (.cell 97 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  1084, 418, 449, 417, 588, 412, 1140, 1260])
                (.split 23
                    (.cell 131 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      1088, 470, 592, 636, 478, 593, 473, 1066, 1274, 1148, 1263])
                    (.absurd 1275)))))
    (.split 9
        (.cell 106 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 294, 289,
          295, 376, 296, 584, 292, 613, 1257])
        (.split 17
            (.cell 156 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 311, 1266,
              1234, 392, 320, 1135, 316, 1267, 319, 631, 1258])
            (.split 18
                (.cell 55 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 586,
                  1268, 449, 417, 588, 412, 1269, 1219, 1140, 1260])
                (.split 19
                    (.split 30
                        (.cell 121 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          650, 652, 1124, 793, 719, 1158, 1157, 656, 657, 662, 716, 792, 1273])
                        (.split 15
                            (.cell 122 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 1168, 1091, 798, 738, 1171, 1170, 742, 1172, 810, 740, 796,
                              1276])
                            (.absurd 1277)))
                    (.absurd 1278)))))

theorem treePart81_check :
    treePart81.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++ [aff [0,
      0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0,
      1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1279 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart82 : CompactCellTree :=
  .absurd 1279

theorem treePart82_check :
    treePart82.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart83 : CompactCellTree :=
  .absurd 82

theorem treePart83_check :
    treePart83.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1132 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart84 : CompactCellTree :=
  .absurd 1132

theorem treePart84_check :
    treePart84.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1201 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart85 : CompactCellTree :=
  .absurd 1201

theorem treePart85_check :
    treePart85.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0,
      0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[2] + length[3] + length[5] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 62, 160, 161, 162, 163, 164 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart86 : CompactCellTree :=
  .split 6
    (.split 17
        (.cell 160 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210,
          584, 290, 288, 292, 1230, 294, 376, 612])
        (.split 18
            (.cell 62 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
              1135, 314, 630, 316, 544, 1234, 392, 440])
            (.split 10
                (.cell 161 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  446, 1084, 588, 410, 1138, 412, 1259, 418, 449, 448])
                (.split 23
                    (.cell 162 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 470, 1088, 593, 471, 1145, 473, 1261, 1066, 1262, 636, 475])
                    (.absurd 1264)))))
    (.split 10
        (.cell 161 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 438,
          1210, 584, 290, 288, 292, 1265, 294, 376, 612])
        (.split 17
            (.cell 160 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 311, 1266,
              1234, 1135, 314, 630, 316, 1267, 319, 392, 440])
            (.split 18
                (.cell 62 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 586,
                  1268, 588, 410, 1138, 412, 1269, 1219, 449, 448])
                (.split 23
                    (.split 24
                        (.cell 163 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          717, 1123, 1270, 716, 1157, 654, 1156, 656, 1271, 1068, 1272, 719, 1247])
                        (.cell 164 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          657, 1272, 662, 716, 1157, 654, 1156, 656, 1271, 1068, 719, 1247]))
                    (.absurd 1264)))))

theorem treePart86_check :
    treePart86.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[3] - length[5] + length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 62, 160, 165, 166, 167, 168, 169 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart87 : CompactCellTree :=
  .split 8
    (.split 17
        (.cell 160 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210,
          584, 290, 288, 292, 1230, 294, 376, 612])
        (.split 18
            (.cell 62 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
              1135, 314, 630, 316, 544, 1234, 392, 440])
            (.split 10
                (.cell 165 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  1084, 418, 588, 410, 1138, 412, 449, 448])
                (.split 23
                    (.cell 166 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      1088, 470, 592, 593, 471, 1145, 473, 1066, 1274, 636, 475])
                    (.absurd 1218)))))
    (.split 9
        (.cell 167 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 294, 289,
          295, 584, 290, 288, 292, 376, 612])
        (.split 17
            (.cell 160 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 311, 1266,
              1234, 1135, 314, 630, 316, 1267, 319, 392, 440])
            (.split 18
                (.cell 62 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 586,
                  1268, 588, 410, 1138, 412, 1269, 1219, 449, 448])
                (.split 19
                    (.split 30
                        (.cell 168 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          650, 652, 1124, 793, 1157, 654, 1156, 656, 657, 662, 716, 719, 1247])
                        (.split 15
                            (.cell 169 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 1168, 1091, 798, 1170, 1280, 1281, 742, 1172, 810, 740, 738,
                              1250])
                            (.absurd 1277)))
                    (.absurd 1278)))))

theorem treePart87_check :
    treePart87.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1282 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart88 : CompactCellTree :=
  .absurd 1282

theorem treePart88_check :
    treePart88.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
      -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1283 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart89 : CompactCellTree :=
  .absurd 1283

theorem treePart89_check :
    treePart89.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++ [aff
      [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 59, 140, 170, 171, 172, 173 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart90 : CompactCellTree :=
  .split 17
    (.cell 170 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210, 584,
      290, 288, 292, 1230, 294, 612, 692, 370])
    (.split 18
        (.cell 59 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
          1135, 314, 630, 316, 544, 1234, 440, 546, 712])
        (.split 6
            (.split 10
                (.cell 171 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 592,
                  1088, 476, 593, 471, 1145, 473, 1146, 479, 475, 596, 715])
                (.split 23
                    (.cell 172 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650,
                      716, 1124, 655, 1157, 654, 1156, 656, 1284, 1068, 1285, 1247, 661, 718])
                    (.absurd 1286)))
            (.split 10
                (.cell 171 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 592,
                  1088, 1287, 593, 471, 1145, 473, 1146, 479, 475, 596, 715])
                (.split 23
                    (.split 24
                        (.cell 140 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                          1091, 1090, 1288, 735, 1170, 1280, 1281, 742, 1289, 1071, 1290, 1250,
                          1291, 737])
                        (.cell 173 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                          809, 1290, 740, 735, 1170, 1280, 1281, 742, 1289, 1071, 1250, 1291, 737]))
                    (.absurd 1147)))))

theorem treePart90_check :
    treePart90.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 59, 96, 105, 118, 120, 130, 170 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart91 : CompactCellTree :=
  .split 17
    (.cell 170 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 287, 1229, 1210, 584,
      290, 288, 292, 1230, 294, 612, 692, 370])
    (.split 18
        (.cell 59 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 542, 1231,
          1135, 314, 630, 316, 544, 1234, 440, 546, 712])
        (.split 8
            (.split 10
                (.cell 96 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 592,
                  476, 479, 593, 471, 1145, 473, 475, 596, 715])
                (.split 23
                    (.cell 130 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650,
                      655, 1124, 716, 1157, 654, 1156, 656, 1068, 1292, 1247, 661, 718])
                    (.absurd 1286)))
            (.split 9
                (.cell 105 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468,
                  479, 476, 592, 593, 471, 1145, 473, 475, 596, 715])
                (.split 19
                    (.split 30
                        (.cell 118 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                          734, 1168, 739, 812, 1170, 1280, 1281, 742, 809, 740, 735, 1250, 1291,
                          737])
                        (.split 15
                            (.cell 120 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
                              826, 1179, 1181, 833, 1182, 1293, 1294, 832, 1184, 1295, 834, 1296,
                              1297, 829])
                            (.absurd 1226)))
                    (.absurd 1298)))))

theorem treePart91_check :
    treePart91.check splitForms farkasReceipts cells
      (((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])])
      ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1299 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart92 : CompactCellTree :=
  .absurd 1299

theorem treePart92_check :
    treePart92.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1,
      -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1282 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart93 : CompactCellTree :=
  .absurd 1282

theorem treePart93_check :
    treePart93.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart94 : CompactCellTree :=
  .absurd 82

theorem treePart94_check :
    treePart94.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) =
      true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1132 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart95 : CompactCellTree :=
  .absurd 1132

theorem treePart95_check :
    treePart95.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1300 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart96 : CompactCellTree :=
  .absurd 1300

theorem treePart96_check :
    treePart96.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, -1, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[10] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 19, 142, 143, 151, 154, 157, 171, 174, 175, 176
and Farkas receipts excluding inconsistent sign branches. -/
def treePart97 : CompactCellTree :=
  .split 20
    (.cell 174 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 431, 244,
      558, 622, 505, 1301, 432, 240, 623])
    (.split 21
        (.cell 19 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261, 272, 267,
          624, 263, 264, 1302, 436, 605, 268])
        (.split 13
            (.split 14
                (.split 22
                    (.cell 142 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      378, 442, 320, 392, 316, 313, 384, 1303, 440, 319, 1304])
                    (.split 26
                        (.cell 143 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          443, 409, 453, 417, 449, 412, 1084, 451, 1305, 448, 1140, 1306, 1307])
                        (.absurd 1308)))
                (.split 22
                    (.split 16
                        (.cell 154 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          443, 409, 453, 417, 449, 412, 416, 418, 1305, 448])
                        (.split 27
                            (.cell 175 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466,
                              467, 592, 637, 478, 636, 618, 479, 593, 473, 1309, 475])
                            (.split 28
                                (.split 31
                                    (.cell 176 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731,
                                      732, 733, 734, 735, 741, 1171, 1101, 1280, 1310, 742, 1311,
                                      1250, 738, 740, 1170])
                                    (.split 29
                                        (.cell 171 [814, 815, 816, 817, 818, 819, 820, 821, 822,
                                          823, 824, 825, 826, 830, 1102, 1183, 1095, 1293, 1312,
                                          832, 1313, 1296, 1314, 1297, 834])
                                        (.absurd 790)))
                                (.absurd 1315))))
                    (.split 26
                        (.cell 157 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          443, 409, 453, 417, 449, 1084, 1316, 412, 1305, 448, 1140, 418])
                        (.absurd 1308))))
            (.split 22
                (.cell 142 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295,
                  293, 296, 376, 292, 634, 289, 1317, 612, 294, 1318])
                (.split 25
                    (.cell 151 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      378, 442, 320, 392, 1232, 1319, 319, 1303, 440, 631, 1320, 714])
                    (.absurd 633)))))

theorem treePart97_check :
    treePart97.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1321 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart98 : CompactCellTree :=
  .absurd 1321

theorem treePart98_check :
    treePart98.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) =
      true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[10] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 144, 145, 177, 178, 179 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart99 : CompactCellTree :=
  .split 20
    (.cell 177 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 1322, 496,
      541, 1323, 515, 1324, 372, 1325, 366, 1326])
    (.split 21
        (.cell 178 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 293, 296,
          1327, 291, 292, 1317, 374, 1328, 634, 297])
        (.split 13
            (.split 22
                (.cell 144 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  453, 417, 449, 412, 416, 446, 1305, 414, 1329, 418, 1330])
                (.split 26
                    (.cell 145 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 637, 478, 636, 473, 618, 470, 1309, 1066, 1331, 1148, 1332, 1333])
                    (.absurd 1334)))
            (.split 22
                (.cell 144 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  453, 417, 449, 412, 803, 446, 1305, 414, 1329, 418, 1330])
                (.split 25
                    (.cell 179 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 637, 478, 636, 1215, 470, 1335, 1309, 1066, 1331, 1148, 1332, 1333])
                    (.absurd 1336)))))

theorem treePart99_check :
    treePart99.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[9] + length[11]` in the row-04
symmetry chamber, with leaves selecting cells 158, 172, 177, 178, 180, 181, 182 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart100 : CompactCellTree :=
  .split 16
    (.split 20
        (.cell 177 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 293, 296,
          634, 710, 584, 1317, 374, 1328, 294, 711])
        (.split 21
            (.cell 178 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378, 442,
              320, 713, 315, 316, 1303, 382, 1337, 714, 321])
            (.split 22
                (.cell 180 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  453, 417, 449, 412, 418, 1084, 1305, 414, 1329])
                (.split 26
                    (.cell 158 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      592, 637, 478, 636, 470, 1088, 473, 1309, 1066, 1331, 1148, 1338])
                    (.absurd 799)))))
    (.split 20
        (.cell 177 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295, 293, 296,
          634, 710, 584, 1317, 374, 1328, 294, 711])
        (.split 21
            (.cell 178 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 378, 442,
              320, 713, 315, 316, 1303, 382, 1337, 714, 321])
            (.split 27
                (.cell 181 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 409,
                  453, 417, 449, 1084, 418, 588, 412, 1305, 414, 1329])
                (.split 28
                    (.split 31
                        (.cell 182 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          650, 716, 1339, 1158, 1124, 654, 793, 656, 1340, 1068, 1341, 719, 662,
                          1157])
                        (.split 29
                            (.cell 172 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              734, 735, 741, 1171, 1091, 1280, 798, 742, 1311, 1071, 1342, 739,
                              1291, 740])
                            (.absurd 1343)))
                    (.absurd 1344)))))

theorem treePart100_check :
    treePart100.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0,
      0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, -1, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0,
      1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1345 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart101 : CompactCellTree :=
  .absurd 1345

theorem treePart101_check :
    treePart101.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0,
      -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1346 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart102 : CompactCellTree :=
  .absurd 1346

theorem treePart102_check :
    treePart102.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1347 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart103 : CompactCellTree :=
  .absurd 1347

theorem treePart103_check :
    treePart103.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 154, 157, 158, 180 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart104 : CompactCellTree :=
  .split 22
    (.split 10
        (.cell 154 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261, 272, 267,
          341, 264, 335, 259, 1302, 273])
        (.split 23
            (.cell 180 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 1322,
              496, 364, 361, 363, 495, 1324, 372, 1325])
            (.absurd 1348)))
    (.split 26
        (.split 10
            (.cell 157 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 1322,
              496, 364, 357, 495, 361, 1324, 366, 580, 674])
            (.split 23
                (.cell 158 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295,
                  293, 296, 376, 367, 288, 292, 1317, 374, 1328, 613, 1349])
                (.absurd 1350)))
        (.absurd 1351))

theorem treePart104_check :
    treePart104.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[5] - length[6] + length[8] + length[9] + length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 161, 162, 171, 172 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart105 : CompactCellTree :=
  .split 27
    (.split 14
        (.absurd 1352)
        (.split 28
            (.split 10
                (.cell 161 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 295,
                  293, 296, 288, 290, 289, 292, 1317, 294, 376, 370])
                (.split 23
                    (.cell 162 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      378, 442, 320, 630, 314, 313, 316, 1303, 382, 1337, 392, 712])
                    (.absurd 1353)))
            (.absurd 1354)))
    (.split 14
        (.absurd 602)
        (.split 28
            (.split 29
                (.split 10
                    (.cell 171 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      378, 442, 320, 1355, 314, 313, 316, 1303, 319, 712, 546, 384])
                    (.split 23
                        (.cell 172 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          443, 409, 453, 417, 1356, 410, 1084, 412, 1305, 414, 1329, 802, 1357,
                          451])
                        (.absurd 1358)))
                (.absurd 1359))
            (.absurd 1354)))

theorem treePart105_check :
    treePart105.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, -1, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 151, 179 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart106 : CompactCellTree :=
  .split 1
    (.absurd 1346)
    (.split 3
        (.absurd 1347)
        (.split 22
            (.absurd 1360)
            (.split 25
                (.split 10
                    (.cell 151 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258,
                      261, 272, 267, 341, 603, 260, 335, 1302, 273, 528, 1361, 578])
                    (.split 23
                        (.cell 179 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354,
                          355, 356, 1322, 496, 364, 625, 357, 363, 1324, 372, 1325, 580, 1362, 581])
                        (.absurd 1348)))
                (.absurd 1363))))

theorem treePart106_check :
    treePart106.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart107 : CompactCellTree :=
  .absurd 82

theorem treePart107_check :
    treePart107.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0,
      1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 509 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart108 : CompactCellTree :=
  .absurd 509

theorem treePart108_check :
    treePart108.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0,
      -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1347 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart109 : CompactCellTree :=
  .absurd 1347

theorem treePart109_check :
    treePart109.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1364 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart110 : CompactCellTree :=
  .absurd 1364

theorem treePart110_check :
    treePart110.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 23, 134, 135, 136, 137, 138, 139, 140, 141
and Farkas receipts excluding inconsistent sign branches. -/
def treePart111 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 134 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 293, 388, 1365,
          295, 634, 710, 584, 1317, 374, 1328, 294, 711])
        (.split 21
            (.cell 23 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 442, 390, 1366,
              378, 713, 315, 316, 1303, 382, 1337, 714, 321])
            (.split 22
                (.split 14
                    (.cell 137 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 637,
                      1087, 1367, 592, 636, 473, 1088, 479, 1309, 1066, 1331, 476, 807])
                    (.split 16
                        (.cell 135 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          1339, 1123, 1368, 716, 719, 656, 655, 662, 1340, 1068, 1341])
                        (.split 27
                            (.cell 138 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733,
                              741, 1090, 1369, 735, 738, 739, 740, 1170, 742, 1311, 1071, 1342])
                            (.split 28
                                (.split 31
                                    (.cell 139 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752,
                                      753, 754, 765, 1370, 1371, 756, 759, 760, 761, 762, 1372,
                                      1074, 1373, 763, 764, 1374])
                                    (.split 29
                                        (.cell 140 [766, 767, 768, 769, 770, 771, 772, 773, 774,
                                          775, 776, 777, 1107, 1104, 1375, 779, 782, 783, 784, 785,
                                          1376, 1077, 1377, 786, 787, 788])
                                        (.absurd 789)))
                                (.absurd 1378)))))
                (.split 26
                    (.cell 136 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 637,
                      1087, 1367, 592, 636, 1088, 1379, 473, 1309, 1066, 1331, 1148, 479])
                    (.absurd 799)))))
    (.split 22
        (.cell 137 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 293, 388, 1365,
          295, 376, 292, 634, 289, 1317, 374, 1328, 294, 1318])
        (.split 20
            (.cell 134 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 442, 390, 1366,
              378, 714, 1380, 1135, 1303, 382, 1337, 319, 1381])
            (.split 21
                (.cell 23 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 453, 407,
                  1382, 409, 1383, 411, 412, 1305, 414, 1329, 803, 1384])
                (.split 25
                    (.cell 141 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 637,
                      1087, 1367, 592, 636, 1215, 1379, 479, 1309, 1066, 1331, 1148, 1385, 807])
                    (.absurd 1386)))))

theorem treePart111_check :
    treePart111.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 1, -1, -1, 0, -1,
      0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])])
      = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1387 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart112 : CompactCellTree :=
  .absurd 1387

theorem treePart112_check :
    treePart112.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1388 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart113 : CompactCellTree :=
  .absurd 1388

theorem treePart113_check :
    treePart113.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff
      [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 1,
      0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1,
      0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 137, 141, 149 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart114 : CompactCellTree :=
  .split 13
    (.split 1
        (.absurd 1389)
        (.split 10
            (.absurd 1390)
            (.split 3
                (.absurd 571)
                (.split 23
                    (.split 24
                        (.split 22
                            (.cell 137 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                              293, 388, 1365, 295, 376, 292, 368, 367, 1317, 374, 1328, 294, 1391])
                            (.split 26
                                (.cell 149 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308,
                                  309, 442, 390, 1366, 378, 392, 316, 380, 379, 1303, 382, 1337,
                                  631, 1392, 1393])
                                (.absurd 1394)))
                        (.absurd 1395))
                    (.absurd 1396)))))
    (.split 1
        (.absurd 1389)
        (.split 10
            (.absurd 1390)
            (.split 3
                (.absurd 571)
                (.split 22
                    (.absurd 703)
                    (.split 23
                        (.split 24
                            (.split 25
                                (.cell 141 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308,
                                  309, 442, 390, 1366, 378, 392, 1232, 379, 1397, 1303, 382, 1337,
                                  631, 1392, 1393])
                                (.absurd 1398))
                            (.absurd 1399))
                        (.absurd 1400))))))

theorem treePart114_check :
    treePart114.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 135, 136 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart115 : CompactCellTree :=
  .split 1
    (.absurd 1389)
    (.split 10
        (.absurd 1390)
        (.split 3
            (.absurd 1401)
            (.split 22
                (.split 23
                    (.split 24
                        (.cell 135 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          293, 388, 1365, 295, 376, 292, 438, 368, 1317, 374, 1328])
                        (.absurd 1399))
                    (.absurd 1400))
                (.split 23
                    (.split 24
                        (.split 26
                            (.cell 136 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              442, 390, 1366, 378, 392, 379, 380, 316, 1303, 382, 1337, 631, 1402])
                            (.absurd 1403))
                        (.absurd 1399))
                    (.absurd 1400)))))

theorem treePart115_check :
    treePart115.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 140, 163 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart116 : CompactCellTree :=
  .split 1
    (.absurd 1389)
    (.split 10
        (.absurd 1390)
        (.split 3
            (.absurd 571)
            (.split 27
                (.split 23
                    (.split 24
                        (.split 28
                            (.cell 163 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              442, 390, 1366, 378, 380, 314, 319, 316, 1303, 382, 1337, 392, 439])
                            (.absurd 1404))
                        (.absurd 1399))
                    (.absurd 1400))
                (.split 23
                    (.split 24
                        (.split 28
                            (.split 29
                                (.cell 140 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 453, 407, 1382, 409, 445, 410, 416, 412, 1305, 414, 1329,
                                  446, 1357, 418])
                                (.absurd 1405))
                            (.absurd 1404))
                        (.absurd 1399))
                    (.absurd 1400)))))

theorem treePart116_check :
    treePart116.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, -1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1406 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart117 : CompactCellTree :=
  .absurd 1406

theorem treePart117_check :
    treePart117.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0,
      -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 17, 91, 92, 93, 94, 95, 96, 97, 98, 99 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart118 : CompactCellTree :=
  .split 3
    (.cell 17 [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 180, 223, 181, 523,
      176, 177, 183, 224])
    (.split 12
        (.absurd 1300)
        (.split 20
            (.cell 91 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 244,
              433, 558, 622, 505, 240, 623])
            (.split 21
                (.cell 17 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  267, 339, 624, 263, 264, 605, 268])
                (.split 22
                    (.split 16
                        (.cell 92 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          295, 296, 368, 376, 292, 289, 294])
                        (.split 14
                            (.cell 93 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 378, 320, 380, 392, 316, 1407, 319, 313, 714])
                            (.split 27
                                (.cell 94 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 409, 417, 445, 449, 1084, 418, 588, 412])
                                (.split 28
                                    (.split 31
                                        (.cell 95 [638, 639, 640, 641, 642, 643, 644, 645, 646,
                                          647, 648, 649, 650, 716, 1158, 659, 1124, 654, 1408, 656,
                                          719, 662, 1157])
                                        (.split 29
                                            (.cell 96 [722, 723, 724, 725, 726, 727, 728, 729, 730,
                                              731, 732, 733, 734, 735, 1171, 1070, 1091, 1280,
                                              1409, 742, 1410, 1291, 740])
                                            (.absurd 1411)))
                                    (.absurd 1412)))))
                    (.split 26
                        (.split 13
                            (.cell 97 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 378, 320, 380, 392, 319, 1413, 316, 631, 384])
                            (.split 25
                                (.cell 98 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 409, 417, 445, 449, 1213, 1316, 418, 1140, 1414, 451])
                                (.cell 99 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 409, 417, 445, 449, 418, 451, 588, 1140, 1414])))
                        (.absurd 1415))))))

theorem treePart118_check :
    treePart118.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1416 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart119 : CompactCellTree :=
  .absurd 1416

theorem treePart119_check :
    treePart119.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1321 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart120 : CompactCellTree :=
  .absurd 1321

theorem treePart120_check :
    treePart120.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 18, 125, 126, 127, 128, 129, 130, 131, 132
and Farkas receipts excluding inconsistent sign branches. -/
def treePart121 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 125 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 496, 1322,
          356, 541, 1323, 515, 372, 497, 366, 1326])
        (.split 21
            (.cell 18 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 296, 293,
              295, 1327, 291, 292, 374, 1417, 634, 297])
            (.split 16
                (.split 22
                    (.cell 126 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443,
                      417, 453, 409, 449, 412, 418, 416, 414, 1418])
                    (.split 26
                        (.cell 131 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466,
                          467, 478, 637, 592, 636, 470, 618, 473, 1066, 1419, 1148, 1420])
                        (.absurd 1336)))
                (.split 27
                    (.cell 128 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443,
                      417, 453, 409, 449, 416, 418, 588, 412, 414, 1418])
                    (.split 14
                        (.cell 127 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466,
                          467, 478, 637, 592, 636, 473, 470, 479, 1066, 1419, 595, 807])
                        (.split 28
                            (.split 31
                                (.cell 129 [722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                                  733, 734, 1171, 741, 735, 1421, 1280, 812, 742, 1071, 1422, 738,
                                  740, 1170])
                                (.split 29
                                    (.cell 130 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823,
                                      824, 825, 826, 1183, 1102, 830, 1222, 1293, 833, 832, 1097,
                                      1423, 1225, 1297, 834])
                                    (.absurd 1424)))
                            (.absurd 1425)))))))
    (.split 22
        (.cell 127 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 496, 1322,
          356, 364, 361, 541, 498, 372, 497, 366, 1426])
        (.split 20
            (.cell 125 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 296, 293,
              295, 634, 710, 584, 374, 1417, 294, 711])
            (.split 21
                (.cell 18 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 320,
                  442, 378, 713, 315, 316, 382, 1427, 714, 321])
                (.split 25
                    (.cell 132 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443,
                      417, 453, 409, 449, 1213, 1316, 418, 414, 1418, 1140, 1428, 803])
                    (.absurd 1429)))))

theorem treePart121_check :
    treePart121.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, 0, 1, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1430 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart122 : CompactCellTree :=
  .absurd 1430

theorem treePart122_check :
    treePart122.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 93, 127, 146, 147 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart123 : CompactCellTree :=
  .split 1
    (.absurd 1431)
    (.split 3
        (.absurd 1432)
        (.split 10
            (.split 22
                (.cell 93 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  267, 335, 341, 264, 339, 260, 273, 1361])
                (.split 26
                    (.cell 146 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 496, 363, 364, 361, 358, 357, 580, 1362, 1433])
                    (.absurd 1434)))
            (.split 23
                (.split 22
                    (.cell 127 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      496, 1322, 356, 364, 361, 358, 357, 372, 497, 366, 1362])
                    (.split 26
                        (.cell 147 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 296, 293, 295, 376, 292, 368, 367, 374, 1417, 613, 1391, 1435])
                        (.absurd 1436)))
                (.absurd 1437))))

theorem treePart123_check :
    treePart123.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1,
      1, 0, 1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 17, 93, 98, 132 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart124 : CompactCellTree :=
  .split 1
    (.absurd 1431)
    (.split 10
        (.split 3
            (.cell 17 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 244,
              239, 558, 242, 243, 240, 245])
            (.split 22
                (.cell 93 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  267, 259, 341, 264, 605, 260, 273, 1361])
                (.split 25
                    (.cell 98 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 496, 495, 364, 625, 357, 1438, 580, 1362, 1433])
                    (.absurd 1439))))
        (.split 3
            (.absurd 1440)
            (.split 22
                (.absurd 1441)
                (.split 23
                    (.split 25
                        (.cell 132 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 296, 293, 295, 376, 671, 367, 1442, 374, 1417, 613, 1391, 1435])
                        (.absurd 1443))
                    (.absurd 1444)))))

theorem treePart124_check :
    treePart124.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 17, 92, 97, 126, 131 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart125 : CompactCellTree :=
  .split 1
    (.absurd 1431)
    (.split 10
        (.split 3
            (.cell 17 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 244,
              239, 558, 242, 243, 240, 245])
            (.split 22
                (.cell 92 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 261,
                  267, 259, 341, 264, 273, 339])
                (.split 26
                    (.cell 97 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 496, 495, 364, 357, 358, 361, 580, 1445])
                    (.absurd 1446))))
        (.split 3
            (.absurd 1447)
            (.split 22
                (.split 23
                    (.cell 126 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      496, 1322, 356, 364, 361, 498, 358, 372, 497])
                    (.absurd 1444))
                (.split 23
                    (.split 26
                        (.cell 131 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 296, 293, 295, 376, 367, 368, 292, 374, 1417, 613, 1448])
                        (.absurd 1443))
                    (.absurd 1444)))))

theorem treePart125_check :
    treePart125.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff
      [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 17, 96, 130, 165, 166 and Farkas receipts
excluding inconsistent sign branches. -/
def treePart126 : CompactCellTree :=
  .split 1
    (.absurd 1431)
    (.split 10
        (.split 3
            (.cell 17 [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 244,
              239, 558, 242, 243, 240, 245])
            (.split 27
                (.split 28
                    (.cell 165 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      356, 496, 495, 358, 359, 366, 361, 364, 498])
                    (.absurd 1449))
                (.split 28
                    (.split 29
                        (.cell 96 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286,
                          295, 296, 288, 368, 290, 289, 292, 438, 692, 294])
                        (.absurd 1450))
                    (.absurd 1451))))
        (.split 3
            (.absurd 1447)
            (.split 27
                (.split 23
                    (.split 28
                        (.cell 166 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 296, 293, 295, 368, 290, 294, 292, 374, 1417, 376, 438])
                        (.absurd 1452))
                    (.absurd 1444))
                (.split 23
                    (.split 28
                        (.split 29
                            (.cell 130 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 320, 442, 378, 380, 314, 384, 316, 382, 1427, 439, 546, 319])
                            (.absurd 1453))
                        (.absurd 1454))
                    (.absurd 1444)))))

theorem treePart126_check :
    treePart126.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 1, 0, 0,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      -1, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 82 to exclude the accumulated affine constraints in
this row-04 branch. -/
def treePart127 : CompactCellTree :=
  .absurd 82

theorem treePart127_check :
    treePart127.check splitForms farkasReceipts cells
      (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true :=
      by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 49, 183, 184, 185, 186, 187, 188, 189, 190, 191 and Farkas
receipts excluding inconsistent sign branches. -/
def treePart128 : CompactCellTree :=
  .split 3
    (.absurd 1455)
    (.split 19
        (.split 12
            (.absurd 1321)
            (.split 20
                (.cell 183 [246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 511,
                  267, 259, 605, 665, 507, 339, 261, 273, 667])
                (.split 21
                    (.cell 49 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      1456, 496, 495, 668, 360, 361, 358, 356, 541, 670])
                    (.split 22
                        (.split 16
                            (.cell 184 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 317, 320, 630, 392, 316, 384, 319, 380, 378])
                            (.split 14
                                (.cell 185 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 1457, 417, 1138, 449, 412, 1306, 418, 445, 409, 451,
                                  803])
                                (.split 27
                                    (.cell 186 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464,
                                      465, 466, 467, 474, 478, 1145, 636, 477, 479, 593, 473, 469,
                                      592])
                                    (.split 28
                                        (.split 31
                                            (.cell 187 [722, 723, 724, 725, 726, 727, 728, 729,
                                              730, 731, 732, 733, 734, 1168, 1171, 1281, 810, 1280,
                                              1458, 742, 1070, 735, 738, 740, 1170])
                                            (.split 29
                                                (.cell 188 [814, 815, 816, 817, 818, 819, 820, 821,
                                                  822, 823, 824, 825, 826, 1179, 1183, 1294, 828,
                                                  1293, 1459, 832, 1460, 830, 1461, 1297, 834])
                                                (.absurd 1462)))
                                        (.absurd 1463)))))
                        (.split 26
                            (.split 13
                                (.cell 189 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404,
                                  405, 443, 447, 417, 1138, 449, 418, 1464, 412, 445, 409, 1140,
                                  416])
                                (.split 25
                                    (.cell 190 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464,
                                      465, 466, 467, 474, 478, 1145, 636, 1215, 1379, 479, 469,
                                      592, 1148, 1465, 618])
                                    (.cell 191 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464,
                                      465, 466, 467, 474, 478, 1145, 636, 479, 618, 593, 469, 592,
                                      1148, 1465])))
                            (.absurd 1466))))))
        (.absurd 1467))

theorem treePart128_check :
    treePart128.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1347 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart129 : CompactCellTree :=
  .absurd 1347

theorem treePart129_check :
    treePart129.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1364 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart130 : CompactCellTree :=
  .absurd 1364

theorem treePart130_check :
    treePart130.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0,
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] + length[8] - length[9] - length[11]` in the
row-04 symmetry chamber, with leaves selecting cells 22, 110, 114, 116, 119, 120, 122, 124, 192
and Farkas receipts excluding inconsistent sign branches. -/
def treePart131 : CompactCellTree :=
  .split 13
    (.split 20
        (.cell 192 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 536, 296, 288,
          634, 710, 584, 1468, 368, 370, 294, 711])
        (.split 21
            (.cell 22 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 317, 320,
              630, 713, 315, 316, 1469, 380, 712, 714, 321])
            (.split 16
                (.split 22
                    (.cell 114 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      474, 478, 1145, 636, 473, 479, 476, 1470, 469, 715])
                    (.split 26
                        (.cell 122 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          650, 652, 1158, 1156, 719, 1124, 655, 656, 1471, 659, 718, 792, 1472])
                        (.absurd 1473)))
                (.split 27
                    (.cell 116 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      474, 478, 1145, 636, 476, 479, 593, 473, 1470, 469, 715])
                    (.split 14
                        (.cell 110 [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
                          650, 652, 1158, 1156, 719, 656, 1124, 662, 1471, 659, 718, 1474, 721])
                        (.split 28
                            (.split 31
                                (.cell 119 [814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824,
                                  825, 826, 1179, 1183, 1294, 1475, 1293, 890, 832, 1184, 1460,
                                  829, 831, 834, 1182])
                                (.split 29
                                    (.cell 120 [743, 744, 745, 746, 747, 748, 749, 750, 751, 752,
                                      753, 754, 755, 1476, 1477, 1478, 1479, 760, 895, 762, 1480,
                                      1073, 758, 1481, 1482, 764])
                                    (.absurd 1483)))
                            (.absurd 1484)))))))
    (.split 22
        (.cell 110 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 536, 296, 288,
          376, 292, 634, 289, 1468, 368, 370, 294, 1318])
        (.split 20
            (.cell 192 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 317, 320,
              630, 714, 1380, 1135, 1469, 380, 712, 319, 1381])
            (.split 21
                (.cell 22 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 443, 447,
                  417, 1138, 1383, 411, 412, 1485, 445, 802, 803, 1384])
                (.split 25
                    (.cell 124 [455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467,
                      474, 478, 1145, 636, 1215, 1379, 479, 1470, 469, 715, 1148, 1385, 807])
                    (.absurd 1386)))))

theorem treePart131_check :
    treePart131.check splitForms farkasReceipts cells
      ((((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1486 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart132 : CompactCellTree :=
  .absurd 1486

theorem treePart132_check :
    treePart132.check splitForms farkasReceipts cells
      (((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++ [aff [0, -1, 0, 0,
      0, 1, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0,
      0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1467 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart133 : CompactCellTree :=
  .absurd 1467

theorem treePart133_check :
    treePart133.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1, -1, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0,
      0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 110, 112, 185, 193 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart134 : CompactCellTree :=
  .split 1
    (.absurd 1389)
    (.split 3
        (.absurd 1487)
        (.split 19
            (.split 9
                (.split 22
                    (.cell 185 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      1488, 496, 363, 364, 361, 358, 357, 498, 356, 366, 1362])
                    (.split 26
                        (.cell 193 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 536, 296, 370, 376, 292, 368, 367, 438, 295, 613, 1391, 1435])
                        (.absurd 1489)))
                (.split 15
                    (.split 22
                        (.cell 110 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 536, 296, 370, 376, 292, 368, 367, 1468, 438, 289, 294, 1391])
                        (.split 26
                            (.cell 112 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 317, 320, 712, 392, 316, 380, 379, 1469, 439, 313, 631, 1392,
                              1393])
                            (.absurd 1394)))
                    (.absurd 684)))
            (.absurd 1490)))

theorem treePart134_check :
    treePart134.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 124, 190 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart135 : CompactCellTree :=
  .split 1
    (.absurd 1389)
    (.split 9
        (.split 3
            (.absurd 1491)
            (.split 22
                (.absurd 1492)
                (.split 19
                    (.split 25
                        (.cell 190 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 536, 296, 289, 376, 671, 367, 1442, 288, 295, 613, 1391, 1435])
                        (.absurd 1443))
                    (.absurd 1493))))
        (.split 3
            (.absurd 571)
            (.split 22
                (.absurd 703)
                (.split 19
                    (.split 15
                        (.split 25
                            (.cell 124 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 317, 320, 313, 392, 1232, 379, 1397, 1469, 630, 384, 631, 1392,
                              1393])
                            (.absurd 1398))
                        (.absurd 1494))
                    (.absurd 1493)))))

theorem treePart135_check :
    treePart135.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1, 1, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1,
      0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] - length[2] + length[5] - length[11]` in the row-04
symmetry chamber, with leaves selecting cells 114, 122, 184, 189 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart136 : CompactCellTree :=
  .split 1
    (.absurd 1389)
    (.split 9
        (.split 3
            (.absurd 1401)
            (.split 22
                (.split 19
                    (.cell 184 [343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
                      514, 496, 366, 364, 361, 498, 358, 495, 356])
                    (.absurd 1493))
                (.split 19
                    (.split 26
                        (.cell 189 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 536, 296, 289, 376, 367, 368, 292, 288, 295, 613, 1448])
                        (.absurd 1495))
                    (.absurd 1493))))
        (.split 3
            (.absurd 1401)
            (.split 22
                (.split 19
                    (.split 15
                        (.cell 114 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
                          286, 536, 296, 289, 376, 292, 438, 368, 1468, 288, 294])
                        (.absurd 1494))
                    (.absurd 1493))
                (.split 19
                    (.split 15
                        (.split 26
                            (.cell 122 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
                              310, 317, 320, 313, 392, 379, 380, 316, 1469, 630, 384, 631, 1402])
                            (.absurd 1403))
                        (.absurd 1494))
                    (.absurd 1493)))))

theorem treePart136_check :
    treePart136.check splitForms farkasReceipts cells
      ((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++ [aff [0, 0, 0, 0,
      0, 0, -1, -1, 0, 0, 1, 0, 1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 1389 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart137 : CompactCellTree :=
  .absurd 1389

theorem treePart137_check :
    treePart137.check splitForms farkasReceipts cells
      (((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++ [aff [0, -1, 0, -1,
      0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 188, 194 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart138 : CompactCellTree :=
  .split 3
    (.absurd 1496)
    (.split 27
        (.split 19
            (.split 28
                (.cell 194 [274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 536,
                  296, 289, 368, 290, 294, 292, 288, 295, 376, 438])
                (.absurd 1452))
            (.absurd 1493))
        (.split 19
            (.split 28
                (.split 29
                    (.cell 188 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      317, 320, 313, 380, 314, 384, 316, 630, 378, 439, 546, 319])
                    (.absurd 1453))
                (.absurd 1497))
            (.absurd 1493)))

theorem treePart138_check :
    treePart138.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 1,
      -1, 0, -1, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] - length[8] - length[9] - length[11]` in the row-04 symmetry
chamber, with leaves selecting cells 120, 169 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart139 : CompactCellTree :=
  .split 3
    (.absurd 571)
    (.split 27
        (.split 19
            (.split 15
                (.split 28
                    (.cell 169 [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
                      317, 320, 313, 380, 314, 319, 316, 1469, 630, 384, 392, 439])
                    (.absurd 1404))
                (.absurd 1494))
            (.absurd 1493))
        (.split 19
            (.split 15
                (.split 28
                    (.split 29
                        (.cell 120 [394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405,
                          443, 447, 417, 1084, 445, 410, 416, 412, 1485, 1138, 451, 446, 1357, 418])
                        (.absurd 1405))
                    (.absurd 1404))
                (.absurd 1494))
            (.absurd 1493)))

theorem treePart139_check :
    treePart139.check splitForms farkasReceipts cells
      ((((((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
      [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++
      [AffineForm.violation (aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1])]) ++
      [AffineForm.violation (aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
      [AffineForm.violation (aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- A branch of the final row-04 cover assembly, starting at split form 1
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch0 : CompactCellTree :=
  .split 1
    treePart0
    (.split 2
      (.split 3
        treePart1
        treePart2)
      (.split 4
        (.split 3
          (.split 5
            treePart3
            (.split 6
              treePart4
              treePart5))
          (.split 5
            treePart6
            (.split 7
              (.split 6
                treePart7
                treePart8)
              (.split 8
                treePart9
                (.split 9
                  treePart10
                  treePart11)))))
        (.split 8
          (.split 10
            treePart12
            treePart13)
          (.split 9
            treePart14
            treePart15))))

theorem treeAssemblyBranch0_check :
    treeAssemblyBranch0.check splitForms farkasReceipts cells
      (base ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1]]) = true := by
  simp only [treeAssemblyBranch0, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm2, splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8,
    splitForm9, splitForm10, treePart0_check, treePart1_check, treePart10_check,
    treePart11_check, treePart12_check, treePart13_check, treePart14_check, treePart15_check,
    treePart2_check, treePart3_check, treePart4_check, treePart5_check, treePart6_check,
    treePart7_check, treePart8_check, treePart9_check]

/-- A branch of the final row-04 cover assembly, starting at split form 1
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch1 : CompactCellTree :=
  .split 1
    (.split 11
      (.split 3
        treePart16
        (.split 12
          treePart17
          (.split 13
            treePart18
            treePart19)))
      (.split 14
        treePart20
        treePart21))
    (.split 11
      (.split 3
        treePart22
        (.split 8
          (.split 12
            treePart23
            treePart24)
          (.split 9
            (.split 12
              treePart25
              treePart26)
            (.split 15
              (.split 12
                treePart27
                treePart28)
              treePart29))))
      (.split 13
        (.split 3
          treePart30
          (.split 16
            treePart31
            treePart32))
        treePart33))

theorem treeAssemblyBranch1_check :
    treeAssemblyBranch1.check splitForms farkasReceipts cells
      ((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++ [aff
        [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  simp only [treeAssemblyBranch1, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm8, splitForm9, splitForm11, splitForm12, splitForm13, splitForm14,
    splitForm15, splitForm16, treePart16_check, treePart17_check, treePart18_check,
    treePart19_check, treePart20_check, treePart21_check, treePart22_check, treePart23_check,
    treePart24_check, treePart25_check, treePart26_check, treePart27_check, treePart28_check,
    treePart29_check, treePart30_check, treePart31_check, treePart32_check, treePart33_check]

/-- A branch of the final row-04 cover assembly, starting at split form 11
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch2 : CompactCellTree :=
  .split 11
    (.split 1
      treePart34
      (.split 3
        treePart35
        (.split 5
          treePart36
          (.split 6
            (.split 17
              treePart37
              (.split 18
                treePart38
                (.split 10
                  (.split 8
                    treePart39
                    (.split 7
                      treePart40
                      (.split 9
                        treePart41
                        (.split 19
                          (.split 12
                            treePart42
                            (.split 20
                              treePart43
                              (.split 21
                                treePart44
                                (.split 13
                                  (.split 14
                                    treePart45
                                    (.split 22
                                      treePart46
                                      treePart47))
                                  treePart48))))
                          treePart49))))
                  treePart50)))
            (.split 10
              treePart51
              (.split 17
                treePart52
                (.split 18
                  treePart53
                  (.split 23
                    (.split 24
                      (.split 12
                        treePart54
                        treePart55)
                      treePart56)
                    treePart57))))))))
    (.split 14
      (.split 13
        (.split 1
          treePart58
          (.split 3
            treePart59
            (.split 5
              treePart60
              (.split 6
                (.split 17
                  treePart61
                  (.split 18
                    treePart62
                    (.split 7
                      treePart63
                      (.split 8
                        treePart64
                        treePart65))))
                treePart66))))
        (.split 1
          treePart67
          (.split 3
            treePart68
            (.split 22
              treePart69
              (.split 25
                (.split 5
                  treePart70
                  (.split 6
                    treePart71
                    treePart72))
                treePart73)))))
      (.split 16
        (.split 1
          treePart74
          (.split 3
            treePart75
            (.split 22
              (.split 5
                treePart76
                (.split 6
                  treePart77
                  treePart78))
              (.split 26
                (.split 5
                  treePart79
                  (.split 7
                    treePart80
                    treePart81))
                treePart82))))
        (.split 1
          treePart83
          (.split 3
            treePart84
            (.split 27
              (.split 28
                (.split 5
                  treePart85
                  (.split 7
                    treePart86
                    treePart87))
                treePart88)
              (.split 28
                (.split 29
                  (.split 5
                    treePart89
                    (.split 7
                      treePart90
                      treePart91))
                  treePart92)
                treePart93))))))

theorem treeAssemblyBranch2_check :
    treeAssemblyBranch2.check splitForms farkasReceipts cells
      (((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1,
        -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch2, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9, splitForm10,
    splitForm11, splitForm12, splitForm13, splitForm14, splitForm16, splitForm17, splitForm18,
    splitForm19, splitForm20, splitForm21, splitForm22, splitForm23, splitForm24, splitForm25,
    splitForm26, splitForm27, splitForm28, splitForm29, treePart34_check, treePart35_check,
    treePart36_check, treePart37_check, treePart38_check, treePart39_check, treePart40_check,
    treePart41_check, treePart42_check, treePart43_check, treePart44_check, treePart45_check,
    treePart46_check, treePart47_check, treePart48_check, treePart49_check, treePart50_check,
    treePart51_check, treePart52_check, treePart53_check, treePart54_check, treePart55_check,
    treePart56_check, treePart57_check, treePart58_check, treePart59_check, treePart60_check,
    treePart61_check, treePart62_check, treePart63_check, treePart64_check, treePart65_check,
    treePart66_check, treePart67_check, treePart68_check, treePart69_check, treePart70_check,
    treePart71_check, treePart72_check, treePart73_check, treePart74_check, treePart75_check,
    treePart76_check, treePart77_check, treePart78_check, treePart79_check, treePart80_check,
    treePart81_check, treePart82_check, treePart83_check, treePart84_check, treePart85_check,
    treePart86_check, treePart87_check, treePart88_check, treePart89_check, treePart90_check,
    treePart91_check, treePart92_check, treePart93_check]

/-- A branch of the final row-04 cover assembly, starting at split form 7
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch3 : CompactCellTree :=
  .split 7
    (.split 6
      (.split 11
        (.split 1
          treePart94
          (.split 3
            treePart95
            (.split 10
              (.split 12
                treePart96
                treePart97)
              (.split 23
                (.split 12
                  treePart98
                  (.split 14
                    treePart99
                    treePart100))
                treePart101))))
        (.split 13
          (.split 1
            treePart102
            (.split 3
              treePart103
              (.split 16
                treePart104
                treePart105)))
          treePart106))
      (.split 11
        (.split 1
          treePart107
          (.split 10
            treePart108
            (.split 3
              treePart109
              (.split 23
                (.split 24
                  (.split 12
                    treePart110
                    treePart111)
                  treePart112)
                treePart113))))
        (.split 14
          treePart114
          (.split 16
            treePart115
            treePart116))))
    (.split 8
      (.split 11
        (.split 1
          treePart117
          (.split 10
            treePart118
            (.split 3
              treePart119
              (.split 23
                (.split 12
                  treePart120
                  treePart121)
                treePart122))))
        (.split 14
          (.split 13
            treePart123
            treePart124)
          (.split 16
            treePart125
            treePart126)))
      (.split 11
        (.split 1
          treePart127
          (.split 9
            treePart128
            (.split 3
              treePart129
              (.split 19
                (.split 15
                  (.split 12
                    treePart130
                    treePart131)
                  treePart132)
                treePart133))))
        (.split 14
          (.split 13
            treePart134
            treePart135)
          (.split 16
            treePart136
            (.split 1
              treePart137
              (.split 9
                treePart138
                treePart139))))))

theorem treeAssemblyBranch3_check :
    treeAssemblyBranch3.check splitForms farkasReceipts cells
      (((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++
        [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  simp only [treeAssemblyBranch3, CompactCellTree.check_split, Bool.and_true, splitForm1,
    splitForm3, splitForm6, splitForm7, splitForm8, splitForm9, splitForm10, splitForm11,
    splitForm12, splitForm13, splitForm14, splitForm15, splitForm16, splitForm19, splitForm23,
    splitForm24, treePart100_check, treePart101_check, treePart102_check, treePart103_check,
    treePart104_check, treePart105_check, treePart106_check, treePart107_check,
    treePart108_check, treePart109_check, treePart110_check, treePart111_check,
    treePart112_check, treePart113_check, treePart114_check, treePart115_check,
    treePart116_check, treePart117_check, treePart118_check, treePart119_check,
    treePart120_check, treePart121_check, treePart122_check, treePart123_check,
    treePart124_check, treePart125_check, treePart126_check, treePart127_check,
    treePart128_check, treePart129_check, treePart130_check, treePart131_check,
    treePart132_check, treePart133_check, treePart134_check, treePart135_check,
    treePart136_check, treePart137_check, treePart138_check, treePart139_check,
    treePart94_check, treePart95_check, treePart96_check, treePart97_check, treePart98_check,
    treePart99_check]

/-- A branch of the final row-04 cover assembly, starting at split form 4
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch4 : CompactCellTree :=
  .split 4
    treeAssemblyBranch2
    treeAssemblyBranch3

theorem treeAssemblyBranch4_check :
    treeAssemblyBranch4.check splitForms farkasReceipts cells
      ((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) ++
        [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  simp only [treeAssemblyBranch4, CompactCellTree.check_split, Bool.and_true, splitForm4,
    treeAssemblyBranch2_check, treeAssemblyBranch3_check]

/-- A branch of the final row-04 cover assembly, starting at split form 2
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch5 : CompactCellTree :=
  .split 2
    treeAssemblyBranch1
    treeAssemblyBranch4

theorem treeAssemblyBranch5_check :
    treeAssemblyBranch5.check splitForms farkasReceipts cells
      (base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1])]) = true :=
        by
  simp only [treeAssemblyBranch5, CompactCellTree.check_split, Bool.and_true, splitForm2,
    treeAssemblyBranch1_check, treeAssemblyBranch4_check]

/-- The complete compact decision tree for row 04 on the symmetry chamber, assembling 140
subtrees whose cell and Farkas certificates are replayed by the cover checker. -/
def tree : CompactCellTree :=
  .split 0
    treeAssemblyBranch0
    treeAssemblyBranch5

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0,
    treeAssemblyBranch0_check, treeAssemblyBranch5_check]

/-- On the chamber the eighteen active rows all hold: the first twelve
because lengths are natural numbers, the last six by definition of the
fundamental domain. -/
theorem base_holds (length : Fin 12 → ℕ) (hChamber : Chamber length) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  obtain ⟨⟨q0, q1, q2, q3⟩, r0, r1⟩ := hChamber
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
theorem rowConnected : row04Core.Connected :=
  (row04Core.connectedCheck_eq_true_iff).mp (by decide +kernel)

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row04Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row04Core (by norm_num) Chamber
    (fun length _ _ => chamber_covers length)
    (fun length forest notLoopy hChamber =>
      chamberPencil_of_compactCellTree (by norm_num) rowConnected
        cells base splitForms farkasReceipts tree cells_valid tree_check
        length forest notLoopy (base_holds length hChamber))

end AtanasovRanganathan.GenusFiveRow04FixedCover
