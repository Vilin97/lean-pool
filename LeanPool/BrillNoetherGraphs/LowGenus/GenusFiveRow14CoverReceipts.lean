/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover

/-!
# Sparse Farkas receipts for the row-14 closed cover

These passive row multipliers are replayed by the corresponding fixed-cover module.
The ordered blocks and their concatenation retain the global receipt indices used by its tree.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow14FixedCover

open Utilities

/-- Farkas receipt block 0 for the row-14 tree, providing global indices 0 through 127. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts0 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 0, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 19,
  weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }] }, { terms :=
  [{ row := 4, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 5, weight := 1 },
  { row := 19, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 19, weight := 1 }]
  }, { terms := [{ row := 7, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 8,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 19,
  weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 19, weight := 1 }] }, { terms
  := [{ row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight :=
  1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row
  := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row
  := 19, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 0,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 20, weight := 1 }] }, { terms :=
  [{ row := 3, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 4, weight := 1 },
  { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }]
  }, { terms := [{ row := 6, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 20, weight := 1 }] }, { terms :=
  [{ row := 10, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11, weight := 1
  }, { row := 20, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 20, weight := 1
  }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row :=
  14, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row :=
  20, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 18,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 21, weight := 1 }] }, { terms :=
  [{ row := 1, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 },
  { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight := 1 }]
  }, { terms := [{ row := 4, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 21,
  weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 21, weight := 1 }] }, { terms :=
  [{ row := 8, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 9, weight := 1 },
  { row := 21, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 21, weight := 1 }]
  }, { terms := [{ row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 15,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 21,
  weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 20, weight :=
  1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight :=
  1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 21, weight :=
  1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row
  := 12, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row
  := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row
  := 14, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row
  := 5, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row
  := 22, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 8, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 9, weight
  := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{
  row := 15, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, {
  row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }]
  }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 21,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms
  := [{ row := 12, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms
  := [{ row := 1, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 0, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 23, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 23, weight := 1
  }] }, { terms := [{ row := 3, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row :=
  4, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  23, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 8, weight
  := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 23, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 23, weight := 1 }] }, { terms
  := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms :=
  [{ row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 },
  { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 2, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms :=
  [{ row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 7, weight := 1 },
  { row := 24, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 9, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 10,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 24, weight := 1 }] }, { terms
  := [{ row := 13, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight :=
  1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 24, weight :=
  1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row
  := 12, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row
  := 24, weight := 1 }] }]

/-- Farkas receipt block 1 for the row-14 tree, providing global indices 128 through 255. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts1 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 22,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 2,
  weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 21,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 3,
  weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 25, weight := 1 }] }, { terms :=
  [{ row := 3, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 4, weight := 1 },
  { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 6, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 7,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 25, weight := 1 }] }, { terms :=
  [{ row := 10, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 11, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 25, weight := 1
  }] }, { terms := [{ row := 13, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row :=
  14, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row :=
  25, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 25, weight := 1 }] }, {
  terms := [{ row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 24,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 2,
  weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 23,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 19,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 16,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 12, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 17, weight :=
  1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 23, weight :=
  1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 3, weight := 1
  }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 20, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 26, weight := 1
  }] }, { terms := [{ row := 1, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row :=
  2, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  26, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 6, weight
  := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 26, weight
  := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row
  := 9, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row
  := 26, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 15, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 23, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 22, weight :=
  1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 26, weight :=
  1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row
  := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row
  := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row
  := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row
  := 0, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row
  := 0, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row
  := 0, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row
  := 16, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row
  := 22, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 21, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 18,
  weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 17,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 16, weight := 1 }, { row := 18,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 19, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms
  := [{ row := 1, weight := 1 }, { row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 3, weight := 1 }, { row := 6,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 2,
  weight := 1 }, { row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }]
  }, { terms := [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 17, weight := 1 },
  { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 1, weight := 1 }, {
  row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, {
  row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, {
  row := 15, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, {
  row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 1, weight := 1 }, { row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 17,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 26, weight := 1 }] }, { terms :=
  [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms :=
  [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 }] }, { terms :=
  [{ row := 0, weight := 1 }, { row := 1, weight := 1 }, { row := 22, weight := 1 }] }, { terms :=
  [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 21, weight := 1 }] }, { terms :=
  [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms :=
  [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 23, weight := 1 }] }, { terms :=
  [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 22, weight := 1 }] }, { terms :=
  [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms :=
  [{ row := 1, weight := 1 }, { row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 3, weight := 1 }, { row := 6,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 14,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 27,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 27, weight := 1 }] }, { terms :=
  [{ row := 2, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 3, weight := 1 },
  { row := 27, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 5, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 6,
  weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 27,
  weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms :=
  [{ row := 9, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 10, weight := 1 },
  { row := 27, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 27, weight := 1 }]
  }]

/-- Farkas receipt block 2 for the row-14 tree, providing global indices 256 through 346. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts2 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 17, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 25, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 27,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 24, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 27, weight := 1 }] }, { terms :=
  [{ row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 12, weight := 1
  }, { row := 14, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1
  }, { row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1
  }, { row := 15, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 }] }, { terms
  := [{ row := 0, weight := 1 }, { row := 15, weight := 1 }, { row := 18, weight := 1 }, { row :=
  22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row :=
  20, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 15, weight := 1 }, { row :=
  21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 15, weight := 1 }, { row :=
  22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 15, weight := 1 }, { row := 18, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 16, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 16, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 21, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }, { row := 17, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 17, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row
  := 20, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 1, weight := 1 }, { row
  := 20, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row
  := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row
  := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight
  := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 17, weight
  := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 18, weight
  := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 18, weight
  := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight
  := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight
  := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight
  := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 14, weight
  := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight
  := 1 }, { row := 16, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight
  := 1 }, { row := 16, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight
  := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight
  := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row
  := 26, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 15, weight := 1 }, { row
  := 19, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 17, weight := 1 }, { row
  := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row
  := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row
  := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 15, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row
  := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row
  := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 18, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row
  := 16, weight := 1 }, { row := 17, weight := 1 }] }]

/-- The complete table of 347 row-14 Farkas receipts, concatenated in the global order
referenced by decision-tree leaves. -/
def farkasReceipts : List Certificate.AffineCover.FarkasData :=
  farkasReceipts0 ++ farkasReceipts1 ++ farkasReceipts2

end AtanasovRanganathan.GenusFiveRow14FixedCover
