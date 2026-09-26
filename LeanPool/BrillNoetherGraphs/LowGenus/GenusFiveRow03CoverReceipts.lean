/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover

/-!
# Sparse Farkas receipts for the row-03 closed cover

These passive row multipliers are replayed by the corresponding fixed-cover module.
The ordered blocks and their concatenation retain the global receipt indices used by its tree.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities

/-- Farkas receipt entries 0 through 127 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts0 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 0, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 16,
  weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 16, weight := 1 }] }, { terms :=
  [{ row := 4, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 5, weight := 1 },
  { row := 16, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 16, weight := 1 }]
  }, { terms := [{ row := 7, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 8,
  weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 16,
  weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 16, weight := 1 }] }, { terms
  := [{ row := 11, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 13, weight :=
  1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 16, weight :=
  1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row
  := 14, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row
  := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row
  := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row
  := 21, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 9, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 10,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 21,
  weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 8, weight := 1
  }, { row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1
  }, { row := 21, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1
  }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row :=
  12, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row :=
  22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row
  := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row
  := 22, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 9, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 10,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms
  := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms
  := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 8, weight := 1
  }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1
  }, { row := 22, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1
  }] }, { terms := [{ row := 12, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row :=
  20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row :=
  20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row :=
  23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row
  := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row
  := 23, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 9, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 10,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 23,
  weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms
  := [{ row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight :=
  1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight :=
  1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 23, weight :=
  1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row
  := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row
  := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row
  := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row
  := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row
  := 24, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 9, weight
  := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, {
  row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 16, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 23,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms
  := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms
  := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 0, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 25, weight := 1
  }] }, { terms := [{ row := 3, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row :=
  4, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row :=
  25, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 25, weight := 1 }] }, {
  terms := [{ row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 8, weight
  := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 25, weight
  := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, {
  row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, {
  row := 25, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 8, weight := 1
  }, { row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 26, weight := 1
  }] }]

/-- Farkas receipt entries 128 through 255 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts1 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 1, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 2,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 26, weight := 1 }] }, { terms :=
  [{ row := 5, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 6, weight := 1 },
  { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 26, weight := 1 }]
  }, { terms := [{ row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 9,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1, weight := 1
  }, { row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 23, weight := 1
  }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 26, weight := 1
  }] }, { terms := [{ row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row :=
  12, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row :=
  26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17,
  weight := 1 }, { row := 20, weight := 2 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }]
  }, { terms := [{ row := 18, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 26, weight := 1 }]
  }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 26, weight := 1 }]
  }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 0, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 27,
  weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 27, weight := 1 }] }, { terms :=
  [{ row := 4, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 },
  { row := 27, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 7, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 8,
  weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 27,
  weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 11, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 22, weight :=
  1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1
  }, { row := 27, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 27, weight := 1
  }] }, { terms := [{ row := 20, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row :=
  25, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row :=
  27, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row
  := 27, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 21, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17,
  weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 21,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 19, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight :=
  1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 25, weight :=
  1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 14, weight :=
  1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row :=
  22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 3, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row
  := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row
  := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row
  := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row
  := 16, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row
  := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 28, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 28, weight
  := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row
  := 6, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row
  := 28, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 28, weight := 1 }] }, {
  terms := [{ row := 9, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 10,
  weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 28,
  weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms
  := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms
  := [{ row := 23, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 20, weight :=
  1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 28, weight :=
  1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row
  := 25, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row
  := 27, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 5, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row
  := 28, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 26, weight := 1 }, { row
  := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row
  := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 14, weight := 1 }, { row
  := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight
  := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight
  := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{
  row := 16, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{
  row := 21, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, {
  row := 11, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, {
  row := 28, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 29, weight := 1 }] },
  { terms := [{ row := 1, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 2,
  weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 29,
  weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 29, weight := 1 }] }, { terms :=
  [{ row := 5, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 6, weight := 1 },
  { row := 29, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 29, weight := 1 }]
  }, { terms := [{ row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 9,
  weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 29,
  weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 29, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 29, weight := 1 }] }, { terms
  := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms
  := [{ row := 21, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 22, weight :=
  1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 29, weight :=
  1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 29, weight := 1 }] }]

/-- Farkas receipt entries 256 through 383 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts2 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 25, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }]
  }, { terms := [{ row := 28, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 5, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 27,
  weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 27,
  weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 25,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21,
  weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 24,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 29,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 28, weight := 1 }] }, { terms
  := [{ row := 24, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 20, weight :=
  1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight :=
  1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight :=
  1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 8, weight :=
  1 }, { row := 11, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16, weight :=
  1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 30, weight :=
  1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row :=
  2, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  30, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 30, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 6, weight
  := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 30, weight
  := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row
  := 9, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row
  := 30, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 30, weight := 1 }] }, {
  terms := [{ row := 21, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 22,
  weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 30,
  weight := 1 }] }, { terms := [{ row := 27, weight := 1 }, { row := 30, weight := 1 }] }, { terms
  := [{ row := 12, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 24, weight :=
  1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1
  }, { row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 29, weight := 1
  }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1
  }, { row := 30, weight := 1 }] }, { terms := [{ row := 28, weight := 1 }, { row := 30, weight := 1
  }] }, { terms := [{ row := 16, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1
  }] }, { terms := [{ row := 20, weight := 1 }, { row := 24, weight := 1 }, { row := 27, weight := 1
  }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1
  }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1
  }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1
  }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1
  }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1
  }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1
  }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1
  }, { row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18,
  weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19,
  weight := 1 }, { row := 20, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 28, weight := 1 }]
  }, { terms := [{ row := 20, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 26,
  weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20,
  weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19,
  weight := 1 }, { row := 20, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 25,
  weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }]
  }, { terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 23, weight := 1 }]
  }, { terms := [{ row := 13, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 14,
  weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 15, weight := 1 }, { row := 21,
  weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 24, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight :=
  1 }, { row := 14, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 24, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 15, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 16, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row
  := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row
  := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row
  := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row
  := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row
  := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row
  := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row
  := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row
  := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row
  := 17, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row
  := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row
  := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row
  := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight :=
  1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 28, weight := 1
  }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1
  }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1
  }, { row := 21, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1
  }, { row := 20, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1
  }, { row := 21, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1
  }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1
  }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1
  }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 22, weight := 1
  }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1
  }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1
  }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1
  }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1
  }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight := 1
  }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1
  }, { row := 18, weight := 1 }, { row := 24, weight := 1 }] }]

/-- Farkas receipt entries 384 through 511 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts3 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 18,
  weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 18, weight := 1 }] }, { terms :=
  [{ row := 4, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 5, weight := 1 },
  { row := 18, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 18, weight := 1 }]
  }, { terms := [{ row := 7, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 8,
  weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 18,
  weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 18, weight := 1 }] }, { terms
  := [{ row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 13, weight :=
  1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 18, weight :=
  1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row
  := 15, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row
  := 18, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, {
  terms := [{ row := 15, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5,
  weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19,
  weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21,
  weight := 2 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15,
  weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }, { row := 24,
  weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms
  := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms
  := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }, { row :=
  24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row :=
  22, weight := 1 }, { row := 26, weight := 2 }] }, { terms := [{ row := 19, weight := 1 }, { row :=
  21, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 2 }] }, { terms := [{ row :=
  18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight :=
  1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 21, weight :=
  1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight :=
  1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight :=
  1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight :=
  1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight :=
  1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight :=
  1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 19, weight :=
  1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row :=
  2, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  19, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 6, weight
  := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 19, weight
  := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row
  := 9, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row
  := 19, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 12,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19,
  weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms
  := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 5, weight :=
  1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight :=
  1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 16, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 16, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight :=
  1 }, { row := 16, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight :=
  1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 28, weight := 1 }] }, {
  terms := [{ row := 18, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, {
  terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 23, weight := 1 }] }, {
  terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 20, weight := 2 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 19, weight := 1 }, { row := 20, weight := 2 }, { row := 21, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, {
  row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, {
  row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, {
  row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, {
  row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, {
  row := 28, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 27, weight := 1 }, {
  row := 28, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, {
  row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, {
  row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, {
  row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, {
  row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, {
  row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, {
  row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{
  row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 21, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{
  row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 22,
  weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 28, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 1 }, { row :=
  27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row :=
  27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 23, weight := 1 }, { row :=
  24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row :=
  29, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 29, weight := 1 }] }, {
  terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row
  := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row
  := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row
  := 30, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 30, weight := 1 }] }, {
  terms := [{ row := 15, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 8,
  weight := 1 }, { row := 11, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 21,
  weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }]
  }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 27, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }]
  }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }]
  }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 },
  { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 },
  { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 18, weight := 1 },
  { row := 19, weight := 2 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 22,
  weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19,
  weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18,
  weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 5, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }]
  }, { terms := [{ row := 21, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }]
  }]

/-- Farkas receipt entries 512 through 639 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts4 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 5, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] },
  { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] },
  { terms := [{ row := 5, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] },
  { terms := [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] },
  { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 26, weight := 1 }] },
  { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }, {
  row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, {
  row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, {
  row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 2 }, {
  row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{
  row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{
  row := 20, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{
  row := 5, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{
  row := 18, weight := 1 }, { row := 19, weight := 2 }, { row := 21, weight := 1 }, { row := 22,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 30,
  weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 30, weight := 1 }] }, { terms
  := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }, { row :=
  24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 29, weight := 1 }] }, {
  terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 30, weight := 1 }] }, {
  terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }, {
  row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, {
  row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, {
  row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, {
  row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }, { row := 21,
  weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5,
  weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }]
  }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }]
  }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 0,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 20, weight := 1 }] }, { terms :=
  [{ row := 3, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 4, weight := 1 },
  { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }]
  }, { terms := [{ row := 6, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 20, weight := 1 }] }, { terms :=
  [{ row := 10, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11, weight := 1
  }, { row := 20, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1
  }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1
  }] }, { terms := [{ row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row :=
  8, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row :=
  14, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row :=
  20, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 12, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5,
  weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5,
  weight := 1 }, { row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 16,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 15,
  weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15,
  weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15,
  weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16,
  weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 15, weight := 1 }, { row :=
  19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row :=
  20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, {
  terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row
  := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row
  := 19, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row
  := 19, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }] }, {
  terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16,
  weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1,
  weight := 1 }, { row := 8, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11,
  weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }]
  }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }]
  }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 24, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }]
  }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 },
  { row := 25, weight := 2 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 },
  { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 },
  { row := 20, weight := 1 }, { row := 26, weight := 2 }] }, { terms := [{ row := 14, weight := 1 },
  { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 7, weight := 1 },
  { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 21,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 25, weight := 1 }, { row := 26,
  weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 25,
  weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms
  := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 25, weight := 1 }, { row := 27, weight := 1 }] }, { terms
  := [{ row := 14, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }, { row :=
  21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row :=
  18, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row :=
  21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row :=
  18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row :=
  5, weight := 1 }, { row := 12, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row :=
  16, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row :=
  16, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row :=
  0, weight := 1 }, { row := 8, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row :=
  14, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row :=
  14, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight :=
  1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 23, weight := 1
  }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 },
  { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, {
  row := 22, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, {
  row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, {
  row := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, {
  row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, {
  row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 20,
  weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 18,
  weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }]

/-- Farkas receipt entries 640 through 767 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts5 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }]
  }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 },
  { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 },
  { row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 },
  { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19,
  weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13,
  weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }]
  }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 27, weight := 1 }]
  }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, {
  row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, {
  row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, {
  row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, {
  row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, {
  row := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, {
  row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{
  row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{
  row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{
  row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{
  row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{
  row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{
  row := 13, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, {
  row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, {
  row := 18, weight := 2 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{
  row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{
  row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight
  := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight
  := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight
  := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight
  := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight
  := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight
  := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight
  := 1 }, { row := 13, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 6, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 11, weight
  := 1 }, { row := 13, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight
  := 1 }, { row := 6, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 6, weight
  := 1 }, { row := 11, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight
  := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight
  := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row
  := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row
  := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row
  := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row
  := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row
  := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row
  := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row
  := 13, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row
  := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row
  := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row
  := 13, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row
  := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row
  := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight :=
  1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1
  }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1
  }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 1
  }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1
  }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1
  }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1
  }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1
  }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1
  }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1
  }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1
  }, { row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms
  := [{ row := 7, weight := 1 }, { row := 12, weight := 1 }, { row := 18, weight := 1 }] }, { terms
  := [{ row := 7, weight := 1 }, { row := 12, weight := 1 }, { row := 19, weight := 1 }] }, { terms
  := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms
  := [{ row := 15, weight := 1 }, { row := 17, weight := 2 }, { row := 18, weight := 1 }, { row :=
  20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row :=
  22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 2 }, { row :=
  18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row :=
  18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row :=
  19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row :=
  18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row :=
  23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row :=
  20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row :=
  18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row :=
  22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row :=
  20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row :=
  16, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row :=
  17, weight := 1 }, { row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row :=
  13, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 24, weight :=
  1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight :=
  1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight :=
  1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight :=
  1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight :=
  1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight :=
  1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight :=
  1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight :=
  1 }, { row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight :=
  1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 24, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 25, weight := 1 }] }, {
  terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row
  := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row
  := 25, weight := 1 }] }]

/-- Farkas receipt entries 768 through 795 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts6 : List Certificate.AffineCover.FarkasData :=
  [{ terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 18, weight := 1 }, {
  row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, {
  row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 18, weight := 1 }, {
  row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 17, weight := 1 }, {
  row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, {
  row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, {
  row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, {
  row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 7, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{
  row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight
  := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight
  := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight
  := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 19, weight
  := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight
  := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 19, weight
  := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight
  := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight
  := 1 }, { row := 7, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, {
  terms := [{ row := 7, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }]

/-- The concatenated Farkas receipt table indexed by the compact row-03 cover tree. -/
def farkasReceipts : List Certificate.AffineCover.FarkasData :=
  farkasReceipts0 ++ farkasReceipts1 ++ farkasReceipts2 ++ farkasReceipts3 ++ farkasReceipts4 ++
  farkasReceipts5 ++ farkasReceipts6

end AtanasovRanganathan.GenusFiveRow03FixedCover
