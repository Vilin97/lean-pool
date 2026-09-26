/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover

/-!
# Sparse Farkas receipts for the row-06 closed cover

These passive row multipliers are replayed by the corresponding fixed-cover module.
The ordered blocks and their concatenation retain the global receipt indices used by its tree.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06FixedCover

open Utilities

/-- Farkas receipt block 0 for the row-06 tree, providing global indices 0 through 127. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts0 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 0, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 2 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 25, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 29, weight := 1 }] }
  ]

/-- Farkas receipt block 1 for the row-06 tree, providing global indices 128 through 255. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts1 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 1, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 27, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 21, weight := 2 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 30, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 33, weight := 1 }] }
  ]

/-- Farkas receipt block 2 for the row-06 tree, providing global indices 256 through 383. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts2 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 17, weight := 2 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 31, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 33, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 27, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 32, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 27, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 25, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 22, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 },
          { row := 27, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 20, weight := 2 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 15, weight := 2 }, { row := 16, weight := 2 },
          { row := 22, weight := 2 }, { row := 24, weight := 1 }, { row := 27, weight := 1 },
          { row := 29, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 },
          { row := 27, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 },
          { row := 27, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 },
          { row := 27, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 2 },
          { row := 21, weight := 1 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 27, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 29, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 16, weight := 2 }, { row := 21, weight := 2 },
          { row := 24, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 29, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 31, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 21, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 22, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 29, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 16, weight := 2 }, { row := 21, weight := 4 },
          { row := 24, weight := 1 }, { row := 28, weight := 2 }, { row := 29, weight := 1 },
          { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 35, weight := 1 }] }
  ]

/-- Farkas receipt block 3 for the row-06 tree, providing global indices 384 through 511. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts3 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 14, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 32, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 34, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 32, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 },
          { row := 22, weight := 1 }, { row := 24, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 35, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 34, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 36, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 34, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 14, weight := 1 }, { row := 16, weight := 2 },
          { row := 21, weight := 2 }, { row := 24, weight := 1 }, { row := 30, weight := 1 },
          { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 21, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 33, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 33, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 34, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 29, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 34, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 29, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 35, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 26, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 35, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 36, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 37, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 38, weight := 1 }] }
  ]

/-- Farkas receipt block 4 for the row-06 tree, providing global indices 512 through 639. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts4 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 26, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 31, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 32, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 36, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 31, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 21, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 34, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 34, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 33, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 33, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 35, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 35, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 34, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 34, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 36, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 36, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 35, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 34, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 35, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 27, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 37, weight := 1 },
          { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 38, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 37, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 2, weight := 2 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 36, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 0, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 1, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 2, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 6, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 11, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 35, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 36, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 40, weight := 2 }] },
    { terms :=
        [{ row := 24, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 29, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 30, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 38, weight := 1 },
          { row := 40, weight := 2 }] },
    { terms :=
        [{ row := 39, weight := 1 }, { row := 40, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 },
          { row := 38, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 14, weight := 1 }, { row := 16, weight := 2 },
          { row := 21, weight := 2 }, { row := 24, weight := 1 }, { row := 27, weight := 1 },
          { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight := 1 },
          { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 26, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 19, weight := 2 }, { row := 22, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 3, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 27, weight := 1 }] }
  ]

/-- Farkas receipt block 5 for the row-06 tree, providing global indices 640 through 767. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts5 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 17, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 12, weight := 1 }, { row := 29, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 26, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 28, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 28, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 30, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 31, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 20, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 2 }, { row := 31, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 21, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 33, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 33, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 26, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 20, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 28, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 28, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 20, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 25, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 2 }, { row := 30, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 30, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 21, weight := 2 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 31, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 31, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 31, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 26, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 31, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 2 },
          { row := 26, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 34, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 35, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 36, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 23, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 23, weight := 1 }, { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 28, weight := 1 }, { row := 39, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 },
          { row := 37, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 26, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 }] }
  ]

/-- Farkas receipt block 6 for the row-06 tree, providing global indices 768 through 895. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts6 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 26, weight := 1 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 22, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 26, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 23, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 20, weight := 2 }, { row := 22, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 28, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 28, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 30, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 29, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 31, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 31, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 30, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 32, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 33, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 33, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 30, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 33, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 24, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 26, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 27, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 28, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 28, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 25, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 29, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 30, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 15, weight := 2 }, { row := 21, weight := 2 },
          { row := 27, weight := 1 }, { row := 30, weight := 1 }, { row := 32, weight := 2 },
          { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 30, weight := 1 }, { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 30, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 30, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 27, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 30, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 30, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 37, weight := 1 }] }
  ]

/-- Farkas receipt block 7 for the row-06 tree, providing global indices 896 through 1023. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts7 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 5, weight := 1 }, { row := 31, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 31, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 14, weight := 1 }, { row := 16, weight := 2 }, { row := 18, weight := 2 },
          { row := 23, weight := 1 }, { row := 26, weight := 1 }, { row := 28, weight := 2 },
          { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 31, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 31, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 31, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 31, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 31, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 34, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 34, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 15, weight := 2 }, { row := 21, weight := 2 },
          { row := 28, weight := 1 }, { row := 33, weight := 2 }, { row := 34, weight := 1 },
          { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 35, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 35, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 35, weight := 1 }, { row := 36, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 36, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 36, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 36, weight := 1 }, { row := 37, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 37, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 2 }, { row := 10, weight := 1 }, { row := 26, weight := 1 },
          { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 37, weight := 1 },
          { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 28, weight := 1 }, { row := 39, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 37, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 },
          { row := 26, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 19, weight := 2 }, { row := 21, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 25, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 27, weight := 1 }, { row := 28, weight := 1 }] },
    { terms :=
        [{ row := 19, weight := 2 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 27, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 27, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 29, weight := 1 }, { row := 30, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight := 1 },
          { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 27, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 27, weight := 1 }, { row := 29, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 27, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 29, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight := 1 },
          { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 29, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 29, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 30, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 3, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight := 1 },
          { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 30, weight := 1 }, { row := 32, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 30, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 29, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 30, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 29, weight := 1 }, { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 18, weight := 2 }, { row := 23, weight := 1 }] },
    { terms :=
        [{ row := 18, weight := 2 }, { row := 25, weight := 1 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 28, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 27, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 27, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 24, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 28, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 34, weight := 2 }] }
  ]

/-- Farkas receipt block 8 for the row-06 tree, providing global indices 1024 through 1073. Each
receipt specifies a positive integer combination of active affine rows for a cell constraint or
a contradiction. -/
def farkasReceipts8 : List Certificate.AffineCover.FarkasData :=
  [
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 29, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 10, weight := 1 }, { row := 24, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 5, weight := 1 }, { row := 29, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 26, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 29, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 30, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 20, weight := 2 }, { row := 31, weight := 1 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 15, weight := 2 }, { row := 20, weight := 2 },
          { row := 27, weight := 1 }, { row := 30, weight := 1 }, { row := 32, weight := 2 },
          { row := 33, weight := 1 }] },
    { terms :=
        [{ row := 10, weight := 1 }, { row := 25, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 31, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 32, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 13, weight := 1 }, { row := 15, weight := 2 }, { row := 20, weight := 2 },
          { row := 29, weight := 2 }, { row := 30, weight := 1 }, { row := 33, weight := 1 },
          { row := 34, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 32, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 31, weight := 1 }, { row := 33, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 33, weight := 1 },
          { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 31, weight := 1 }, { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 },
          { row := 34, weight := 1 }, { row := 35, weight := 1 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 33, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 32, weight := 1 }, { row := 34, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 34, weight := 1 },
          { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 32, weight := 1 }, { row := 37, weight := 2 }] },
    { terms :=
        [{ row := 4, weight := 2 }, { row := 34, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 33, weight := 1 }, { row := 35, weight := 2 }] },
    { terms :=
        [{ row := 5, weight := 1 }, { row := 7, weight := 1 }, { row := 35, weight := 1 },
          { row := 36, weight := 2 }] },
    { terms :=
        [{ row := 31, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 22, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 8, weight := 2 }, { row := 10, weight := 1 }, { row := 25, weight := 1 },
          { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 9, weight := 1 }, { row := 22, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 33, weight := 1 }, { row := 38, weight := 1 }] },
    { terms :=
        [{ row := 7, weight := 1 }, { row := 33, weight := 1 }, { row := 38, weight := 2 }] },
    { terms :=
        [{ row := 8, weight := 1 }, { row := 14, weight := 1 }, { row := 19, weight := 1 },
          { row := 25, weight := 1 }, { row := 27, weight := 1 }] }
  ]

/-- The complete table of 1074 row-06 Farkas receipts, concatenated in the global order
referenced by decision-tree leaves. -/
def farkasReceipts : List Certificate.AffineCover.FarkasData :=
  farkasReceipts0 ++ farkasReceipts1 ++ farkasReceipts2 ++ farkasReceipts3 ++ farkasReceipts4 ++
  farkasReceipts5 ++ farkasReceipts6 ++ farkasReceipts7 ++ farkasReceipts8

end AtanasovRanganathan.GenusFiveRow06FixedCover
