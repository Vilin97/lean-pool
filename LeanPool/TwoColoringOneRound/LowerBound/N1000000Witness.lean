/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000Witness

open Distributed2Coloring.LowerBound.N1000000Data

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev masks : Array Nat :=
  #[0, 1, 2, 4, 8, 10, 12, 16, 17, 20, 32, 33, 34, 64, 66, 68, 80, 84, 96, 98, 128, 129, 132,
    136, 140, 160, 161, 256, 257, 258, 264, 266, 272, 273]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev tTr : Array Nat :=
  #[0, 1, 4, 13, 2, 5, 14, 7, 8, 16, 20, 21, 23, 3, 6, 15, 9, 17, 22, 24, 10, 11, 18, 12, 19,
    25, 26, 27, 28, 30, 29, 31, 32, 33]
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def idIndex : Nat := 33

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varToOrbitRep : Array Nat :=
  #[0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17, 18, 19, 25, 26, 27, 28, 29, 31, 32]
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeVar' : Nat := 11

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev LabelTriple := Nat × Nat × Nat

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepU : Array LabelTriple := #[
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
  (0, 1, 2),
]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepV : Array LabelTriple := #[
  (3, 4, 5),
  (0, 3, 4),
  (3, 0, 4),
  (3, 4, 0),
  (1, 0, 3),
  (1, 3, 0),
  (3, 1, 4),
  (0, 1, 3),
  (3, 1, 0),
  (3, 4, 1),
  (0, 3, 1),
  (3, 0, 1),
  (2, 3, 0),
  (2, 1, 0),
  (2, 3, 1),
  (2, 0, 1),
  (3, 2, 1),
  (0, 2, 1),
  (3, 4, 2),
  (0, 3, 2),
  (3, 0, 2),
  (1, 0, 2),
  (3, 1, 2),
]

end N1000000Witness

end Distributed2Coloring.LowerBound
