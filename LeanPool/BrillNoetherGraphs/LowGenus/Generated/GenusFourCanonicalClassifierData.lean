/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Certificate.CubicMatrixCanonical

/-!
# Generated data for the pruned cubic classifier at n = 6

Passive data only, deliberately separated from its proof consumer.  The
checker recomputes the pruned traversal; this file stores only the six atlas
pair-multiplicity tables and the twenty connected canonical leaf payloads.

Generated classifier data, checked by the consuming Lean declarations.
-/

@[expose] public section
namespace AtanasovRanganathan.Generated.GenusFourCanonicalClassifierData

open Utilities.Certificate.CubicMatrixReplay
/-- A connected canonical leaf's atlas index and matching vertex map. -/
abbrev Payload := Fin 6 × (Fin 6 → Fin 6)

/-- Pair-multiplicity tables of the six atlas rows, in atlas order. -/
def atlasTable : Fin 6 → Fin 6 → Fin 6 → ℕ :=
  ![
    ![![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 2, 1, 0], ![0, 1, 2, 0, 0, 0], ![1, 1,
      1, 0, 0, 0], ![2, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 0, 2, 0, 1], ![0, 1, 2, 0, 0, 0], ![1, 2,
      0, 0, 0, 0], ![2, 0, 1, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 1, 0, 1], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 0, 1, 0], ![1, 0,
      1, 1, 0, 0], ![2, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 2, 0, 0], ![0, 1, 2, 0, 0, 0], ![1, 1,
      0, 0, 0, 1], ![2, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0], ![1, 1,
      1, 0, 0, 0], ![1, 1, 1, 0, 0, 0]],
    ![![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 1, 1], ![0, 1, 0, 1, 0, 1], ![1, 0, 1, 0, 1, 0], ![1, 1,
      0, 1, 0, 0], ![1, 1, 1, 0, 0, 0]]
  ]

/-- Base-four lookup key for a leaf row list.  Payloads are independently
checked entry by entry, so a key collision cannot validate a bad leaf. -/
def rowKey (rows : List (List ℕ)) : ℕ :=
  rows.foldl (fun acc row => row.foldl (fun a x => a * 4 + x) acc) 0

/-- Payloads of all twenty connected leaves reached by the pruned traversal. -/
def payloadTable : List (ℕ × Payload) :=
  [
    (6379776, (0, ![0, 1, 2, 3, 4, 5])),
    (6391872, (1, ![0, 1, 2, 3, 4, 5])),
    (6428160, (1, ![0, 2, 1, 3, 4, 5])),
    (6440256, (0, ![0, 2, 1, 3, 4, 5])),
    (6624528, (2, ![0, 1, 2, 3, 4, 5])),
    (6636624, (2, ![0, 2, 1, 3, 4, 5])),
    (6636804, (2, ![0, 2, 3, 1, 4, 5])),
    (6637569, (3, ![0, 1, 2, 3, 4, 5])),
    (6685008, (0, ![0, 3, 1, 2, 4, 5])),
    (6685188, (1, ![0, 3, 1, 2, 4, 5])),
    (6685953, (3, ![0, 2, 1, 3, 4, 5])),
    (22046976, (0, ![1, 0, 2, 3, 4, 5])),
    (22107456, (4, ![0, 1, 2, 3, 4, 5])),
    (22291728, (2, ![1, 0, 4, 2, 3, 5])),
    (22303824, (5, ![0, 1, 2, 3, 4, 5])),
    (22304004, (5, ![0, 1, 2, 3, 5, 4])),
    (22304769, (2, ![1, 4, 0, 5, 2, 3])),
    (22548576, (3, ![1, 0, 5, 2, 3, 4])),
    (22548756, (2, ![2, 0, 5, 3, 1, 4])),
    (22549521, (2, ![2, 0, 5, 1, 3, 4]))]

end AtanasovRanganathan.Generated.GenusFourCanonicalClassifierData
