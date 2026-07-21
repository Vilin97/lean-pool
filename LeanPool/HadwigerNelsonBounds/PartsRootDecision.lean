/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData0
import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData1
import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData2
import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData3

/-!
# Complete normalized root dispatch

The 1,023-node trie has 432 leaves, one for each proper normalized coloring of
the 13-vertex 2-Golomb root. Every leaf names a separately checked Parts tree.
-/

namespace HadwigerNelsonBounds

/-- All chunks of the complete normalized root-decision trie. -/
def partsRootDecisionNodes : Array (Array PartsRootNode) := #[
  partsRootDecisionChunk0,
  partsRootDecisionChunk1,
  partsRootDecisionChunk2,
  partsRootDecisionChunk3,
  partsRootDecisionChunk4,
  partsRootDecisionChunk5,
  partsRootDecisionChunk6,
  partsRootDecisionChunk7,
  partsRootDecisionChunk8,
  partsRootDecisionChunk9,
  partsRootDecisionChunk10,
  partsRootDecisionChunk11,
  partsRootDecisionChunk12,
  partsRootDecisionChunk13,
  partsRootDecisionChunk14,
  partsRootDecisionChunk15,
]

theorem partsRootDecision_verifies :
    PartsRootVerifiesNodeB partsRootDecisionNodes 1024
      partsNormalizedRootPath 0 = true := by
  decide

/-- No proper coloring of the Parts graph extends the normalized fixed root. -/
theorem no_parts_coloring_of_normalized_root {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring partsNormalizedRootPath) : False := by
  exact partsRootDecision_not_colorable partsRootDecisionNodes 1023
    partsRootDecision_verifies hproper hroots

end HadwigerNelsonBounds
