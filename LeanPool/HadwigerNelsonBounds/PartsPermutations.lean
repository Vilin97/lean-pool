/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsPermutationData0
import LeanPool.HadwigerNelsonBounds.PartsPermutationData1
import LeanPool.HadwigerNelsonBounds.PartsPermutationData2
import LeanPool.HadwigerNelsonBounds.PartsPermutationData3
import LeanPool.HadwigerNelsonBounds.PartsPermutationData4
import LeanPool.HadwigerNelsonBounds.PartsPermutationData5

/-! The six exact automorphisms of the normalized Parts root. -/

namespace HadwigerNelsonBounds

/-- Apply one of the six stored automorphisms of the exact base graph. -/
def partsPermuteVertex (symmetry : Fin 6) (vertex : Fin 481) : Fin 481 :=
  match symmetry.val with
  | 0 => partsVertexPermutation0 vertex
  | 1 => partsVertexPermutation1 vertex
  | 2 => partsVertexPermutation2 vertex
  | 3 => partsVertexPermutation3 vertex
  | 4 => partsVertexPermutation4 vertex
  | 5 => partsVertexPermutation5 vertex
  | _ => vertex

end HadwigerNelsonBounds
