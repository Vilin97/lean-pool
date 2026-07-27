/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra00
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra01
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra02
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra03
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra04
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra05
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra06
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra07
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra08
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra09
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra10
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra11
import LeanPool.Erdos97ConvexOctagon.ResidualAlgebra12

/-! # Erdős 97 convex-octagon formalization: Residual Obstructions -/

namespace Erdos97Octagon

/-- None of the thirteen explicit candidate systems has a convex-independent
realisation. This statement does not assert that the family is exhaustive. -/
theorem residualRepresentative_not_convex_realises
    (classIndex : Fin 13) {p : Vertex → Plane}
    (hC : ConvexIndependent ℝ p) :
    ¬ Realises p (residualRepresentative classIndex) := by
  fin_cases classIndex
  · exact residualRepresentative00_not_realises hC.injective
  · exact residualRepresentative01_not_realises hC.injective
  · exact residualRepresentative02_not_realises hC.injective
  · exact residualRepresentative03_not_realises hC.injective
  · exact residualRepresentative04_not_realises hC.injective
  · exact residualRepresentative05_not_realises hC.injective
  · exact residualRepresentative06_not_realises hC.injective
  · exact residualRepresentative07_not_realises hC.injective
  · exact residualRepresentative08_not_realises hC.injective
  · exact residualRepresentative09_not_realises hC.injective
  · exact residualRepresentative10_not_realises hC.injective
  · exact residualRepresentative11_not_convex_realises hC
  · exact residualRepresentative12_not_realises hC.injective

end Erdos97Octagon
