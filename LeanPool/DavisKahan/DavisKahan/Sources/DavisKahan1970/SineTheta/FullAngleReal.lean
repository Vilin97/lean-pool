/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngleReal

/-!
# Literal full angle for real subspaces

The full real angle is the direct sum of the two source-directed angles after
canonical complexification, exactly paralleling the complex source definition.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Literal full real operator angle on complexified coordinates. -/
noncomputable def sourceFullAngleR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  fullAngleBlockC (complexifySubmodule U) (complexifySubmodule V)

/-- Literal sine of the full real operator angle. -/
noncomputable def sourceFullSinR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  fullSinAngleBlockC (complexifySubmodule U) (complexifySubmodule V)

end

end ExactSinTheta
end DavisKahan
end TauCeti
