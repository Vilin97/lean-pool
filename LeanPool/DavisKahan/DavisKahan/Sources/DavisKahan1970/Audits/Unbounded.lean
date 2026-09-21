/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.SpectralSubspace
import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Real
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngineDirect
import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Specializations
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.PartIIIPresentation

/-! # Unbounded -/

open TauCeti.DavisKahan.Sylvester

/-!
# Full unbounded sine-theta trusted-dependency audit

Compile this leaf directly to inspect the trusted dependencies of the two
ordered engines, the genuine all-gap Sylvester theorem, and the final
source-shaped sine-theta capstones.
-/

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

end ExactSinTheta
end DavisKahan
end TauCeti
