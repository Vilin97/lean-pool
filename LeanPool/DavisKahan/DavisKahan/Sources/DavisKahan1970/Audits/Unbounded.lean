/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.SpectralSubspace
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Real
public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngineDirect
public import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Specializations
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.PartIIIPresentation

/-! # Unbounded -/

@[expose] public section

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
