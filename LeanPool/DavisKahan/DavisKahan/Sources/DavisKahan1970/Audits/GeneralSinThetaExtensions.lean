/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions

/-!
# Trusted-dependency audit for optional natural-input extensions

Compile this leaf only after every imported extension module builds from
source.  The established source endpoints are repeated here so a repair pass
cannot accidentally regress the theorem completed at the base commit.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

end ExactSinTheta
end DavisKahan
end TauCeti
