/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomProcess

/-!
# Gaussian width vocabulary

Background Wikipedia references:
* Gaussian process: https://en.wikipedia.org/wiki/Gaussian_process
* Mean width: https://en.wikipedia.org/wiki/Mean_width
* Convex geometry: https://en.wikipedia.org/wiki/Convex_geometry

Note: wiki.md listed `https://en.wikipedia.org/wiki/Gaussian_width`, but this
was not verified as a dedicated Wikipedia page. The background links above are
related to the usual mathematical context, not a direct Wikipedia-backed
formula citation. Actual Gaussian-width theorems are future work.

The standard mathematical formula usually formalized later is
`w(T) = E sup_{t in T} <g, t>` for a standard Gaussian vector `g`, but this file
does not define that formula.
-/

namespace HighDimProb

/--
Placeholder type for a Gaussian-width functional on subsets of a space.

Formula audit note: `Set E -> R` only reserves the type of a future functional.
It does not assert the Gaussian-width formula `w(T) = E sup_{t in T} <g, t>`,
so there is no Wikipedia-backed formula to cite here.
-/
abbrev GaussianWidthFunctional (E : Type*) := Set E → ℝ

end HighDimProb
