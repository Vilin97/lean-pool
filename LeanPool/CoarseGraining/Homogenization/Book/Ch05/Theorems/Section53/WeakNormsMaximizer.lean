/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

/-! # Weak Norms Maximizer -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53

/-!
# Deterministic weak-norm bounds for the maximizer

Top-level module for the second manuscript lemma in Section 5.3,
`l.weak.norms.maximizer.homogenization.scale`.  The apex theorem and its
paired gradient/flux constituents are proved in
`Section53/WeakNormsMaximizer/Assembly.lean` inside `namespace
WeakNormsMaximizer` and re-exported here at the `Section53` namespace level
so downstream callers can use the short manuscript-shaped name.
-/

export WeakNormsMaximizer
  (weakNormsMaximizer_homogenizationScale
   weakNormsMaximizerGradient_homogenizationScale
   weakNormsMaximizerFlux_homogenizationScale)

end Section53
end Ch05
end Book
end Homogenization
