/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.FirstVariation

/-! # First Variation -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 first-variation theorem for response maximizers. -/
theorem responseFirstVariationTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseFirstVariationTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseFirstVariationTheory U a

/-- Public first-variation identity for any response maximizer. -/
theorem firstVariationValue_eq_zero {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) (w : Solution U a) :
    firstVariationValue U a p q v w = 0 :=
  firstVariationValue_eq_zero_of_isResponseMaximizer
    (responseFirstVariationTheory U a) hv w

end

end Ch02
end Book
end Homogenization
