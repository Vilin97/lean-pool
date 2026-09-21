/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.AEEq

/-! # Public -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# Public Chapter 2.5 Homogenization Error Package

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

/-- Aggregate unconditional public theorem package for the Sec. 2.5
homogenization-error facts currently needed downstream. -/
theorem homogenizationErrorTheory (d : ℕ) [NeZero d] :
    HomogenizationErrorTheory d := by
  refine ⟨?_⟩
  intro Q a a0
  exact homogenizationErrorInfinityOneBasicTheory Q a a0

end

end Ch02
end Book
end Homogenization
