/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p

/-! # Poincare -/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

/-- Public bundled mean-zero `L²` Poincare estimate on bounded open convex
domains. -/
noncomputable def meanZeroL2PoincareEstimate {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    H1CoerciveEstimate U := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  exact Homogenization.h1CoerciveEstimate_of_isOpenBoundedConvexDomain hU

/-- Public existential form of mean-zero `L²` Poincare on bounded open convex
domains. -/
theorem exists_meanZeroL2PoincareConstant {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : H1MeanZeroFunction U, u.valueL2Norm ≤ C * u.gradientL2Norm := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  exact Homogenization.exists_poincare_constant_of_isOpenBoundedConvexDomain hU

/-- Public bundled finite-`p` mean-zero Poincare estimate on bounded open
convex domains. -/
noncomputable def meanZeroW1pPoincareEstimate {d : ℕ}
    {U : Set (Vec d)} {q : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hq : 1 < q) :
    W1pPoincareEstimate U (ENNReal.ofReal q) :=
  Homogenization.w1pPoincareEstimate_of_isOpenBoundedConvexDomain hU hq

/-- Public finite-`p` sub-average Poincare estimate on bounded open convex
domains. -/
theorem exists_subAverageW1pPoincareConstant {d : ℕ} [NeZero d]
    {U : Set (Vec d)} {q : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : W1pFunction U (ENNReal.ofReal q),
        u.subAverageLpSeminorm ≤ C * u.gradientCoordLpSeminormSum :=
  W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain hU hq

end

end Ch01
end Book
end Homogenization
