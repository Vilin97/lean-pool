/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34

/-!
# Operator Constant Nonneg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Real


namespace CKN.Foundation.Euclidean

/-- The gradient operator constant is nonnegative. -/
theorem czGradientOperatorConstant_nonneg : 0 ≤ czGradientOperatorConstant := by
  unfold czGradientOperatorConstant czGradientComponentConstant
  positivity

/-- The P1 operator constant is nonnegative. -/
theorem czP1OperatorConstant_nonneg : 0 ≤ czP1OperatorConstant := by
  unfold czP1OperatorConstant czP1Constant
  positivity

end CKN.Foundation.Euclidean

namespace CKN

/-- The Lin 3.4 force constant is nonnegative given a nonnegative parameter. -/
theorem lin34ForceConstant_nonneg {C₁₃ : ℝ} (hC : 0 ≤ C₁₃) : 0 ≤ lin34ForceConstant C₁₃ := by
  unfold lin34ForceConstant
  positivity

end CKN
