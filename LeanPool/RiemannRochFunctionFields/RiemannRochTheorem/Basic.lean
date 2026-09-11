/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.WeilDifferential.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Riemann–Roch theorem
This is pure packaging of the duality theorem together with the definition of the index of
specialty.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

/-- **Riemann–Roch** (Stichtenoth Thm. 1.5.15): for a canonical divisor `W`,

`ℓ(D) = deg D + 1 − g + ℓ(W − D)`. -/
theorem riemann_roch {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    (ell k K D : ℤ) = deg k K D + 1 - (genus k K : ℤ) + ell k K (W - D) := by
  have hi := indexOfSpecialty_eq k K D
  have hdual := indexOfSpecialty_eq_ell_sub k K hW D
  omega

end FunctionField.Chart
