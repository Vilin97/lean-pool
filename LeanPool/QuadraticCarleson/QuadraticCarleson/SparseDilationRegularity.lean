/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseDilation

/-!
# Regularity and sublinearity under positive dilation

The finite high-scale sparse family is transferred to the paper's positive
modulations by positive spatial dilation. These elementary identities retain
the original test-function addition, scalar multiplication and absolute-value
operator, and transfer continuity and local integrability of the outputs.
-/

open Function MeasureTheory

namespace QuadraticCarleson


noncomputable
section

namespace L0Infinity

@[simp] theorem dilate_add (a : ℝ) (ha : 0 < a) (f g : L0Infinity) :
    dilate a ha (add f g) = add (dilate a ha f) (dilate a ha g) := rfl

@[simp] theorem dilate_smul (a : ℝ) (ha : 0 < a) (c : ℂ) (f : L0Infinity) :
    dilate a ha (smul c f) = smul c (dilate a ha f) := rfl

end L0Infinity

namespace SparseDilationRegularity

open KrauseLaceySparseDilation

/-- Spatial dilation preserves the exact sublinearity requirements used by
the finite sparse-maximal theorem. -/
theorem isSublinear_dilatedOperator (a : ℝ) (ha : 0 < a)
    {T : TestOperator} (hT : IsSublinear T) :
    IsSublinear (dilatedOperator a ha T) := by
  constructor
  · intro f g x
    simpa only [dilatedOperator, L0Infinity.dilate_add] using
      hT.1 (L0Infinity.dilate a ha f) (L0Infinity.dilate a ha g) (a * x)
  · intro c f x
    simpa only [dilatedOperator, L0Infinity.dilate_smul] using
      hT.2 c (L0Infinity.dilate a ha f) (a * x)

/-- Taking an absolute value commutes exactly with the operator dilation. -/
@[simp] theorem absoluteValue_dilatedOperator (a : ℝ) (ha : 0 < a)
    (T : TestOperator) :
    absoluteValueOperator (dilatedOperator a ha T) =
      dilatedOperator a ha (absoluteValueOperator T) := rfl

/-- Continuity of each original output gives continuity of each dilated
output by composition with multiplication by the dilation factor. -/
theorem continuous_dilatedOperator (a : ℝ) (ha : 0 < a)
    {T : TestOperator} (hT : ∀ f : L0Infinity, Continuous (T f))
    (f : L0Infinity) : Continuous (dilatedOperator a ha T f) :=
  (hT (L0Infinity.dilate a ha f)).comp (continuous_const.mul continuous_id)

/-- The continuity available for the concrete finite suffix maximum supplies
the local-integrability clause of the finite sparse-maximal hypothesis. -/
theorem locallyIntegrable_dilatedOperator_of_continuous (a : ℝ) (ha : 0 < a)
    {T : TestOperator} (hT : ∀ f : L0Infinity, Continuous (T f))
    (f : L0Infinity) : LocallyIntegrable (dilatedOperator a ha T f) volume :=
  (continuous_dilatedOperator a ha hT f).locallyIntegrable


end SparseDilationRegularity
end
end QuadraticCarleson
