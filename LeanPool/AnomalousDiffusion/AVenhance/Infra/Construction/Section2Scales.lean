/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.RecursionIncrement

/-! Canonical scalar scales in the Section 2 regularity induction. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Construction

/-- The radius sequence in `e.recurrence`, with its source initial value. -/
def section2Radius {β : ℝ} (I : Ingredients β) : ℕ → ℝ
  | 0 => 1
  | m + 1 => (9 / 4) * section2Radius I m +
      2 ^ 7 * (epsilon β I.Λ (m + 1))⁻¹

/-- The amplitude sequence in `e.recurrence`, with its source initial value. -/
def section2Amplitude {β : ℝ} (I : Ingredients β) : ℕ → ℝ
  | 0 => 1
  | m + 1 => section2Amplitude I m +
      2 ^ 7 * a β I.Λ (m + 1) * epsilon β I.Λ (m + 1) ^ 2 *
        section2Radius I m ^ 2 +
      2 ^ 18 * a β I.Λ (m + 1)

/-- The source-defined radius and amplitude sequences satisfy the induction
scale data used by the stream-regularity proof. -/
theorem section2Scales_canonical {β : ℝ} (I : Ingredients β) :
    Section2Scales I (section2Radius I) (section2Amplitude I) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    rfl

end AVenhance.Infra.Construction
