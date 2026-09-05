/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module


public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of finite products and sums
-/

variable {ι α β M : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mM : MeasurableSpace M} [CommMonoid M] [MeasurableMul₂ M]

-- TODO: Replace `Finset.measurable_prod'`
/-- Compositional version of `Finset.measurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.measurable_sum` for use by `fun_prop`. -/]
public
lemma Finset.measurable_prod'' {f : ι → α → β → M} {g : α → β} {s : Finset ι}
    (hf : ∀ i ∈ s, Measurable ↿(f i)) (hg : Measurable g) :
    Measurable fun a ↦ (∏ i ∈ s, f i a) (g a) := by
  simp only [prod_apply]
  fun_prop (disch := assumption)
