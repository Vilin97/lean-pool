/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Scalar

/-!
# Scalar concentration basics

Verified Wikipedia references:
* Concentration inequality: https://en.wikipedia.org/wiki/Concentration_inequality
* Expected value: https://en.wikipedia.org/wiki/Expected_value

Note: the tail-event monotonicity lemmas here are support vocabulary for
concentration bounds, not a standalone named concentration inequality.

Small reusable event and expectation bridges for scalar concentration proofs.
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/-- Upper-tail events shrink as the threshold increases. -/
theorem upperTailEvent_subset_of_le {Omega : Type*} [MeasurableSpace Omega]
    (X : RealRandomVariable Omega) {s t : Real} (hst : s <= t) :
    upperTailEvent X t ⊆ upperTailEvent X s :=
  fun _ h => hst.trans h

/-- Lower-tail events grow as the threshold increases. -/
theorem lowerTailEvent_subset_of_le {Omega : Type*} [MeasurableSpace Omega]
    (X : RealRandomVariable Omega) {s t : Real} (hst : s <= t) :
    lowerTailEvent X s ⊆ lowerTailEvent X t :=
  fun _ h => h.trans hst

/-- Absolute-tail events shrink as the threshold increases. -/
theorem absTailEvent_subset_of_le {Omega : Type*} [MeasurableSpace Omega]
    (X : RealRandomVariable Omega) {s t : Real} (hst : s <= t) :
    absTailEvent X t ⊆ absTailEvent X s :=
  fun _ h => hst.trans h

/-- A pointwise nonnegative real random variable has nonnegative expectation. -/
theorem expect_nonneg_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX_nonneg : forall omega, 0 <= X omega) :
    0 <= expect P X := by
  exact integral_nonneg_of_ae (ae_of_all P hX_nonneg)

/-- Compatibility form of `expect_nonneg_of_nonneg` with an explicit integrability argument. -/
theorem expect_nonneg_of_nonneg_integrable {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (_hX : IntegrableRealRandomVariable P X) (hX_nonneg : forall omega, 0 <= X omega) :
    0 <= expect P X :=
  expect_nonneg_of_nonneg X hX_nonneg

/--
For a pointwise nonnegative integrable real random variable, its `lintegral`
through `ENNReal.ofReal` is the `ENNReal.ofReal` of its HighDimProb expectation.
-/
theorem lintegral_ofReal_eq_ofReal_expect {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX : IntegrableRealRandomVariable P X) (hX_nonneg : forall omega, 0 <= X omega) :
    (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) = ENNReal.ofReal (expect P X) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hX (ae_of_all P hX_nonneg)]

/--
For an a.e.-nonnegative integrable real random variable, its `lintegral`
through `ENNReal.ofReal` is the `ENNReal.ofReal` of its HighDimProb expectation.
-/
theorem lintegral_ofReal_eq_ofReal_expect_ae_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX : IntegrableRealRandomVariable P X)
    (hX_nonneg : Filter.Eventually (fun omega => 0 <= X omega) (ae P)) :
    (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) = ENNReal.ofReal (expect P X) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hX hX_nonneg]

end

end HighDimProb
