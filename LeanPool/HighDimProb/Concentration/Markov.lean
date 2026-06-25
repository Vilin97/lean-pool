/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Markov inequality

HighDimProb-facing wrapper around Mathlib's lintegral Markov inequality.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Markov%27s_inequality
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/--
Markov's inequality for a pointwise nonnegative integrable real random variable.

Formula reference: for nonnegative `X` and `a > 0`,
`P(X >= a) <= E[X] / a`; see
https://en.wikipedia.org/wiki/Markov%27s_inequality

The proof uses Mathlib's `MeasureTheory.meas_ge_le_lintegral_div`, then converts the
nonnegative `lintegral` back to the HighDimProb expectation wrapper.
-/
theorem markov_inequality_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX : IntegrableRealRandomVariable P X) (hX_nonneg : forall omega, 0 <= X omega)
    {a : Real} (ha : 0 < a) :
    upperTailProb P X a <= ENNReal.ofReal (expect P X / a) := by
  have h_meas : AEMeasurable (fun omega => ENNReal.ofReal (X omega)) P :=
    hX.aemeasurable.ennreal_ofReal
  have h_markov :
      P {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} <=
        (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) / ENNReal.ofReal a :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas
      (by exact (ENNReal.ofReal_ne_zero_iff.mpr ha))
      (by simp)
  have h_event :
      {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} = upperTailEvent X a := by
    ext omega
    exact ENNReal.ofReal_le_ofReal_iff (hX_nonneg omega)
  calc
    upperTailProb P X a =
        P {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} := by
          rw [h_event]
          rfl
    _ <= (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) / ENNReal.ofReal a := h_markov
    _ = ENNReal.ofReal (expect P X / a) := by
          rw [lintegral_ofReal_eq_ofReal_expect X hX hX_nonneg]
          exact (ENNReal.ofReal_div_of_pos ha).symm

/-- Short HighDimProb-facing alias for `markov_inequality_nonneg`. -/
theorem markov_inequality {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX : IntegrableRealRandomVariable P X) (hX_nonneg : forall omega, 0 <= X omega)
    {a : Real} (ha : 0 < a) :
    upperTailProb P X a <= ENNReal.ofReal (expect P X / a) :=
  markov_inequality_nonneg X hX hX_nonneg ha

/--
Markov's inequality for an a.e.-nonnegative integrable real random variable.

Formula reference: this keeps the same Markov bound
`P(X >= a) <= E[X] / a`; see
https://en.wikipedia.org/wiki/Markov%27s_inequality

The tail event is pointwise, but the proof only needs a.e. nonnegativity for
the `lintegral`/expectation bridge.
-/
theorem markov_inequality_ae_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} (X : RealRandomVariable Omega)
    (hX : IntegrableRealRandomVariable P X)
    (hX_nonneg : Filter.Eventually (fun omega => 0 <= X omega) (ae P))
    {a : Real} (ha : 0 < a) :
    upperTailProb P X a <= ENNReal.ofReal (expect P X / a) := by
  have h_meas : AEMeasurable (fun omega => ENNReal.ofReal (X omega)) P :=
    hX.aemeasurable.ennreal_ofReal
  have h_markov :
      P {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} <=
        (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) / ENNReal.ofReal a :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas
      (by exact (ENNReal.ofReal_ne_zero_iff.mpr ha))
      (by simp)
  have h_event :
      {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} = upperTailEvent X a := by
    ext omega
    change (ENNReal.ofReal a <= ENNReal.ofReal (X omega)) <-> a <= X omega
    apply Iff.intro
    · intro hle
      by_contra hlt
      have hxlt : X omega < a := lt_of_not_ge hlt
      have hlt_enn : ENNReal.ofReal (X omega) < ENNReal.ofReal a :=
        (ENNReal.ofReal_lt_ofReal_iff ha).mpr hxlt
      exact not_le_of_gt hlt_enn hle
    · intro hle
      exact ENNReal.ofReal_le_ofReal hle
  calc
    upperTailProb P X a =
        P {omega | ENNReal.ofReal a <= ENNReal.ofReal (X omega)} := by
          rw [h_event]
          rfl
    _ <= (∫⁻ omega, ENNReal.ofReal (X omega) ∂P) / ENNReal.ofReal a := h_markov
    _ = ENNReal.ofReal (expect P X / a) := by
          rw [lintegral_ofReal_eq_ofReal_expect_ae_nonneg X hX hX_nonneg]
          exact (ENNReal.ofReal_div_of_pos ha).symm

end

end HighDimProb
