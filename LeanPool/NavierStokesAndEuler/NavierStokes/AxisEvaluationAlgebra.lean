/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisEvaluation
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisOperators
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Actual profile equations for the coefficient operators

The identities here combine the convergent, smooth evaluation of `AxisSpace`
with the exact compatible coefficient operators of `AxisOperators`.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisOperators

namespace NavierStokes.AxisEvaluationAlgebra

theorem powerSeries_mul {f g : ℕ → ℝ} {Y : ℝ}
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖)) :
    (∑' n : ℕ, Y ^ n * f n) * (∑' n : ℕ, Y ^ n * g n) =
      ∑' n : ℕ, Y ^ n * ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

theorem profile_series_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n => ‖Y ^ n * coefficient I (weight ε) A n η‖) := by
  simpa only [Real.norm_eq_abs] using (profile_hasSum I hε A (p := (Y, η)) hY).summable.abs

/-- Multiplication in the coefficient space evaluates to pointwise multiplication. -/
theorem profile_product (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (product I hε A B) (Y, η) =
      profile I ε A (Y, η) * profile I ε B (Y, η) := by
  rw [profile, profile, profile, powerSeries_mul
    (profile_series_norm_summable I hε A hY) (profile_series_norm_summable I hε B hY)]
  apply tsum_congr
  intro n
  rw [coefficient_product I hε A B n hη]

theorem profile_axis (I : Window) (ε : ℝ) (A : AxisSpace I ε) (η : ℝ) :
    profile I ε A (0, η) = coefficient I (weight ε) A 0 η := by
  unfold profile
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem profile_deriv_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    deriv (fun y => profile I ε A (y, η)) Y = mixedSeries I ε A 1 0 (Y, η) := by
  have hd := mixedSeries_hasDerivAt_Y I hε A 0 0 hY hη
  rw [mixedSeries_zero] at hd
  exact hd.deriv

theorem profile_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    deriv (fun x => profile I ε A (Y, x)) η = mixedSeries I ε A 0 1 (Y, η) := by
  have hd := mixedSeries_hasDerivAt_eta I hε A 0 0 hY hη
  rw [mixedSeries_zero] at hd
  exact hd.deriv

theorem profile_iteratedDeriv_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k : ℕ) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv k (fun y => profile I ε A (y, η)) Y = mixedSeries I ε A k 0 (Y, η) := by
  simpa only [mixedSeries_zero, Nat.zero_add] using iteratedDeriv_Y I hε A 0 0 k hY hη

def radialValue (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  p.1 * mixedSeries I ε A 2 0 p + (r : ℝ) * mixedSeries I ε A 1 0 p

theorem radialValue_eq_derivatives (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    radialValue I ε r A (Y, η) =
      Y * iteratedDeriv 2 (fun y => profile I ε A (y, η)) Y +
        (r : ℝ) * deriv (fun y => profile I ε A (y, η)) Y := by
  rw [profile_iteratedDeriv_Y I hε A 2 hY hη, profile_deriv_Y I hε A hY hη]
  rfl

theorem polynomialJet_radial (r n : ℕ) (Y : ℝ) :
    Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y =
      radialDivisor r n * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet, radialDivisor, Nat.descFactorial_succ]
  | succ n =>
      have he : n + 1 + 1 - 2 = n := by omega
      simp only [polynomialJet, Nat.descFactorial_succ, Nat.descFactorial_zero,
        Nat.sub_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simp only [Nat.add_sub_cancel, he]
      unfold radialDivisor
      push_cast
      rw [pow_succ]
      ring

/-- Coefficient formula for the actual regular radial differential operator. -/
theorem radialValue_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    radialValue I ε r A (Y, η) =
      ∑' n : ℕ, radialDivisor r n * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have h₂ := mixedSeries_summable I hε A 2 0 (p := (Y, η)) hY
  have h₁ := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  have hs := (h₂.mul_left Y).add (h₁.mul_left (r : ℝ))
  calc
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 n (Y, η) +
        (r : ℝ) * term I ε A 1 0 n (Y, η)) := by
      rw [Summable.tsum_add (h₂.mul_left Y) (h₁.mul_left (r : ℝ)), tsum_mul_left, tsum_mul_left]
      rfl
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 (n + 1) (Y, η) +
        (r : ℝ) * term I ε A 1 0 (n + 1) (Y, η)) := by
      rw [hs.tsum_eq_zero_add]
      simp [term, polynomialJet]
    _ = _ := by
      apply tsum_congr
      intro n
      calc
        _ = (Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y) *
            coefficient I (weight ε) A (n + 1) η := by unfold term coefficient; ring
        _ = _ := by rw [polynomialJet_radial]

/-- The regular inverse is a genuine right inverse on evaluated profiles. -/
theorem regularInverse_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (regularInverse I hε r hr A) (Y, η) = profile I ε A (Y, η) := by
  rw [radialValue_series I hε r _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε (regularInverse I hε r hr A) (n + 1) 0 η = _
  rw [jet_regularInverse_succ I hε r hr A n 0 hη]
  change radialDivisor r n * Y ^ n * (coefficient I (weight ε) A n η / radialDivisor r n) = _
  field_simp [(radialDivisor_pos hr n).ne']

theorem regularInverse_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (regularInverse I hε r hr A) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_regularInverse_zero I hε r hr A 0 hη

theorem derivativeSeries (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, ((n : ℝ) + 1) * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have hs := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  unfold mixedSeries
  rw [hs.tsum_eq_zero_add]
  simp only [term, polynomialJet, Nat.zero_descFactorial_succ, Nat.cast_zero,
    zero_mul, zero_add]
  apply tsum_congr
  intro n
  simp [coefficient]

theorem jet_average_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (average I hε A) n m η = inputJet I ε A n m η / ((n : ℝ) + 1) := by
  change inputJet I ε (linearLift I hε (averageData I hε) A) n m η = _
  rw [jet_linearLift I hε (averageData I hε) A n m hη]
  change (1 / ((n : ℝ) + 1)) * inputJet I ε A n (0 + m) η = _
  rw [Nat.zero_add]
  ring

theorem jet_primitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (primitive I hε A) n m η = primitiveScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (primitiveData I hε) A) n m η = _
  rw [jet_linearLift I hε (primitiveData I hε) A n m hη]
  change primitiveScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem jet_parameterPrimitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (parameterPrimitive I hε A) n m η =
      primitiveScale n * inputJet I ε A n.pred (1 + m) η := by
  change inputJet I ε (linearLift I hε (parameterPrimitiveData I hε) A) n m η = _
  exact jet_linearLift I hε (parameterPrimitiveData I hε) A n m hη

theorem jet_mulY_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (mulY I hε A) n m η = multiplyYScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (multiplyYData I hε) A) n m η = _
  rw [jet_linearLift I hε (multiplyYData I hε) A n m hη]
  change multiplyYScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem primitive_Y_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    mixedSeries I ε (primitive I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  rw [derivativeSeries I hε _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change ((n : ℝ) + 1) * Y ^ n * inputJet I ε (primitive I hε A) (n + 1) 0 η = _
  rw [jet_primitive_eval I hε A (n + 1) 0 hη]
  simp only [primitiveScale, Nat.pred_succ]
  change ((n : ℝ) + 1) * Y ^ n * (1 / ((n : ℝ) + 1) * coefficient I (weight ε) A n η) = _
  field_simp

theorem primitive_hasDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => profile I ε (primitive I hε A) (y, η)) (profile I ε A (Y, η)) Y := by
  have hd := mixedSeries_hasDerivAt_Y I hε (primitive I hε A) 0 0 hY hη
  rw [mixedSeries_zero, primitive_Y_value I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩] at hd
  exact hd

theorem primitive_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (primitive I hε A) (0, η) = 0 := by
  rw [profile_axis]
  change inputJet I ε (primitive I hε A) 0 0 η = _
  rw [jet_primitive_eval I hε A 0 0 hη]
  simp [primitiveScale]

theorem profile_mulY (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (mulY I hε A) (Y, η) = Y * profile I ε A (Y, η) := by
  have hs := (profile_hasSum I hε (mulY I hε A) (p := (Y, η)) hY).summable
  unfold profile
  rw [hs.tsum_eq_zero_add]
  have hzero : coefficient I (weight ε) (mulY I hε A) 0 η = 0 := by
    change inputJet I ε (mulY I hε A) 0 0 η = _
    rw [jet_mulY_eval I hε A 0 0 hη]
    simp [multiplyYScale]
  rw [hzero, mul_zero, zero_add, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y ^ (n + 1) * inputJet I ε (mulY I hε A) (n + 1) 0 η = _
  rw [jet_mulY_eval I hε A (n + 1) 0 hη]
  simp only [multiplyYScale, Nat.pred_succ, one_mul, pow_succ]
  change Y ^ n * Y * coefficient I (weight ε) A n η = _
  ring

theorem primitive_eq_mulY_average (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) : primitive I hε A = mulY I hε (average I hε A) := by
  apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
  intro n η hη
  change inputJet I ε (primitive I hε A) n 0 η = inputJet I ε (mulY I hε (average I hε A)) n 0 η
  rw [jet_primitive_eval I hε A n 0 hη, jet_mulY_eval I hε (average I hε A) n 0 hη,
    jet_average_eval I hε A n.pred 0 hη]
  cases n <;> simp [primitiveScale, multiplyYScale, div_eq_mul_inv, mul_comm]

theorem average_times_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    Y * profile I ε (average I hε A) (Y, η) = profile I ε (primitive I hε A) (Y, η) := by
  rw [primitive_eq_mulY_average, profile_mulY I hε _ hY hη]

theorem parameterSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (m : ℕ) (Y η : ℝ) :
    mixedSeries I ε A 0 m (Y, η) = ∑' n : ℕ, Y ^ n * inputJet I ε A n m η := by
  simp only [mixedSeries, term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one,
    Nat.sub_zero, one_mul, inputJet]

theorem parameterSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (m : ℕ) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * inputJet I ε A n m η‖) := by
  simpa only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_mul, Prod.fst, Prod.snd, inputJet, Real.norm_eq_abs] using
    (mixedSeries_summable I hε A 0 m (p := (Y, η)) hY).abs

theorem polynomialJet_dot (n : ℕ) (Y : ℝ) :
    Y * polynomialJet n 1 Y = (n : ℝ) * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet]
  | succ n =>
      simp only [polynomialJet, Nat.descFactorial_one, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem dotSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y η : ℝ) :
    Y * mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
  rw [mixedSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) = _
  rw [← mul_assoc, polynomialJet_dot]
  ring

theorem dotSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)‖) := by
  have hs := ((mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY).mul_left Y).abs
  convert! hs using 1
  funext n
  change |Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)| =
    |Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η)|
  have he : Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) =
      Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
    rw [← mul_assoc, polynomialJet_dot]
    ring
  rw [he]

theorem radialValue_of_convolution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (C : AxisSpace I ε) (f g : ℕ → ℝ) {Y η : ℝ} (hY : |Y| < 20)
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖))
    (hC : ∀ n, radialDivisor r n * inputJet I ε C (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) :
    radialValue I ε r C (Y, η) = (∑' n, Y ^ n * f n) * (∑' n, Y ^ n * g n) := by
  rw [radialValue_series I hε r C hY, powerSeries_mul hf hg]
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε C (n + 1) 0 η = _
  calc
    _ = Y ^ n * (radialDivisor r n * inputJet I ε C (n + 1) 0 η) := by ring
    _ = _ := by rw [hC n]

theorem differentialFamily_cancel (I : Window) (ε : ℝ) (r p : ℕ) (hr : 1 ≤ r)
    (d : ℕ → ℝ) (A B : AxisSpace I ε) (n : ℕ) (η : ℝ) :
    radialDivisor r n * differentialFamily I ε r p d A B (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, inputJet I ε A ij.1 p η *
        (d ij.2 * inputJet I ε B ij.2 0 η) := by
  simp only [differentialFamily, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  field_simp [(radialDivisor_pos hr n).ne']

/-- The parameter derivative is on the first factor and the radial dot is
on the second factor, as required by the manuscript's mixed estimate. -/
theorem inverseMixed_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseMixed I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [parameterSeries, dotSeries]
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseMixed I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 1 hr (fun j => (j : ℝ)) A B n η

theorem inverseParamProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * profile I ε B (Y, η) := by
  rw [parameterSeries]
  change radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
    (∑' n, Y ^ n * inputJet I ε A n 1 η) * (∑' n, Y ^ n * inputJet I ε B n 0 η)
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (parameterSeries_norm_summable I hε B 0 hY)
  intro n
  rw [jet_inverseParamProduct I hε r hr A B (n + 1) 0 hη]
  simpa only [one_mul] using differentialFamily_cancel I ε r 1 hr (fun _ => 1) A B n η

theorem inverseDotProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
      profile I ε A (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [dotSeries]
  change radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
    (∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η) *
      (∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε B n 0 η))
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 0 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseDotProduct I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 0 hr (fun j => (j : ℝ)) A B n η

theorem inverseMixed_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseMixed I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseMixed I hε r hr A B 0 0 hη

theorem inverseParamProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseParamProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseParamProduct I hε r hr A B 0 0 hη

theorem inverseDotProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseDotProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseDotProduct I hε r hr A B 0 0 hη

theorem parameterPrimitive_eta_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (Y : ℝ) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      mixedSeries I ε (primitive I hε A) 0 1 (Y, η) := by
  rw [parameterSeries]
  unfold profile
  apply tsum_congr
  intro n
  change Y ^ n * inputJet I ε (parameterPrimitive I hε A) n 0 η = _
  rw [jet_parameterPrimitive_eval I hε A n 0 hη, jet_primitive_eval I hε A n 1 hη]

/-- The pressure parameter primitive is the actual parameter derivative
of the radial primitive. -/
theorem parameterPrimitive_eq_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      deriv (fun x => profile I ε (primitive I hε A) (Y, x)) η := by
  rw [profile_deriv_eta I hε _ hY hη]
  exact parameterPrimitive_eta_value I hε A Y ⟨hη.1.le, hη.2.le⟩

theorem parameterPrimitive_Y_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    mixedSeries I ε (parameterPrimitive I hε A) 1 0 (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) := by
  rw [derivativeSeries I hε _ hY, parameterSeries]
  apply tsum_congr
  intro n
  change ((n : ℝ) + 1) * Y ^ n * inputJet I ε (parameterPrimitive I hε A) (n + 1) 0 η = _
  rw [jet_parameterPrimitive_eval I hε A (n + 1) 0 hη]
  simp only [primitiveScale, Nat.pred_succ, Nat.add_zero]
  field_simp

theorem parameterPrimitive_hasDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => profile I ε (parameterPrimitive I hε A) (y, η))
      (deriv (fun x => profile I ε A (Y, x)) η) Y := by
  have hd := mixedSeries_hasDerivAt_Y I hε (parameterPrimitive I hε A) 0 0 hY hη
  rw [mixedSeries_zero, parameterPrimitive_Y_value I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩] at hd
  rwa [profile_deriv_eta I hε A hY hη]

theorem parameterPrimitive_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (parameterPrimitive I hε A) (0, η) = 0 := by
  rw [profile_axis]
  change inputJet I ε (parameterPrimitive I hε A) 0 0 η = _
  rw [jet_parameterPrimitive_eval I hε A 0 0 hη]
  simp [primitiveScale]

theorem radial_segment_mem {Y y : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hy : y ∈ uIcc (0 : ℝ) Y) : y ∈ Ioo (-20 : ℝ) 20 := by
  rcases le_total (0 : ℝ) Y with h | h
  · rw [uIcc_of_le h] at hy
    exact ⟨lt_of_lt_of_le (by norm_num) hy.1, hy.2.trans_lt hY.2⟩
  · rw [uIcc_of_ge h] at hy
    exact ⟨hY.1.trans_le hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩

/-- The coefficient primitive equals the ordinary oriented integral. -/
theorem primitive_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (primitive I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  have hcont : ContinuousOn (fun y => profile I ε A (y, η)) (uIcc (0 : ℝ) Y) := by
    intro y hy
    have hd := mixedSeries_hasDerivAt_Y I hε A 0 0 (radial_segment_mem hY hy) hη
    rw [mixedSeries_zero] at hd
    exact hd.continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => primitive_hasDerivAt I hε A (radial_segment_mem hY hy) hη)
    hcont.intervalIntegrable
  rw [primitive_axis_zero I hε A ⟨hη.1.le, hη.2.le⟩, sub_zero] at hi
  exact hi.symm

theorem average_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    Y * profile I ε (average I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  rw [average_times_Y I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩]
  exact primitive_integral I hε A hY hη

theorem regularInverse_actual_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    Y * iteratedDeriv 2 (fun y => profile I ε (regularInverse I hε r hr A) (y, η)) Y +
      (r : ℝ) * deriv (fun y => profile I ε (regularInverse I hε r hr A) (y, η)) Y =
      profile I ε A (Y, η) := by
  rw [← radialValue_eq_derivatives I hε r _ hY hη]
  exact regularInverse_equation I hε r hr A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩

theorem inverseMixed_actual_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    Y * iteratedDeriv 2 (fun y => profile I ε (inverseMixed I hε r hr A B) (y, η)) Y +
      (r : ℝ) * deriv (fun y => profile I ε (inverseMixed I hε r hr A B) (y, η)) Y =
      deriv (fun x => profile I ε A (Y, x)) η *
        (Y * deriv (fun y => profile I ε B (y, η)) Y) := by
  rw [← radialValue_eq_derivatives I hε r _ hY hη,
    profile_deriv_eta I hε A hY hη, profile_deriv_Y I hε B hY hη]
  exact inverseMixed_equation I hε r hr A B (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩

theorem average_axis (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (0, η) = profile I ε A (0, η) := by
  rw [profile_axis, profile_axis]
  change inputJet I ε (average I hε A) 0 0 η = inputJet I ε A 0 0 η
  rw [jet_average_eval I hε A 0 0 hη]
  norm_num

theorem average_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (Y, η) +
      Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  have hs := (parameterSeries_norm_summable I hε (average I hε A) 0 (η := η) hY).of_norm
  have hd := (dotSeries_norm_summable I hε (average I hε A) (η := η) hY).of_norm
  change (∑' n : ℕ, Y ^ n * inputJet I ε (average I hε A) n 0 η) +
    Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) =
    ∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η
  rw [dotSeries, ← hs.tsum_add hd]
  apply tsum_congr
  intro n
  rw [jet_average_eval I hε A n 0 hη]
  field_simp ; ring

end NavierStokes.AxisEvaluationAlgebra
