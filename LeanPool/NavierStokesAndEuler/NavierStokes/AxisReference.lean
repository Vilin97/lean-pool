/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalAxisBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisSeries

/-!
# Identification and positivity of the actual natural-axis reference

The reference is the image of the unit datum under the constructed Banach-space
resolvent. Its coefficient recurrence identifies its evaluation with the entire
leading series. Uniform estimates for the actual nonlinear profiles then preserve
positivity and a strict logarithmic-slope margin at one common parameter scale.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisReference

open Set AxisCoefficientSpace AxisWeightEstimates NaturalAxisBridge
open scoped BigOperators Topology ContDiff


theorem coefficient_naturalOperator_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) 0 η = 0 := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hz := AxisOperators.jet_regularInverse_zero I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) 0 hη
  dsimp only [AxisOperators.inputJet] at hz
  rw [hz, mul_zero]

theorem coefficient_naturalOperator_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) (n + 1) η =
      (1 / 2 : ℝ) * (coefficient I (weight ε) χ 0 η *
        coefficient I (weight ε) A n η / radialDivisor 2 n) := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hs := AxisOperators.jet_regularInverse_succ I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) n 0 hη
  dsimp only [AxisOperators.inputJet] at hs
  rw [hs]
  change (1 / 2 : ℝ) *
      (coefficient I (weight ε) (AxisOperators.product I hε χ A) n η /
        radialDivisor 2 n) = _
  rw [coefficient_product_constant I hε χ A hχ n hη]
  rfl

/-- The unit datum is preserved at the axis by the actual resolvent. -/
theorem reference_coefficient_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval)
    (he : coefficient I (weight ε) e 0 η = 1) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η = 1 := by
  have heq := congrArg (fun A : AxisSpace I ε => coefficient I (weight ε) A 0 η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) 0 η =
      coefficient I (weight ε) e 0 η at heq
  rw [coefficient_naturalOperator_zero I hε χ _ hη, add_zero, he] at heq
  exact heq

/-- Every higher coefficient is forced by the resolvent equation; the
recurrence is derived from the bounded operators, rather than postulated. -/
theorem reference_coefficient_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η =
      (-coefficient I (weight ε) χ 0 η / 2) *
        coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η /
          radialDivisor 2 n := by
  have heq := congrArg
    (fun A : AxisSpace I ε => coefficient I (weight ε) A (n + 1) η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) (n + 1) η =
      coefficient I (weight ε) e (n + 1) η at heq
  rw [coefficient_naturalOperator_succ I hε χ _ hχ n hη,
    he (n + 1) (by omega) η hη] at heq
  linear_combination heq

/-- The constructed resolvent has the factorial coefficients of the
regular Bessel-type reference. -/
theorem reference_coefficient (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (n : ℕ) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η =
      (-coefficient I (weight ε) χ 0 η / 2) ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  induction n with
  | zero => simpa using reference_coefficient_zero I hε χ e hη he0
  | succ n ih =>
      rw [reference_coefficient_succ I hε χ e hχ he n hη, ih]
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        radialDivisor, Nat.cast_ofNat, pow_succ]
      field_simp; ring

/-- Evaluation of the actual coefficient-space reference equals the
entire leading series at every real radius. -/
theorem reference_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (Y : ℝ) :
    AxisEvaluation.profile I ε (AxisResolvent.naturalResolvent I hε χ e) (Y, η) =
      AxisSeries.profile (coefficient I (weight ε) χ 0 η) Y := by
  rw [AxisEvaluation.profile, AxisSeries.profile_eq_tsum]
  apply tsum_congr
  intro n
  rw [reference_coefficient I hε χ e hχ he hη he0 n]
  rw [← mul_div_assoc, ← mul_pow]
  congr 2
  ring

/-- In particular, the leading pair used by the nonlinear existence theorem
has exactly this angular series. -/
theorem referenceCoefficients_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) =
      AxisSeries.profile (inputValue I ε χ η) Y := by
  exact reference_profile_eq_series I hε χ d.one hd.chi_radial hd.one_radial
    hη (hd.one_value η hη) Y

theorem referenceCoefficients_deriv_Y_eq (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    deriv (fun y => AxisEvaluation.profile I ε
      (referenceCoefficients I hε χ d).1 (y, η)) Y =
        deriv (AxisSeries.profile (inputValue I ε χ η)) Y := by
  congr 2
  funext y
  exact referenceCoefficients_profile_eq_series I hε χ d hd hη y

/-- The lower bound concerns the reference constructed by the resolvent,
not a separately declared comparison function. -/
theorem referenceCoefficients_gt_quarter (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η Y : ℝ} (hη : η ∈ I.interval)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) :
    1 / 4 < AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) := by
  rw [referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_gt_quarter _ Y hχ0 hχ1 hY0 hY1

theorem referenceCoefficients_log_slope_at_four (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    236 / 100 <
      -8 * deriv (fun y => AxisEvaluation.profile I ε
        (referenceCoefficients I hε χ d).1 (y, η)) 4 /
          AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (4, η) := by
  rw [referenceCoefficients_deriv_Y_eq I hε χ d hd hη,
    referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_log_slope_at_four _ hχ99 hχ1

/-- Quantitative stability of the strict slope margin under simultaneous
value and first-derivative errors of at most `1/1000`. -/
theorem log_slope_stability {v₀ v d₀ d : ℝ}
    (hv₀ : 1 / 4 < v₀) (hvalue : |v - v₀| ≤ 1 / 1000)
    (hderiv : |d - d₀| ≤ 1 / 1000) (hslope : 236 / 100 < -8 * d₀ / v₀) :
    1 / 8 < v ∧ 23 / 10 < -8 * d / v := by
  have hv : 1 / 8 < v := by
    have := (abs_le.mp hvalue).1
    linarith
  refine ⟨hv, ?_⟩
  have hvpos : 0 < v := by linarith
  have hv₀pos : 0 < v₀ := by linarith
  rw [lt_div_iff₀ hvpos]
  rw [lt_div_iff₀ hv₀pos] at hslope
  have he0 := (abs_le.mp hvalue).2
  have he1 := (abs_le.mp hderiv).2
  nlinarith

/-- A single lower bound on the scale makes both evaluation constants
small enough for positivity and logarithmic-slope stability. -/
theorem scaled_error_le {C C₀ C₁ K Λ : ℝ}
    (hCsum : C ≤ C₀ + C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hΛ : 1 + 500 * (C₀ + C₁) * K ≤ Λ) :
    C * (K / (2 * Λ)) ≤ 1 / 1000 := by
  have hsum : 0 ≤ C₀ + C₁ := add_nonneg hC₀ hC₁
  have hΛpos : 0 < Λ := by nlinarith [mul_nonneg hsum hK]
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * Λ)]
  nlinarith [mul_le_mul_of_nonneg_right hCsum hK]

/-- This explicit threshold controls both values and first radial derivatives
on `|Y|≤5`, uniformly over the parameter interval. -/
def stabilityScale (ε K : ℝ) : ℝ :=
  1 + 500 * (AxisEvaluation.jetBound ε 5 0 0 + AxisEvaluation.jetBound ε 5 1 0) * K

theorem stabilityScale_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    0 < stabilityScale ε K := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  unfold stabilityScale
  positivity

theorem value_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |Φ p - Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 0 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_right hC₁) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 0 0 p hY hη).1
  exact le_trans (by simpa only [mixedDerivative, iteratedDeriv_zero] using he) hb

theorem radial_deriv_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |partialY Φ p - partialY Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 1 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_left hC₀) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 1 0 p hY hη).1
  exact le_trans
    (by simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one, partialY] using he) hb

/-- Uniform closeness to the actual reference preserves a positive margin
on the full closed radial interval. -/
theorem positive_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {Y η : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10)
    (hη : η ∈ Ioo I.left I.right)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    1 / 8 < Φ (Y, η) := by
  have href := referenceCoefficients_gt_quarter I hε χ d hd
    (show η ∈ I.interval from ⟨hη.1.le, hη.2.le⟩) hχ0 hχ1 hY0 hY1
  have he := value_error_le I hε hK hΛ herr
    (p := (Y, η)) (by simpa only [abs_of_nonneg hY0] using (show Y ≤ 5 by linarith)) hη
  have he' := (abs_le.mp he).1
  linarith

/-- The same scale preserves a strict slope greater than `2.3` wherever
the parameter coefficient is at least `0.99`. -/
theorem log_slope_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {η : ℝ} (hη : η ∈ Ioo I.left I.right)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hη' : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
  have href := referenceCoefficients_gt_quarter I hε χ d hd hη'
    (by linarith : 0 ≤ inputValue I ε χ η) hχ1
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 41 / 10)
  have hslope := referenceCoefficients_log_slope_at_four I hε χ d hd hη' hχ99 hχ1
  exact (log_slope_stability href
    (value_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    (radial_deriv_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    hslope).2

/-- One sufficiently large scale gives the actual smooth nonlinear
profiles, all mixed-derivative estimates, uniform positivity, and the strict
angular slope bound, simultaneously for the full amplitude norm ball. -/
theorem exists_positive_scaled_profiles (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d)
    (hχ : ∀ η ∈ I.interval, 0 ≤ inputValue I ε χ η ∧ inputValue I ε χ η ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisSpace I ε, ‖a‖ ≤ M → RadiallyConstant I ε a →
      ∃ Φ u B P : ℝ × ℝ → ℝ,
        IsScaledSolution I (parameters I ε χ d) (1 / Λ) (inputValue I ε a) Φ u B P ∧
        UniformMixedError I ε (errorConstant I hε χ d M hM / (2 * Λ))
          Φ u (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
          (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) ∧
        (∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ η ∈ Ioo I.left I.right, 1 / 8 < Φ (Y, η)) ∧
        (∀ η ∈ Ioo I.left I.right, 99 / 100 ≤ inputValue I ε χ η →
          23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η)) := by
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := exists_scaled_profiles I hε χ d hd M hM
  refine ⟨max Λ₀ (stabilityScale ε (errorConstant I hε χ d M hM)),
    hΛ₀.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ a ha harad
  obtain ⟨Φ, u, B, P, hsol, herr⟩ := hexists Λ ((le_max_left _ _).trans hΛ) a ha harad
  have hscale : stabilityScale ε (errorConstant I hε χ d M hM) ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have hK := errorConstant_nonneg I hε χ d M hM
  refine ⟨Φ, u, B, P, hsol, herr, ?_, ?_⟩
  · intro Y hY η hη
    have hχη := hχ η ⟨hη.1.le, hη.2.le⟩
    exact positive_of_uniformMixedError I hε χ d hd hK hscale herr
      hY.1 hY.2 hη hχη.1 hχη.2
  · intro η hη hχ99
    exact log_slope_of_uniformMixedError I hε χ d hd hK hscale herr hη hχ99
      (hχ η ⟨hη.1.le, hη.2.le⟩).2

end NavierStokes.AxisReference

end
