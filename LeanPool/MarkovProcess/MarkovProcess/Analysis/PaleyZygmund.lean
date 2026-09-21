/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The Paley--Zygmund inequality

For a nonnegative extended-real random variable `Z` with finite mean on a probability space and a
level `rho`, the mass above `rho * E Z` is bounded below by the second-moment ratio,

  `(1 - rho) ^ 2 * (E Z) ^ 2 ≤ E (Z ^ 2) * mu {rho * E Z ≤ Z}`.

The subtraction is the truncated one of `ℝ≥0∞`, so a level `rho ≥ 1` leaves the trivial bound and
needs no separate hypothesis.  The primary form
(`MeasureTheory.lintegral_sq_mul_measure_ge_le`) is division-free, so it needs neither positivity
nor finiteness of the second moment; the divided form
(`MeasureTheory.le_measure_ge_of_lintegral_sq_ne_top`) is the familiar
`(1 - rho) ^ 2 (E Z) ^ 2 / E (Z ^ 2) ≤ mu {rho * E Z ≤ Z}`, whose finite-mean hypothesis is
supplied by the second moment through the Cauchy--Schwarz inequality
(`MeasureTheory.lintegral_le_rpow_lintegral_sq`).

Everything is stated for `ℝ≥0∞`-valued functions and carries no integrability side condition.
-/

open scoped ENNReal NNReal

-- The namespace placement is upstream-facing: this is pure measure theory, with no process
-- structure and no state space.
namespace MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Cauchy--Schwarz on a measurable set: the integral of a nonnegative extended-real function over
`A` is at most the square root of its second moment times the square root of the mass of `A`. -/
theorem setLIntegral_le_rpow_lintegral_sq_mul_rpow (mu : Measure Omega) {Z : Omega → ℝ≥0∞}
    (hZ : AEMeasurable Z mu) {A : Set Omega} (hA : MeasurableSet A) :
    ∫⁻ omega in A, Z omega ∂mu ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ) := by
  have hindicator : AEMeasurable (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) mu :=
    (measurable_const.indicator hA).aemeasurable
  have hsplit : ∫⁻ omega in A, Z omega ∂mu =
      ∫⁻ omega, (Z * A.indicator (fun _ ↦ (1 : ℝ≥0∞))) omega ∂mu := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun omega ↦ ?_
    by_cases homega : omega ∈ A
    · simp only [Pi.mul_apply, Set.indicator_of_mem homega, mul_one]
    · simp only [Pi.mul_apply, Set.indicator_of_notMem homega, mul_zero]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu Real.HolderConjugate.two_two hZ hindicator
  have hsquare : ∀ omega : Omega, Z omega ^ (2 : ℝ) = Z omega ^ (2 : ℕ) := by
    intro omega
    rw [← ENNReal.rpow_natCast (Z omega) 2]
    norm_num
  have hind : ∀ omega : Omega,
      A.indicator (fun _ ↦ (1 : ℝ≥0∞)) omega ^ (2 : ℝ) =
        A.indicator (fun _ ↦ (1 : ℝ≥0∞)) omega := by
    intro omega
    by_cases homega : omega ∈ A
    · simp only [Set.indicator_of_mem homega, ENNReal.one_rpow]
    · simp only [Set.indicator_of_notMem homega]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [hsplit]
  refine hholder.trans (le_of_eq ?_)
  rw [lintegral_congr hsquare, lintegral_congr hind, lintegral_indicator_const hA (1 : ℝ≥0∞),
    one_mul]

/-- A finite second moment on a probability space forces a finite mean. -/
theorem lintegral_le_rpow_lintegral_sq (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : AEMeasurable Z mu) :
    ∫⁻ omega, Z omega ∂mu ≤ (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) := by
  have h := setLIntegral_le_rpow_lintegral_sq_mul_rpow mu hZ MeasurableSet.univ
  rwa [Measure.restrict_univ, measure_univ, ENNReal.one_rpow, mul_one] at h

/-- **The Paley--Zygmund inequality**, in division-free form: on a probability space the mass of
the event `{rho * E Z ≤ Z}` obeys
`(1 - rho) ^ 2 * (E Z) ^ 2 ≤ E (Z ^ 2) * mu {rho * E Z ≤ Z}`.  The subtraction is the truncated one
of `ℝ≥0∞`, so a level `rho ≥ 1` gives the trivial bound `0 ≤ …`. -/
theorem lintegral_sq_mul_measure_ge_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hfin : ∫⁻ omega, Z omega ∂mu ≠ ⊤) (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) *
        mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by
  set m : ℝ≥0∞ := ∫⁻ omega, Z omega ∂mu
  set a : ℝ≥0∞ := (rho : ℝ≥0∞) * m with ha
  set A : Set Omega := {omega | a ≤ Z omega}
  have hA : MeasurableSet A := measurableSet_le measurable_const hZ
  have hcompl : ∫⁻ omega in Aᶜ, Z omega ∂mu ≤ a := by
    calc
      ∫⁻ omega in Aᶜ, Z omega ∂mu ≤ ∫⁻ _omega in Aᶜ, a ∂mu := by
        refine setLIntegral_mono' hA.compl fun omega homega ↦ ?_
        exact le_of_lt (not_le.mp homega)
      _ = a * mu Aᶜ := setLIntegral_const _ _
      _ ≤ a * 1 := mul_le_mul_right prob_le_one a
      _ = a := mul_one a
  have hsum : m = ∫⁻ omega in A, Z omega ∂mu + ∫⁻ omega in Aᶜ, Z omega ∂mu :=
    (lintegral_add_compl _ hA).symm
  have hsub : m - a ≤ ∫⁻ omega in A, Z omega ∂mu := by
    refine tsub_le_iff_right.mpr ?_
    calc
      m = ∫⁻ omega in A, Z omega ∂mu + ∫⁻ omega in Aᶜ, Z omega ∂mu := hsum
      _ ≤ ∫⁻ omega in A, Z omega ∂mu + a := add_le_add le_rfl hcompl
  have hlin : ((1 : ℝ≥0∞) - rho) * m = m - a := by
    rw [ENNReal.sub_mul fun _ _ ↦ hfin, one_mul, ha]
  have hCS := setLIntegral_le_rpow_lintegral_sq_mul_rpow mu hZ.aemeasurable hA
  have hkey : ((1 : ℝ≥0∞) - rho) * m ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ) := by
    rw [hlin]
    exact hsub.trans hCS
  calc
    ((1 : ℝ≥0∞) - rho) ^ 2 * m ^ 2 = (((1 : ℝ≥0∞) - rho) * m) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ ((∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left' hkey 2
    _ = (∫⁻ omega, Z omega ^ 2 ∂mu) * mu A := by
      rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ)) 2,
        ← ENNReal.rpow_natCast ((mu A) ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

/-- **The Paley--Zygmund inequality**, in divided form.  The finite-mean hypothesis of the
division-free version is supplied by the finite second moment. -/
theorem le_measure_ge_of_lintegral_sq_ne_top (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hsq : ∫⁻ omega, Z omega ^ 2 ∂mu ≠ ⊤)
    (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 / (∫⁻ omega, Z omega ^ 2 ∂mu) ≤
      mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by
  have hfin : ∫⁻ omega, Z omega ∂mu ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_le_rpow_lintegral_sq mu hZ.aemeasurable)
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hsq
  exact ENNReal.div_le_of_le_mul
    ((lintegral_sq_mul_measure_ge_le mu hZ hfin rho).trans_eq (mul_comm _ _))

end MeasureTheory
