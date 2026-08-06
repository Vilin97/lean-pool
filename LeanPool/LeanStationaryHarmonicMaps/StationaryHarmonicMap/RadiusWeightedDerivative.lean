/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusPrimitive

/-!
# Weighted radius derivative formulas

This module upgrades interval-indicator radius derivative formulas to general
radius weights and identifies the radial derivative density.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- A bounded interval-indicator radius coefficient preserves ball integrability. -/
theorem integrable_indicatorConst_norm_mul_of_integrableOn_ball
    {n : ℕ} {f : Domain n → ℝ} {a b R0 k : ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    Integrable
      (fun x : Domain n =>
        (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖ * f x)
      (volume.restrict (Metric.ball (0 : Domain n) R0)) := by
  have hcoeff_meas :
      AEStronglyMeasurable
        (fun x : Domain n => (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖)
        (volume.restrict (Metric.ball (0 : Domain n) R0)) := by
    have hmeas :
        Measurable
          (fun x : Domain n => (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖) := by
      simpa [Function.comp_def] using
        ((measurable_const.indicator measurableSet_Ioo).comp
          continuous_norm.measurable :
          Measurable
            (((Ioo a b).indicator (fun _ : ℝ => k)) ∘
              fun x : Domain n => ‖x‖))
    exact hmeas.aestronglyMeasurable
  have hcoeff_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖(Ioo a b).indicator (fun _ : ℝ => k) ‖x‖‖ ≤ ‖k‖ := by
    filter_upwards with x
    by_cases hx : ‖x‖ ∈ Ioo a b
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  exact
    (integrableOn_bdd_mul_of_integrableOn
      (n := n) (Ω := Metric.ball (0 : Domain n) R0)
      (c := fun x : Domain n => (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖)
      (g := f) (C := ‖k‖) hf hcoeff_meas hcoeff_bound).integrable

/-- A bounded interval-indicator radius coefficient preserves integrability of
the derivative of the ball-integral radius function on `(0, R0)`. -/
theorem integrable_indicatorConst_mul_deriv_ballIntegral_on_radiusInterval
    {n : ℕ}
    {f : Domain n → ℝ} {a b R0 k : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R0)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    Integrable
      (fun rho : ℝ =>
        (Ioo a b).indicator (fun _ : ℝ => k) rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
      (volume.restrict (Ioo (0 : ℝ) R0)) := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hR0_nonneg : 0 ≤ R0 := ha.trans (hab.trans hb)
  have hderiv_intvl : IntervalIntegrable (deriv F) volume (0 : ℝ) R0 := by
    simpa [F] using
      ((hac (by norm_num) hR0_nonneg le_rfl).intervalIntegrable_deriv)
  have hderiv_on :
      IntegrableOn (deriv F) (Ioo (0 : ℝ) R0) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hderiv_intvl
  have hderiv :
      Integrable (deriv F) (volume.restrict (Ioo (0 : ℝ) R0)) :=
    hderiv_on.integrable
  have hcoeff_meas :
      AEStronglyMeasurable
        (fun rho : ℝ => (Ioo a b).indicator (fun _ : ℝ => k) rho)
        (volume.restrict (Ioo (0 : ℝ) R0)) := by
    exact (measurable_const.indicator measurableSet_Ioo).aestronglyMeasurable
  have hcoeff_bound :
      ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
        ‖(Ioo a b).indicator (fun _ : ℝ => k) rho‖ ≤ ‖k‖ := by
    filter_upwards with rho
    by_cases hrho : rho ∈ Ioo a b
    · simp [Set.indicator_of_mem hrho]
    · simp [Set.indicator_of_notMem hrho]
  simpa [F] using hderiv.bdd_mul hcoeff_meas hcoeff_bound

/-- An arbitrary admissible radius weight preserves integrability of the
derivative of the ball-integral radius function on `(0, R0)`. -/
theorem RadiusWeightOn.integrable_mul_deriv_ballIntegral_on_radiusInterval
    {n : ℕ}
    {f : Domain n → ℝ} {R0 : ℝ} {c : ℝ → ℝ}
    (hc : RadiusWeightOn R0 c)
    (hR0_nonneg : 0 ≤ R0)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    Integrable
      (fun rho : ℝ =>
        c rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
      (radiusIntervalMeasure R0) := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hderiv_intvl : IntervalIntegrable (deriv F) volume (0 : ℝ) R0 := by
    simpa [F] using
      ((hac (by norm_num) hR0_nonneg le_rfl).intervalIntegrable_deriv)
  have hderiv_on :
      IntegrableOn (deriv F) (Ioo (0 : ℝ) R0) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hderiv_intvl
  have hderiv : Integrable (deriv F) (radiusIntervalMeasure R0) := by
    simpa [radiusIntervalMeasure] using hderiv_on.integrable
  rcases hc.exists_ae_bound with ⟨C, _hC_nonneg, hC⟩
  simpa [F] using hderiv.bdd_mul hc.aestronglyMeasurable hC

/-- Finite linear combinations of interval indicators satisfy the radius
derivative formula, once the finite-sum integrability needed for Bochner
linearity is supplied.  The next measure-theoretic step is to discharge those
integrability hypotheses from boundedness of the weights. -/
theorem ballIntegralRadiusDerivativeFormulaForFiniteIndicatorConst_Ioo
    {n : ℕ} [NeZero n]
    {ι : Type*} {s : Finset ι}
    {f : Domain n → ℝ} {R0 : ℝ}
    {a b k : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0)
    (hleft_int : ∀ i ∈ s,
      Integrable
        (fun x : Domain n =>
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖ * f x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hright_int : ∀ i ∈ s,
      Integrable
        (fun rho : ℝ =>
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho *
            deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        (volume.restrict (Ioo (0 : ℝ) R0))) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖) *
          f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) *
        deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hleft_sum :
      (∫ x in Metric.ball (0 : Domain n) R0,
          (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖) *
            f x)
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        ∑ i ∈ s,
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖ * f x := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x _hx
    simpa using
      (Finset.sum_mul s
        (fun i : ι => (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖)
        (f x))
  have hright_sum :
      (∫ rho in Ioo (0 : ℝ) R0,
        (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) *
          deriv F rho)
        =
      ∫ rho in Ioo (0 : ℝ) R0,
        ∑ i ∈ s,
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho * deriv F rho := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro rho _hrho
    simpa using
      (Finset.sum_mul s
        (fun i : ι => (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho)
        (deriv F rho))
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
        (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖) *
          f x)
        =
      ∑ i ∈ s,
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖ * f x := by
      rw [hleft_sum]
      exact integral_finsetSum s hleft_int
    _ =
      ∑ i ∈ s,
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho * deriv F rho := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ballIntegralRadiusDerivativeFormulaForIndicatorConst_Ioo
        (n := n) (f := f) (a := a i) (b := b i) (R0 := R0) (k := k i)
        (ha i hi) (hab i hi) (hb i hi) hf hac
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) *
          deriv F rho) := by
      rw [hright_sum]
      exact (integral_finsetSum s hright_int).symm

/-- Finite linear combinations of interval indicators satisfy the radius
derivative formula.  The integrability side conditions are automatic from
boundedness of the interval-indicator coefficients and absolute continuity of
the ball-integral radius function. -/
theorem ballIntegralRadiusDerivativeFormulaForFiniteIndicatorConst_Ioo_of_radius_ac
    {n : ℕ} [NeZero n]
    {ι : Type*} {s : Finset ι}
    {f : Domain n → ℝ} {R0 : ℝ}
    {a b k : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) ‖x‖) *
          f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      (∑ i ∈ s, (Ioo (a i) (b i)).indicator (fun _ : ℝ => k i) rho) *
        deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  exact ballIntegralRadiusDerivativeFormulaForFiniteIndicatorConst_Ioo
    (n := n) (s := s) (f := f) (R0 := R0) (a := a) (b := b) (k := k)
    ha hab hb hf hac
    (fun i _hi =>
      integrable_indicatorConst_norm_mul_of_integrableOn_ball
        (n := n) (f := f) (a := a i) (b := b i) (R0 := R0) (k := k i) hf)
    (fun i hi =>
      integrable_indicatorConst_mul_deriv_ballIntegral_on_radiusInterval
        (n := n) (f := f) (a := a i) (b := b i) (R0 := R0) (k := k i)
        (ha i hi) (hab i hi) (hb i hi) hac)

/-- A dominated-convergence transfer principle for passing the radius derivative
formula from approximating radius weights to the limiting radius weight.  This
is the measure-theoretic bridge needed after constructing finite interval-step
approximations of a general admissible radius weight. -/
theorem ballIntegralRadiusDerivativeFormula_of_dominated_approx
    {n : ℕ}
    {f : Domain n → ℝ} {R0 : ℝ}
    {c : ℝ → ℝ} {cSeq : ℕ → ℝ → ℝ}
    {boundLeft : Domain n → ℝ} {boundRight : ℝ → ℝ}
    (hleft_meas : ∀ N : ℕ,
      AEStronglyMeasurable
        (fun x : Domain n => cSeq N ‖x‖ * f x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hleft_bound_int :
      Integrable boundLeft (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hleft_bound : ∀ N : ℕ,
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖cSeq N ‖x‖ * f x‖ ≤ boundLeft x)
    (hleft_lim :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        Filter.Tendsto (fun N : ℕ => cSeq N ‖x‖ * f x) Filter.atTop
          (𝓝 (c ‖x‖ * f x)))
    (hright_meas : ∀ N : ℕ,
      AEStronglyMeasurable
        (fun rho : ℝ =>
          cSeq N rho *
            deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        (volume.restrict (Ioo (0 : ℝ) R0)))
    (hright_bound_int :
      Integrable boundRight (volume.restrict (Ioo (0 : ℝ) R0)))
    (hright_bound : ∀ N : ℕ,
      ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
        ‖cSeq N rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho‖
          ≤ boundRight rho)
    (hright_lim :
      ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
        Filter.Tendsto
          (fun N : ℕ =>
            cSeq N rho *
              deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
          Filter.atTop
          (𝓝 (c rho *
            deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)))
    (hformula : ∀ N : ℕ,
      (∫ x in Metric.ball (0 : Domain n) R0, cSeq N ‖x‖ * f x)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        cSeq N rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)) :
    (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      c rho * deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  have hleft_tendsto :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ x in Metric.ball (0 : Domain n) R0, cSeq N ‖x‖ * f x)
        Filter.atTop
        (𝓝 (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)) := by
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (Metric.ball (0 : Domain n) R0))
        (F := fun N x => cSeq N ‖x‖ * f x)
        (f := fun x : Domain n => c ‖x‖ * f x)
        boundLeft hleft_meas hleft_bound_int hleft_bound hleft_lim)
  have hright_tendsto :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ rho in Ioo (0 : ℝ) R0,
            cSeq N rho *
              deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        Filter.atTop
        (𝓝 (∫ rho in Ioo (0 : ℝ) R0,
          c rho * deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho)) := by
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (Ioo (0 : ℝ) R0))
        (F := fun N rho =>
          cSeq N rho *
            deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        (f := fun rho : ℝ =>
          c rho *
            deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        boundRight hright_meas hright_bound_int hright_bound hright_lim)
  have hleft_as_right :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ rho in Ioo (0 : ℝ) R0,
            cSeq N rho *
              deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        Filter.atTop
        (𝓝 (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)) :=
    hleft_tendsto.congr' (Filter.Eventually.of_forall hformula)
  exact tendsto_nhds_unique hleft_as_right hright_tendsto

/-- The radius derivative formula is unchanged under a.e. modification of the
radius weight, provided the pulled-back spatial coefficient is also unchanged
a.e. on the ball. -/
theorem ballIntegralRadiusDerivativeFormula_congr_ae_weight
    {n : ℕ}
    {f : Domain n → ℝ} {R0 : ℝ} {c d : ℝ → ℝ}
    (hleft :
      (fun x : Domain n => c ‖x‖ * f x)
        =ᶠ[ae (volume.restrict (Metric.ball (0 : Domain n) R0))]
      (fun x : Domain n => d ‖x‖ * f x))
    (hright :
      (fun rho : ℝ =>
        c rho * deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
        =ᶠ[ae (volume.restrict (Ioo (0 : ℝ) R0))]
      (fun rho : ℝ =>
        d rho * deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho))
    (hformula :
      (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        c rho * deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho)) :
    (∫ x in Metric.ball (0 : Domain n) R0, d ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      d rho * deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  calc
    (∫ x in Metric.ball (0 : Domain n) R0, d ‖x‖ * f x)
        =
      (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x) := by
        exact (integral_congr_ae hleft).symm
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        c rho * deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := hformula
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        d rho * deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
        exact integral_congr_ae hright

/-- A finite interval-step approximation of a radius weight upgrades the
finite-interval radius derivative formula to that limiting weight. -/
theorem ballIntegralRadiusDerivativeFormula_of_finiteIntervalStepApprox
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {c : ℝ → ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0)
    (happrox : RadiusWeightFiniteIntervalStepApprox R0 c) :
    (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      c rho * deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  classical
  rcases happrox with
    ⟨C, hC_nonneg, s, a, b, k, ha, hab, hb, hbound, hlim⟩
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  let cSeq : ℕ → ℝ → ℝ := fun N rho =>
    ∑ i ∈ s N, (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho
  have hderiv_intvl : IntervalIntegrable (deriv F) volume (0 : ℝ) R0 := by
    simpa [F] using
      ((hac (by norm_num) hR0_nonneg le_rfl).intervalIntegrable_deriv)
  have hderiv_on :
      IntegrableOn (deriv F) (Ioo (0 : ℝ) R0) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hderiv_intvl
  have hderiv :
      Integrable (deriv F) (volume.restrict (Ioo (0 : ℝ) R0)) :=
    hderiv_on.integrable
  refine
    ballIntegralRadiusDerivativeFormula_of_dominated_approx
      (n := n) (f := f) (R0 := R0) (c := c) (cSeq := cSeq)
      (boundLeft := fun x : Domain n => C * ‖f x‖)
      (boundRight := fun rho : ℝ => C * ‖deriv F rho‖)
      ?hleft_meas ?hleft_bound_int ?hleft_bound ?hleft_lim
      ?hright_meas ?hright_bound_int ?hright_bound ?hright_lim ?hformula
  · intro N
    have hsum_int :
        Integrable
          (fun x : Domain n =>
            ∑ i ∈ s N,
              (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖ *
                f x)
          (volume.restrict (Metric.ball (0 : Domain n) R0)) := by
      exact integrable_finsetSum (s N) (fun i hi =>
        integrable_indicatorConst_norm_mul_of_integrableOn_ball
          (n := n) (f := f) (a := a N i) (b := b N i)
          (R0 := R0) (k := k N i) hf)
    have hcongr :
        (fun x : Domain n =>
          ∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖ *
              f x)
          =ᶠ[ae (volume.restrict (Metric.ball (0 : Domain n) R0))]
        (fun x : Domain n => cSeq N ‖x‖ * f x) := by
      filter_upwards with x
      dsimp [cSeq]
      exact (Finset.sum_mul (s N)
        (fun i : ℕ =>
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖)
        (f x)).symm
    exact (hsum_int.congr hcongr).aestronglyMeasurable
  · simpa using hf.integrable.norm.const_mul C
  · intro N
    filter_upwards with x
    calc
      ‖cSeq N ‖x‖ * f x‖
          = ‖cSeq N ‖x‖‖ * ‖f x‖ := norm_mul (cSeq N ‖x‖) (f x)
      _ ≤ C * ‖f x‖ :=
          mul_le_mul (hbound N ‖x‖) le_rfl (norm_nonneg (f x)) hC_nonneg
  · filter_upwards with x
    simpa [cSeq] using (hlim ‖x‖).mul_const (f x)
  · intro N
    have hsum_int :
        Integrable
          (fun rho : ℝ =>
            ∑ i ∈ s N,
              (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho *
                deriv F rho)
          (volume.restrict (Ioo (0 : ℝ) R0)) := by
      exact integrable_finsetSum (s N) (fun i hi =>
        integrable_indicatorConst_mul_deriv_ballIntegral_on_radiusInterval
          (n := n) (f := f) (a := a N i) (b := b N i)
          (R0 := R0) (k := k N i)
          (ha N i hi) (hab N i hi) (hb N i hi) hac)
    have hcongr :
        (fun rho : ℝ =>
          ∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho *
              deriv F rho)
          =ᶠ[ae (volume.restrict (Ioo (0 : ℝ) R0))]
        (fun rho : ℝ => cSeq N rho * deriv F rho) := by
      filter_upwards with rho
      dsimp [cSeq]
      exact (Finset.sum_mul (s N)
        (fun i : ℕ =>
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho)
        (deriv F rho)).symm
    exact (hsum_int.congr hcongr).aestronglyMeasurable
  · simpa using hderiv.norm.const_mul C
  · intro N
    filter_upwards with rho
    calc
      ‖cSeq N rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho‖
          = ‖cSeq N rho‖ * ‖deriv F rho‖ := by
            simp [F, norm_mul]
      _ ≤ C * ‖deriv F rho‖ :=
          mul_le_mul (hbound N rho) le_rfl (norm_nonneg (deriv F rho)) hC_nonneg
  · filter_upwards with rho
    simpa [cSeq, F] using (hlim rho).mul_const (deriv F rho)
  · intro N
    simpa [cSeq, F] using
      ballIntegralRadiusDerivativeFormulaForFiniteIndicatorConst_Ioo_of_radius_ac
        (n := n) (s := s N) (f := f) (R0 := R0)
        (a := a N) (b := b N) (k := k N)
        (fun i hi => ha N i hi)
        (fun i hi => hab N i hi)
        (fun i hi => hb N i hi)
        hf hac

/-- A finite interval-step approximation away from a countable exceptional set
also upgrades the finite-interval radius derivative formula to the limiting
weight. -/
theorem ballIntegralRadiusDerivativeFormula_of_finiteIntervalStepApproxAE
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {c : ℝ → ℝ}
    (hR0_pos : 0 < R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0)
    (happrox : RadiusWeightFiniteIntervalStepApproxAE R0 c) :
    (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      c rho * deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  classical
  rcases happrox with
    ⟨C, hC_nonneg, bad, hbad_count, s, a, b, k, ha, hab, hb, hbound, hlim⟩
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  let cSeq : ℕ → ℝ → ℝ := fun N rho =>
    ∑ i ∈ s N, (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho
  have hR0_nonneg : 0 ≤ R0 := hR0_pos.le
  have hderiv_intvl : IntervalIntegrable (deriv F) volume (0 : ℝ) R0 := by
    simpa [F] using
      ((hac (by norm_num) hR0_nonneg le_rfl).intervalIntegrable_deriv)
  have hderiv_on :
      IntegrableOn (deriv F) (Ioo (0 : ℝ) R0) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hderiv_intvl
  have hderiv :
      Integrable (deriv F) (volume.restrict (Ioo (0 : ℝ) R0)) :=
    hderiv_on.integrable
  refine
    ballIntegralRadiusDerivativeFormula_of_dominated_approx
      (n := n) (f := f) (R0 := R0) (c := c) (cSeq := cSeq)
      (boundLeft := fun x : Domain n => C * ‖f x‖)
      (boundRight := fun rho : ℝ => C * ‖deriv F rho‖)
      ?hleft_meas ?hleft_bound_int ?hleft_bound ?hleft_lim
      ?hright_meas ?hright_bound_int ?hright_bound ?hright_lim ?hformula
  · intro N
    have hsum_int :
        Integrable
          (fun x : Domain n =>
            ∑ i ∈ s N,
              (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖ *
                f x)
          (volume.restrict (Metric.ball (0 : Domain n) R0)) := by
      exact integrable_finsetSum (s N) (fun i hi =>
        integrable_indicatorConst_norm_mul_of_integrableOn_ball
          (n := n) (f := f) (a := a N i) (b := b N i)
          (R0 := R0) (k := k N i) hf)
    have hcongr :
        (fun x : Domain n =>
          ∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖ *
              f x)
          =ᶠ[ae (volume.restrict (Metric.ball (0 : Domain n) R0))]
        (fun x : Domain n => cSeq N ‖x‖ * f x) := by
      filter_upwards with x
      dsimp [cSeq]
      exact (Finset.sum_mul (s N)
        (fun i : ℕ =>
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) ‖x‖)
        (f x)).symm
    exact (hsum_int.congr hcongr).aestronglyMeasurable
  · simpa using hf.integrable.norm.const_mul C
  · intro N
    filter_upwards with x
    calc
      ‖cSeq N ‖x‖ * f x‖
          = ‖cSeq N ‖x‖‖ * ‖f x‖ := norm_mul (cSeq N ‖x‖) (f x)
      _ ≤ C * ‖f x‖ :=
          mul_le_mul (hbound N ‖x‖) le_rfl (norm_nonneg (f x)) hC_nonneg
  · filter_upwards
      [ae_norm_mem_Ioo_zero_radius_on_ball (n := n) hR0_pos,
        ae_norm_not_mem_countable_on_ball (n := n) (R0 := R0) hbad_count]
      with x hxI hxbad
    simpa [cSeq] using (hlim ‖x‖ hxI hxbad).mul_const (f x)
  · intro N
    have hsum_int :
        Integrable
          (fun rho : ℝ =>
            ∑ i ∈ s N,
              (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho *
                deriv F rho)
          (volume.restrict (Ioo (0 : ℝ) R0)) := by
      exact integrable_finsetSum (s N) (fun i hi =>
        integrable_indicatorConst_mul_deriv_ballIntegral_on_radiusInterval
          (n := n) (f := f) (a := a N i) (b := b N i)
          (R0 := R0) (k := k N i)
          (ha N i hi) (hab N i hi) (hb N i hi) hac)
    have hcongr :
        (fun rho : ℝ =>
          ∑ i ∈ s N,
            (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho *
              deriv F rho)
          =ᶠ[ae (volume.restrict (Ioo (0 : ℝ) R0))]
        (fun rho : ℝ => cSeq N rho * deriv F rho) := by
      filter_upwards with rho
      dsimp [cSeq]
      exact (Finset.sum_mul (s N)
        (fun i : ℕ =>
          (Ioo (a N i) (b N i)).indicator (fun _ : ℝ => k N i) rho)
        (deriv F rho)).symm
    exact (hsum_int.congr hcongr).aestronglyMeasurable
  · simpa using hderiv.norm.const_mul C
  · intro N
    filter_upwards with rho
    calc
      ‖cSeq N rho *
          deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho‖
          = ‖cSeq N rho‖ * ‖deriv F rho‖ := by
            simp [F, norm_mul]
      _ ≤ C * ‖deriv F rho‖ :=
          mul_le_mul (hbound N rho) le_rfl (norm_nonneg (deriv F rho)) hC_nonneg
  · have hbad_ae :
        ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0), rho ∉ bad := by
      have hnull : (volume : Measure ℝ) bad = 0 :=
        hbad_count.measure_zero volume
      have hae : ∀ᵐ rho ∂(volume : Measure ℝ), rho ∉ bad := by
        simpa [ae_iff] using hnull
      exact ae_mono (Measure.restrict_le_self (s := Ioo (0 : ℝ) R0)) hae
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hbad_ae] with rho hrho hnotbad
    simpa [cSeq, F] using (hlim rho hrho hnotbad).mul_const (deriv F rho)
  · intro N
    simpa [cSeq, F] using
      ballIntegralRadiusDerivativeFormulaForFiniteIndicatorConst_Ioo_of_radius_ac
        (n := n) (s := s N) (f := f) (R0 := R0)
        (a := a N) (b := b N) (k := k N)
        (fun i hi => ha N i hi)
        (fun i hi => hab N i hi)
        (fun i hi => hb N i hi)
        hf hac

/-- Local one-dimensional derivative identification for the radial density
obtained from all restricted radius-weighted integral identities.  On every
compact subinterval of `(0, R0)`, the representing density agrees a.e. with the
derivative of the ball integral radius function. -/
theorem ballIntegralRadiusDerivativeIdentificationForWeights_on_Ioo
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {R0 : ℝ} {D : ℝ → ℝ} {a b : ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hD_loc : LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume)
    (hweighted : ∀ c : ℝ → ℝ,
      RadiusWeightOn R0 c →
        (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
          =
        (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho))
    (ha : 0 < a) (hab : a ≤ b) (hb : b < R0) :
    ∀ᵐ rho ∂volume.restrict (Ioo a b),
      deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have ha_nonneg : 0 ≤ a := ha.le
  have hb_le_R0 : b ≤ R0 := hb.le
  have hIcc_subset : Icc a b ⊆ Ioo (0 : ℝ) R0 := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩
  have hD_intOn : IntegrableOn D (Icc a b) volume :=
    hD_loc.integrableOn_compact_subset hIcc_subset isCompact_Icc
  have hD_int : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hD_intOn
  have hinc : ∀ {r : ℝ}, r ∈ Icc a b → F r - F a = ∫ rho in a..r, D rho := by
    intro r hr
    have har : a ≤ r := hr.1
    have hrR0 : r ≤ R0 := hr.2.trans hb_le_R0
    have hf_r : IntegrableOn f (Metric.ball (0 : Domain n) r) volume :=
      hf.mono_set (Metric.ball_subset_ball hrR0)
    have hann :
        (∫ x in Metric.ball (0 : Domain n) R0,
            (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
          =
        F r - F a := by
      simpa [F] using
        ball_annulus_indicator_integral_eq_energy_diff
          (n := n) (f := f) (a := a) (b := r) (R0 := R0)
          har hrR0 hf_r
    have hweight :
        (∫ x in Metric.ball (0 : Domain n) R0,
            (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
          =
        (∫ rho in Ioo (0 : ℝ) R0,
            (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) rho * D rho) :=
      hweighted
        ((Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)))
        (radiusWeightOn_indicator_one (R0 := R0) (a := a) (b := r))
    have hinterval :
        (∫ rho in Ioo (0 : ℝ) R0,
            (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) rho * D rho)
          =
        ∫ rho in a..r, D rho :=
      integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
        (f := D) ha_nonneg har hrR0
    calc
      F r - F a
          =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x := hann.symm
      _ =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo a r).indicator (fun _ : ℝ => (1 : ℝ)) rho * D rho := hweight
      _ = ∫ rho in a..r, D rho := hinterval
  let G : ℝ → ℝ := fun r : ℝ => F a + ∫ rho in a..r, D rho
  have hFG : EqOn F G (Icc a b) := by
    intro r hr
    have hr_eq := hinc hr
    dsimp [G]
    linarith
  have hD_ae := hD_int.ae_hasDerivAt_integral
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hD_ae]
    with rho hrho hderiv
  have hrho_uIcc : rho ∈ uIcc a b := by
    simpa [uIcc_of_le hab] using (mem_Icc_of_Ioo hrho)
  have ha_uIcc : a ∈ uIcc a b := by
    simpa [uIcc_of_le hab]
  have hIntDeriv :
      HasDerivAt (fun r : ℝ => ∫ rho in a..r, D rho) (D rho) rho :=
    hderiv hrho_uIcc a ha_uIcc
  have hG_deriv : HasDerivAt G (D rho) rho := by
    simpa [G] using hIntDeriv.const_add (F a)
  have hFG_eventually : F =ᶠ[𝓝 rho] G :=
    Filter.mem_of_superset (Icc_mem_nhds hrho.1 hrho.2) hFG
  calc
    deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho
        = deriv F rho := rfl
    _ = deriv G rho := hFG_eventually.deriv_eq
    _ = D rho := hG_deriv.deriv

/-- The restricted-weight radial representation determines the a.e. derivative
of the ball integral radius function on the whole radius interval. -/
theorem ballIntegralRadiusDerivativeIdentificationForWeights (n : ℕ) :
    BallIntegralRadiusDerivativeIdentificationForWeights n := by
  intro hne f R0 D hf hD_loc hweighted
  let : NeZero n := hne
  dsimp [radiusIntervalMeasure]
  refine ae_restrict_of_ae_restrict_inter_Ioo
    (μ := volume) (s := Ioo (0 : ℝ) R0) ?_
  intro a b ha hb hab
  have hlocal :
      ∀ᵐ rho ∂volume.restrict (Ioo a b),
        deriv (fun r : ℝ =>
          ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho :=
    ballIntegralRadiusDerivativeIdentificationForWeights_on_Ioo
      (n := n) (f := f) (R0 := R0) (D := D)
      (a := a) (b := b) hf hD_loc hweighted ha.1 hab.le hb.2
  have hset : Ioo (0 : ℝ) R0 ∩ Ioo a b = Ioo a b := by
    ext rho
    constructor
    · intro hrho
      exact hrho.2
    · intro hrho
      exact ⟨⟨lt_trans ha.1 hrho.1, lt_trans hrho.2 hb.2⟩, hrho⟩
  simpa [hset] using hlocal

/-- Unrestricted radius-weighted identities imply the same derivative
identification, by forgetting the restriction on test weights. -/
theorem ballIntegralRadiusDerivativeIdentification (n : ℕ) :
    BallIntegralRadiusDerivativeIdentification n := by
  intro hne f R0 D hf hD_loc hweighted
  let : NeZero n := hne
  exact
    ballIntegralRadiusDerivativeIdentificationForWeights
      (n := n) (f := f) (R0 := R0) (D := D)
      hf hD_loc (fun c _hc => hweighted c)

/-- After the derivative-identification theorem is proved, a restricted
weighted radial representation alone gives the combined radial-density
representation. -/
theorem ballIntegralRadiusDerivativeRepresentationForWeights_of_weightedRepresentation_identified
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n) :
    BallIntegralRadiusDerivativeRepresentationForWeights n :=
  ballIntegralRadiusDerivativeRepresentationForWeights_of_weightedRepresentation
    (n := n) hweighted (ballIntegralRadiusDerivativeIdentificationForWeights n)

/-- After the derivative-identification theorem is proved, a restricted
weighted radial representation alone gives the packaged radius-derivative
formula. -/
theorem ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation_identified
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n) :
    BallIntegralRadiusDerivativeFormulaForWeights n :=
  ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation
    (n := n) hweighted (ballIntegralRadiusDerivativeIdentificationForWeights n)

/-- After the unrestricted derivative-identification theorem is proved, an
unrestricted weighted radial representation alone gives the combined
radial-density representation. -/
theorem ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation_identified
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentation n) :
    BallIntegralRadiusDerivativeRepresentation n :=
  ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation
    (n := n) hweighted (ballIntegralRadiusDerivativeIdentification n)

/-- After the unrestricted derivative-identification theorem is proved, an
unrestricted weighted radial representation alone gives the packaged
radius-derivative formula. -/
theorem ballIntegralRadiusDerivativeFormula_of_weightedRepresentation_identified
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentation n) :
    BallIntegralRadiusDerivativeFormula n :=
  ballIntegralRadiusDerivativeFormula_of_representation
    (n := n)
    (ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation_identified
      (n := n) hweighted)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
