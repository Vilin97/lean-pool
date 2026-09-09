/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricTorusInverse
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFamilyTorusInverse
public import LeanPool.NavierStokesAndEuler.NavierStokes.PressureStream
public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
public import LeanPool.NavierStokesAndEuler.NavierStokes.TorusAverages
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformFourierAlias

@[expose] public section

/-!
# The exact temporal mean update

The native-to-absolute inverse identity is derived from the actual covering
map, Fourier coefficients, and uniqueness for the zero-mean periodic
directional equation. Band factors remain explicit.
-/

noncomputable section

namespace NavierStokes.TemporalMeanUpdate

open Set Filter MeasureTheory Function
open TorusInverse
open scoped Topology ContDiff BigOperators Interval

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))

noncomputable def partialY (f : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ f z (0, 1)
noncomputable def timeDerivative (f : Plane → ℂ) (z : Plane) : ℂ :=
  fderiv ℝ f z (vector .temporal)

theorem partialY_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialY f) :=
  (ContinuousLinearMap.apply ℝ ℂ (0, 1)).contDiff.comp (hf.fderiv_right (by simp))

theorem coefficient_const_mul (c : ℂ) (f : Plane → ℂ) (k : Frequency) :
    SmoothFourierData.coefficient (fun z => c * f z) k = c * SmoothFourierData.coefficient f k := by
  simp only [SmoothFourierData.coefficient, SmoothFourierData.unitCoeff_const_mul]

theorem coefficient_add {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : Frequency) :
    SmoothFourierData.coefficient (fun z => f z + g z) k =
      SmoothFourierData.coefficient f k + SmoothFourierData.coefficient g k := by
  let K := SmoothFourierData.kernel k
  have hK : ContDiff ℝ ∞ K := ParametricTorusInverse.kernel_smooth k
  have hif : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, K (x, y) * f (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      ((hK.mul hf).comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hig : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, K (x, y) * g (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      ((hK.mul hg).comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hi (y : ℝ) : (∫ x in (0 : ℝ)..1, K (x, y) * (f (x, y) + g (x, y))) =
      (∫ x in (0 : ℝ)..1, K (x, y) * f (x, y)) + (∫ x in (0 : ℝ)..1, K (x, y) * g (x, y)) := by
    simp_rw [mul_add]
    exact intervalIntegral.integral_add
      (((hK.mul hf).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
      (((hK.mul hg).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
  simp only [SmoothFourierData.coefficient_eq_doubleIntegral]
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, K (x, y) * (f (x, y) + g (x, y))) = _
  simp_rw [hi]
  exact intervalIntegral.integral_add (hif.continuous.intervalIntegrable 0 1)
    (hig.continuous.intervalIntegrable 0 1)

/-- Fourier differentiation, including the zero first frequency. -/
theorem coefficient_partialX {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (SmoothFourierData.partialX f) k =
      (omega * (k.1 : ℂ)) * SmoothFourierData.coefficient f k := by
  by_cases hk : k.1 = 0
  · have hi (y : ℝ) : SmoothFourierData.unitCoeff
        (fun x => SmoothFourierData.partialX f (x, y)) 0 = 0 := by
      rw [SmoothFourierData.unitCoeff_eq_integral]
      simp only [neg_zero, fourier_zero, one_mul]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => SmoothFourierData.hasDerivAt_slice ((hf.differentiable (by simp)) (x, y)))
        (((SmoothFourierData.partialX_smooth hf).continuous.comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)]
      have he : f (1, y) = f (0, y) := by simpa using hp (0, y) (1, 0)
      rw [he, sub_self]
    simp only [SmoothFourierData.coefficient, hk, hi, Int.cast_zero, mul_zero, zero_mul]
    simp [SmoothFourierData.unitCoeff_eq_integral]
  · have hden : omega * (k.1 : ℂ) ≠ 0 := mul_ne_zero omega_ne_zero (by exact_mod_cast hk)
    rw [SmoothFourierData.coefficient_partialX hf hp hk, ← mul_assoc, mul_inv_cancel₀ hden, one_mul]

theorem swap_partialY {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    SmoothFourierData.swapFunction (partialY f) =
      SmoothFourierData.partialX (SmoothFourierData.swapFunction f) := by
  funext z
  let L : Plane →L[ℝ] Plane := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have h := ((hf.differentiable (by simp)) (z.2, z.1)).hasFDerivAt.comp z L.hasFDerivAt
  change fderiv ℝ f (z.2, z.1) (0, 1) = fderiv ℝ (f ∘ L) z (1, 0)
  rw [h.fderiv]
  rfl

theorem coefficient_partialY {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (partialY f) k =
      (omega * (k.2 : ℂ)) * SmoothFourierData.coefficient f k := by
  rw [SmoothFourierData.coefficient_swap (partialY_smooth hf).continuous k, swap_partialY hf,
    coefficient_partialX (SmoothFourierData.swapFunction_smooth hf)
      (SmoothFourierData.swapFunction_periodic hp)]
  rw [← SmoothFourierData.coefficient_swap hf.continuous k]

theorem timeDerivative_eq_partials (f : Plane → ℂ) (z : Plane) :
    timeDerivative f z = ((vector .temporal).1 : ℂ) * SmoothFourierData.partialX f z +
      ((vector .temporal).2 : ℂ) * partialY f z := by
  have hv : vector .temporal = (vector .temporal).1 • ((1, 0) : Plane) +
      (vector .temporal).2 • ((0, 1) : Plane) := by ext <;> simp
  conv_lhs => rw [timeDerivative, hv, map_add, map_smul, map_smul]
  simp only [Complex.real_smul, SmoothFourierData.partialX, partialY]

/-- The temporal Fourier symbol is the actual multiplier of the derivative. -/
theorem coefficient_timeDerivative {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (timeDerivative f) k =
      (omega * (symbol .temporal k : ℂ)) * SmoothFourierData.coefficient f k := by
  have heq : timeDerivative f = fun z => ((vector .temporal).1 : ℂ) * SmoothFourierData.partialX f
    z +
      ((vector .temporal).2 : ℂ) * partialY f z := funext (timeDerivative_eq_partials f)
  rw [heq, coefficient_add (contDiff_const.mul (SmoothFourierData.partialX_smooth hf))
    (contDiff_const.mul (partialY_smooth hf)), coefficient_const_mul, coefficient_const_mul,
    coefficient_partialX hf hp, coefficient_partialY hf hp]
  have hs : (symbol .temporal k : ℂ) =
      (k.1 : ℂ) * ((vector .temporal).1 : ℂ) + (k.2 : ℂ) * ((vector .temporal).2 : ℂ) := by
    exact_mod_cast symbol_formula .temporal k
  rw [hs]
  ring

/-- Uniqueness for the smooth periodic temporal equation with a prescribed
mean. The proof uses actual Fourier differentiation and reconstruction. -/
theorem timeDerivative_unique {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : SmoothFourierData.UnitPeriodic f) (hpg : SmoothFourierData.UnitPeriodic g)
    (hD : timeDerivative f = timeDerivative g)
    (hm : TorusAverages.squareAverage f = TorusAverages.squareAverage g) : f = g := by
  have hc : SmoothFourierData.coefficient f = SmoothFourierData.coefficient g := by
    funext k
    by_cases hk : k = 0
    · subst k
      simpa only [SmoothFourierData.coefficient_zero_eq_integral, TorusAverages.squareAverage]
        using hm
    · have he := congrArg (fun q => SmoothFourierData.coefficient q k) hD
      rw [coefficient_timeDerivative hf hpf, coefficient_timeDerivative hg hpg] at he
      exact mul_left_cancel₀ (mul_ne_zero omega_ne_zero
        (Complex.ofReal_ne_zero.mpr (symbol_ne_zero .temporal hk))) he
  funext z
  rw [← SmoothFourierData.series_coefficient hf hpf z,
    ← SmoothFourierData.series_coefficient hg hpg z, hc]

/-- The actual integer covering as a continuous linear map. -/
noncomputable def coverLinear : Plane →L[ℝ] Plane :=
  ((3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + (5 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem coverLinear_apply (z : Plane) : coverLinear z = TorusAverages.covering z := by
  simp [coverLinear, TorusAverages.covering]

noncomputable def coverMap : ℕ → Plane →L[ℝ] Plane
  | 0 => ContinuousLinearMap.id ℝ Plane
  | n + 1 => coverLinear.comp (coverMap n)

theorem coverMap_eq_iterate (n : ℕ) (z : Plane) :
    coverMap n z = TorusAverages.covering^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change coverLinear (coverMap n z) = _
      rw [coverLinear_apply, ih, Function.iterate_succ_apply']

theorem coverLinear_temporal :
    coverLinear (vector .temporal) = ChartScales.Tg • vector .temporal := by
  rw [coverLinear_apply]
  ext <;> dsimp [TorusAverages.covering, vector, ChartScales.Tg, SlotColoring.coverGrowth]
  · nlinarith [DiophantineGraph.sqrt_two_square]
  · ring

theorem coverMap_temporal (n : ℕ) :
    coverMap n (vector .temporal) = ChartScales.Tg ^ n • vector .temporal := by
  induction n with
  | zero => simp [coverMap]
  | succ n ih =>
      change coverLinear (coverMap n (vector .temporal)) = _
      rw [ih, map_smul, coverLinear_temporal, smul_smul, pow_succ]

theorem coverLinear_lattice (k : Frequency) :
    coverLinear ((k.1 : ℝ), (k.2 : ℝ)) =
      (((DiophantineGraph.coveringFrequency k).1 : ℝ),
        ((DiophantineGraph.coveringFrequency k).2 : ℝ)) := by
  rw [coverLinear_apply]
  simp [TorusAverages.covering, DiophantineGraph.coveringFrequency]

theorem coverMap_lattice (n : ℕ) (k : Frequency) :
    coverMap n ((k.1 : ℝ), (k.2 : ℝ)) =
      (((DiophantineGraph.coveringFrequency^[n] k).1 : ℝ),
        ((DiophantineGraph.coveringFrequency^[n] k).2 : ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change coverLinear (coverMap n ((k.1 : ℝ), (k.2 : ℝ))) = _
      rw [ih, coverLinear_lattice, Function.iterate_succ_apply']

theorem periodic_coverMap {f : Plane → ℂ} (hp : SmoothFourierData.UnitPeriodic f) (n : ℕ) :
    SmoothFourierData.UnitPeriodic (fun z => f (coverMap n z)) := by
  intro z k
  change f (coverMap n (z + ((k.1 : ℝ), (k.2 : ℝ)))) = f (coverMap n z)
  rw [map_add, coverMap_lattice]
  exact hp _ _

theorem timeDerivative_coverMap {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : Plane) :
    timeDerivative (fun x => f (coverMap n x)) z =
      ChartScales.Tg ^ n • timeDerivative f (coverMap n z) := by
  have hd := ((hf.differentiable (by simp)) (coverMap n z)).hasFDerivAt.comp z
    (coverMap n).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [timeDerivative, hd.fderiv]
  change fderiv ℝ f (coverMap n z) (coverMap n (vector .temporal)) = _
  rw [coverMap_temporal, map_smul]
  rfl

noncomputable def absoluteInverse (f : Plane → ℂ) : Plane → ℂ :=
  directionalInverse .temporal (SmoothFourierData.coefficient f)

theorem absoluteInverse_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) : ContDiff ℝ ∞ (absoluteInverse f) :=
  contDiff_directionalInverse .temporal (SmoothFourierData.rapid_coefficient hf hp)

theorem absoluteInverse_periodic (f : Plane → ℂ) :
    SmoothFourierData.UnitPeriodic (absoluteInverse f) := by
  intro z k
  exact directionalInverse_periodic .temporal (SmoothFourierData.coefficient f) z k.1 k.2

theorem absoluteInverse_zeroMean {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) : TorusAverages.squareAverage (absoluteInverse f) = 0
      := by
  have ha := SmoothFourierData.rapid_coefficient hf hp
  let g : C(Torus, ℂ) := ⟨torusSeries (inverseCoeff .temporal (SmoothFourierData.coefficient f)),
    continuous_torusSeries (ha.inverseCoeff .temporal)⟩
  have hg : SmoothFourierData.torusLift g = absoluteInverse f := by
    funext Y
    exact (series_eq_torusSeries (inverseCoeff .temporal (SmoothFourierData.coefficient f)) Y).symm
  rw [← hg, TorusAverages.squareAverage_torusLift]
  exact inverse_zero_mean .temporal ha

theorem absoluteInverse_solves {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (hm : TorusAverages.squareAverage f = 0) :
    timeDerivative (absoluteInverse f) = f := by
  funext z
  exact SmoothFourierData.inverse_solves_smooth_periodic .temporal hf hp hm z

/-- The native factor is forced by the covering derivative and zero-mean
uniqueness. Both sides are the actual Fourier-defined inverse. -/
theorem absoluteInverse_coverMap {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (hm : TorusAverages.squareAverage f = 0) (n : ℕ) :
    absoluteInverse (fun z => f (coverMap n z)) =
      fun z => (ChartScales.Tg ^ n)⁻¹ • absoluteInverse f (coverMap n z) := by
  have hfc : ContDiff ℝ ∞ (fun z => f (coverMap n z)) := hf.comp (coverMap n).contDiff
  have hpc := periodic_coverMap hp n
  have hmc : TorusAverages.squareAverage (fun z => f (coverMap n z)) = 0 := by
    simp_rw [coverMap_eq_iterate]
    exact (TorusAverages.squareAverage_covering_iterate hf.continuous hp n).trans hm
  have hi := absoluteInverse_smooth hf hp
  have hip := absoluteInverse_periodic f
  have hright : ContDiff ℝ ∞ (fun z => (ChartScales.Tg ^ n)⁻¹ • absoluteInverse f (coverMap n z)) :=
    (hi.comp (coverMap n).contDiff).const_smul _
  apply timeDerivative_unique (absoluteInverse_smooth hfc hpc) hright
    (absoluteInverse_periodic _) (fun z k => congrArg ((ChartScales.Tg ^ n)⁻¹ • ·)
      (periodic_coverMap hip n z k))
  · rw [absoluteInverse_solves hfc hpc hmc]
    funext z
    have hs := (((hi.comp (coverMap n).contDiff).differentiable (by simp))
      z).hasFDerivAt.fun_const_smul
      ((ChartScales.Tg ^ n)⁻¹)
    simp only [Function.comp_def] at hs
    symm
    rw [timeDerivative, hs.fderiv]
    change (ChartScales.Tg ^ n)⁻¹ • timeDerivative (fun x => absoluteInverse f (coverMap n x)) z = _
    rw [timeDerivative_coverMap hi, absoluteInverse_solves hf hp hm, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ChartScales.Tg_pos.ne'), one_smul]
  · rw [absoluteInverse_zeroMean hfc hpc]
    simp only [TorusAverages.squareAverage, intervalIntegral.integral_smul]
    change 0 = (ChartScales.Tg ^ n)⁻¹ • TorusAverages.squareAverage
      (fun z => absoluteInverse f (coverMap n z))
    simp_rw [coverMap_eq_iterate]
    rw [TorusAverages.squareAverage_covering_iterate hi.continuous hip n,
      absoluteInverse_zeroMean hf hp, smul_zero]

/-- The native chart prefactor, including the physical velocity rescaling. -/
noncomputable def chartPrefactor (h : ℝ) (n : ℕ) : ℝ :=
  (ChartScales.timeCoefficient h n)⁻¹

theorem chartPrefactor_pos (h : ℝ) (n : ℕ) : 0 < chartPrefactor h n :=
  inv_pos.mpr (ChartScales.timeCoefficient_pos h n)

theorem chartPrefactor_eq (h : ℝ) (n : ℕ) :
    chartPrefactor h n = ChartScales.Q n ^ (-1 - h) *
      (ChartScales.Tg ^ ChartScales.nativeIndex h n)⁻¹ := by
  have he : -1 - h = -(1 + h) := by ring
  simp only [chartPrefactor, ChartScales.timeCoefficient, mul_inv_rev, he,
    Real.rpow_neg (ChartScales.Q_pos n).le]

/-- The exponential-looking native factors together cost just one power of
the slow band scale. -/
theorem chartPrefactor_bound (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    ‖chartPrefactor h n‖ ≤ ChartScales.Tg * ChartScales.S n := by
  rw [Real.norm_eq_abs, abs_of_pos (chartPrefactor_pos h n)]
  exact ChartScales.timeCoefficient_inv_upper h hh hn

theorem chartPrefactor_bandBound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (s : WeightedClasses.StripData D) (h : ℝ) (hh : 0 ≤ h)
    (hs : ∀ n, s.slow n = ChartScales.S (n + 4)) :
    WeightedClasses.BandBound s 0 (fun n => chartPrefactor h (n + 4)) := by
  refine ⟨ChartScales.Tg, ChartScales.Tg_pos.le, 1, ?_⟩
  intro n
  simpa only [Real.rpow_zero, mul_one, pow_one, hs] using
    chartPrefactor_bound h hh (Nat.le_add_left 4 n)

/-- Multiplication by the actual chart prefactor preserves the class
exponent, for bands numbered `n+4` where the native-index bounds hold. -/
theorem meanClass_chartPrefactor {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : WeightedClasses.StripData D} {α h : ℝ} {f : ℕ → D → E}
    (hh : 0 ≤ h) (hs : ∀ n, s.slow n = ChartScales.S (n + 4))
    (hf : WeightedClasses.MeanClass s α f) :
    WeightedClasses.MeanClass s α (fun n z => chartPrefactor h (n + 4) • f n z) := by
  unfold WeightedClasses.MeanClass
  simpa only [add_zero] using hf.band_smul (chartPrefactor_bandBound s h hh hs)

/-- Finite initial bands are absorbed into an explicit constant. The native
indices are unchanged; the slow scale may be `max 1 (S n)`. -/
theorem chartPrefactor_bandBound_all {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (s : WeightedClasses.StripData D) (h : ℝ) (hh : 0 ≤ h)
    (hs : ∀ n, ChartScales.S n ≤ s.slow n) :
    WeightedClasses.BandBound s 0 (chartPrefactor h) := by
  let A := ∑ i ∈ Finset.range 4, chartPrefactor h i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => (chartPrefactor_pos h i).le)
  have hK : 0 ≤ ChartScales.Tg + A := add_nonneg ChartScales.Tg_pos.le hA
  refine ⟨ChartScales.Tg + A, hK, 1, ?_⟩
  intro n
  simp only [Real.rpow_zero, mul_one, pow_one]
  by_cases hn : 4 ≤ n
  · exact (chartPrefactor_bound h hh hn).trans
      (mul_le_mul (le_add_of_nonneg_right hA) (hs n)
        (sq_nonneg (n : ℝ)) hK)
  · rw [Real.norm_eq_abs, abs_of_pos (chartPrefactor_pos h n)]
    have hnA : chartPrefactor h n ≤ A :=
      Finset.single_le_sum (fun i _ => (chartPrefactor_pos h i).le)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    exact hnA.trans ((le_add_of_nonneg_left ChartScales.Tg_pos.le).trans
      (le_mul_of_one_le_right hK (s.one_le_slow n)))

theorem meanClass_chartPrefactor_all {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : WeightedClasses.StripData D} {α h : ℝ} {f : ℕ → D → E}
    (hh : 0 ≤ h) (hs : ∀ n, ChartScales.S n ≤ s.slow n)
    (hf : WeightedClasses.MeanClass s α f) :
    WeightedClasses.MeanClass s α (fun n z => chartPrefactor h n • f n z) := by
  unfold WeightedClasses.MeanClass
  simpa only [add_zero] using hf.band_smul (chartPrefactor_bandBound_all s h hh hs)

section CenteredSource

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Remove exactly the auxiliary torus average, retaining every slow parameter. -/
noncomputable def centered (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  f z - PressureStream.torusAverage f (z.1, z.2.1)

theorem centered_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (centered f) :=
  hf.sub ((PressureStream.torusAverage_contDiff hf).comp
    (contDiff_fst.prodMk contDiff_snd.fst))

theorem centered_zeroMean {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : ℝ × S) : PressureStream.torusAverage (centered f) p = 0 := by
  change PressureStream.torusAverage (fun z => f z - PressureStream.torusAverage f (z.1, z.2.1)) p
    = 0
  rw [PressureStream.torusAverage_sub_slow hf, sub_self]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem centered_periodic {f : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) : PressureStream.TorusPeriodicLift (centered f) := by
  intro r s Y k
  simp only [centered]
  have he := hp r s Y k
  dsimp at he
  rw [he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem centered_supported {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (centered f) := by
  intro z hz
  by_contra hout
  have hf0 : f z = 0 := by
    by_contra hn
    exact hout (hs hn)
  have hm0 : PressureStream.torusAverage f (z.1, z.2.1) = 0 := by
    by_contra hn
    exact hout (PressureStream.torusAverage_supported hs hn)
  exact hz (by simp [centered, hf0, hm0])

end CenteredSource

/-- Taking a real part commutes with the actual double integral. -/
theorem squareAverage_re {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    TorusAverages.squareAverage (fun z => (f z).re) = (TorusAverages.squareAverage f).re := by
  have hi : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, f (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      (hf.comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hxs (y : ℝ) : IntervalIntegrable (fun x => f (x, y)) volume 0 1 :=
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, (f (x, y)).re) =
      (∫ x in (0 : ℝ)..1, f (x, y)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hxs y)
  unfold TorusAverages.squareAverage
  simp_rw [show ∀ y : ℝ, (∫ x in (0 : ℝ)..1, (f (x, y)).re) =
      (∫ x in (0 : ℝ)..1, f (x, y)).re from fun y => hx y]
  exact Complex.reCLM.intervalIntegral_comp_comm (hi.continuous.intervalIntegrable 0 1)

section FamilyInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The source in joint slow-parameter/torus coordinates, with the real
source embedded isometrically in the complex Fourier construction. -/
noncomputable def sourceToFamily (f : PressureStream.Lift S → ℝ)
    (z : (ℝ × S) × Plane) : ℂ := f (z.1.1, (z.1.2, z.2))

theorem sourceToFamily_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sourceToFamily f) :=
  Complex.ofRealCLM.contDiff.comp
    (hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv.contDiff)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceToFamily_periodic {f : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) : SmoothFamilyTorusInverse.Periodic (sourceToFamily
      f) := by
  intro p Y k
  exact congrArg Complex.ofReal (hp p.1 p.2 Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceToFamily_mean (f : PressureStream.Lift S → ℝ) (p : ℝ × S) :
    SmoothFamilyTorusInverse.mean (sourceToFamily f) p =
      (PressureStream.torusAverage f p : ℂ) := by
  rw [SmoothFamilyTorusInverse.mean_eq_integral]
  simp only [sourceToFamily, PressureStream.torusAverage, PressureStream.torusInner,
    ← intervalIntegral.integral_ofReal]

/-- The actual normalized temporal Fourier inverse on a real joint family. -/
noncomputable def temporalInverse (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f) ((z.1, z.2.1), z.2.2)).re

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalInverse_periodic (f : PressureStream.Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (temporalInverse f) := by
  intro r s Y k
  exact congrArg Complex.re
    (SmoothFamilyTorusInverse.inverse_periodic .temporal (sourceToFamily f) (r, s) Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalInverse_supported {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (temporalInverse f) := by
  have hsource : ∀ p : ℝ × S, p ∉ Prod.fst ⁻¹' Icc a b → ∀ Y : Plane,
      sourceToFamily f (p, Y) = 0 := by
    intro p hp Y
    have hf0 : f (p.1, (p.2, Y)) = 0 := by
      by_contra hn
      exact hp (hs hn)
    simp only [sourceToFamily, hf0, Complex.ofReal_zero]
  intro z hz
  by_contra hn
  have hi := SmoothFamilyTorusInverse.inverse_preserves_parameter_support .temporal
    (sourceToFamily f) (Prod.fst ⁻¹' Icc a b) hsource (z.1, z.2.1) hn z.2.2
  exact hz (by simp only [temporalInverse, hi, Complex.zero_re])

variable [FiniteDimensional ℝ S]

theorem temporalInverse_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) : ContDiff ℝ ∞ (temporalInverse f) :=
  (Complex.reCLM.contDiff.comp (SmoothFamilyTorusInverse.inverse_smooth .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp))).comp
    (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv.contDiff

theorem temporalInverse_zeroMean {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (temporalInverse f) p = 0 := by
  have hi := SmoothFamilyTorusInverse.inverse_smooth .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp)
  have hm := SmoothFamilyTorusInverse.inverse_zeroMean .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp) p
  rw [SmoothFamilyTorusInverse.mean_eq_integral] at hm
  change TorusAverages.squareAverage
    (fun Y => (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f) (p, Y)).re) = 0
  have hs : ContDiff ℝ ∞ (fun Y => SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f)
    (p, Y)) :=
    SmoothFamilyTorusInverse.slice_smooth hi p
  rw [squareAverage_re hs]
  exact (congrArg Complex.re hm).trans rfl

/-- The real joint inverse solves the genuine Fréchet directional equation. -/
theorem temporalInverse_solves {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (z : PressureStream.Lift S) :
    PressureStream.graphDz ((0 : S), vector .temporal) (temporalInverse f) z = f z := by
  have hfs := sourceToFamily_smooth hf
  have hps := sourceToFamily_periodic hp
  have hms : SmoothFamilyTorusInverse.ZeroMean (sourceToFamily f) := by
    intro p
    rw [sourceToFamily_mean, hm p, Complex.ofReal_zero]
  let q : (ℝ × S) × Plane := ((z.1, z.2.1), z.2.2)
  let L := (LinearIsometryEquiv.prodAssoc ℝ ℝ S
    Plane).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hi := SmoothFamilyTorusInverse.inverse_smooth .temporal hfs hps
  have hD := (Complex.reCLM.hasFDerivAt.comp q
    (((hi.differentiable (by simp)) q).hasFDerivAt)).comp z L.hasFDerivAt
  change HasFDerivAt (temporalInverse f) _ z at hD
  rw [PressureStream.graphDz, hD.fderiv]
  change (fderiv ℝ (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f)) q
    (0, vector .temporal)).re = f z
  have he := congrFun (SmoothFamilyTorusInverse.inverse_solves .temporal hfs hps hms) q
  change fderiv ℝ (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f)) q
    (0, vector .temporal) = sourceToFamily f q at he
  rw [he]
  rfl

end FamilyInverse

section ExactUpdate

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
/-- Fiberwise native-to-absolute covariance for the actual real family inverse. -/
theorem temporalInverse_coverMap {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (n : ℕ) (z : PressureStream.Lift S) :
    temporalInverse (fun p => f (p.1, (p.2.1, coverMap n p.2.2))) z =
      (ChartScales.Tg ^ n)⁻¹ * temporalInverse f (z.1, (z.2.1, coverMap n z.2.2)) := by
  let q : Plane → ℂ := fun Y => sourceToFamily f ((z.1, z.2.1), Y)
  have hq : ContDiff ℝ ∞ q := SmoothFamilyTorusInverse.slice_smooth (sourceToFamily_smooth hf) _
  have hqp : SmoothFourierData.UnitPeriodic q := sourceToFamily_periodic hp _
  have hqm : TorusAverages.squareAverage q = 0 := by
    change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      sourceToFamily f ((z.1, z.2.1), (x, y))) = 0
    rw [← SmoothFamilyTorusInverse.mean_eq_integral, sourceToFamily_mean, hm, Complex.ofReal_zero]
  change (absoluteInverse (fun Y => q (coverMap n Y)) z.2.2).re =
    (ChartScales.Tg ^ n)⁻¹ * (absoluteInverse q (coverMap n z.2.2)).re
  rw [absoluteInverse_coverMap hq hqp hqm n]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The desired angular or axial mean increment in its native chart. -/
noncomputable def desiredIncrement (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  -chartPrefactor h n * temporalInverse (centered f) z

/-- The actual fast-time derivative, including its chart coefficient. -/
noncomputable def fastDerivative (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  ChartScales.timeCoefficient h n * PressureStream.graphDz ((0 : S), vector .temporal) f z

theorem desiredIncrement_smooth (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    ContDiff ℝ ∞ (desiredIncrement h n f) :=
  contDiff_const.mul (temporalInverse_smooth (centered_smooth hf) (centered_periodic hp))

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem desiredIncrement_periodic (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (desiredIncrement h n f) := by
  intro r s Y k
  exact congrArg (-chartPrefactor h n * ·) (temporalInverse_periodic (centered f) r s Y k)

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem desiredIncrement_supported (h : ℝ) (n : ℕ) {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (desiredIncrement h n f) := by
  intro z hz
  apply temporalInverse_supported (centered_supported hs)
  intro hi
  exact hz (by simp only [desiredIncrement, hi, mul_zero])

theorem desiredIncrement_zeroMean (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (desiredIncrement h n f) p = 0 := by
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    -chartPrefactor h n * temporalInverse (centered f) (p.1, (p.2, (x, y)))) = 0
  simp_rw [intervalIntegral.integral_const_mul]
  change -chartPrefactor h n * PressureStream.torusAverage (temporalInverse (centered f)) p = 0
  rw [temporalInverse_zeroMean (centered_smooth hf) (centered_periodic hp), mul_zero]

/-- In particular this gives both the angular `r²` bar mass and axial `r`
bar mass without an extra normalization term. -/
theorem desiredIncrement_barMass (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (w : ℝ → ℝ) (s : S) :
    (∫ r, w r * PressureStream.torusAverage (desiredIncrement h n f) (r, s)) = 0 := by
  simp_rw [desiredIncrement_zeroMean h n hf hp, mul_zero, integral_zero]

/-- Exact cancellation of the source's zero-bar part. -/
theorem desiredIncrement_fastDerivative (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    fastDerivative h n (desiredIncrement h n f) z = -centered f z := by
  have hi := temporalInverse_smooth (centered_smooth hf) (centered_periodic hp)
  have hD := (((hi.differentiable (by simp)) z).hasFDerivAt).const_smul (-chartPrefactor h n)
  change HasFDerivAt (desiredIncrement h n f) _ z at hD
  rw [fastDerivative, PressureStream.graphDz, hD.fderiv]
  change ChartScales.timeCoefficient h n * (-chartPrefactor h n *
    PressureStream.graphDz ((0 : S), vector .temporal) (temporalInverse (centered f)) z) = _
  rw [temporalInverse_solves (centered_smooth hf) (centered_periodic hp) (centered_zeroMean hf)]
  simp only [chartPrefactor, neg_mul, mul_neg, ← mul_assoc,
    mul_inv_cancel₀ (ChartScales.timeCoefficient_pos h n).ne', one_mul]

omit [FiniteDimensional ℝ S] in
theorem fastDerivative_sub (h : ℝ) (n : ℕ) {f g : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : PressureStream.Lift S) :
    fastDerivative h n (fun p => f p - g p) z = fastDerivative h n f z - fastDerivative h n g z :=
      by
  simp only [fastDerivative, PressureStream.graphDz,
    fderiv_fun_sub ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z),
    _root_.sub_apply, mul_sub]

end ExactUpdate

section NativePullback

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def pullbackCover (i : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ := f (z.1, (z.2.1, coverMap i z.2.2))

theorem pullbackCover_smooth (i : ℕ) {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pullbackCover i f) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
    ((coverMap i).contDiff.comp contDiff_snd.snd)))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pullbackCover_periodic (i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) : PressureStream.TorusPeriodicLift (pullbackCover i
      f) := by
  intro r s Y k
  change f (r, (s, coverMap i (Y + ((k.1 : ℝ), (k.2 : ℝ))))) = f (r, (s, coverMap i Y))
  rw [map_add, coverMap_lattice]
  exact hp r s _ _

theorem torusAverage_pullbackCover (i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (pullbackCover i f) p = PressureStream.torusAverage f p := by
  change TorusAverages.squareAverage (fun Y => f (p.1, (p.2, coverMap i Y))) =
    TorusAverages.squareAverage (fun Y => f (p.1, (p.2, Y)))
  simp_rw [coverMap_eq_iterate]
  exact TorusAverages.squareAverage_covering_iterate_real
    (hf.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hp p.1 p.2) i

theorem centered_pullbackCover (i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    centered (pullbackCover i f) = pullbackCover i (centered f) := by
  funext z
  change f (z.1, (z.2.1, coverMap i z.2.2)) -
    PressureStream.torusAverage (pullbackCover i f) (z.1, z.2.1) =
      f (z.1, (z.2.1, coverMap i z.2.2)) - PressureStream.torusAverage f (z.1, z.2.1)
  rw [torusAverage_pullbackCover i hf hp]

/-- Pulling the native update through its actual covering gives the same
absolute temporal inverse. There is exactly one native `Tg⁻ⁱ` factor. -/
theorem desiredIncrement_native_pullback (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    pullbackCover (ChartScales.nativeIndex h n) (desiredIncrement h n f) z =
      -ChartScales.Q n ^ (-1 - h) *
        temporalInverse (centered (pullbackCover (ChartScales.nativeIndex h n) f)) z := by
  rw [centered_pullbackCover (ChartScales.nativeIndex h n) hf hp]
  change -chartPrefactor h n * temporalInverse (centered f)
      (z.1, (z.2.1, coverMap (ChartScales.nativeIndex h n) z.2.2)) =
    -ChartScales.Q n ^ (-1 - h) * temporalInverse
      (fun p => centered f (p.1, (p.2.1, coverMap (ChartScales.nativeIndex h n) p.2.2))) z
  rw [temporalInverse_coverMap (centered_smooth hf) (centered_periodic hp)
    (centered_zeroMean hf), chartPrefactor_eq]
  ring

end NativePullback

section AxialReconstruction

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def axialPotential (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamPotential d a b M ((0 : S), v) (desiredIncrement h n f)

noncomputable def axialUpdate (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : S), v)
    (axialPotential d a b M v h n f)

noncomputable def radialUpdate (d a b M : ℝ) (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamBeta w (axialPotential d a b M v h n f)

omit [FiniteDimensional ℝ S] in
theorem radialUpdate_smul_direction (d a b M : ℝ) (v : Plane) (w : S × Plane) (h c : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) :
    radialUpdate d a b M v (c • w) h n f = fun z => c * radialUpdate d a b M v w h n f z := by
  funext z
  have hv : ((0 : ℝ), c • w) = c • ((0 : ℝ), w) := by simp
  simp only [radialUpdate, PressureStream.streamBeta, PressureStream.graphDz, hv, map_smul,
    smul_eq_mul, mul_neg]

/-- The retained compactification alias, with its physical `1/r` factor. -/
noncomputable def axialAlias (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.divideRadius (RadialPullback.physicalAlias d a b M ((0 : S), v)
    (PressureStream.weightedSource (desiredIncrement h n f)))

omit [FiniteDimensional ℝ S] in
theorem axialAlias_eq_cutoff_total {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) :
    axialAlias d a b M v h n f z =
      (deriv (RadialPullback.physicalCutoff d a b) z.1 *
        PressureStream.physicalTotal d a M ((0 : S), v)
          (PressureStream.weightedSource (desiredIncrement h n f)) z) / z.1 := by
  unfold axialAlias PressureStream.divideRadius
  rw [RadialPullback.physicalAlias_eq_cutoff_derivative_global ha hab hd]
  rfl

theorem axialPotential_smooth {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) : ContDiff ℝ ∞ (axialPotential d a b M v h n f) :=
  PressureStream.streamPotential_contDiff ha hab hd (0, v)
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs)

theorem axialPotential_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (axialPotential d a b M v h n f) :=
  PressureStream.streamPotential_supported ha hab hd (0, v)
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs)

theorem axialUpdate_smooth {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) : ContDiff ℝ ∞ (axialUpdate d a b M v h n f) :=
  PressureStream.streamGamma_contDiff ha hab hd (0, v)
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs)

theorem axialUpdate_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (axialUpdate d a b M v h n f) :=
  PressureStream.streamGamma_supported (axialPotential_supported ha hab hd v h n hf hp hs)
    (PressureStream.physicalSpeed d M) (0, v)

theorem radialUpdate_smooth {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) : ContDiff ℝ ∞ (radialUpdate d a b M v w h n f) :=
  PressureStream.streamBeta_contDiff ha hab hd (0, v) w
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs)

theorem radialUpdate_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (radialUpdate d a b M v w h n f) :=
  PressureStream.streamBeta_supported (axialPotential_supported ha hab hd v h n hf hp hs) w

theorem axialAlias_smooth {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) : ContDiff ℝ ∞ (axialAlias d a b M v h n f) :=
  PressureStream.divideRadius_contDiff ha
    (RadialPullback.physicalAlias_contDiff ha hab hd
      (PressureStream.weightedSource_contDiff (desiredIncrement_smooth h n hf hp))
      (PressureStream.weightedSource_supported (desiredIncrement_supported h n hs)) M (0, v))
    (RadialPullback.physicalAlias_supported ha hab hd M (0, v) _)

omit [FiniteDimensional ℝ S] in
theorem axialAlias_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ) :
    RadialAlias.RadiallySupported a b (axialAlias d a b M v h n f) :=
  PressureStream.divideRadius_supported
    (RadialPullback.physicalAlias_supported ha hab hd M (0, v) _)

/-- No compactification error is removed from the reconstructed axial field. -/
theorem axialUpdate_eq_desired_sub_alias {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane) (h : ℝ) (n : ℕ)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (hs : RadialAlias.RadiallySupported a b f) :
    axialUpdate d a b M v h n f = fun z => desiredIncrement h n f z - axialAlias d a b M v h n f z
      := by
  funext z
  exact PressureStream.streamGamma_eq_desired_sub_alias_global ha hab hd (0, v)
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs) z

theorem update_divergence_zero {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) (z : PressureStream.Lift S) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed d M) (0, v) w
      (radialUpdate d a b M v w h n f) (axialUpdate d a b M v h n f) z = 0 :=
  PressureStream.reconstructed_divergence_zero ha hab hd (0, v) w
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs) z

theorem axialUpdate_zeroMean {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) (p : ℝ × S) :
    PressureStream.torusAverage (axialUpdate d a b M v h n f) p = 0 := by
  have he := PressureStream.streamGamma_bar_eq_desired (M := M) ha hab hd v
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs)
    (desiredIncrement_periodic h n f) (desiredIncrement_barMass h n hf hp id) p
  exact he.trans (desiredIncrement_zeroMean h n hf hp p)

/-- Fast time cancels the axial zero-bar source, retaining exactly the
fast-time derivative of the compactification alias. -/
theorem axialUpdate_fast_residual {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) (z : PressureStream.Lift S) :
    fastDerivative h n (axialUpdate d a b M v h n f) z + centered f z =
      -fastDerivative h n (axialAlias d a b M v h n f) z := by
  rw [axialUpdate_eq_desired_sub_alias ha hab hd v h n hf hp hs,
    fastDerivative_sub h n (desiredIncrement_smooth h n hf hp)
      (axialAlias_smooth ha hab hd v h n hf hp hs), desiredIncrement_fastDerivative h n hf hp]
  ring

/-- The actual two-component fast-time update and incompressible stream,
with the exact axial alias in the resulting residual. -/
theorem temporal_mean_update {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ) {fθ fz : PressureStream.Lift S → ℝ}
    (hθ : ContDiff ℝ ∞ fθ) (hz : ContDiff ℝ ∞ fz)
    (hpθ : PressureStream.TorusPeriodicLift fθ) (hpz : PressureStream.TorusPeriodicLift fz)
    (hsz : RadialAlias.RadiallySupported a b fz) (z : PressureStream.Lift S) :
    fastDerivative h n (desiredIncrement h n fθ) z + centered fθ z = 0 ∧
    fastDerivative h n (axialUpdate d a b M v h n fz) z + centered fz z =
      -fastDerivative h n (axialAlias d a b M v h n fz) z ∧
    PressureStream.graphDivergence (PressureStream.physicalSpeed d M) (0, v) w
      (radialUpdate d a b M v w h n fz) (axialUpdate d a b M v h n fz) z = 0 ∧
    PressureStream.torusAverage (desiredIncrement h n fθ) (z.1, z.2.1) = 0 ∧
    PressureStream.torusAverage (axialUpdate d a b M v h n fz) (z.1, z.2.1) = 0 := by
  refine ⟨?_, axialUpdate_fast_residual ha hab hd v h n hz hpz hsz z,
    update_divergence_zero ha hab hd v w h n hz hpz hsz z,
    desiredIncrement_zeroMean h n hθ hpθ _, axialUpdate_zeroMean ha hab hd v h n hz hpz hsz _⟩
  rw [desiredIncrement_fastDerivative h n hθ hpθ, neg_add_cancel]

end AxialReconstruction

section WeightedStream

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed smooth radial multiplier preserves the actual all-jet class.
The constant is obtained from the derivative product rule on the compact annulus. -/
theorem meanClass_radialMultiply (a b : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {s : WeightedClasses.StripData (ℝ × E)} {α : ℝ} {g : ℕ → ℝ × E → V}
    (hdomain : ∀ z ∈ s.domain, z.1 ∈ Icc a b) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (hclass : WeightedClasses.MeanClass s α g) :
    WeightedClasses.MeanClass s α (fun n z => φ z.1 • g n z) := by
  refine ⟨hclass.weight_nonneg, fun n => ((hφ.comp contDiff_fst).smul (hg n)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hbound⟩ := hclass.bounds m
  obtain ⟨K, hK, hmul⟩ := RadialPullback.radial_multiplier_finiteJets_uniform (E := E) (V := V) a b
    hφ m
  refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
  intro n z hz j hj
  have hA := WeightedClasses.majorant_nonneg s (fun _ z => s.zeta z) α hC p n z
    (s.zeta_nonneg z hz)
  have hout := hmul (g n) (hg n) z (hdomain z hz)
    (WeightedClasses.majorant s (fun _ z => s.zeta z) α C p n z) hA (hbound n z hz) j hj
  apply hout.trans_eq
  unfold WeightedClasses.majorant
  ring

/-- Division by the positive radius preserves the class for supported
fields. A globally smooth positive regularization proves all derivative bounds. -/
theorem meanClass_divideRadius {a b : ℝ} (ha : 0 < a)
    {s : WeightedClasses.StripData (ℝ × E)} {α : ℝ} {g : ℕ → ℝ × E → ℝ}
    (hdomain : ∀ z ∈ s.domain, z.1 ∈ Icc a b) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : WeightedClasses.MeanClass s α g) :
    WeightedClasses.MeanClass s α (fun n => PressureStream.divideRadius (g n)) := by
  let φ : ℝ → ℝ := fun r => (RadialPullback.positiveRadius (a / 4) r)⁻¹
  have hφ : ContDiff ℝ ∞ φ := (RadialPullback.positiveRadius_contDiff (a / 4)).inv
    (fun r => (RadialPullback.positiveRadius_pos (by positivity) r).ne')
  have heq : (fun n => PressureStream.divideRadius (g n)) = (fun n z => φ z.1 • g n z) := by
    funext n z
    by_cases hr : a ≤ z.1
    · dsimp [PressureStream.divideRadius, φ]
      rw [RadialPullback.positiveRadius_eq_self (by positivity) (by linarith)]
      simp only [div_eq_mul_inv, mul_comm]
    · have hg0 : g n z = 0 := by
        by_contra hn
        exact hr (hs n hn).1
      simp [PressureStream.divideRadius, hg0]
  rw [heq]
  exact meanClass_radialMultiply a b hφ hdomain hg hclass

/-- The actual stream potential preserves the original exponential weight
and its exponent, uniformly for all bandwise transport coefficients. -/
theorem meanClass_streamPotential {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (g : ℕ → ℝ × E → ℝ)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α g) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => PressureStream.streamPotential d a b (M n) (v n) (g n)) := by
  let s : WeightedClasses.StripData (ℝ × E) :=
    WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR
  have hdomain : ∀ z ∈ s.domain, z.1 ∈ Icc a b := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hw : WeightedClasses.MeanClass s α (fun n => PressureStream.weightedSource (g n)) := by
    unfold PressureStream.weightedSource
    simpa only [smul_eq_mul, id_eq] using
      meanClass_radialMultiply a b (φ := id) contDiff_id hdomain hg hclass
  have hwc := fun n => PressureStream.weightedSource_contDiff (hg n)
  have hws := fun n => PressureStream.weightedSource_supported (hs n)
  have hic := RadialPullback.meanClass_physicalCompact ha hab hd hcL hcR ε R hε hεone hR α M v
    (fun n => PressureStream.weightedSource (g n)) hwc hws hw
  exact meanClass_divideRadius ha hdomain
    (fun n => RadialPullback.physicalCompact_contDiff ha hab hd (hwc n) (hws n) (M n) (v n))
    (fun n => RadialPullback.physicalCompact_supported ha hab hd (hwc n) (hws n) (M n) (v n)) hic

/-- A fixed full axial direction may include every slow variable. Its actual
derivative of the stream has the same class exponent. -/
theorem meanClass_streamBeta {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (w : E) (g : ℕ → ℝ × E → ℝ)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α g) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => PressureStream.streamBeta w (PressureStream.streamPotential d a b (M n) (v n) (g
        n))) := by
  have hi := meanClass_streamPotential ha hab hd hcL hcR ε R hε hεone hR α M v g hg hs hclass
  have hD := (hi.directional (0, w)).map (-ContinuousLinearMap.id ℝ ℝ)
  unfold WeightedClasses.MeanClass PressureStream.streamBeta PressureStream.graphDz
  simpa only [
    _root_.neg_apply, ContinuousLinearMap.id_apply] using hD

end WeightedStream

section AliasPullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def aliasFactor (d a r : ℝ) : ℝ :=
  RadialPullback.radialJacobian d (RadialPullback.positiveRadius (a / 4) r) /
    RadialPullback.positiveRadius (a / 4) r

theorem aliasFactor_smooth {a : ℝ} (ha : 0 < a) (d : ℝ) : ContDiff ℝ ∞ (aliasFactor d a) := by
  have hr := RadialPullback.positiveRadius_contDiff (a / 4)
  have hn (r : ℝ) := (RadialPullback.positiveRadius_pos (show 0 < a / 4 by positivity) r).ne'
  exact (contDiff_const.mul (hr.rpow_const_of_ne hn)).div hr hn

/-- The physical divided alias is exactly a fixed radial multiplier times
the normalized transport alias pulled through the power chart. -/
theorem dividedAlias_eq_pullback {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) (g : ℝ × E → ℝ) :
    PressureStream.divideRadius (RadialPullback.physicalAlias d a b M v g) =
      fun z => aliasFactor d a z.1 * UniformFourierAlias.exactAlias
        (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) M v (RadialPullback.normalizeSource d a
          g)
          (RadialPullback.liftChart (RadialPullback.powerChart d a) z) := by
  funext z
  by_cases hr : a ≤ z.1
  · dsimp [PressureStream.divideRadius, RadialPullback.physicalAlias,
    UniformFourierAlias.exactAlias,
      RadialPullback.liftChart, aliasFactor]
    rw [RadialPullback.positiveRadius_eq_self (show 0 < a / 4 by positivity) (by linarith)]
    ring
  · have hχ := RadialPullback.deriv_interiorCutoff_zero_left
      (Real.rpow_lt_rpow ha.le hab hd) (RadialPullback.powerChart_lt_left ha hd (lt_of_not_ge
        hr)).le
    simp only [PressureStream.divideRadius, RadialPullback.physicalAlias,
      UniformFourierAlias.exactAlias,
      RadialPullback.liftChart, hχ, mul_zero, zero_smul, zero_div]

/-- A uniform full-jet estimate for the actual physical alias follows from
the corresponding normalized alias estimate. The transfer constant is fixed
before the source, transport coefficient, and transport direction are given. -/
theorem dividedAlias_finiteJets_transfer {d a b : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (g : ℝ × E → ℝ),
      ContDiff ℝ ∞ g → RadialAlias.RadiallySupported a b g →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ m, ∀ z : ℝ × E, ‖iteratedFDeriv ℝ j (UniformFourierAlias.exactAlias
        (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) M v
          (RadialPullback.normalizeSource d a g)) z‖ ≤ C) →
      ∀ j ≤ m, ∀ z : ℝ × E,
        ‖iteratedFDeriv ℝ j (PressureStream.divideRadius (RadialPullback.physicalAlias d a b M v
          g)) z‖ ≤
          K * C := by
  obtain ⟨KP, hKP, hcomp⟩ := RadialPullback.radial_comp_finiteJets_uniform (E := E) (V := ℝ)
    a b (RadialPullback.powerChart_contDiff ha d) m
  obtain ⟨KM, hKM, hmul⟩ := RadialPullback.radial_multiplier_finiteJets_uniform (E := E) (V := ℝ)
    a b (aliasFactor_smooth ha d) m
  refine ⟨KM * KP, mul_nonneg hKM hKP, ?_⟩
  intro M v g hg hs C hC hbound j hj z
  let A := UniformFourierAlias.exactAlias (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d))
    M v (RadialPullback.normalizeSource d a g)
  have hAs : ContDiff ℝ ∞ A := UniformFourierAlias.exactAlias_smooth
    (TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d))
    (RadialPullback.normalizeSource_contDiff ha hd hg) (RadialPullback.normalizeSource_supported ha
      hab hd hs)
  by_cases hz : z.1 ∈ Icc a b
  · rw [dividedAlias_eq_pullback ha hab hd v g]
    change ‖iteratedFDeriv ℝ j (fun y => aliasFactor d a y.1 •
      (A ∘ RadialPullback.liftChart (RadialPullback.powerChart d a)) y) z‖ ≤ _
    have hc := hcomp A hAs z hz C hC
      (fun i hi => hbound i hi (RadialPullback.liftChart (RadialPullback.powerChart d a) z))
    have hm := hmul (A ∘ RadialPullback.liftChart (RadialPullback.powerChart d a))
      (hAs.comp (RadialPullback.liftChart_contDiff (RadialPullback.powerChart_contDiff ha d))) z hz
      (KP * C) (mul_nonneg hKP hC) hc j hj
    exact hm.trans_eq (by ring)
  · have hz0 : iteratedFDeriv ℝ j
        (PressureStream.divideRadius (RadialPullback.physicalAlias d a b M v g)) z = 0 := by
      by_contra hn
      exact hz (TransportPrimitive.iteratedFDeriv_supported
        (PressureStream.divideRadius_supported (RadialPullback.physicalAlias_supported ha hab hd M
          v g)) j hn)
    rw [hz0, norm_zero]
    exact mul_nonneg (mul_nonneg hKM hKP) hC

end AliasPullback

section WeightedTemporal

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem meanClass_temporalInverse {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => temporalInverse (f n)) :=
  UniformFourierAlias.meanClass_realInverse .temporal ha hcL hcR ε R hε hεone hR hf hfc hp

theorem meanClass_centered {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => centered (f n)) :=
  UniformFourierAlias.meanClass_realCenterSource ha hcL hcR ε R hε hεone hR hf hfc hp

/-- The complete desired temporal update preserves the original exponent in
every band, including the initial bands. No inverse estimate is assumed. -/
theorem meanClass_desiredIncrement {a b cL cR h : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => desiredIncrement h n (f n)) := by
  have hc := meanClass_centered ha hcL hcR ε R hε hεone hR hf hfc hp
  have hi := meanClass_temporalInverse ha hcL hcR ε R hε hεone hR hc
    (fun n => centered_smooth (hfc n)) (fun n => centered_periodic (hp n))
  have hm := (meanClass_chartPrefactor_all hh hscale hi).map (-ContinuousLinearMap.id ℝ ℝ)
  change WeightedClasses.MeanClass _ α
    (fun n z => -chartPrefactor h n * temporalInverse (centered (f n)) z)
  unfold WeightedClasses.MeanClass
  simpa only [desiredIncrement, _root_.neg_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, neg_mul] using hm

theorem meanClass_axialPotential {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (v : ℕ → Plane)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => axialPotential d a b (M n) (v n) h n (f n)) :=
  meanClass_streamPotential ha hab hd hcL hcR ε R hε hεone hR α M (fun n => (0, v n))
    (fun n => desiredIncrement h n (f n)) (fun n => desiredIncrement_smooth h n (hfc n) (hp n))
    (fun n => desiredIncrement_supported h n (hs n))
    (meanClass_desiredIncrement ha hcL hcR hh ε R hε hεone hR hscale hf hfc hp)

theorem meanClass_radialUpdate {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (v : ℕ → Plane) (w : S × Plane)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => radialUpdate d a b (M n) (v n) w h n (f n)) :=
  meanClass_streamBeta ha hab hd hcL hcR ε R hε hεone hR α M (fun n => (0, v n)) w
    (fun n => desiredIncrement h n (f n)) (fun n => desiredIncrement_smooth h n (hfc n) (hp n))
    (fun n => desiredIncrement_supported h n (hs n))
    (meanClass_desiredIncrement ha hcL hcR hh ε R hε hεone hR hscale hf hfc hp)

/-- The actual chart axial direction carries `ε`; its radial stream
component therefore gains one full mean-class exponent. -/
theorem meanClass_scaledRadialUpdate {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (v : ℕ → Plane) (w : S × Plane)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) (α + 1)
      (fun n => radialUpdate d a b (M n) (v n) (ε n • w) h n (f n)) := by
  let st := WeightedRadialPrimitive.logStripData (E := S × Plane) a b cL cR ha hcL hcR ε R hε hεone
    hR
  have hb : WeightedClasses.BandBound st 1 ε := by
    have h := WeightedClasses.bandBound_rpow st 1
    simp only [Real.rpow_one] at h
    exact h
  have hi := meanClass_radialUpdate ha hab hd hcL hcR hh ε R hε hεone hR hscale M v w hf hfc hp hs
  have hout := hi.band_smul hb
  have heq : (fun n => radialUpdate d a b (M n) (v n) (ε n • w) h n (f n)) =
      (fun n z => ε n • radialUpdate d a b (M n) (v n) w h n (f n) z) := by
    funext n z
    exact congrFun (radialUpdate_smul_direction d a b (M n) (v n) w h (ε n) n (f n)) z
  rw [heq]
  exact hout

end WeightedTemporal

section PhysicalAliasSuperflat

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem normalizeSource_periodic (d a : ℝ) {g : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift g) :
    PressureStream.TorusPeriodicLift (RadialPullback.normalizeSource d a g) := by
  intro r s Y k
  dsimp [RadialPullback.normalizeSource, RadialPullback.liftChart]
  have he := hp (RadialPullback.inverseChart d a r) s Y k
  dsimp at he
  rw [he]

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem normalizeSource_torusAverage (d a : ℝ) (g : PressureStream.Lift S → ℝ) (p : ℝ × S) :
    PressureStream.torusAverage (RadialPullback.normalizeSource d a g) p =
      RadialPullback.sourceMultiplier d a p.1 *
        PressureStream.torusAverage g (RadialPullback.inverseChart d a p.1, p.2) := by
  simp only [PressureStream.torusAverage, PressureStream.torusInner,
    RadialPullback.normalizeSource, RadialPullback.liftChart, smul_eq_mul,
    intervalIntegral.integral_const_mul]

/-- The actual physical divided alias is uniformly superflat for the
manuscript's radial frequencies and any jointly smooth zero-bar source family. -/
theorem dividedAlias_superflat {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {g : ℕ → PressureStream.Lift S → ℝ}
    (hg : WeightedClasses.MeanClass (UniformFourierAlias.chartStrip a b cL cR ha hcL hcR h hh) α g)
    (hgc : ∀ n, ContDiff ℝ ∞ (g n)) (hgp : ∀ n, PressureStream.TorusPeriodicLift (g n))
    (hgm : ∀ n p, PressureStream.torusAverage (g n) p = 0)
    (hgs : ∀ n, RadialAlias.RadiallySupported a b (g n)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : PressureStream.Lift S,
      ‖iteratedFDeriv ℝ j (PressureStream.divideRadius
        (RadialPullback.physicalAlias d a b (ChartScales.radialCoefficient h n)
          ((0 : S), vector .radial) (g n))) z‖ ≤ C * ChartScales.epsilon h n ^ N := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hcLU : 0 < d ^ 2 * cL := mul_pos (sq_pos_of_pos hd) hcL
  have hcRU : 0 < d ^ 2 * cR := mul_pos (sq_pos_of_pos hd) hcR
  let G := fun n => RadialPullback.normalizeSource d a (g n)
  have hG : WeightedClasses.MeanClass
      (UniformFourierAlias.chartStrip (a ^ d) (b ^ d) (d ^ 2 * cL) (d ^ 2 * cR)
        haU hcLU hcRU h hh) α G :=
    UniformFourierAlias.meanClass_normalizeSource ha hab hd hcL hcR
      (ChartScales.epsilon h) UniformFourierAlias.bandSlow (ChartScales.epsilon_pos h)
      (ChartScales.epsilon_le_one h hh.le) UniformFourierAlias.one_le_bandSlow hg hgc
  have hGc : ∀ n, ContDiff ℝ ∞ (G n) := fun n => RadialPullback.normalizeSource_contDiff ha hd (hgc
    n)
  have hGp : ∀ n, UniformFourierAlias.SourcePeriodic (G n) := fun n => normalizeSource_periodic d a
    (hgp n)
  have hGm : ∀ n p, UniformFourierAlias.sourceMean (G n) p = 0 := by
    intro n p
    change PressureStream.torusAverage (RadialPullback.normalizeSource d a (g n)) p = 0
    rw [normalizeSource_torusAverage, hgm, mul_zero]
  have hGs := fun n => RadialPullback.normalizeSource_supported ha hab hd (hgs n)
  let χ := TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)
  have hχ : ContDiff ℝ ∞ χ := TransportPrimitive.interiorCutoff_contDiff _ _
  have hleft : ∀ U ≤ a ^ d, χ U = 0 := fun U hU =>
    TransportPrimitive.interiorCutoff_zero habU (by linarith)
  have hright : ∀ U, b ^ d ≤ U → χ U = 1 := fun U hU =>
    TransportPrimitive.interiorCutoff_one habU (by linarith)
  obtain ⟨C, hC, hb⟩ := UniformFourierAlias.radial_realMeanClass_alias_superflat
    haU habU.le hcLU hcRU hh hχ hleft hright hG hGc hGp hGm hGs m N
  obtain ⟨K, hK, ht⟩ := dividedAlias_finiteJets_transfer (E := S × Plane) ha hab hd m
  refine ⟨K * C, mul_nonneg hK hC, ?_⟩
  filter_upwards [hb] with n hn
  intro j hj z
  have hcε : 0 ≤ C * ChartScales.epsilon h n ^ N :=
    mul_nonneg hC (pow_nonneg (ChartScales.epsilon_pos h n).le _)
  have he := ht (ChartScales.radialCoefficient h n) ((0 : S), vector .radial) (g n)
    (hgc n) (hgs n) (C * ChartScales.epsilon h n ^ N) hcε hn j hj z
  exact he.trans_eq (by ring)

/-- Superflatness of the exact alias in the constructed temporal axial update. -/
theorem axialAlias_superflat {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass (UniformFourierAlias.chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : PressureStream.Lift S,
      ‖iteratedFDeriv ℝ j
        (axialAlias d a b (ChartScales.radialCoefficient h n) (vector .radial) h n (f n)) z‖ ≤
          C * ChartScales.epsilon h n ^ N := by
  let st := UniformFourierAlias.chartStrip (E := S × Plane) a b cL cR ha hcL hcR h hh
  let g := fun n => desiredIncrement h n (f n)
  have hg : WeightedClasses.MeanClass st α g := meanClass_desiredIncrement ha hcL hcR hh.le
    (ChartScales.epsilon h) UniformFourierAlias.bandSlow (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h hh.le) UniformFourierAlias.one_le_bandSlow
    (fun n => le_max_right 1 (ChartScales.S n)) hf hfc hp
  have hgc := fun n => desiredIncrement_smooth h n (hfc n) (hp n)
  have hgp := fun n => desiredIncrement_periodic h n (f n)
  have hgs := fun n => desiredIncrement_supported h n (hs n)
  have hw : WeightedClasses.MeanClass st α (fun n => PressureStream.weightedSource (g n)) := by
    unfold PressureStream.weightedSource
    simpa only [smul_eq_mul, id_eq] using
      meanClass_radialMultiply a b (φ := id) contDiff_id
        (s := st) (fun z hz => ⟨hz.1.le, hz.2.le⟩) hgc hg
  have hwm : ∀ n p, PressureStream.torusAverage (PressureStream.weightedSource (g n)) p = 0 := by
    intro n p
    rw [PressureStream.torusAverage_weightedSource, desiredIncrement_zeroMean h n (hfc n) (hp n),
      mul_zero]
  exact dividedAlias_superflat ha hab hd hcL hcR hh hw
    (fun n => PressureStream.weightedSource_contDiff (hgc n))
    (fun n => PressureStream.weightedSource_periodic (hgp n)) hwm
    (fun n => PressureStream.weightedSource_supported (hgs n)) m N

omit [FiniteDimensional ℝ S] [NormedSpace ℝ S] in
theorem temporalVector_norm_le_one : ‖((0 : ℝ), ((0 : S), vector .temporal))‖ ≤ 1 := by
  have ha : |Real.sqrt 2 - 1| ≤ 1 := abs_le.mpr
    ⟨by linarith [Real.sqrt_nonneg (2 : ℝ)], by linarith [ChartScales.sqrt_two_lt_two]⟩
  simp only [Prod.norm_def, vector, norm_zero, Real.norm_eq_abs, abs_one]
  exact max_le zero_le_one (max_le zero_le_one (max_le ha le_rfl))

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem timeCoefficient_norm_le_one {h : ℝ} (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    ‖ChartScales.timeCoefficient h n‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (ChartScales.timeCoefficient_pos h n)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hS : 1 ≤ ChartScales.S n := by dsimp [ChartScales.S]; nlinarith
  exact (ChartScales.timeCoefficient_bounds h hh hn).2.trans
    (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS)

/-- The actual fast-time residual alias is superflat in every full joint jet. -/
theorem axialAlias_fastDerivative_superflat {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass (UniformFourierAlias.chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : PressureStream.Lift S,
      ‖iteratedFDeriv ℝ j (fastDerivative h n
        (axialAlias d a b (ChartScales.radialCoefficient h n) (vector .radial) h n (f n))) z‖ ≤
          C * ChartScales.epsilon h n ^ N := by
  obtain ⟨C, hC, hb⟩ := axialAlias_superflat ha hab hd hcL hcR hh hf hfc hp hs (m + 1) N
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 4] with n hn hn4
  intro j hj z
  let A := axialAlias d a b (ChartScales.radialCoefficient h n) (vector .radial) h n (f n)
  have hA : ContDiff ℝ ∞ A := axialAlias_smooth ha hab hd (vector .radial) h n (hfc n) (hp n) (hs n)
  have hpartial := UniformFourierAlias.finiteJetBound_fixedPartial hA (s := Set.univ) (m := m)
    (C := C * ChartScales.epsilon h n ^ N) (fun i hi x _ => hn i hi x)
    ((0 : ℝ), ((0 : S), vector .temporal)) temporalVector_norm_le_one
  have hD := PressureStream.graphDz_contDiff hA ((0 : S), vector .temporal)
  change ‖iteratedFDeriv ℝ j (fun p => ChartScales.timeCoefficient h n •
    PressureStream.graphDz ((0 : S), vector .temporal) A p) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hD.contDiffAt.of_le (nat_le_smooth j))]
  change ‖ChartScales.timeCoefficient h n •
    (iteratedFDeriv ℝ j (PressureStream.graphDz ((0 : S), vector .temporal) A) z)‖ ≤ _
  calc
    _ = ‖ChartScales.timeCoefficient h n‖ *
        ‖iteratedFDeriv ℝ j (PressureStream.graphDz ((0 : S), vector .temporal) A) z‖ :=
      norm_smul (ChartScales.timeCoefficient h n)
        (iteratedFDeriv ℝ j (PressureStream.graphDz ((0 : S), vector .temporal) A) z)
    _ ≤ _ := (mul_le_mul (timeCoefficient_norm_le_one hh.le hn4)
      (hpartial j hj z (Set.mem_univ z)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end PhysicalAliasSuperflat

section InteriorAliasClass

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem interiorCutoff_deriv_zero_left {a b U : ℝ} (hab : a < b)
    (hU : U < (2 * a + b) / 3) : deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have he : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hU] with u hu
    exact TransportPrimitive.interiorCutoff_zero hab hu.le
  exact ((hasDerivAt_const U (0 : ℝ)).congr_of_eventuallyEq he).deriv

theorem interiorCutoff_deriv_zero_right {a b U : ℝ} (hab : a < b)
    (hU : (a + 2 * b) / 3 < U) : deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have he : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hU] with u hu
    exact TransportPrimitive.interiorCutoff_one hab hu.le
  exact ((hasDerivAt_const U (1 : ℝ)).congr_of_eventuallyEq he).deriv

/-- The physical alias has support in one fixed compact subannulus,
uniformly in the source, band, and direction. -/
theorem dividedAlias_interior_support {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d) :
    ∃ c e : ℝ, a < c ∧ c < e ∧ e < b ∧ ∀ (M : ℝ) (v : E) (g : ℝ × E → ℝ),
      RadialAlias.RadiallySupported c e (PressureStream.divideRadius (RadialPullback.physicalAlias
        d a b M v g)) := by
  have hb : 0 < b := ha.trans hab
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  let cU := (2 * a ^ d + b ^ d) / 3
  let eU := (a ^ d + 2 * b ^ d) / 3
  have hacU : a ^ d < cU := by dsimp [cU]; linarith
  have hceU : cU < eU := by dsimp [cU, eU]; linarith
  have hebU : eU < b ^ d := by dsimp [eU]; linarith
  have hcU : 0 < cU := haU.trans hacU
  have heU : 0 < eU := hcU.trans hceU
  let c := cU ^ d⁻¹
  let e := eU ^ d⁻¹
  have hac : a < c := by
    simpa only [Real.rpow_rpow_inv ha.le hd.ne'] using
      Real.rpow_lt_rpow haU.le hacU (inv_pos.mpr hd)
  have hce : c < e := Real.rpow_lt_rpow hcU.le hceU (inv_pos.mpr hd)
  have heb : e < b := by
    simpa only [Real.rpow_rpow_inv hb.le hd.ne'] using
      Real.rpow_lt_rpow heU.le hebU (inv_pos.mpr hd)
  have hcPow : c ^ d = cU := Real.rpow_inv_rpow hcU.le hd.ne'
  have hePow : e ^ d = eU := Real.rpow_inv_rpow heU.le hd.ne'
  have hleft (r : ℝ) (hr : r < c) :
      deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) (RadialPullback.powerChart d a r) =
        0 := by
    apply interiorCutoff_deriv_zero_left habU
    change RadialPullback.powerChart d a r < cU
    by_cases hra : a ≤ r
    · rw [RadialPullback.powerChart_eq ha (by linarith) d]
      exact (Real.rpow_lt_rpow (ha.trans_le hra).le hr hd).trans_eq hcPow
    · exact (RadialPullback.powerChart_lt_left ha hd (lt_of_not_ge hra)).trans hacU
  have hright (r : ℝ) (hr : e < r) :
      deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) (RadialPullback.powerChart d a r) =
        0 := by
    apply interiorCutoff_deriv_zero_right habU
    change eU < RadialPullback.powerChart d a r
    rw [RadialPullback.powerChart_eq ha (by linarith) d, ← hePow]
    exact Real.rpow_lt_rpow (ha.trans (hac.trans hce)).le hr hd
  refine ⟨c, e, hac, hce, heb, ?_⟩
  intro M v g z hz
  constructor
  · by_contra hn
    have he := hleft z.1 (lt_of_not_ge hn)
    exact hz (by simp only [PressureStream.divideRadius, RadialPullback.physicalAlias,
      he, mul_zero, zero_smul, zero_div])
  · by_contra hn
    have he := hright z.1 (lt_of_not_ge hn)
    exact hz (by simp only [PressureStream.divideRadius, RadialPullback.physicalAlias,
      he, mul_zero, zero_smul, zero_div])

/-- A fixed interior support converts uniform band bounds into the full
weighted class by an actual positive minimum of the exponential weight. -/
theorem meanClass_of_interior_bounds {a b c e cL cR α : ℝ}
    (ha : 0 < a) (hac : a < c) (he : e < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {f : ℕ → ℝ × E → V} (hfc : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported c e (f n))
    (hf : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n j, j ≤ m → ∀ z : ℝ × E,
      ‖iteratedFDeriv ℝ j (f n) z‖ ≤ C * ε n ^ α * R n ^ p) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f := by
  let st := WeightedRadialPrimitive.logStripData (E := E) a b cL cR ha hcL hcR ε R hε hεone hR
  have hmem (r : ℝ) (hr : r ∈ Icc c e) : ((r, (0 : E)) : ℝ × E) ∈ st.domain :=
    ⟨hac.trans_le hr.1, hr.2.trans_lt he⟩
  have hcont : ContinuousOn (fun r : ℝ => st.zeta (r, (0 : E))) (Icc c e) :=
    st.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hpos (r : ℝ) (hr : r ∈ Icc c e) : 0 < st.zeta (r, (0 : E)) :=
    WeightedRadialPrimitive.zeta_pos cL cR (WeightedRadialPrimitive.logPosition_mem ha (hmem r hr))
  obtain ⟨η, hη, hηbound⟩ := UniformCone.positive_uniform_margin isCompact_Icc hcont hpos
  refine ⟨fun n z hz => st.zeta_nonneg z hz, fun n => (hfc n).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hbound⟩ := hf m
  refine ⟨C / η, div_nonneg hC hη.le, p, ?_⟩
  intro n z hz j hj
  by_cases hzi : z.1 ∈ Icc c e
  · have hζ : η ≤ st.zeta z := hηbound z.1 hzi
    have hgr : R n ^ p ≤ st.growth n z ^ p :=
      pow_le_pow_left₀ (zero_le_one.trans (hR n)) (st.slow_le_growth n z) p
    have hA : 0 ≤ C / η * ε n ^ α * st.growth n z ^ p :=
      mul_nonneg (mul_nonneg (div_nonneg hC hη.le) (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (st.growth_nonneg n z) p)
    calc
      _ ≤ C * ε n ^ α * R n ^ p := hbound n j hj z
      _ ≤ C * ε n ^ α * st.growth n z ^ p :=
        mul_le_mul_of_nonneg_left hgr (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      _ = (C / η * ε n ^ α * st.growth n z ^ p) * η := by field_simp
      _ ≤ (C / η * ε n ^ α * st.growth n z ^ p) * st.zeta z := mul_le_mul_of_nonneg_left hζ hA
      _ = _ := rfl
  · have hzero : iteratedFDeriv ℝ j (f n) z = 0 :=
      Classical.byContradiction (fun hn => hzi (TransportPrimitive.iteratedFDeriv_supported (hs n)
        j hn))
    rw [hzero, norm_zero]
    exact WeightedClasses.majorant_nonneg st (fun _ z => st.zeta z) α
      (div_nonneg hC hη.le) p n z (st.zeta_nonneg z hz)

end InteriorAliasClass

section CompleteWeightedUpdate

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem dividedAlias_global_bounds {a b d cL cR α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (M : ℕ → ℝ) (hM : ∀ n, M n ≠ 0) {g : ℕ → PressureStream.Lift S → ℝ}
    (hg : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α g)
    (hgc : ∀ n, ContDiff ℝ ∞ (g n)) (hgp : ∀ n, PressureStream.TorusPeriodicLift (g n))
    (hgm : ∀ n p, PressureStream.torusAverage (g n) p = 0)
    (hgs : ∀ n, RadialAlias.RadiallySupported a b (g n)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n j, j ≤ m → ∀ z : PressureStream.Lift S,
      ‖iteratedFDeriv ℝ j (PressureStream.divideRadius
        (RadialPullback.physicalAlias d a b (M n) ((0 : S), vector .radial) (g n))) z‖ ≤
          C * ε n ^ α * R n ^ p := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hcLU : 0 < d ^ 2 * cL := mul_pos (sq_pos_of_pos hd) hcL
  have hcRU : 0 < d ^ 2 * cR := mul_pos (sq_pos_of_pos hd) hcR
  let G := fun n => RadialPullback.normalizeSource d a (g n)
  have hG := UniformFourierAlias.meanClass_normalizeSource ha hab hd hcL hcR ε R hε hεone hR hg hgc
  have hGc : ∀ n, ContDiff ℝ ∞ (G n) := fun n => RadialPullback.normalizeSource_contDiff ha hd (hgc
    n)
  have hGp : ∀ n, UniformFourierAlias.SourcePeriodic (G n) := fun n => normalizeSource_periodic d a
    (hgp n)
  have hGm : ∀ n p, UniformFourierAlias.sourceMean (G n) p = 0 := by
    intro n p
    change PressureStream.torusAverage (RadialPullback.normalizeSource d a (g n)) p = 0
    rw [normalizeSource_torusAverage, hgm, mul_zero]
  have hGs := fun n => RadialPullback.normalizeSource_supported ha hab hd (hgs n)
  obtain ⟨C, hC, p, hsource⟩ := UniformFourierAlias.meanClass_global_finiteJets
    haU hcLU hcRU ε R hε hεone hR hG hGs hGc m
  let χ := TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)
  have hχ : ContDiff ℝ ∞ χ := TransportPrimitive.interiorCutoff_contDiff _ _
  have hleft : ∀ U ≤ a ^ d, χ U = 0 := fun U hU =>
    TransportPrimitive.interiorCutoff_zero habU (by linarith)
  have hright : ∀ U, b ^ d ≤ U → χ U = 1 := fun U hU =>
    TransportPrimitive.interiorCutoff_one habU (by linarith)
  obtain ⟨KA, hKA, hbA⟩ := UniformFourierAlias.real_exactAlias_finiteJets (S := S) .radial
    habU.le hχ hleft hright m 0
  obtain ⟨KT, hKT, hbT⟩ := dividedAlias_finiteJets_transfer (E := S × Plane) ha hab hd m
  refine ⟨KT * KA * C, mul_nonneg (mul_nonneg hKT hKA) hC, p, ?_⟩
  intro n j hj z
  let B := C * ε n ^ α * R n ^ p
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
    (pow_nonneg (zero_le_one.trans (hR n)) _)
  have hAb : ∀ i ≤ m, ∀ y : PressureStream.Lift S,
      ‖iteratedFDeriv ℝ i (UniformFourierAlias.exactAlias χ (M n) ((0 : S), vector .radial) (G n))
        y‖ ≤ KA * B := by
    intro i hi y
    have he := hbA (G n) (hGc n) (hGp n) (hGm n) (hGs n) B hB
      (fun k hk x _ => hsource n k (by simpa using hk) x (Set.mem_univ x)) (M n) (hM n) i hi y
    simpa only [pow_zero, mul_one] using he
  have he := hbT (M n) ((0 : S), vector .radial) (g n) (hgc n) (hgs n)
    (KA * B) (mul_nonneg hKA hB) hAb j hj z
  exact he.trans_eq (by dsimp [B]; ring)

/-- The actual divided compactification alias lies in the same weighted
class; its fixed interior support supplies the full edge weight. -/
theorem meanClass_dividedAlias {a b d cL cR α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (M : ℕ → ℝ) (hM : ∀ n, M n ≠ 0) {g : ℕ → PressureStream.Lift S → ℝ}
    (hg : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α g)
    (hgc : ∀ n, ContDiff ℝ ∞ (g n)) (hgp : ∀ n, PressureStream.TorusPeriodicLift (g n))
    (hgm : ∀ n p, PressureStream.torusAverage (g n) p = 0)
    (hgs : ∀ n, RadialAlias.RadiallySupported a b (g n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => PressureStream.divideRadius
        (RadialPullback.physicalAlias d a b (M n) ((0 : S), vector .radial) (g n))) := by
  obtain ⟨c, e, hac, _, heb, hs⟩ := dividedAlias_interior_support (E := S × Plane) ha hab hd
  apply meanClass_of_interior_bounds ha hac heb hcL hcR ε R hε hεone hR
  · intro n
    exact PressureStream.divideRadius_contDiff ha
      (RadialPullback.physicalAlias_contDiff ha hab hd (hgc n) (hgs n) (M n) (0, vector .radial))
      (RadialPullback.physicalAlias_supported ha hab hd (M n) (0, vector .radial) (g n))
  · exact fun n => hs (M n) (0, vector .radial) (g n)
  · exact dividedAlias_global_bounds ha hab hd hcL hcR ε R hε hεone hR M hM hg hgc hgp hgm hgs

theorem meanClass_axialAlias {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (hM : ∀ n, M n ≠ 0)
    {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => axialAlias d a b (M n) (vector .radial) h n (f n)) := by
  let st := WeightedRadialPrimitive.logStripData (E := S × Plane) a b cL cR ha hcL hcR ε R hε hεone
    hR
  let g := fun n => desiredIncrement h n (f n)
  have hg : WeightedClasses.MeanClass st α g :=
    meanClass_desiredIncrement ha hcL hcR hh ε R hε hεone hR hscale hf hfc hp
  have hgc := fun n => desiredIncrement_smooth h n (hfc n) (hp n)
  have hgp := fun n => desiredIncrement_periodic h n (f n)
  have hgs := fun n => desiredIncrement_supported h n (hs n)
  have hw : WeightedClasses.MeanClass st α (fun n => PressureStream.weightedSource (g n)) := by
    unfold PressureStream.weightedSource
    simpa only [smul_eq_mul, id_eq] using
      meanClass_radialMultiply a b (φ := id) contDiff_id
        (s := st) (fun z hz => ⟨hz.1.le, hz.2.le⟩) hgc hg
  have hwm : ∀ n p, PressureStream.torusAverage (PressureStream.weightedSource (g n)) p = 0 := by
    intro n p
    rw [PressureStream.torusAverage_weightedSource, desiredIncrement_zeroMean h n (hfc n) (hp n),
      mul_zero]
  exact meanClass_dividedAlias ha hab hd hcL hcR ε R hε hεone hR M hM hw
    (fun n => PressureStream.weightedSource_contDiff (hgc n))
    (fun n => PressureStream.weightedSource_periodic (hgp n)) hwm
    (fun n => PressureStream.weightedSource_supported (hgs n))

/-- The reconstructed axial field, including its exact nonzero alias,
has the original mean-class exponent. -/
theorem meanClass_axialUpdate {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (hM : ∀ n, M n ≠ 0)
    {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => axialUpdate d a b (M n) (vector .radial) h n (f n)) := by
  have hi := meanClass_desiredIncrement ha hcL hcR hh ε R hε hεone hR hscale hf hfc hp
  have hA := meanClass_axialAlias ha hab hd hcL hcR hh ε R hε hεone hR hscale M hM hf hfc hp hs
  have hout := hi.add (hA.map (-ContinuousLinearMap.id ℝ ℝ))
  have heq : (fun n => axialUpdate d a b (M n) (vector .radial) h n (f n)) =
      fun n z => desiredIncrement h n (f n) z + -axialAlias d a b (M n) (vector .radial) h n (f n)
        z := by
    funext n z
    simpa only [sub_eq_add_neg] using congrFun
      (axialUpdate_eq_desired_sub_alias ha hab hd (vector .radial) h n (hfc n) (hp n) (hs n)) z
  rw [heq]
  unfold WeightedClasses.MeanClass
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using hout

end CompleteWeightedUpdate

end NavierStokes.TemporalMeanUpdate
