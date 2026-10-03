/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection

/-!
# Coefficients of finite real Fourier expansions

The real Fourier coefficient map is a left inverse to finite synthesis for an orthonormal mode
family. This gives the coefficient-side part of the Galerkin initial projection bridge.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance projectionMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance projectionMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance projectionProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

variable {n : ℕ}

/-- Projecting a finite linear combination onto an orthonormal family recovers its coefficients.
The explicit integrability premise keeps this lemma independent of the topology chosen for the
mode family. -/
theorem modeProjectionCoefficients_modeExpansion
    (mode : Fin n → Torus → ℝ)
    (horth : ∀ i j, ∫ x : Torus, mode i x * mode j x = if i = j then 1 else 0)
    (c : Coefficients n)
    (hprod : ∀ i j, Integrable (fun x : Torus => mode i x * mode j x) volume) :
    modeProjectionCoefficients n mode (modeExpansion n mode c) = c := by
  ext j
  change (∫ x : Torus, modeExpansion n mode c x * mode j x) = c j
  rw [show (fun x : Torus => modeExpansion n mode c x * mode j x) =
      fun x => ∑ i, c i * (mode i x * mode j x) by
    funext x
    simp only [modeExpansion]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, horth]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hne
      simp [hne]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro i hi
    exact (hprod i j).const_mul (c i)

/-- In particular the positive real Fourier frame has an exact coefficient reconstruction on its
own finite span. -/
theorem realFourierModeFin_projectionCoefficients_expansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) = c := by
  apply modeProjectionCoefficients_modeExpansion
    (mode := realFourierModeFin N)
    (realFourierModeFin_orthonormal N)
  intro i j
  exact ((realFourierModeFin_continuous N i).mul
      (realFourierModeFin_continuous N j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Complex Fourier coefficients commute with finite real-mode synthesis. -/
theorem mFourierCoeff_modeExpansion (n : ℕ)
    (mode : Fin n → Torus → ℝ) (c : Coefficients n) (l : Fin 2 → ℤ)
    (hmode : ∀ i, Continuous (mode i)) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion n mode c x : ℝ) : Torus → ℂ) l =
      ∑ i, (c i : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x => (mode i x : ℂ)) l := by
  let character := UnitAddTorus.mFourier (-l)
  have hterm : ∀ i : Fin n,
      Integrable (fun x : Torus => character x * (mode i x : ℂ)) volume := by
    intro i
    have hcont : Continuous (fun x : Torus => character x * (mode i x : ℂ)) :=
      character.continuous.mul (Complex.continuous_ofReal.comp (hmode i))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint : (fun x : Torus => character x *
      (modeExpansion n mode c x : ℂ)) =
    fun x => ∑ i, (c i : ℂ) * (character x * (mode i x : ℂ)) := by
    funext x
    simp only [modeExpansion, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change (∫ x : Torus, character x * (modeExpansion n mode c x : ℂ)) = _
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    rfl
  · intro i hi
    exact (hterm i).const_mul (c i : ℂ)

/-- Reindex the Fourier coefficient of a real frame expansion by its constant, cosine, and sine
modes. -/
def realFourierFrameCoefficientContribution (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (l : Fin 2 → ℤ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) : ℂ :=
  (c (realFourierIndexEquivFin N (some (p, false))) : ℂ) *
      ((Real.sqrt 2 / 2 : ℝ) *
        (if l = representativeFrequency p then 1 else 0) +
        (Real.sqrt 2 / 2 : ℝ) *
        (if l = -representativeFrequency p then 1 else 0)) +
    (c (realFourierIndexEquivFin N (some (p, true))) : ℂ) *
      (((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
        (if l = representativeFrequency p then 1 else 0) -
        ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
        (if l = -representativeFrequency p then 1 else 0))

theorem ProjectionCoefficients.realFourierFrameContribution_zero_of_positive_other (N : ℕ)
    (c : Coefficients (RealFourierDimension N))
    (p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (hpq : q ≠ p) :
    realFourierFrameCoefficientContribution N c (representativeFrequency p) q = 0 := by
  have hpos : representativeFrequency p ≠ representativeFrequency q := by
    intro h
    exact hpq (representativeFrequency_injective h.symm)
  have hneg : representativeFrequency p ≠ -representativeFrequency q :=
    representativeFrequency_ne_neg p q
  simp [realFourierFrameCoefficientContribution, hpos, hneg]

theorem ProjectionCoefficients.realFourierFrameContribution_zero_of_negative_other (N : ℕ)
    (c : Coefficients (RealFourierDimension N))
    (p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (hpq : q ≠ p) :
    realFourierFrameCoefficientContribution N c (-representativeFrequency p) q = 0 := by
  have hpos : -representativeFrequency p ≠ representativeFrequency q := by
    intro h
    have h' : representativeFrequency q = -representativeFrequency p := h.symm
    exact representativeFrequency_ne_neg q p h'
  have hneg : -representativeFrequency p ≠ -representativeFrequency q := by
    intro h
    have h' : representativeFrequency p = representativeFrequency q :=
      neg_injective h
    exact hpq (representativeFrequency_injective h').symm
  simp [realFourierFrameCoefficientContribution, hpos, hneg]

/-- Reindex the Fourier coefficient of a real frame expansion by its constant, cosine, and sine
modes. -/
theorem realFourierModeFin_mFourierCoeff_expansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x : ℂ)) l =
      (c (realFourierIndexEquivFin N none) : ℂ) * (if l = 0 then 1 else 0) +
        ∑ p, realFourierFrameCoefficientContribution N c l p := by
  let e := realFourierIndexEquivFin N
  have hmode : ∀ i, Continuous (realFourierModeFin N i) :=
    realFourierModeFin_continuous N
  rw [mFourierCoeff_modeExpansion (RealFourierDimension N)
    (realFourierModeFin N) c l hmode]
  rw [← Equiv.sum_comp e
    (fun i => (c i : ℂ) *
      UnitAddTorus.mFourierCoeff (fun x => (realFourierModeFin N i x : ℂ)) l)]
  have hmodeCast (a : RealFourierIndex N) :
      (fun x => (realFourierModeFin N (e a) x : ℂ)) =
        fun x => (realFourierMode N a x : ℂ) := by
    funext x
    simp [realFourierModeFin, e]
  change (∑ a : Option
      ({p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} × Bool),
        (c (e a) : ℂ) *
          UnitAddTorus.mFourierCoeff
            (fun x => (realFourierModeFin N (e a) x : ℂ)) l) = _
  rw [Fintype.sum_option]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  simp_rw [hmodeCast, realFourierMode_const_fourierCoeff,
    realFourierMode_cos_fourierCoeff, realFourierMode_sin_fourierCoeff]
  simp only [mul_ite, mul_one, mul_zero, Finset.univ_eq_attach, Complex.ofReal_div,
      Complex.ofReal_ofNat,
    mul_neg, realFourierFrameCoefficientContribution, add_right_inj, e]
  apply Finset.sum_congr rfl
  intro p hp
  ring_nf

theorem ProjectionCoefficients.integrable_mFourier_mul_of_integrable_real {f : Torus → ℝ}
    (hf : Integrable f (volume : Measure Torus)) (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => UnitAddTorus.mFourier (-k) x * (f x : ℂ)) volume := by
  have hchar : AEStronglyMeasurable (UnitAddTorus.mFourier (-k)) volume :=
    (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure Torus),
      ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
    filter_upwards with x
    calc
      ‖UnitAddTorus.mFourier (-k) x‖ ≤ ‖UnitAddTorus.mFourier (-k)‖ :=
        ContinuousMap.norm_coe_le_norm _ _
      _ = 1 := UnitAddTorus.mFourier_norm
  exact (hf.ofReal).bdd_mul hchar hbound

/-- The cosine coefficient of real data is the real part of its complex Fourier coefficient. -/
theorem realFourierMode_projectionCoefficient_cos (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    ∫ x : Torus, f x * realFourierMode N (some (p, false)) x =
      Real.sqrt 2 *
        (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ))
          (representativeFrequency p)).re := by
  let k := representativeFrequency p
  let coeff := UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k
  have hcoeff : Integrable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x * (f x : ℂ)) volume :=
    ProjectionCoefficients.integrable_mFourier_mul_of_integrable_real hf k
  have hreal : coeff.re = ∫ x : Torus,
      (UnitAddTorus.mFourier (-k) x * (f x : ℂ)).re := by
    dsimp [coeff, UnitAddTorus.mFourierCoeff]
    exact (Complex.reCLM.integral_comp_comm hcoeff).symm
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier (-k) x * (f x : ℂ)).re =
        f x * (UnitAddTorus.mFourier k x).re := by
    intro x
    rw [UnitAddTorus.mFourier_neg]
    simp [Complex.mul_re]
    ring
  have hmode : realFourierMode N (some (p, false)) =
      fun x => Real.sqrt 2 * (UnitAddTorus.mFourier k x).re := by
    funext x
    simp [realFourierMode, k]
  calc
    _ = Real.sqrt 2 * ∫ x : Torus,
          f x * (UnitAddTorus.mFourier k x).re := by
      rw [hmode]
      rw [show (fun x : Torus => f x *
          (Real.sqrt 2 * (UnitAddTorus.mFourier k x).re)) =
          fun x => Real.sqrt 2 * (f x * (UnitAddTorus.mFourier k x).re) by
        funext x
        ring]
      exact integral_const_mul _ _
    _ = Real.sqrt 2 * coeff.re := by
      rw [hreal]
      congr 1
      exact (integral_congr_ae (Filter.Eventually.of_forall hpoint)).symm

/-- The sine coefficient of real data is minus the imaginary part of its complex Fourier
coefficient. -/
theorem realFourierMode_projectionCoefficient_sin (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    ∫ x : Torus, f x * realFourierMode N (some (p, true)) x =
      -Real.sqrt 2 *
        (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ))
          (representativeFrequency p)).im := by
  let k := representativeFrequency p
  let coeff := UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k
  have hcoeff : Integrable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x * (f x : ℂ)) volume :=
    ProjectionCoefficients.integrable_mFourier_mul_of_integrable_real hf k
  have himag : coeff.im = ∫ x : Torus,
      (UnitAddTorus.mFourier (-k) x * (f x : ℂ)).im := by
    dsimp [coeff, UnitAddTorus.mFourierCoeff]
    exact (Complex.imCLM.integral_comp_comm hcoeff).symm
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier (-k) x * (f x : ℂ)).im =
        -(f x * (UnitAddTorus.mFourier k x).im) := by
    intro x
    rw [UnitAddTorus.mFourier_neg]
    simp [Complex.mul_im]
    ring
  have hmode : realFourierMode N (some (p, true)) =
      fun x => Real.sqrt 2 * (UnitAddTorus.mFourier k x).im := by
    funext x
    simp [realFourierMode, k]
  have hInt : ∫ x : Torus,
      (UnitAddTorus.mFourier (-k) x * (f x : ℂ)).im =
        -(∫ x : Torus, f x * (UnitAddTorus.mFourier k x).im) := by
    calc
      _ = ∫ x : Torus, -(f x * (UnitAddTorus.mFourier k x).im) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by rw [integral_neg]
  calc
    _ = Real.sqrt 2 * ∫ x : Torus,
          f x * (UnitAddTorus.mFourier k x).im := by
      rw [hmode]
      rw [show (fun x : Torus => f x *
          (Real.sqrt 2 * (UnitAddTorus.mFourier k x).im)) =
          fun x => Real.sqrt 2 * (f x * (UnitAddTorus.mFourier k x).im) by
        funext x
        ring]
      exact integral_const_mul _ _
    _ = -Real.sqrt 2 * coeff.im := by
      rw [himag]
      rw [hInt]
      ring

/-- The coefficient assigned to the constant mode is the mean of the initial datum. -/
theorem realFourierModeFin_projectionCoefficient_const (N : ℕ)
    {f : Torus → ℝ} (_hf : Integrable f (volume : Measure Torus)) :
    (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f)
      (realFourierIndexEquivFin N none) = ∫ x : Torus, f x := by
  change (∫ x : Torus, f x *
      realFourierModeFin N (realFourierIndexEquivFin N none) x) = _
  have hmode : realFourierModeFin N (realFourierIndexEquivFin N none) =
      realFourierMode N none := by
    funext x
    simp [realFourierModeFin, realFourierIndexEquivFin]
  rw [hmode]
  simp [realFourierMode]

/-- The cosine coefficient assigned by real projection agrees with the real part of the complex
Fourier coefficient. -/
theorem realFourierModeFin_projectionCoefficient_cos (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f)
      (realFourierIndexEquivFin N (some (p, false))) =
      Real.sqrt 2 *
        (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ))
          (representativeFrequency p)).re := by
  change (∫ x : Torus, f x *
      realFourierModeFin N (realFourierIndexEquivFin N (some (p, false))) x) = _
  have hmode : realFourierModeFin N (realFourierIndexEquivFin N (some (p, false))) =
      realFourierMode N (some (p, false)) := by
    funext x
    simp [realFourierModeFin, realFourierIndexEquivFin]
  rw [hmode]
  exact realFourierMode_projectionCoefficient_cos N hf p

/-- The sine coefficient assigned by real projection agrees with minus the imaginary part of the
complex Fourier coefficient. -/
theorem realFourierModeFin_projectionCoefficient_sin (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f)
      (realFourierIndexEquivFin N (some (p, true))) =
      -Real.sqrt 2 *
        (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ))
          (representativeFrequency p)).im := by
  change (∫ x : Torus, f x *
      realFourierModeFin N (realFourierIndexEquivFin N (some (p, true))) x) = _
  have hmode : realFourierModeFin N (realFourierIndexEquivFin N (some (p, true))) =
      realFourierMode N (some (p, true)) := by
    funext x
    simp [realFourierModeFin, realFourierIndexEquivFin]
  rw [hmode]
  exact realFourierMode_projectionCoefficient_sin N hf p

/-- The zero Fourier coefficient of real data is its real integral. -/
theorem mFourierCoeff_real_zero_integral {f : Torus → ℝ}
    (hf : Integrable f (volume : Measure Torus)) :
    UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) 0 =
      (∫ x : Torus, f x : ℝ) := by
  have hzero : UnitAddTorus.mFourier (0 : Fin 2 → ℤ) =
      (1 : C(Torus, ℂ)) := UnitAddTorus.mFourier_zero
  change (∫ x : Torus,
      UnitAddTorus.mFourier (-(0 : Fin 2 → ℤ)) x * (f x : ℂ)) = _
  rw [neg_zero, hzero]
  simpa using (Complex.ofRealCLM.integral_comp_comm hf)

/-- For integrable real data, the real sine/cosine projection has the same Fourier coefficients
as the datum throughout its cutoff. This is the finite-dimensional initial trace identity used by
the positive-cutoff Galerkin ODE. -/
theorem realFourierModeFin_projectionExpansion_fourierCoeff_zero (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus)) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f) x : ℂ))
        0 = UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) 0 := by
  rw [realFourierModeFin_mFourierCoeff_expansion]
  have hconst := realFourierModeFin_projectionCoefficient_const N hf
  have hcoef := mFourierCoeff_real_zero_integral hf
  have hfreq (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
      representativeFrequency p ≠ 0 := representativeFrequency_ne_zero p
  have hfreq0 (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
      0 ≠ representativeFrequency p := Ne.symm (hfreq p)
  simp [hconst, hcoef, hfreq, hfreq0, realFourierFrameCoefficientContribution]

/-- The real sine/cosine projection preserves each positive representative's complex Fourier
coefficient. -/
theorem realFourierModeFin_projectionExpansion_fourierCoeff_positive (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f) x : ℂ))
        (representativeFrequency p) =
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) (representativeFrequency p) := by
  classical
  let c := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  let a := UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) (representativeFrequency p)
  have hcos := realFourierModeFin_projectionCoefficient_cos N hf p
  have hsin := realFourierModeFin_projectionCoefficient_sin N hf p
  have hfreq : representativeFrequency p ≠ 0 := representativeFrequency_ne_zero p
  have hsum : (∑ q : {q : ℤ × ℤ // q ∈ positiveFrequencyRepresentatives N},
      realFourierFrameCoefficientContribution N c (representativeFrequency p) q) =
      realFourierFrameCoefficientContribution N c (representativeFrequency p) p := by
    calc
      _ = ∑ q, if q = p then
            realFourierFrameCoefficientContribution N c (representativeFrequency p) p
          else 0 := by
        apply Fintype.sum_congr
        intro q
        by_cases hqp : q = p
        · simp [hqp]
        · simp [ProjectionCoefficients.realFourierFrameContribution_zero_of_positive_other N c p q
            hqp, hqp]
      _ = _ := by simp [eq_comm]
  rw [realFourierModeFin_mFourierCoeff_expansion]
  simp only [ite_eq_right hfreq, mul_zero]
  rw [hsum]
  simp only [realFourierFrameCoefficientContribution]
  have hidxCos : c (realFourierIndexEquivFin N (some (p, false))) =
      Real.sqrt 2 * a.re := by
    simpa [c, a] using hcos
  have hidxSin : c (realFourierIndexEquivFin N (some (p, true))) =
      -Real.sqrt 2 * a.im := by
    simpa [c, a] using hsin
  rw [hidxCos, hidxSin]
  have hnotneg : representativeFrequency p ≠ -representativeFrequency p :=
    representativeFrequency_ne_neg p p
  simp only [ite_eq_right hnotneg, ite_true, mul_zero, add_zero, sub_zero]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hscale : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    calc
      Real.sqrt 2 * (Real.sqrt 2 / 2) = (Real.sqrt 2 ^ 2) / 2 := by ring
      _ = 2 / 2 := by rw [hsqrt]
      _ = 1 := by norm_num
  apply Complex.ext
  · simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_one, neg_mul,
      Complex.ofReal_neg,
      mul_neg, neg_neg, zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero,
      sub_zero, Complex.div_ofNat_re, Complex.mul_im, zero_mul, add_zero, Complex.div_ofNat_im,
          zero_div, Complex.I_re,
      Complex.I_im, sub_self]
    change Real.sqrt 2 * a.re * (Real.sqrt 2 / 2) = a.re
    calc
      _ = a.re * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by ring
      _ = a.re := by rw [hscale]; ring
  · simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_one, neg_mul,
      Complex.ofReal_neg,
      mul_neg, neg_neg, zero_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.div_ofNat_im, zero_div, zero_mul, add_zero,
          Complex.div_ofNat_re, Complex.I_im,
      Complex.I_re, sub_self]
    change Real.sqrt 2 * a.im * (Real.sqrt 2 / 2) = a.im
    calc
      _ = a.im * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by ring
      _ = a.im := by rw [hscale]; ring

/-- The real sine/cosine projection preserves the negative-frequency coefficient by conjugation. -/
theorem realFourierModeFin_projectionExpansion_fourierCoeff_negative (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f) x : ℂ))
        (-representativeFrequency p) =
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) (-representativeFrequency p) := by
  classical
  let c := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  let a := UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) (representativeFrequency p)
  have hcos := realFourierModeFin_projectionCoefficient_cos N hf p
  have hsin := realFourierModeFin_projectionCoefficient_sin N hf p
  have hfreq : -representativeFrequency p ≠ 0 := neg_ne_zero.mpr
    (representativeFrequency_ne_zero p)
  have hsum : (∑ q : {q : ℤ × ℤ // q ∈ positiveFrequencyRepresentatives N},
      realFourierFrameCoefficientContribution N c (-representativeFrequency p) q) =
      realFourierFrameCoefficientContribution N c (-representativeFrequency p) p := by
    calc
      _ = ∑ q, if q = p then
            realFourierFrameCoefficientContribution N c (-representativeFrequency p) p
          else 0 := by
        apply Fintype.sum_congr
        intro q
        by_cases hqp : q = p
        · simp [hqp]
        · simp [ProjectionCoefficients.realFourierFrameContribution_zero_of_negative_other N c p q
            hqp, hqp]
      _ = _ := by simp [eq_comm]
  rw [realFourierModeFin_mFourierCoeff_expansion]
  simp only [ite_eq_right hfreq, mul_zero]
  rw [hsum]
  simp only [realFourierFrameCoefficientContribution]
  have hidxCos : c (realFourierIndexEquivFin N (some (p, false))) =
      Real.sqrt 2 * a.re := by
    simpa [c, a] using hcos
  have hidxSin : c (realFourierIndexEquivFin N (some (p, true))) =
      -Real.sqrt 2 * a.im := by
    simpa [c, a] using hsin
  rw [hidxCos, hidxSin]
  have hnotpos : -representativeFrequency p ≠ representativeFrequency p := by
    intro h
    exact representativeFrequency_ne_neg p p h.symm
  simp only [ite_eq_right hnotpos, ite_true, mul_zero]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hscale : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    calc
      Real.sqrt 2 * (Real.sqrt 2 / 2) = (Real.sqrt 2 ^ 2) / 2 := by ring
      _ = 2 / 2 := by rw [hsqrt]
      _ = 1 := by norm_num
  rw [mFourierCoeff_real_neg f (representativeFrequency p)]
  apply Complex.ext
  · simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_one, zero_add,
      neg_mul,
      Complex.ofReal_neg, mul_neg, sub_neg_eq_add, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.div_ofNat_re, Complex.mul_im, zero_mul, add_zero,
          Complex.div_ofNat_im, zero_div,
      Complex.neg_re, Complex.I_re, Complex.I_im, sub_self, neg_zero, RCLike.star_def,
          Complex.conj_re]
    change Real.sqrt 2 * a.re * (Real.sqrt 2 / 2) = a.re
    calc
      _ = a.re * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by ring
      _ = a.re := by rw [hscale]; ring
  · simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_one, zero_add,
      neg_mul,
      Complex.ofReal_neg, mul_neg, sub_neg_eq_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
          Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.div_ofNat_im, zero_div, zero_mul, add_zero,
          Complex.div_ofNat_re,
      Complex.neg_im, Complex.I_im, Complex.I_re, sub_self, RCLike.star_def, Complex.conj_im,
          neg_inj]
    change Real.sqrt 2 * a.im * (Real.sqrt 2 / 2) = a.im
    calc
      _ = a.im * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by ring
      _ = a.im := by rw [hscale]; ring

/-- Every Fourier coefficient in the symmetric cutoff is preserved by the real-mode projection. -/
theorem realFourierModeFin_projectionExpansion_fourierCoeff (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (l : Fin 2 → ℤ) (hl : frequencyPair l ∈ symmetricFrequencyBox N) :
    UnitAddTorus.mFourierCoeff
        (fun x => (modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f) x : ℂ)) l =
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) l := by
  rcases (frequencyBox_partition N (frequencyPair l)).mp hl with hzero | hpos | hneg
  · have hlzero : l = 0 := by
      have hrec : pairFrequency (frequencyPair l) = l := pairFrequency_frequencyPair l
      have hpairzero : pairFrequency (0, 0) = (0 : Fin 2 → ℤ) := by
        funext i
        fin_cases i <;> simp [pairFrequency]
      calc
        l = pairFrequency (frequencyPair l) := hrec.symm
        _ = pairFrequency (0, 0) := congrArg pairFrequency hzero
        _ = 0 := hpairzero
    subst l
    exact realFourierModeFin_projectionExpansion_fourierCoeff_zero N hf
  · let q : {q : ℤ × ℤ // q ∈ positiveFrequencyRepresentatives N} :=
      ⟨frequencyPair l, hpos⟩
    have hlpos : l = representativeFrequency q := by
      calc
        l = pairFrequency (frequencyPair l) := (pairFrequency_frequencyPair l).symm
        _ = pairFrequency q.1 := rfl
        _ = representativeFrequency q := rfl
    rw [hlpos]
    exact realFourierModeFin_projectionExpansion_fourierCoeff_positive N hf q
  · let q : {q : ℤ × ℤ // q ∈ positiveFrequencyRepresentatives N} :=
      ⟨-frequencyPair l, hneg⟩
    have hlneg : l = -representativeFrequency q := by
      calc
        l = pairFrequency (frequencyPair l) := (pairFrequency_frequencyPair l).symm
        _ = pairFrequency (-q.1) := by simp [q]
        _ = -pairFrequency q.1 := pairFrequency_neg q.1
        _ = -representativeFrequency q := rfl
    rw [hlneg]
    exact realFourierModeFin_projectionExpansion_fourierCoeff_negative N hf q

/-- The real projection coefficients reconstruct the finite Fourier projection of arbitrary
integrable real data. The proof identifies every coefficient in the symmetric cutoff, including
both signs of each nonzero frequency. -/
theorem realFourierModeFin_projectionExpansion_eq_projection (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus)) :
    modeExpansion (RealFourierDimension N) (realFourierModeFin N)
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f) =
      realFourierProjection N f := by
  classical
  funext x
  let c := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  have hsum : complexFourierPartialSumComplex N
      (fun y => (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c y : ℂ)) x =
      complexFourierPartialSum N f x := by
    unfold complexFourierPartialSumComplex complexFourierPartialSum
    apply Finset.sum_congr rfl
    intro p hp
    have hpair : frequencyPair (pairFrequency p) = p := by
      rcases p with ⟨a, b⟩
      apply Prod.ext <;> simp [frequencyPair, pairFrequency]
    have hcoeff := realFourierModeFin_projectionExpansion_fourierCoeff N hf
      (pairFrequency p) (by simpa [hpair] using hp)
    rw [hcoeff]
  have hexp := congrFun (realFourierProjection_complexification N
    (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c)) x
  have hfproj := congrFun (realFourierProjection_complexification N f) x
  have hsum' : complexFourierPartialSum N
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) x =
      complexFourierPartialSum N f x := by
    simpa [complexFourierPartialSumComplex, complexFourierPartialSum] using hsum
  have hcomplex :
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x : ℂ) =
        (realFourierProjection N f x : ℂ) := by
    calc
      _ = (realFourierProjection N
          (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) x : ℂ) := by
            rw [realFourierProjection_modeExpansion]
      _ = complexFourierPartialSum N
          (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) x := hexp
      _ = complexFourierPartialSum N f x := hsum'
      _ = _ := hfproj.symm
  exact_mod_cast congrArg Complex.re hcomplex

end AVenhance.Infra.Parabolic.FourierGalerkin

end
