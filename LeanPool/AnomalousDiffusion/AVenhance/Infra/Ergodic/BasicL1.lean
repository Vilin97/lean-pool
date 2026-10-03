/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Periodic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Fourier coefficient bounds for the basic ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open MeasureTheory

noncomputable section

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicBasicL1MeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩

local instance avInfraErgodicBasicL1MeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance avInfraErgodicBasicL1IsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem BasicL1.integrable_mul_continuousMap {d : ℕ} {g : UnitTorus d → ℂ}
    (hg : Integrable g) (f : C(UnitTorus d, ℂ)) : Integrable (fun x => g x * f x) := by
  have hg' : IntegrableOn g Set.univ volume := by simpa [IntegrableOn] using hg
  simpa [IntegrableOn, mul_comm] using
    hg'.continuousOn_mul f.continuous.continuousOn isCompact_univ

/-- Pair an integrable torus function with a continuous test function, linearly in the test. -/
def BasicL1.pairingLinearMap {d : ℕ} (g : UnitTorus d → ℂ) (hg : Integrable g) :
    C(UnitTorus d, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, g x * f x
  map_add' f h := by
    simp only [ContinuousMap.add_apply, mul_add]
    rw [integral_add (BasicL1.integrable_mul_continuousMap hg f)
      (BasicL1.integrable_mul_continuousMap hg h)]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    calc
      ∫ x, g x * (c * f x) = ∫ x, c * (g x * f x) := by
        congr 1
        funext x
        ring
      _ = c * ∫ x, g x * f x := integral_const_mul c _

/-- Continuous linear form obtained by pairing with an integrable torus function. -/
def BasicL1.pairingContinuousLinearMap {d : ℕ} (g : UnitTorus d → ℂ)
    (hg : Integrable g) : C(UnitTorus d, ℂ) →L[ℂ] ℂ :=
  (BasicL1.pairingLinearMap g hg).mkContinuous (∫ x, ‖g x‖) fun f => by
    calc
      ‖BasicL1.pairingLinearMap g hg f‖ = ‖∫ x, g x * f x‖ := rfl
      _ ≤ ∫ x, ‖g x * f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖g x‖ * ‖f‖ := by
        apply integral_mono
        · exact (BasicL1.integrable_mul_continuousMap hg f).norm
        · simpa [mul_comm] using hg.norm.const_mul ‖f‖
        · intro x
          change ‖g x * f x‖ ≤ ‖g x‖ * ‖f‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖g x‖) * ‖f‖ := by rw [integral_mul_const]

theorem BasicL1.pairing_apply_fourierTerm {d : ℕ} (g : UnitTorus d → ℂ)
    (hg : Integrable g) (a : ℂ) (k : Fin d → ℤ) :
    BasicL1.pairingContinuousLinearMap g hg (a • UnitAddTorus.mFourier k) =
      a * UnitAddTorus.mFourierCoeff g (-k) := by
  change (∫ x, g x * (a * UnitAddTorus.mFourier k x)) = _
  rw [show (fun x => g x * (a * UnitAddTorus.mFourier k x)) =
      (fun x => a * (UnitAddTorus.mFourier k x * g x)) by
        funext x
        ring]
  rw [integral_const_mul]
  simp [UnitAddTorus.mFourierCoeff, smul_eq_mul]

/-- Integrating a Fourier series against an `L¹` function gives the usual
coefficient pairing. -/
theorem hasSum_integral_mul_fourierCoeff {d : ℕ}
    (f : C(UnitTorus d, ℂ)) (g : UnitTorus d → ℂ) (hg : Integrable g)
    (hf : Summable (UnitAddTorus.mFourierCoeff f)) :
    HasSum
      (fun k => UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourierCoeff g (-k))
      (∫ x, f x * g x) := by
  have hseries := UnitAddTorus.hasSum_mFourier_series_of_summable hf
  have hpair := (BasicL1.pairingContinuousLinearMap g hg).hasSum hseries
  have hterms : ∀ k : Fin d → ℤ,
      UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourierCoeff g (-k) =
        BasicL1.pairingContinuousLinearMap g hg
          (UnitAddTorus.mFourierCoeff f k • UnitAddTorus.mFourier k) := by
    intro k
    exact (BasicL1.pairing_apply_fourierTerm g hg _ k).symm
  have hintegral : (∫ x, g x * f x) = ∫ x, f x * g x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [← hintegral]
  exact hpair.congr_fun hterms

/-- A Fourier coefficient of an integrable function is bounded by its `L¹`
norm on the normalized torus. -/
theorem mFourierCoeff_norm_le_integral_norm {d : ℕ}
    (g : UnitTorus d → ℂ) (k : Fin d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff g k‖ ≤ ∫ x, ‖g x‖ := by
  unfold UnitAddTorus.mFourierCoeff
  calc
    ‖∫ x, UnitAddTorus.mFourier (-k) x • g x‖ ≤
        ∫ x, ‖UnitAddTorus.mFourier (-k) x • g x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [UnitAddTorus.mFourier]

/-- A translation-invariant function has zero Fourier coefficient whenever
the character is nontrivial on the translation. -/
theorem mFourierCoeff_eq_zero_of_translation_invariant {d : ℕ}
    (g : UnitTorus d → ℂ) (k : Fin d → ℤ) (a : UnitTorus d)
    (hga : ∀ x, g (x + a) = g x)
    (hchar : UnitAddTorus.mFourier (-k) a ≠ 1) :
    UnitAddTorus.mFourierCoeff g k = 0 := by
  let χ := UnitAddTorus.mFourier (-k) a
  have htrans := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure (UnitTorus d)))
    (fun x : UnitTorus d => UnitAddTorus.mFourier (-k) x * g x) a
  have hchar_add (x : UnitTorus d) :
      UnitAddTorus.mFourier (-k) (x + a) =
        UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier (-k) a := by
    change (∏ j : Fin d, fourier (-k j) ((x + a) j)) =
      (∏ j : Fin d, fourier (-k j) (x j)) *
        (∏ j : Fin d, fourier (-k j) (a j))
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    change fourier (-k j) (x j + a j) = _
    rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add]
    exact Circle.coe_mul _ _
  have hfactor :
      (∫ x : UnitTorus d, UnitAddTorus.mFourier (-k) (x + a) * g (x + a)) =
        χ * ∫ x : UnitTorus d, UnitAddTorus.mFourier (-k) x * g x := by
    calc
      _ = ∫ x : UnitTorus d,
          χ * (UnitAddTorus.mFourier (-k) x * g x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hga x, hchar_add]
        dsimp [χ]
        ring
      _ = χ * ∫ x : UnitTorus d, UnitAddTorus.mFourier (-k) x * g x :=
        integral_const_mul χ _
  have hcoeff : UnitAddTorus.mFourierCoeff g k = χ *
      UnitAddTorus.mFourierCoeff g k := by
    unfold UnitAddTorus.mFourierCoeff
    simp only [smul_eq_mul]
    calc
      _ = ∫ x : UnitTorus d, UnitAddTorus.mFourier (-k) (x + a) * g (x + a) :=
        htrans.symm
      _ = χ * ∫ x : UnitTorus d, UnitAddTorus.mFourier (-k) x * g x := hfactor
      _ = _ := rfl
  have hmul : (χ - 1) * UnitAddTorus.mFourierCoeff g k = 0 := by
    calc
      (χ - 1) * UnitAddTorus.mFourierCoeff g k =
          χ * UnitAddTorus.mFourierCoeff g k - UnitAddTorus.mFourierCoeff g k := by ring
      _ = 0 := sub_eq_zero.mpr hcoeff.symm
  rcases mul_eq_zero.mp hmul with hχ | hgk
  · exact False.elim (hchar (sub_eq_zero.mp hχ))
  · exact hgk

/-- Fast-periodic torus functions have no coefficient at a character that is
nontrivial on a coordinate fast-period shift. -/
theorem mFourierCoeff_eq_zero_of_fastTorusShift {d N : ℕ}
    (g : UnitTorus d → ℂ) (k : Fin d → ℤ) (i : Fin d)
    (hg : ∀ x, g (x + fastTorusShift N i) = g x)
    (hchar : UnitAddTorus.mFourier (-k) (fastTorusShift N i) ≠ 1) :
    UnitAddTorus.mFourierCoeff g k = 0 :=
  mFourierCoeff_eq_zero_of_translation_invariant g k (fastTorusShift N i) hg hchar

theorem BasicL1.mFourier_fastTorusShift_formula {d N : ℕ} (hN : 0 < N)
    (k : Fin d → ℤ) (i : Fin d) :
    UnitAddTorus.mFourier (-k) (fastTorusShift N i) =
      Complex.exp (2 * Real.pi * Complex.I * (-(k i : ℤ) : ℂ) / (N : ℂ)) := by
  change (∏ j : Fin d, fourier (-k j) (fastTorusShift N i j)) = _
  rw [Finset.prod_eq_single i]
  · have hi : fastTorusShift N i i = ((1 : ℝ) / (N : ℝ) : UnitAddCircle) := by
      simp [fastTorusShift]
    rw [hi, fourier_coe_apply]
    congr 1
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
  · intro j hj hji
    have hzero : fastTorusShift N i j = 0 := by simp [fastTorusShift, hji]
    rw [hzero, fourier_eval_zero]
  · simp

theorem BasicL1.exp_two_pi_I_mul_int_div_eq_one_iff {n : ℤ} {N : ℕ} (hN : N ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) = 1 ↔
      (N : ℤ) ∣ n := by
  cases n with
  | ofNat n =>
      change Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) = 1 ↔
        (N : ℤ) ∣ (n : ℤ)
      rw [Int.natCast_dvd_natCast]
      exact Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
        (k := n) (N := N) hN
  | negSucc n =>
      have hpos := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
        (k := n + 1) (N := N) hN
      have harg : 2 * Real.pi * Complex.I * (Int.negSucc n : ℂ) / (N : ℂ) =
          -(2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) / (N : ℂ)) := by
        simp only [Int.negSucc_eq, Int.cast_neg, Int.cast_add, Int.cast_natCast]
        push_cast
        ring
      rw [harg, Complex.exp_neg, inv_eq_one, hpos, Int.natCast_dvd]
      simp [Int.natAbs_negSucc]

/-- A frequency lies in the sublattice `N ℤ^d`. -/
def IsFastFrequency {d : ℕ} (N : ℕ) (k : Fin d → ℤ) : Prop :=
  ∀ i, (N : ℤ) ∣ k i

instance fastFrequencyDecidable {d N : ℕ} (k : Fin d → ℤ) :
    Decidable (IsFastFrequency N k) := by
  unfold IsFastFrequency
  infer_instance

theorem BasicL1.hasSum_sub_single {ι : Type*} [DecidableEq ι]
    (i₀ : ι) {f : ι → ℂ} {s : ℂ} (hf : HasSum f s) :
    HasSum (fun k => if k = i₀ then 0 else f k) (s - f i₀) := by
  have hsingle : HasSum (fun k : ι => if k = i₀ then f i₀ else 0) (f i₀) :=
    hasSum_ite_eq i₀ (f i₀)
  have hsub := hf.sub hsingle
  have heq : (fun k => if k = i₀ then 0 else f k) =
      fun k => f k - (if k = i₀ then f i₀ else 0) := by
    funext k
    by_cases hk : k = i₀ <;> simp [hk]
  rw [heq]
  exact hsub

/-- A coefficient of an `N⁻¹`-periodic function vanishes at every frequency
whose selected coordinate is not divisible by `N`. -/
theorem mFourierCoeff_eq_zero_of_fastPeriod_not_dvd {d N : ℕ}
    {g : UnitTorus d → ℂ} (hN : 0 < N) (k : Fin d → ℤ) (i : Fin d)
    (hg : ∀ x, g (x + fastTorusShift N i) = g x)
    (hnot : ¬ (N : ℤ) ∣ k i) :
    UnitAddTorus.mFourierCoeff g k = 0 := by
  apply mFourierCoeff_eq_zero_of_fastTorusShift g k i hg
  intro hchar
  have hexp : Complex.exp
      (2 * Real.pi * Complex.I * (-(k i : ℤ) : ℂ) / (N : ℂ)) = 1 := by
    simpa [BasicL1.mFourier_fastTorusShift_formula hN k i] using hchar
  have hexp' : Complex.exp
      (2 * Real.pi * Complex.I * ((-(k i) : ℤ) : ℂ) / (N : ℂ)) = 1 := by
    simpa only [Int.cast_neg] using hexp
  have hdiv : (N : ℤ) ∣ -(k i) :=
    (BasicL1.exp_two_pi_I_mul_int_div_eq_one_iff hN.ne').mp hexp'
  apply hnot
  simpa using hdiv

/-- A function invariant under every coordinate fast-period shift has
Fourier support contained in the sublattice `N ℤ^d`. -/
theorem mFourierCoeff_eq_zero_of_not_fastFrequencyLattice {d N : ℕ}
    {g : UnitTorus d → ℂ} (hN : 0 < N) (k : Fin d → ℤ)
    (hg : ∀ i x, g (x + fastTorusShift N i) = g x)
    (hnot : ¬ ∀ i, (N : ℤ) ∣ k i) :
    UnitAddTorus.mFourierCoeff g k = 0 := by
  classical
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  exact mFourierCoeff_eq_zero_of_fastPeriod_not_dvd hN k i (hg i) hi

theorem BasicL1.mFourierCoeff_zero_eq_integral {d : ℕ}
    (f : UnitTorus d → ℂ) :
    UnitAddTorus.mFourierCoeff f (0 : Fin d → ℤ) = ∫ x, f x := by
  simp [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero]

/-- Fourier covariance bound from exponential coefficient decay and fast
frequency support. The lattice exponential tail is left explicit so callers
can use the sharp counting estimate appropriate to their dimension. -/
theorem torusCovariance_le_fourier_envelope {d N : ℕ}
    (F : C(UnitTorus d, ℂ)) (G : UnitTorus d → ℂ) (hG : Integrable G)
    (hF : Summable (UnitAddTorus.mFourierCoeff F))
    (A rate : ℝ) (hA : 0 ≤ A)
    (hdecay : ∀ k, k ≠ 0 → IsFastFrequency N k →
      ‖UnitAddTorus.mFourierCoeff F k‖ ≤ A * Real.exp (-rate * ‖k‖))
    (hzero : ∀ k, k ≠ 0 → ¬ IsFastFrequency N k →
      UnitAddTorus.mFourierCoeff G (-k) = 0)
    (htail : Summable (fun k : Fin d → ℤ =>
      if k = 0 then 0 else if IsFastFrequency N k then
        Real.exp (-rate * ‖k‖) else 0)) :
    ‖(∫ x, F x * G x) - (∫ x, F x) * (∫ x, G x)‖ ≤
      A * (∫ x, ‖G x‖) *
        ∑' k : Fin d → ℤ,
          if k = 0 then 0 else if IsFastFrequency N k then
            Real.exp (-rate * ‖k‖) else 0 := by
  classical
  let a : (Fin d → ℤ) → ℂ := fun k =>
    UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourierCoeff G (-k)
  let b : (Fin d → ℤ) → ℂ := fun k => if k = 0 then 0 else a k
  let tail : (Fin d → ℤ) → ℝ := fun k =>
    if k = 0 then 0 else if IsFastFrequency N k then Real.exp (-rate * ‖k‖) else 0
  have hpair := hasSum_integral_mul_fourierCoeff F G hG hF
  have ha0 : a 0 = (∫ x, F x) * (∫ x, G x) := by
    simp [a, BasicL1.mFourierCoeff_zero_eq_integral]
  have hb : HasSum b ((∫ x, F x * G x) - a 0) := by
    have hpa : HasSum a (∫ x, F x * G x) := by simpa [a] using hpair
    have hb' := BasicL1.hasSum_sub_single (0 : Fin d → ℤ) hpa
    simpa [b, a] using hb'
  have hnorm : Summable (fun k : Fin d → ℤ => ‖b k‖) := hb.summable.norm
  have htailScaled : Summable (fun k : Fin d → ℤ =>
      (A * ∫ x, ‖G x‖) * tail k) := htail.mul_left _
  have hterm : ∀ k : Fin d → ℤ, ‖b k‖ ≤
      (A * ∫ x, ‖G x‖) * tail k := by
    intro k
    by_cases hk0 : k = 0
    · simp [b, tail, hk0]
    · by_cases hlat : IsFastFrequency N k
      · simp only [b, hk0, ite_false, tail, hlat, ite_true]
        rw [norm_mul]
        calc
          ‖UnitAddTorus.mFourierCoeff F k‖ *
              ‖UnitAddTorus.mFourierCoeff G (-k)‖ ≤
              (A * Real.exp (-rate * ‖k‖)) * ∫ x, ‖G x‖ :=
            mul_le_mul (hdecay k hk0 hlat) (mFourierCoeff_norm_le_integral_norm G (-k))
              (norm_nonneg _) (mul_nonneg hA (Real.exp_nonneg _))
          _ = (A * ∫ x, ‖G x‖) * Real.exp (-rate * ‖k‖) := by ring
      · have hz := hzero k hk0 hlat
        simp [a, b, tail, hk0, hlat, hz]
  have htsum := Summable.tsum_mono hnorm htailScaled hterm
  have hcov : (∫ x, F x * G x) - (∫ x, F x) * (∫ x, G x) = ∑' k, b k := by
    calc
      _ = (∫ x, F x * G x) - a 0 := by rw [ha0]
      _ = ∑' k, b k := hb.tsum_eq.symm
  calc
    _ = ‖∑' k : Fin d → ℤ, b k‖ := by rw [hcov]
    _ ≤ ∑' k : Fin d → ℤ, ‖b k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : Fin d → ℤ, (A * ∫ x, ‖G x‖) * tail k := htsum
    _ = A * (∫ x, ‖G x‖) * ∑' k : Fin d → ℤ, tail k := by
      rw [tsum_mul_left]
    _ = _ := by rfl

end

end AVenhance.Infra.Ergodic
