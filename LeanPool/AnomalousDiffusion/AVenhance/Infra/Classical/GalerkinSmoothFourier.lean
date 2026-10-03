/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.SmoothClassical
public import Mathlib.Analysis.PSeries

/-! Fourier coefficient bounds for the all-order Galerkin limits. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothFourierMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothFourierMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothFourierProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalSmoothFourierOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace AVenhance.Infra.Classical

/-- Every Fourier coefficient of a derivative limit is uniformly bounded in time by its `L²`
bound. -/
theorem classicalGalerkinWordLimitFourierCoeffPath_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc (0 : ℝ) 1,
      ∀ k : Fin 2 → ℤ,
        ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k t‖ ≤ C := by
  obtain ⟨C, hC, hL2⟩ := classicalGalerkinWordScalarPathLimit_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
  refine ⟨C, hC, ?_⟩
  intro t k
  change ‖classicalComplexFourierCoeffCLM k
      (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w t)‖ ≤ C
  rw [classicalComplexFourierCoeffCLM_apply]
  exact (classicalComplexFourierCoeff_norm_le
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t)) k).trans
    ((classicalRealToComplexTorusCLM_norm_le _).trans (hL2 t))

theorem GalerkinSmoothFourier.classicalScaledIntegerFrequencyWeight_summable :
    Summable (fun n : ℤ => (1 + 2 * Real.pi * |(n : ℝ)|) ^ (-(2 : ℝ))) := by
  have hbase := Real.summable_abs_int_rpow (b := (2 : ℝ)) (by norm_num)
  have hzero : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    change {n : ℤ | (if n = 0 then (1 : ℝ) else 0) ≠ 0}.Finite
    exact (Set.finite_singleton (0 : ℤ)).subset (by
      intro n hn
      by_contra hn0
      simp [hn0] at hn)
  apply Summable.of_norm_bounded (hbase.add hzero)
  intro n
  have hnonneg : 0 ≤ (1 + 2 * Real.pi * |(n : ℝ)|) ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg hnonneg]
  by_cases hn : n = 0
  · simp [hn]
  · have hcast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have habs : 0 < |(n : ℝ)| := abs_pos.mpr hcast
    have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hbaseDen : |(n : ℝ)| ≤ 1 + 2 * Real.pi * |(n : ℝ)| := by
      nlinarith [abs_nonneg (n : ℝ)]
    have hpow : (1 + 2 * Real.pi * |(n : ℝ)|) ^ (-(2 : ℝ)) ≤
        |(n : ℝ)| ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (le_of_lt habs)]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      exact Real.rpow_le_rpow (le_of_lt habs) hbaseDen (by norm_num)
    have hnorm : ‖|(n : ℝ)| ^ (-(2 : ℝ))‖ = |(n : ℝ)| ^ (-(2 : ℝ)) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    simpa [hn, hnorm] using hpow

theorem classicalScaledTorusFrequencyWeight_summable :
    Summable (fun k : Fin 2 → ℤ =>
      (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (-(2 : ℝ)) *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (-(2 : ℝ))) := by
  let w : ℤ → ℝ := fun n => (1 + 2 * Real.pi * |(n : ℝ)|) ^ (-(2 : ℝ))
  have hw := GalerkinSmoothFourier.classicalScaledIntegerFrequencyWeight_summable
  have hwpos (n : ℤ) : 0 ≤ w n := Real.rpow_nonneg (by positivity) _
  have hpairs : Summable (fun q : ℤ × ℤ => w q.1 * w q.2) :=
    hw.mul_of_nonneg hw hwpos hwpos
  have hfreq := (finTwoArrowEquiv ℤ).summable_iff.mpr hpairs
  simpa [w, finTwoArrowEquiv, Function.comp_def] using hfreq

/-- Summable product weight controlling the two-dimensional Fourier tail. -/
def classicalScaledTorusFrequencyWeight (k : Fin 2 → ℤ) : ℝ :=
  (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (-(2 : ℝ)) *
    (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (-(2 : ℝ))

theorem GalerkinSmoothFourier.classicalScaledTorusFrequencyWeight_eq_inv (k : Fin 2 → ℤ) :
    classicalScaledTorusFrequencyWeight k =
      ((1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ 2 *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ 2)⁻¹ := by
  have h0 : (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (-(2 : ℝ)) =
      ((1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 2)
  have h1 : (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (-(2 : ℝ)) =
      ((1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 2)
  rw [classicalScaledTorusFrequencyWeight, h0, h1, ← mul_inv]

theorem classicalWeightedCoeff_frequencyPower_le
    (n : ℕ) (x y a C : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hweight : (1 + x) ^ (n + 2) * (1 + y) ^ (n + 2) * a ≤ C) :
    a * (x + y) ^ n ≤ C *
      ((1 + x) ^ (-(2 : ℝ)) * (1 + y) ^ (-(2 : ℝ))) := by
  let D : ℝ := (1 + x) ^ 2 * (1 + y) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : x + y ≤ (1 + x) * (1 + y) := by nlinarith [mul_nonneg hx hy]
  have hpow : (x + y) ^ n ≤ (1 + x) ^ n * (1 + y) ^ n := by
    calc
      (x + y) ^ n ≤ ((1 + x) * (1 + y)) ^ n := by gcongr
      _ = (1 + x) ^ n * (1 + y) ^ n := by rw [mul_pow]
  have hsmall : a * (x + y) ^ n ≤ a * (1 + x) ^ n * (1 + y) ^ n := by
    calc
      _ ≤ a * ((1 + x) ^ n * (1 + y) ^ n) := mul_le_mul_of_nonneg_left hpow ha
      _ = _ := by ring
  have hscale : a * (x + y) ^ n * D ≤ C := by
    calc
      _ ≤ a * (1 + x) ^ n * (1 + y) ^ n * D :=
        mul_le_mul_of_nonneg_right hsmall (le_of_lt hD)
      _ = (1 + x) ^ (n + 2) * (1 + y) ^ (n + 2) * a := by
        dsimp [D]
        rw [pow_add, pow_add]
        ring
      _ ≤ C := hweight
  have hdiv : a * (x + y) ^ n ≤ C / D := (le_div_iff₀ hD).2 hscale
  have hDweight : (1 + x) ^ (-(2 : ℝ)) * (1 + y) ^ (-(2 : ℝ)) = D⁻¹ := by
    have h0 : (1 + x) ^ (-(2 : ℝ)) = ((1 + x) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      exact congrArg Inv.inv (Real.rpow_natCast _ 2)
    have h1 : (1 + y) ^ (-(2 : ℝ)) = ((1 + y) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      exact congrArg Inv.inv (Real.rpow_natCast _ 2)
    rw [h0, h1]
    dsimp [D]
    rw [← mul_inv]
  calc
    a * (x + y) ^ n ≤ C / D := hdiv
    _ = C * ((1 + x) ^ (-(2 : ℝ)) * (1 + y) ^ (-(2 : ℝ))) := by
      rw [div_eq_mul_inv, ← hDweight]

theorem GalerkinSmoothFourier.classicalGalerkinFourierMode_contDiff (a : ℂ)
    (k : Fin 2 → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => a * AVenhance.Infra.Torus.torusCharacter (-k) x) :=
  contDiff_const.mul
    ((AVenhance.Infra.Torus.torusCharacter_contDiff (-k)).of_le (by simp))

theorem GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_norm_le
    (a : ℂ) (k : Fin 2 → ℤ) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => a * AVenhance.Infra.Torus.torusCharacter (-k) y) x‖ ≤
      ‖a‖ * (2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|)) ^ n := by
  have hcd : ContDiffAt ℝ (n : ℕ∞)
      (AVenhance.Infra.Torus.torusCharacter (-k)) x :=
    ((AVenhance.Infra.Torus.torusCharacter_contDiff (-k)).of_le (by simp)).contDiffAt
  rw [show (fun y : Vec 2 => a * AVenhance.Infra.Torus.torusCharacter (-k) y) =
      a • AVenhance.Infra.Torus.torusCharacter (-k) by rfl]
  rw [iteratedFDeriv_const_smul_apply (x := x) (i := n) hcd, norm_smul]
  calc
    ‖a‖ * ‖iteratedFDeriv ℝ n
        (AVenhance.Infra.Torus.torusCharacter (-k)) x‖ ≤
      ‖a‖ * ((2 * Real.pi) ^ n *
        (∑ i : Fin 2, |(k i : ℝ)|) ^ n) :=
      mul_le_mul_of_nonneg_left
        (AVenhance.Infra.Heat.norm_iteratedFDeriv_torusCharacter_le k n x)
        (norm_nonneg _)
    _ = ‖a‖ * (2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|)) ^ n := by
      exact congrArg (fun z : ℝ => ‖a‖ * z)
        (mul_pow (2 * Real.pi) (∑ i : Fin 2, |(k i : ℝ)|) n).symm

theorem GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_weighted_bound
    (a : ℂ) (k : Fin 2 → ℤ) (n : ℕ) (x : Vec 2) (C : ℝ)
    (hC : (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (n + 2) *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (n + 2) * ‖a‖ ≤ C) :
    ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => a * AVenhance.Infra.Torus.torusCharacter (-k) y) x‖ ≤
      C * classicalScaledTorusFrequencyWeight k := by
  let u : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let v : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have ha : 0 ≤ ‖a‖ := norm_nonneg _
  have hfreq : 2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|) = u + v := by
    simp [u, v, Fin.sum_univ_succ]
    ring
  have hcoeff := classicalWeightedCoeff_frequencyPower_le n u v ‖a‖ C
    hu hv ha (by simpa [u, v] using hC)
  calc
    ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => a • AVenhance.Infra.Torus.torusCharacter (-k) y) x‖ ≤
      ‖a‖ * (2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|)) ^ n :=
      GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_norm_le a k n x
    _ = ‖a‖ * (u + v) ^ n := by rw [hfreq]
    _ ≤ C * classicalScaledTorusFrequencyWeight k := by
      simpa [u, v, classicalScaledTorusFrequencyWeight] using hcoeff

/-- The multiplier associated with one ordered list of spatial derivatives. -/
def classicalGalerkinWordFourierMultiplier (k : Fin 2 → ℤ) (w : List (Fin 2)) : ℂ :=
  (w.map fun i => 2 * Real.pi * Complex.I * (k i : ℂ)).prod

/-- Fourier coefficients of the derivative limits satisfy the full ordered-word multiplier
identity. -/
theorem classicalGalerkinWordLimitFourierCoeff_word
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (k : Fin 2 → ℤ) (t : Icc (0 : ℝ) 1) :
    classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k t =
      classicalGalerkinWordFourierMultiplier k w *
        classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [] k t := by
  induction w with
  | nil => simp [classicalGalerkinWordFourierMultiplier]
  | cons i w ih =>
      rw [classicalGalerkinWordLimitFourierCoeff_derivative]
      rw [ih]
      simp [classicalGalerkinWordFourierMultiplier, List.map_cons, List.prod_cons,
        mul_assoc]

/-- The norm of a repeated coordinate multiplier is the corresponding scalar frequency power. -/
theorem classicalGalerkinWordFourierMultiplier_replicate_norm
    (k : Fin 2 → ℤ) (i : Fin 2) (p : ℕ) :
    ‖classicalGalerkinWordFourierMultiplier k (List.replicate p i)‖ =
      (2 * Real.pi * |(k i : ℝ)|) ^ p := by
  induction p with
  | zero => simp [classicalGalerkinWordFourierMultiplier]
  | succ p ih =>
      change ‖(2 * Real.pi * Complex.I * (k i : ℂ)) *
          classicalGalerkinWordFourierMultiplier k (List.replicate p i)‖ = _
      rw [norm_mul, ih]
      have hmode : ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ =
          2 * Real.pi * |(k i : ℝ)| := by
        simp [Complex.norm_I, Complex.norm_intCast,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hmode, pow_succ]
      ring

theorem GalerkinSmoothFourier.classicalMaxFrequencyCoefficientBound (p : ℕ) (x y a C₀ C₁ C₂ C₃ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₀ : a ≤ C₀) (h₁ : x ^ p * a ≤ C₁) (h₂ : y ^ p * a ≤ C₂)
    (h₃ : x ^ p * y ^ p * a ≤ C₃) :
    max 1 x ^ p * max 1 y ^ p * a ≤ C₀ + C₁ + C₂ + C₃ := by
  by_cases hx1 : x ≤ 1
  · by_cases hy1 : y ≤ 1
    · simpa [max_eq_left hx1, max_eq_left hy1] using
        (show a ≤ C₀ + C₁ + C₂ + C₃ by linarith)
    · have hy1' : 1 ≤ y := le_of_not_ge hy1
      simpa [max_eq_left hx1, max_eq_right hy1'] using
        (show y ^ p * a ≤ C₀ + C₁ + C₂ + C₃ by linarith [h₂])
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    by_cases hy1 : y ≤ 1
    · simpa [max_eq_right hx1', max_eq_left hy1] using
        (show x ^ p * a ≤ C₀ + C₁ + C₂ + C₃ by linarith [h₁])
    · have hy1' : 1 ≤ y := le_of_not_ge hy1
      simpa [max_eq_right hx1', max_eq_right hy1'] using
        (show x ^ p * y ^ p * a ≤ C₀ + C₁ + C₂ + C₃ by linarith [h₃])

theorem GalerkinSmoothFourier.classicalOneAddFrequency_pow_le (p : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ p ≤ 2 ^ p * max 1 x ^ p := by
  have hlinear : 1 + x ≤ 2 * max 1 x := by
    by_cases hx1 : x ≤ 1
    · rw [max_eq_left hx1]
      linarith
    · rw [max_eq_right (le_of_not_ge hx1)]
      linarith
  calc
    (1 + x) ^ p ≤ (2 * max 1 x) ^ p := by gcongr
    _ = 2 ^ p * max 1 x ^ p := by rw [mul_pow]

theorem GalerkinSmoothFourier.classicalWeightedFrequencyCoefficientBound
    (p : ℕ) (x y a C₀ C₁ C₂ C₃ : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₀ : a ≤ C₀) (h₁ : x ^ p * a ≤ C₁) (h₂ : y ^ p * a ≤ C₂)
    (h₃ : x ^ p * y ^ p * a ≤ C₃) :
    (1 + x) ^ p * (1 + y) ^ p * a ≤
      2 ^ p * 2 ^ p * (C₀ + C₁ + C₂ + C₃) := by
  have hmax := GalerkinSmoothFourier.classicalMaxFrequencyCoefficientBound p x y a C₀ C₁ C₂ C₃
    hC₀ hC₁ hC₂ hC₃ h₀ h₁ h₂ h₃
  have hpowx := GalerkinSmoothFourier.classicalOneAddFrequency_pow_le p x hx
  have hpowy := GalerkinSmoothFourier.classicalOneAddFrequency_pow_le p y hy
  calc
    (1 + x) ^ p * (1 + y) ^ p * a ≤
        (2 ^ p * max 1 x ^ p) * (2 ^ p * max 1 y ^ p) * a := by
      gcongr
    _ = 2 ^ p * 2 ^ p * (max 1 x ^ p * max 1 y ^ p * a) := by ring
    _ ≤ 2 ^ p * 2 ^ p * (C₀ + C₁ + C₂ + C₃) := by
      gcongr

/-- Uniform derivative energy bounds give polynomial decay of the base Fourier coefficients in both
coordinate directions. -/
theorem classicalGalerkinBaseFourierCoeff_weighted_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Fin 2 → ℤ, ∀ t : Icc (0 : ℝ) 1,
      (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ p *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ p *
          ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k t‖ ≤ C := by
  let w₀ := List.replicate p (0 : Fin 2)
  let w₁ := List.replicate p (1 : Fin 2)
  obtain ⟨C₀, hC₀, hbase⟩ := classicalGalerkinWordLimitFourierCoeffPath_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per []
  obtain ⟨C₁, hC₁, hfirst⟩ := classicalGalerkinWordLimitFourierCoeffPath_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w₀
  obtain ⟨C₂, hC₂, hsecond⟩ := classicalGalerkinWordLimitFourierCoeffPath_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w₁
  obtain ⟨C₃, hC₃, hmixed⟩ := classicalGalerkinWordLimitFourierCoeffPath_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (w₀ ++ w₁)
  refine ⟨2 ^ p * 2 ^ p * (C₀ + C₁ + C₂ + C₃), by positivity, ?_⟩
  intro k t
  let x : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let y : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  let a : ℝ := ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] k t‖
  have hx : 0 ≤ x := by positivity
  have hy : 0 ≤ y := by positivity
  have ha : 0 ≤ a := by positivity
  have h0 : a ≤ C₀ := by simpa [a] using hbase t k
  have hmult0 := classicalGalerkinWordLimitFourierCoeff_word
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w₀ k t
  have hmult1 := classicalGalerkinWordLimitFourierCoeff_word
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w₁ k t
  have hmult01 := classicalGalerkinWordLimitFourierCoeff_word
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (w₀ ++ w₁) k t
  have hmulNorm0 : ‖classicalGalerkinWordFourierMultiplier k w₀‖ = x ^ p := by
    simpa [w₀, x] using classicalGalerkinWordFourierMultiplier_replicate_norm k 0 p
  have hmulNorm1 : ‖classicalGalerkinWordFourierMultiplier k w₁‖ = y ^ p := by
    simpa [w₁, y] using classicalGalerkinWordFourierMultiplier_replicate_norm k 1 p
  have hmulNorm01 : ‖classicalGalerkinWordFourierMultiplier k (w₀ ++ w₁)‖ =
      x ^ p * y ^ p := by
    rw [show classicalGalerkinWordFourierMultiplier k (w₀ ++ w₁) =
        classicalGalerkinWordFourierMultiplier k w₀ *
          classicalGalerkinWordFourierMultiplier k w₁ by
        simp [classicalGalerkinWordFourierMultiplier, List.map_append, List.prod_append],
      norm_mul, hmulNorm0, hmulNorm1]
  have h1 : x ^ p * a ≤ C₁ := by
    calc
      x ^ p * a = ‖classicalGalerkinWordFourierMultiplier k w₀ *
          classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k t‖ := by
        rw [norm_mul, hmulNorm0]
      _ = ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w₀ k t‖ := by rw [← hmult0]
      _ ≤ C₁ := hfirst t k
  have h2 : y ^ p * a ≤ C₂ := by
    calc
      y ^ p * a = ‖classicalGalerkinWordFourierMultiplier k w₁ *
          classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k t‖ := by
        rw [norm_mul, hmulNorm1]
      _ = ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w₁ k t‖ := by rw [← hmult1]
      _ ≤ C₂ := hsecond t k
  have h3 : x ^ p * y ^ p * a ≤ C₃ := by
    calc
      x ^ p * y ^ p * a = ‖classicalGalerkinWordFourierMultiplier k (w₀ ++ w₁) *
          classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k t‖ := by
        rw [norm_mul, hmulNorm01]
      _ = ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (w₀ ++ w₁) k t‖ := by rw [← hmult01]
      _ ≤ C₃ := hmixed t k
  simpa [x, y, a] using GalerkinSmoothFourier.classicalWeightedFrequencyCoefficientBound p x y a
    C₀ C₁ C₂ C₃ hx hy ha hC₀ hC₁ hC₂ hC₃ h0 h1 h2 h3

/-- Bound on the Fourier coefficients of the classical Galerkin solution. -/
noncomputable def classicalGalerkinFourierCoefficientBound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (n : ℕ) : ℝ :=
  Classical.choose (classicalGalerkinBaseFourierCoeff_weighted_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (n + 2))

theorem classicalGalerkinFourierCoefficientBound_nonneg
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (n : ℕ) :
    0 ≤ classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per n := by
  exact (Classical.choose_spec (classicalGalerkinBaseFourierCoeff_weighted_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (n + 2))).1

theorem classicalGalerkinFourierCoefficientBound_spec
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (n : ℕ) :
    ∀ k : Fin 2 → ℤ, ∀ t : Icc (0 : ℝ) 1,
      (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (n + 2) *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (n + 2) *
          ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k t‖ ≤
        classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per n :=
  (Classical.choose_spec (classicalGalerkinBaseFourierCoeff_weighted_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (n + 2))).2

/-- One Fourier term of the classical Galerkin solution series. -/
def classicalGalerkinFourierSeriesTerm
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) : C(UnitAddTorus (Fin 2), ℂ) :=
  classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] k t • UnitAddTorus.mFourier k

theorem classicalGalerkinFourierSeriesTerm_summable
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    Summable (classicalGalerkinFourierSeriesTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  let C := classicalGalerkinFourierCoefficientBound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0
  have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0
  have hw := classicalScaledTorusFrequencyWeight_summable
  have hmajor : Summable (fun k : Fin 2 → ℤ => C *
      classicalScaledTorusFrequencyWeight k) := hw.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro k
  rw [classicalGalerkinFourierSeriesTerm, norm_smul, UnitAddTorus.mFourier_norm, mul_one]
  let x : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let y : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  let a := ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] k t‖
  have hweighted := classicalGalerkinFourierCoefficientBound_spec
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0 k t
  have hbound := classicalWeightedCoeff_frequencyPower_le 0 x y a C
    (by positivity) (by positivity) (norm_nonneg _) (by simpa [x, y, a] using hweighted)
  simpa [C, x, y, a, classicalScaledTorusFrequencyWeight, pow_zero] using hbound

/-- Continuous torus-valued limit of the classical Galerkin Fourier series. -/
noncomputable def classicalGalerkinFourierContinuousLimit
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    C(UnitAddTorus (Fin 2), ℂ) :=
  ∑' k : Fin 2 → ℤ, classicalGalerkinFourierSeriesTerm φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t k

/-- Smooth Euclidean periodic lift of the classical Galerkin limit. -/
noncomputable def classicalGalerkinSmoothLift
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) : Vec 2 → ℂ :=
  fun x => ∑' k : Fin 2 → ℤ,
    classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per [] k t * AVenhance.Infra.Torus.torusCharacter (-k) x

theorem classicalGalerkinSmoothLift_contDiff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  let C : ℕ → ℝ := fun n => classicalGalerkinFourierCoefficientBound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per n
  let v : ℕ → (Fin 2 → ℤ) → ℝ := fun n k => C n *
    classicalScaledTorusFrequencyWeight k
  have hv : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Summable (v n) := by
    intro n hn
    exact classicalScaledTorusFrequencyWeight_summable.mul_left (C n)
  refine contDiff_tsum (𝕜 := ℝ) (E := Vec 2) (F := ℂ)
    (f := fun k x => classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per [] k t * AVenhance.Infra.Torus.torusCharacter (-k) x)
    (v := v) (N := (⊤ : ℕ∞)) ?_ hv ?_
  · intro k
    exact GalerkinSmoothFourier.classicalGalerkinFourierMode_contDiff
      (classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [] k t) k
  · intro n k x hn
    exact GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_weighted_bound
      (classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [] k t) k n x (C n) (by
          simpa [C] using classicalGalerkinFourierCoefficientBound_spec
            φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per n k t)

theorem classicalGalerkinFourierContinuousLimit_toLp
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    ContinuousMap.toLp 2 volume ℂ
        (classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t) =
      classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [] t) := by
  let g : (Fin 2 → ℤ) → C(UnitAddTorus (Fin 2), ℂ) :=
    classicalGalerkinFourierSeriesTerm φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hg : Summable g := by
    simpa [g] using classicalGalerkinFourierSeriesTerm_summable
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hL2 : HasSum (fun k : Fin 2 → ℤ =>
      ContinuousMap.toLp 2 volume ℂ (g k))
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [] t)) := by
    have hbasis := UnitAddTorus.hasSum_mFourier_series_L2
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [] t))
    simpa [g, classicalGalerkinFourierSeriesTerm,
      classicalGalerkinWordLimitFourierCoeffPath,
      classicalGalerkinLimitFourierCoeffPath, UnitAddTorus.mFourierLp,
      classicalComplexFourierCoeffCLM_apply] using hbasis
  change ContinuousMap.toLp 2 volume ℂ (∑' k, g k) = _
  rw [ContinuousLinearMap.map_tsum (ContinuousMap.toLp 2 volume ℂ) hg]
  exact hL2.tsum_eq

theorem classicalGalerkinSmoothLift_eq_continuousLimit
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) (x : Vec 2) :
    classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per t x =
      classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per t (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
  let g : (Fin 2 → ℤ) → C(UnitAddTorus (Fin 2), ℂ) :=
    classicalGalerkinFourierSeriesTerm φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hg : Summable g := by
    simpa [g] using classicalGalerkinFourierSeriesTerm_summable
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  calc
    classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t x =
        ∑' k : Fin 2 → ℤ, g k (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
          apply tsum_congr
          intro k
          simp [g, classicalGalerkinFourierSeriesTerm,
            AVenhance.Infra.Torus.torusCharacter, UnitAddTorus.mFourier]
    _ = (∑' k : Fin 2 → ℤ, g k)
        (AVenhance.Infra.Torus.toUnitTorus 2 x) := ContinuousMap.tsum_apply hg _
    _ = _ := rfl

theorem classicalGalerkinSmoothLift_periodic
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    AVenhance.IsZ2Periodic (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  apply (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).mp
  intro m x
  unfold classicalGalerkinSmoothLift
  apply tsum_congr
  intro k
  rw [AVenhance.Infra.Torus.torusCharacter_periodic (-k) m x]

end AVenhance.Infra.Classical

end
