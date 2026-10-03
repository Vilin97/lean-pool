/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Smooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Smooth Classical

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus
open Homogenization
open scoped FourierTransform ENNReal

namespace AVenhance.Infra.Heat

/-- The real linear phase associated with an integer frequency. -/
def frequencyPhaseCLM (k : Frequency) : Vec 2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, (k i : ℝ) • ContinuousLinearMap.proj i

@[simp] theorem frequencyPhaseCLM_apply (k : Frequency) (x : Vec 2) :
    frequencyPhaseCLM k x = ∑ i : Fin 2, (k i : ℝ) * x i := by
  simp [frequencyPhaseCLM]

theorem SmoothClassical.norm_proj_le_one (i : Fin 2) :
    ‖(ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa using (norm_le_pi_norm x i)

theorem norm_frequencyPhaseCLM_le (k : Frequency) :
    ‖frequencyPhaseCLM k‖ ≤ ∑ i : Fin 2, |(k i : ℝ)| := by
  calc
    ‖frequencyPhaseCLM k‖ ≤ ∑ i : Fin 2,
        ‖(k i : ℝ) • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, |(k i : ℝ)| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |(k i : ℝ)| * ‖(ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)‖ ≤
            |(k i : ℝ)| * 1 := by gcongr; exact SmoothClassical.norm_proj_le_one i
        _ = |(k i : ℝ)| := mul_one _

theorem SmoothClassical.torusCharacter_neg_frequencyPhase (k : Frequency) :
    torusCharacter (-k) = fun x : Vec 2 =>
      (Real.fourierChar (frequencyPhaseCLM k x) : ℂ) := by
  funext x
  rw [Real.fourierChar_apply]
  have hphase : ((2 * Real.pi * frequencyPhaseCLM k x : ℝ) : ℂ) * Complex.I =
      ∑ i : Fin 2, (2 * Real.pi * Complex.I) * (k i : ℂ) * (x i : ℂ) := by
    rw [frequencyPhaseCLM_apply]
    push_cast
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hphase, Complex.exp_sum]
  simp only [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, neg_neg, fourier_coe_apply]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  push_cast
  norm_num

theorem SmoothClassical.iteratedDeriv_fourierChar (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (Real.fourierChar x : ℂ)) =
      fun x => (2 * Real.pi * Complex.I)^n * (Real.fourierChar x : ℂ) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, Real.deriv_fourierChar]
    simp [pow_succ, mul_assoc]

theorem SmoothClassical.norm_iteratedFDeriv_fourierChar (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.fourierChar x : ℂ)) x‖ ≤
      (2 * Real.pi)^n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, SmoothClassical.iteratedDeriv_fourierChar]
  simp [norm_pow, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]

theorem SmoothClassical.contDiff_fourierChar :
    ContDiff ℝ ⊤ (fun x : ℝ => (Real.fourierChar x : ℂ)) := by
  have hformula : (fun x : ℝ => (Real.fourierChar x : ℂ)) =
      (fun x : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (x : ℂ))) := by
    funext x
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [hformula]
  have hcast : ContDiff ℝ ⊤ (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_id
  have harg : ContDiff ℝ ⊤
      (fun x : ℝ => (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * (x : ℂ)) :=
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => ((2 * Real.pi : ℝ) : ℂ) * Complex.I)).mul hcast
  exact Complex.contDiff_exp.comp harg

/-- Uniform Fréchet derivative bound for a torus character in terms of its frequency. -/
theorem norm_iteratedFDeriv_torusCharacter_le (k : Frequency) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (torusCharacter (-k)) x‖ ≤
      (2 * Real.pi)^n * (∑ i : Fin 2, |(k i : ℝ)|)^n := by
  rw [SmoothClassical.torusCharacter_neg_frequencyPhase]
  change ‖iteratedFDeriv ℝ n
    ((fun t : ℝ => (Real.fourierChar t : ℂ)) ∘ frequencyPhaseCLM k) x‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (frequencyPhaseCLM k)
    SmoothClassical.contDiff_fourierChar x (i := n) (by simp)]
  calc
    ‖(iteratedFDeriv ℝ n (fun x : ℝ => (Real.fourierChar x : ℂ))
          (frequencyPhaseCLM k x)).compContinuousLinearMap
          (fun _ : Fin n => frequencyPhaseCLM k)‖ ≤
    ‖iteratedFDeriv ℝ n (fun t : ℝ => (Real.fourierChar t : ℂ))
          (frequencyPhaseCLM k x)‖ *
          ∏ _ : Fin n, ‖frequencyPhaseCLM k‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (2 * Real.pi)^n * (∑ i : Fin 2, |(k i : ℝ)|)^n := by
      rw [Finset.prod_const, Finset.card_fin]
      gcongr
      · exact SmoothClassical.norm_iteratedFDeriv_fourierChar n (frequencyPhaseCLM k x)
      · exact norm_frequencyPhaseCLM_le k

/-- Exact all-orders derivative multiplier for one torus character, evaluated
on arbitrary directions. -/
theorem iteratedFDeriv_torusCharacter_apply (k : Frequency) (n : ℕ)
    (x : Vec 2) (v : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (torusCharacter (-k)) x v =
      (2 * Real.pi * Complex.I)^n * torusCharacter (-k) x *
        ∏ j : Fin n, frequencyPhaseCLM k (v j) := by
  rw [SmoothClassical.torusCharacter_neg_frequencyPhase]
  change iteratedFDeriv ℝ n
    ((fun t : ℝ => (Real.fourierChar t : ℂ)) ∘ frequencyPhaseCLM k) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (frequencyPhaseCLM k)
    SmoothClassical.contDiff_fourierChar x (i := n) (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, SmoothClassical.iteratedDeriv_fourierChar]
  simp only [Complex.real_smul, Complex.ofReal_prod]
  ring

theorem SmoothClassical.frequencyL1_le (k : Frequency) :
    (∑ i : Fin 2, |(k i : ℝ)|) ≤ 2 * Real.sqrt (frequencySq k) := by
  have hq : 0 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
  have hcoord (i : Fin 2) : |(k i : ℝ)| ≤ Real.sqrt (frequencySq k) := by
    have hcoordSq : (k i : ℝ)^2 ≤ frequencySq k := by
      unfold frequencySq
      exact Finset.single_le_sum (fun j hj => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hq]
    exact hcoordSq
  rw [Fin.sum_univ_succ]
  have h0 := hcoord 0
  have h1 := hcoord 1
  norm_num at h0 h1 ⊢
  linarith

theorem SmoothClassical.character_derivative_radial_bound (k : Frequency) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (torusCharacter (-k)) x‖ ≤
      2^n * (2 * Real.pi * Real.sqrt (frequencySq k))^n := by
  calc
    ‖iteratedFDeriv ℝ n (torusCharacter (-k)) x‖ ≤
        (2 * Real.pi)^n * (∑ i : Fin 2, |(k i : ℝ)|)^n :=
      norm_iteratedFDeriv_torusCharacter_le k n x
    _ ≤ (2 * Real.pi)^n * (2 * Real.sqrt (frequencySq k))^n := by
      gcongr
      exact SmoothClassical.frequencyL1_le k
    _ = 2^n * (2 * Real.pi * Real.sqrt (frequencySq k))^n := by ring

/-- One Fourier mode of the positive-time heat evolution, lifted to Euclidean space. -/
def SmoothClassical.heatSeriesMode {s : ℝ} (hs : 0 < s) (f : TorusL2 2)
    (k : Frequency) : Vec 2 → ℂ := fun x =>
  UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k * torusCharacter (-k) x

theorem SmoothClassical.heatSeriesMode_contDiff {s : ℝ} (hs : 0 < s) (f : TorusL2 2)
    (k : Frequency) : ContDiff ℝ ⊤ (SmoothClassical.heatSeriesMode hs f k) := by
  change ContDiff ℝ ⊤ (fun x : Vec 2 =>
    UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k * torusCharacter (-k) x)
  exact contDiff_const.mul (torusCharacter_contDiff (-k))

theorem SmoothClassical.heatSeriesMode_iteratedFDeriv_bound {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (n : ℕ) (k : Frequency) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x‖ ≤
      (2^n * (Nat.factorial n : ℝ) * (1 / Real.sqrt (s/2))^n) *
        (‖(UnitAddTorus.mFourierBasis.repr f) k‖ *
          Real.exp (-(2 * Real.pi^2 * s) * frequencySq k)) := by
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let half : ℝ := s / 2
  have hhalf : 0 < half := by dsimp [half]; positivity
  have hq : 0 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
  have hmult : heatMultiplier s k = heatMultiplier half k * heatMultiplier half k := by
    rw [heatMultiplier, heatMultiplier, ← Real.exp_add]
    congr 1
    dsimp [half]
    ring
  have hcoeff : UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k =
      (heatMultiplier s k : ℂ) * a k := by
    rw [mFourierCoeff_heatTorusL2 hs.le]
    simp only [a, UnitAddTorus.mFourierBasis_repr]
  have hscalar : ‖UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k‖ =
      heatMultiplier half k * heatMultiplier half k * ‖a k‖ := by
    rw [hcoeff, hmult, norm_mul]
    have hm0 : 0 ≤ heatMultiplier half k := (Real.exp_pos _).le
    simp [Complex.norm_real, abs_of_nonneg hm0]
  have hrad := radialHeatMultiplier_bound hhalf n k
  have hmode :
      ‖iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x‖ ≤
        ‖UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k‖ *
          ‖iteratedFDeriv ℝ n (torusCharacter (-k)) x‖ := by
    change ‖iteratedFDeriv ℝ n
      (fun y => UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k •
        torusCharacter (-k) y) x‖ ≤ _
    have hcd : ContDiffAt ℝ (n : ℕ∞) (torusCharacter (-k)) x := by
      exact ((torusCharacter_contDiff (-k)).of_le (by simp)).contDiffAt
    rw [show (fun y : Vec 2 =>
        UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • torusCharacter (-k) y) =
          UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • torusCharacter (-k)
        from rfl]
    rw [iteratedFDeriv_const_smul_apply (x := x) (i := n) hcd]
    rw [norm_smul]
  have hexp : heatMultiplier half k =
      Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) := by
    rw [heatMultiplier]
    dsimp [half]
    congr 1
    ring
  calc
    ‖iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x‖ ≤
        ‖UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k‖ *
          ‖iteratedFDeriv ℝ n (torusCharacter (-k)) x‖ := hmode
    _ ≤ (heatMultiplier half k * heatMultiplier half k * ‖a k‖) *
          (2^n * (2 * Real.pi * Real.sqrt (frequencySq k))^n) := by
      rw [hscalar]
      exact mul_le_mul_of_nonneg_left
        (SmoothClassical.character_derivative_radial_bound k n x)
        (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _))
    _ ≤ (2^n * (Nat.factorial n : ℝ) *
          (1 / Real.sqrt half)^n) * (‖a k‖ * heatMultiplier half k) := by
      have hm0 : 0 ≤ heatMultiplier half k := (Real.exp_pos _).le
      have ha0 : 0 ≤ ‖a k‖ := norm_nonneg _
      calc
        heatMultiplier half k * heatMultiplier half k * ‖a k‖ *
            (2^n * ((2 * Real.pi * Real.sqrt (frequencySq k))^n))
            = ((2:ℝ)^n * ‖a k‖ * heatMultiplier half k) *
                ((2 * Real.pi * Real.sqrt (frequencySq k))^n * heatMultiplier half k) := by ring
        _ ≤ ((2:ℝ)^n * ‖a k‖ * heatMultiplier half k) *
              ((Nat.factorial n : ℝ) * (1 / Real.sqrt half)^n) :=
          mul_le_mul_of_nonneg_left hrad (by positivity)
        _ = (2^n * (Nat.factorial n : ℝ) * (1 / Real.sqrt half)^n) *
              (‖a k‖ * heatMultiplier half k) := by ring
    _ = (2^n * (Nat.factorial n : ℝ) * (1 / Real.sqrt (s/2))^n) *
          (‖a k‖ * Real.exp (-(2 * Real.pi^2 * s) * frequencySq k)) := by
      rw [show half = s/2 by rfl, hexp]

/-- Exact all-orders Fourier multiplier for one mode of the classical heat
series. -/
theorem heatSeriesMode_iteratedFDeriv_apply {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (n : ℕ) (k : Frequency) (x : Vec 2)
    (v : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x v =
      UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k *
        (2 * Real.pi * Complex.I)^n * torusCharacter (-k) x *
          ∏ j : Fin n, frequencyPhaseCLM k (v j) := by
  change iteratedFDeriv ℝ n
    (fun y => UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k •
      torusCharacter (-k) y) x v = _
  have hcd : ContDiffAt ℝ (n : ℕ∞) (torusCharacter (-k)) x := by
    exact ((torusCharacter_contDiff (-k)).of_le (by simp)).contDiffAt
  rw [show (fun y : Vec 2 =>
      UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • torusCharacter (-k) y) =
        UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • torusCharacter (-k)
      from rfl]
  rw [iteratedFDeriv_const_smul_apply (x := x) (i := n) hcd]
  change UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k *
      iteratedFDeriv ℝ n (torusCharacter (-k)) x v = _
  rw [iteratedFDeriv_torusCharacter_apply]
  ring

/-- The classical Euclidean Fourier series representative of the heat evolution. -/
noncomputable def heatTorusSmoothLift {s : ℝ} (hs : 0 < s) (f : TorusL2 2) :
    Vec 2 → ℂ := fun x => ∑' k : Frequency, SmoothClassical.heatSeriesMode hs f k x

theorem heatTorusSmoothLift_contDiff {s : ℝ} (hs : 0 < s) (f : TorusL2 2) :
    ContDiff ℝ (⊤ : ℕ∞) (heatTorusSmoothLift hs f) := by
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let b : lp (fun _ : Frequency => ℂ) 2 := ⟨
    (fun k : Frequency => (Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) : ℂ)),
    gaussianWeight_memLp (2 * Real.pi^2 * s) (by positivity)⟩
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
    ENNReal.HolderConjugate.toReal (by norm_num)
  have hprod : Summable (fun k : Frequency => ‖a k‖ * ‖b k‖) :=
    lp.summable_mul hpq a b
  let v : ℕ → Frequency → ℝ := fun n k =>
    (2^n * (Nat.factorial n : ℝ) * (1 / Real.sqrt (s/2))^n) *
      (‖a k‖ * ‖b k‖)
  have hv : ∀ n : ℕ, Summable (v n) := by
    intro n
    exact hprod.mul_left _
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' k : Frequency, SmoothClassical.heatSeriesMode hs f k x)
  refine contDiff_tsum (𝕜 := ℝ) (E := Vec 2) (F := ℂ)
    (f := fun k => SmoothClassical.heatSeriesMode hs f k) (v := v) (N := (⊤ : ℕ∞)) ?_ ?_ ?_
  · intro k
    exact (SmoothClassical.heatSeriesMode_contDiff hs f k).of_le (by simp)
  · intro n hn
    exact hv n
  · intro n k x hn
    have hb : ‖b k‖ = Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) := by
      dsimp [b]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      ‖iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x‖ ≤
          (2^n * (Nat.factorial n : ℝ) * (1 / Real.sqrt (s/2))^n) *
            (‖a k‖ * Real.exp (-(2 * Real.pi^2 * s) * frequencySq k)) :=
        SmoothClassical.heatSeriesMode_iteratedFDeriv_bound hs f n k x
      _ = v n k := by simp [v, hb]

theorem heatTorusSmoothLift_eq_heatTorusContinuous {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (x : Vec 2) :
    heatTorusSmoothLift hs f x = heatTorusContinuous hs f (toUnitTorus 2 x) := by
  let g : Frequency → C(UnitAddTorus (Fin 2), ℂ) := fun k =>
    UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k • UnitAddTorus.mFourier k
  have hg : Summable g := by
    apply Summable.of_norm_bounded (heatFourierCoeff_summable hs f)
    intro k
    simp [g, norm_smul, UnitAddTorus.mFourier_norm]
  calc
    heatTorusSmoothLift hs f x =
        ∑' k : Frequency, g k (toUnitTorus 2 x) := by
      apply tsum_congr
      intro k
      simp [SmoothClassical.heatSeriesMode, g, torusCharacter,
        UnitAddTorus.mFourier]
    _ = (∑' k : Frequency, g k) (toUnitTorus 2 x) :=
      ContinuousMap.tsum_apply hg (toUnitTorus 2 x)
    _ = heatTorusContinuous hs f (toUnitTorus 2 x) := rfl

/-- The classical `n`-th Fréchet derivative is obtained by differentiating
the heat Fourier series term by term. Its multiplier on a direction tuple is
the product of the corresponding linear frequency phases. -/
theorem heatTorusSmoothLift_iteratedFDeriv_apply {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (n : ℕ) (x : Vec 2) (v : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (heatTorusSmoothLift hs f) x v =
      ∑' k : Frequency,
        UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k *
          (2 * Real.pi * Complex.I)^n * torusCharacter (-k) x *
            ∏ j : Fin n, frequencyPhaseCLM k (v j) := by
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let b : lp (fun _ : Frequency => ℂ) 2 := ⟨
    (fun k : Frequency => (Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) : ℂ)),
    gaussianWeight_memLp (2 * Real.pi^2 * s) (by positivity)⟩
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
    ENNReal.HolderConjugate.toReal (by norm_num)
  have hprod : Summable (fun k : Frequency => ‖a k‖ * ‖b k‖) :=
    lp.summable_mul hpq a b
  let w : ℕ → Frequency → ℝ := fun m k =>
    (2^m * (Nat.factorial m : ℝ) * (1 / Real.sqrt (s/2))^m) *
      (‖a k‖ * ‖b k‖)
  have hw : ∀ m : ℕ, Summable (w m) := by
    intro m
    exact hprod.mul_left _
  have hderiv : ∀ (m : ℕ) (k : Frequency) (y : Vec 2),
      (m : ℕ∞) ≤ (⊤ : ℕ∞) →
        ‖iteratedFDeriv ℝ m (SmoothClassical.heatSeriesMode hs f k) y‖ ≤ w m k := by
    intro m k y hm
    have hb : ‖b k‖ = Real.exp (-(2 * Real.pi^2 * s) * frequencySq k) := by
      dsimp [b]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      ‖iteratedFDeriv ℝ m (SmoothClassical.heatSeriesMode hs f k) y‖ ≤
          (2^m * (Nat.factorial m : ℝ) * (1 / Real.sqrt (s/2))^m) *
            (‖a k‖ * Real.exp (-(2 * Real.pi^2 * s) * frequencySq k)) :=
        SmoothClassical.heatSeriesMode_iteratedFDeriv_bound hs f m k y
      _ = w m k := by simp [w, hb]
  have hsum := iteratedFDeriv_tsum_apply
    (𝕜 := ℝ) (E := Vec 2) (F := ℂ)
    (f := fun k => SmoothClassical.heatSeriesMode hs f k) (v := w) (N := (⊤ : ℕ∞))
    (hf := fun k => (SmoothClassical.heatSeriesMode_contDiff hs f k).of_le (by simp))
    (hv := fun m hm => hw m)
    (h'f := hderiv) (k := n) (by simp) x
  have hderivSummable : Summable
      (fun k : Frequency => iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x) := by
    apply Summable.of_norm_bounded (hw n)
    intro k
    exact hderiv n k x (by simp)
  have hsumCoord :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) ℂ v).map_tsum
      hderivSummable
  have hEval := congrArg (fun T => T v) hsum
  calc
    iteratedFDeriv ℝ n (heatTorusSmoothLift hs f) x v =
        ∑' k : Frequency, iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x v := by
      calc
        _ = (∑' k : Frequency, iteratedFDeriv ℝ n (SmoothClassical.heatSeriesMode hs f k) x) v := by
          change iteratedFDeriv ℝ n
            (fun y => ∑' k : Frequency, SmoothClassical.heatSeriesMode hs f k y) x v = _
          exact hEval
        _ = _ := hsumCoord
    _ = ∑' k : Frequency,
        UnitAddTorus.mFourierCoeff (heatTorusL2 s hs.le f) k *
          (2 * Real.pi * Complex.I)^n * torusCharacter (-k) x *
            ∏ j : Fin n, frequencyPhaseCLM k (v j) := by
      apply tsum_congr
      intro k
      exact heatSeriesMode_iteratedFDeriv_apply hs f n k x v

end AVenhance.Infra.Heat
