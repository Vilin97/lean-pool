/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.PSeries
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! # `H² ⊂ L∞` on the 2-torus

For a smooth `ℤ²`-periodic function `u : Vec 2 → ℝ` we prove
`|u x| ≤ sobolevConst * (‖u‖₂ + ‖∂₀²u‖₂ + ‖∂₁²u‖₂)`,
by expanding `u` in its (absolutely convergent) Fourier series and applying Cauchy–Schwarz
against the weight `sobolevWeight k = 1 + (2π)⁴(k₀⁴ + k₁⁴)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.AnalyticBridge

/-- The Fourier weight `1 + (2π)⁴ (k₀⁴ + k₁⁴)` on `ℤ²`. -/
def sobolevWeight (k : Fin 2 → ℤ) : ℝ :=
  1 + (2 * Real.pi) ^ 4 * ((k 0 : ℝ) ^ 4 + (k 1 : ℝ) ^ 4)

theorem sobolevWeight_pos (k : Fin 2 → ℤ) : 0 < sobolevWeight k := by
  unfold sobolevWeight
  positivity

/-- `1 ≤ (2π)⁴`, in abstract-real form. -/
theorem Sobolev.one_le_two_pi_pow_four : (1 : ℝ) ≤ (2 * Real.pi) ^ 4 := by
  have h : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  exact one_le_pow₀ h

/-- Product bound `(1 + a²)(1 + b²) ≤ 2 (1 + a⁴ + b⁴)`. -/
theorem Sobolev.prod_le_two_mul (a b : ℝ) :
    (1 + a ^ 2) * (1 + b ^ 2) ≤ 2 * (1 + (a ^ 4 + b ^ 4)) := by
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (a ^ 2 - b ^ 2)]

theorem Sobolev.prod_le_two_mul_sobolevWeight (k : Fin 2 → ℤ) :
    (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) ≤ 2 * sobolevWeight k := by
  have h1 := Sobolev.prod_le_two_mul (k 0 : ℝ) (k 1 : ℝ)
  have hs : 0 ≤ (k 0 : ℝ) ^ 4 + (k 1 : ℝ) ^ 4 := by positivity
  have h2 : (k 0 : ℝ) ^ 4 + (k 1 : ℝ) ^ 4 ≤
      (2 * Real.pi) ^ 4 * ((k 0 : ℝ) ^ 4 + (k 1 : ℝ) ^ 4) := by
    simpa using mul_le_mul_of_nonneg_right Sobolev.one_le_two_pi_pow_four hs
  unfold sobolevWeight
  linarith

/-- One-dimensional summability of `1 / (1 + n²)` over `ℤ`. -/
theorem Sobolev.summable_one_div_one_add_sq :
    Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  have hbase : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually hbase ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := hn
    exact_mod_cast this
  have hpos : 0 < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hpos (by linarith)

/-- The inverse Sobolev weight is summable over `ℤ²`. -/
theorem summable_inv_sobolevWeight : Summable (fun k : Fin 2 → ℤ => (sobolevWeight k)⁻¹) := by
  have hprod : Summable (fun p : ℤ × ℤ =>
      (1 / (1 + (p.1 : ℝ) ^ 2)) * (1 / (1 + (p.2 : ℝ) ^ 2))) :=
    Summable.mul_of_nonneg Sobolev.summable_one_div_one_add_sq Sobolev.summable_one_div_one_add_sq
      (fun n => by positivity) (fun n => by positivity)
  have hcomp : Summable (fun k : Fin 2 → ℤ =>
      (1 / (1 + (k 0 : ℝ) ^ 2)) * (1 / (1 + (k 1 : ℝ) ^ 2))) := by
    simpa [Function.comp_def] using (Equiv.summable_iff (piFinTwoEquiv (fun _ : Fin 2 => ℤ))).mpr
        hprod
  refine Summable.of_nonneg_of_le (fun k => (inv_pos.mpr (sobolevWeight_pos k)).le)
    (fun k => ?_) (hcomp.mul_left 2)
  have hw := sobolevWeight_pos k
  have hp : 0 < (1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2) := by positivity
  have hle := Sobolev.prod_le_two_mul_sobolevWeight k
  calc (sobolevWeight k)⁻¹ ≤ 2 * ((1 + (k 0 : ℝ) ^ 2) * (1 + (k 1 : ℝ) ^ 2))⁻¹ := by
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hw hp]
        linarith
    _ = 2 * ((1 / (1 + (k 0 : ℝ) ^ 2)) * (1 / (1 + (k 1 : ℝ) ^ 2))) := by
        rw [one_div_mul_one_div, one_div]

/-- The Sobolev constant `(∑_{k ∈ ℤ²} (1 + (2π)⁴ (k₀⁴ + k₁⁴))⁻¹)^{1/2}`. -/
def sobolevConst : ℝ := Real.sqrt (∑' k : Fin 2 → ℤ, (sobolevWeight k)⁻¹)

theorem sobolevConst_pos : 0 < sobolevConst := by
  unfold sobolevConst
  apply Real.sqrt_pos.mpr
  exact summable_inv_sobolevWeight.tsum_pos (fun k => (inv_pos.mpr (sobolevWeight_pos k)).le)
    0 (inv_pos.mpr (sobolevWeight_pos 0))

/-! ### Coordinate derivatives of smooth periodic real functions -/

/-- The real coordinate derivative `∂ᵢ u`. -/
def Sobolev.coordPartial (i : Fin 2) (u : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun y => fderiv ℝ u y (basisVec i)

theorem Sobolev.contDiff_coordPartial {u : Vec 2 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 2) :
    ContDiff ℝ ∞ (Sobolev.coordPartial i u) :=
  (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem Sobolev.isZ2Periodic_coordPartial {u : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic u)
    (i : Fin 2) : AVenhance.IsZ2Periodic (Sobolev.coordPartial i u) := by
  intro n y
  have hfun : (fun z => u (z + AVenhance.latticeShift n)) = u := funext fun z => hp n z
  have h : fderiv ℝ (fun z => u (z + AVenhance.latticeShift n)) y =
      fderiv ℝ u (y + AVenhance.latticeShift n) := fderiv_comp_add_right _
  rw [hfun] at h
  simp only [Sobolev.coordPartial]
  rw [← h]

/-- The second coordinate derivative as the iterated Fréchet derivative. -/
theorem Sobolev.coordPartial_coordPartial {u : Vec 2 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 2)
    (y : Vec 2) :
    Sobolev.coordPartial i (Sobolev.coordPartial i u) y =
      iteratedFDeriv ℝ 2 u y (fun _ => basisVec i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) y :=
    (hu.fderiv_right (m := 1) (by simp)).differentiable (by simp) y
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fun z => fderiv ℝ u z (basisVec i)) y (basisVec i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-! ### Parseval for `u` and its pure second derivatives -/

/-- The squared modulus of a Fourier multiplier `2πi m`. -/
theorem Sobolev.norm_sq_fourierMultiplier (m : ℤ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ))‖ ^ 2 = (2 * Real.pi) ^ 2 * (m : ℝ) ^ 2 := by
  have h : ‖(2 * Real.pi * Complex.I * (m : ℂ))‖ = 2 * Real.pi * |(m : ℝ)| := by
    simp [Complex.norm_I, Complex.norm_intCast, abs_of_nonneg, Real.pi_pos.le]
  rw [h, mul_pow, sq_abs]

theorem Sobolev.norm_sq_multiplier_twice (m : ℤ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ)) * ((2 * Real.pi * Complex.I * (m : ℂ)) * z)‖ ^ 2 =
      (2 * Real.pi) ^ 4 * (m : ℝ) ^ 4 * ‖z‖ ^ 2 := by
  have ha := Sobolev.norm_sq_fourierMultiplier m
  generalize (2 * Real.pi * Complex.I * (m : ℂ)) = a at ha ⊢
  calc ‖a * (a * z)‖ ^ 2 = (‖a‖ ^ 2) ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_mul, norm_mul]
        ring
    _ = _ := by
        rw [ha]
        ring

/-- Fourier coefficients of the second coordinate derivative. -/
theorem Sobolev.smoothFourierCoeff_second {u : Vec 2 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hp : AVenhance.IsZ2Periodic u) (i : Fin 2) (k : Fin 2 → ℤ) :
    Torus.smoothFourierCoeff (Torus.realToComplex (Sobolev.coordPartial i (Sobolev.coordPartial i
        u))) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((2 * Real.pi * Complex.I * (k i : ℂ)) *
          Torus.smoothFourierCoeff (Torus.realToComplex u) k) := by
  have h1 := Torus.smoothFourierCoeff_spaceGrad (hu.of_le (by simp)) hp i k
  have h2 := Torus.smoothFourierCoeff_spaceGrad
    ((Sobolev.contDiff_coordPartial hu i).of_le (by simp)) (Sobolev.isZ2Periodic_coordPartial hp
        i) i k
  change Torus.smoothFourierCoeff (fun x => (AVenhance.spaceGrad (Sobolev.coordPartial i u) x i :
      ℂ)) k = _
  rw [h2]
  change _ * Torus.smoothFourierCoeff (fun x => (AVenhance.spaceGrad u x i : ℂ)) k = _
  rw [h1]

/-- Parseval for `u`. -/
theorem Sobolev.hasSum_sq_zeroth {u : Vec 2 → ℝ} (hu : ContDiff ℝ ∞ u) :
    HasSum (fun k : Fin 2 → ℤ => ‖Torus.smoothFourierCoeff (Torus.realToComplex u) k‖ ^ 2)
      (AVenhance.l2NormSq u) :=
  Torus.hasSum_sq_realToComplexFourierCoeff (hu.of_le (by simp))

/-- Parseval for the pure second derivative `∂ᵢ²u`, weighted by `(2π)⁴ kᵢ⁴`. -/
theorem Sobolev.hasSum_sq_second {u : Vec 2 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hp : AVenhance.IsZ2Periodic u) (i : Fin 2) :
    HasSum (fun k : Fin 2 → ℤ =>
        (2 * Real.pi) ^ 4 * (k i : ℝ) ^ 4 *
          ‖Torus.smoothFourierCoeff (Torus.realToComplex u) k‖ ^ 2)
      (AVenhance.l2NormSq (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec i))) := by
  have hw : ContDiff ℝ ∞ (Sobolev.coordPartial i (Sobolev.coordPartial i u)) :=
    Sobolev.contDiff_coordPartial (Sobolev.contDiff_coordPartial hu i) i
  have h := Torus.hasSum_sq_realToComplexFourierCoeff (hw.of_le (by simp))
  have hfun : (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec i)) =
      Sobolev.coordPartial i (Sobolev.coordPartial i u) := funext fun y =>
          (Sobolev.coordPartial_coordPartial hu i y).symm
  rw [hfun]
  convert h using 1
  funext k
  rw [Sobolev.smoothFourierCoeff_second hu hp i k, Sobolev.norm_sq_multiplier_twice]

/-! ### Cauchy–Schwarz against the Sobolev weight -/

/-- Finite Cauchy–Schwarz: weighted `ℓ²` control gives finite `ℓ¹` control. -/
theorem Sobolev.sum_norm_le_sobolevConst_mul {c : (Fin 2 → ℤ) → ℂ} {S : ℝ}
    (hsum : HasSum (fun k => sobolevWeight k * ‖c k‖ ^ 2) S) (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, ‖c k‖ ≤ sobolevConst * Real.sqrt S := by
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun k => ‖c k‖ * Real.sqrt (sobolevWeight k)) (fun k => (Real.sqrt (sobolevWeight k))⁻¹)
  have hterm : ∀ k, ‖c k‖ * Real.sqrt (sobolevWeight k) * (Real.sqrt (sobolevWeight k))⁻¹ =
      ‖c k‖ := fun k => by
    have : Real.sqrt (sobolevWeight k) ≠ 0 := (Real.sqrt_pos.mpr (sobolevWeight_pos k)).ne'
    field_simp
  have hsq1 : ∀ k, (‖c k‖ * Real.sqrt (sobolevWeight k)) ^ 2 = sobolevWeight k * ‖c k‖ ^ 2 :=
    fun k => by
      rw [mul_pow, Real.sq_sqrt (sobolevWeight_pos k).le]
      ring
  have hsq2 : ∀ k, ((Real.sqrt (sobolevWeight k))⁻¹) ^ 2 = (sobolevWeight k)⁻¹ := fun k => by
    rw [inv_pow, Real.sq_sqrt (sobolevWeight_pos k).le]
  simp only [hterm, hsq1, hsq2] at hCS
  have h1 : ∑ k ∈ s, sobolevWeight k * ‖c k‖ ^ 2 ≤ S :=
    sum_le_hasSum s (fun k _ => by have := sobolevWeight_pos k; positivity) hsum
  have h2 : ∑ k ∈ s, (sobolevWeight k)⁻¹ ≤ ∑' k, (sobolevWeight k)⁻¹ :=
    summable_inv_sobolevWeight.sum_le_tsum s (fun k _ => (inv_pos.mpr (sobolevWeight_pos k)).le)
  refine hCS.trans ?_
  rw [mul_comm]
  exact mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-! ### Pointwise Fourier expansion of a smooth periodic function -/

/-- A continuous periodic function descends to a continuous function on the torus. -/
theorem Sobolev.continuous_periodicToTorus {f : Vec 2 → ℂ} (hc : Continuous f)
    (hp : Torus.IsZdPeriodic f) : Continuous (Torus.periodicToTorus f) := by
  have hq : IsOpenQuotientMap (Torus.toUnitTorus 2) :=
    IsOpenQuotientMap.piMap (f := fun _ : Fin 2 => ((↑) : ℝ → UnitAddCircle))
      (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  rw [← hq.continuous_comp_iff]
  have : Torus.periodicToTorus f ∘ Torus.toUnitTorus 2 = f :=
    Torus.fromUnitTorus_periodicToTorus hp
  rw [this]
  exact hc

/-- The torus Fourier coefficient of the periodic transfer is `smoothFourierCoeff`. -/
theorem Sobolev.mFourierCoeff_periodicToTorus (f : Vec 2 → ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (Torus.periodicToTorus f) k = Torus.smoothFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff Torus.smoothFourierCoeff
  rw [← Torus.integral_periodicToTorus_eq_unitCell (fun x => Torus.torusCharacter k x * f x)]
  apply integral_congr_ae
  filter_upwards with y
  change UnitAddTorus.mFourier (-k) y * f (Torus.unitTorusRepresentative 2 y) =
    UnitAddTorus.mFourier (-k) (Torus.toUnitTorus 2 (Torus.unitTorusRepresentative 2 y)) *
      f (Torus.unitTorusRepresentative 2 y)
  rw [Torus.toUnitTorus_unitTorusRepresentative]

/-- Pointwise bound from weighted `ℓ²` control of the Fourier coefficients. -/
theorem Sobolev.norm_le_sobolevConst_mul_sqrt {f : Vec 2 → ℂ} (hc : Continuous f)
    (hp : Torus.IsZdPeriodic f) {S : ℝ}
    (hsum : HasSum (fun k => sobolevWeight k * ‖Torus.smoothFourierCoeff f k‖ ^ 2) S)
    (x : Vec 2) : ‖f x‖ ≤ sobolevConst * Real.sqrt S := by
  have hsumm : Summable (fun k => ‖Torus.smoothFourierCoeff f k‖) :=
    summable_of_sum_le (fun k => norm_nonneg _) (Sobolev.sum_norm_le_sobolevConst_mul hsum)
  let g : C(UnitAddTorus (Fin 2), ℂ) := ⟨Torus.periodicToTorus f,
      Sobolev.continuous_periodicToTorus hc hp⟩
  have hcoeff : ∀ k, UnitAddTorus.mFourierCoeff g k = Torus.smoothFourierCoeff f k :=
    Sobolev.mFourierCoeff_periodicToTorus f
  have hgsumm : Summable (UnitAddTorus.mFourierCoeff g) := by
    have : UnitAddTorus.mFourierCoeff g = Torus.smoothFourierCoeff f := funext hcoeff
    rw [this]
    exact hsumm.of_norm
  have hser := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hgsumm
    (Torus.toUnitTorus 2 x)
  have hgx : g (Torus.toUnitTorus 2 x) = f x :=
    congrFun (Torus.fromUnitTorus_periodicToTorus hp) x
  rw [hgx] at hser
  have hbound : ‖f x‖ ≤ ∑' k, ‖Torus.smoothFourierCoeff f k‖ := by
    refine hser.norm_le_of_bounded hsumm.hasSum (fun k => ?_)
    rw [hcoeff, norm_smul]
    have hm : ‖UnitAddTorus.mFourier k (Torus.toUnitTorus 2 x)‖ ≤ 1 := by
      calc ‖UnitAddTorus.mFourier k (Torus.toUnitTorus 2 x)‖
          ≤ ‖UnitAddTorus.mFourier k‖ := ContinuousMap.norm_coe_le_norm _ _
        _ = 1 := UnitAddTorus.mFourier_norm
    calc ‖Torus.smoothFourierCoeff f k‖ * ‖UnitAddTorus.mFourier k (Torus.toUnitTorus 2 x)‖
        ≤ ‖Torus.smoothFourierCoeff f k‖ * 1 := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = ‖Torus.smoothFourierCoeff f k‖ := mul_one _
  exact hbound.trans (hasSum_le_of_sum_le hsumm.hasSum (Sobolev.sum_norm_le_sobolevConst_mul hsum))

/-! ### Main theorem -/

theorem Sobolev.sqrt_add_add_le (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Real.sqrt (A + B + C) ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C := by
  have ha := Real.sqrt_nonneg A
  have hb := Real.sqrt_nonneg B
  have hc := Real.sqrt_nonneg C
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hA' := Real.sq_sqrt hA
  have hB' := Real.sq_sqrt hB
  have hC' := Real.sq_sqrt hC
  nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]

theorem Sobolev.l2NormSq_nonneg (f : Vec 2 → ℝ) : 0 ≤ AVenhance.l2NormSq f :=
  setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg (f x))

/-- `H² ⊂ L∞` on `𝕋²`: a smooth `ℤ²`-periodic function is bounded by its `L²` norm and the
`L²` norms of its pure second derivatives. -/
theorem abs_le_sobolevConst_mul {u : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hp : IsZ2Periodic u) (x : Vec 2) :
    |u x| ≤ sobolevConst *
      (Real.sqrt (l2NormSq u) +
        Real.sqrt (l2NormSq (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec 0))) +
        Real.sqrt (l2NormSq (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec 1)))) := by
  have hu' : ContDiff ℝ ∞ u := hu
  have hsum : HasSum
      (fun k : Fin 2 → ℤ => sobolevWeight k *
        ‖Torus.smoothFourierCoeff (Torus.realToComplex u) k‖ ^ 2)
      (l2NormSq u +
        l2NormSq (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec 0)) +
        l2NormSq (fun y => iteratedFDeriv ℝ 2 u y (fun _ => basisVec 1))) := by
    have h := ((Sobolev.hasSum_sq_zeroth hu').add (Sobolev.hasSum_sq_second hu' hp 0)).add
      (Sobolev.hasSum_sq_second hu' hp 1)
    convert h using 1
    funext k
    simp only [sobolevWeight]
    ring
  have hc : Continuous (Torus.realToComplex u) :=
    Complex.ofRealCLM.continuous.comp hu'.continuous
  have hper : Torus.IsZdPeriodic (Torus.realToComplex u) := by
    intro n y
    have h := hp n y
    exact congrArg (fun r : ℝ => (r : ℂ)) h
  have hmain := Sobolev.norm_le_sobolevConst_mul_sqrt hc hper hsum x
  have hnorm : ‖Torus.realToComplex u x‖ = |u x| := by
    simp [Torus.realToComplex]
  rw [hnorm] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ sobolevConst_pos.le)
  exact Sobolev.sqrt_add_add_le _ _ _ (Sobolev.l2NormSq_nonneg _) (Sobolev.l2NormSq_nonneg _)
      (Sobolev.l2NormSq_nonneg _)

end AVenhance.Infra.Section5.AnalyticBridge
