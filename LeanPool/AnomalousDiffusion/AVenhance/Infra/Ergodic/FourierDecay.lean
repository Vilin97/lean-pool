/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Fourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Fourier decay from averaged derivative bounds -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

/- Derivatives in one fixed coordinate, iterated `n` times. -/
/-- Iterate differentiation in one coordinate direction. -/
def coordDerivIter {d : ℕ} (i : Fin d) : ℕ → (Vec d → ℂ) → Vec d → ℂ
  | 0, f => f
  | n + 1, f => coordDeriv i (coordDerivIter i n f)

theorem FourierDecay.coordDeriv_contDiff_top {d : ℕ} (i : Fin d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordDeriv i f) := by
  have h := hf.contDiff_fderiv_apply (m := ∞) (by simp)
  have hc : ContDiff ℝ ∞ (fun x : Vec d => (x, basisVec i)) :=
    contDiff_id.prodMk contDiff_const
  convert h.comp hc using 1
  ext x
  rfl

theorem coordDerivIter_contDiff_top {d : ℕ} (i : Fin d) (n : ℕ)
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordDerivIter i n f) := by
  induction n with
  | zero => simpa [coordDerivIter] using hf
  | succ n ih =>
      simpa [coordDerivIter] using FourierDecay.coordDeriv_contDiff_top i ih

theorem FourierDecay.coordDeriv_periodic {d : ℕ} (i : Fin d) {f : Vec d → ℂ}
    (hf : IsZdPeriodic f) : IsZdPeriodic (coordDeriv i f) := by
  intro k x
  let a : Vec d := intVector k
  have hfun : (fun y : Vec d => f (y + a)) = f := by
    funext y
    exact hf k y
  have hder : fderiv ℝ f (x + a) = fderiv ℝ f x := by
    calc
      fderiv ℝ f (x + a) = fderiv ℝ (fun y => f (y + a)) x := by
        rw [fderiv_comp_add_right]
      _ = fderiv ℝ f x := by rw [hfun]
  exact congrArg (fun L : Vec d →L[ℝ] ℂ => L (basisVec i)) hder

theorem coordDerivIter_periodic {d : ℕ} (i : Fin d) (n : ℕ)
    {f : Vec d → ℂ} (hf : IsZdPeriodic f) :
    IsZdPeriodic (coordDerivIter i n f) := by
  induction n with
  | zero => simpa [coordDerivIter] using hf
  | succ n ih =>
      simpa [coordDerivIter] using FourierDecay.coordDeriv_periodic i ih

theorem smoothFourierCoeff_norm_le_integral_norm {d : ℕ}
    {f : Vec d → ℂ} (k : Fin d → ℤ) :
    ‖smoothFourierCoeff f k‖ ≤ ∫ x in unitCell d, ‖f x‖ := by
  rw [smoothFourierCoeff]
  calc
    _ ≤ ∫ x, ‖torusCharacter k x * f x‖
        ∂((volume : Measure (Vec d)).restrict (unitCell d)) :=
      norm_integral_le_integral_norm _
    _ = ∫ x in unitCell d, ‖f x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul]
      have hchar : ‖torusCharacter k x‖ = 1 := by
        simp [torusCharacter, UnitAddTorus.mFourier]
      rw [hchar, one_mul]

theorem smoothFourierCoeff_coordDerivIter {d : ℕ} (hd : 0 < d)
    (i : Fin d) (n : ℕ) {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f) (k : Fin d → ℤ) :
    smoothFourierCoeff (coordDerivIter i n f) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) ^ n * smoothFourierCoeff f k := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  induction n with
  | zero => simp [coordDerivIter]
  | succ n ih =>
      have hmult := smoothFourierCoeff_coordDeriv i
        ((coordDerivIter_contDiff_top i n hf).of_le (by simp))
        (coordDerivIter_periodic i n hper) k
      rw [coordDerivIter, hmult, ih]
      ring

/- The derivative premise records the source's order-positive averaged
   analyticity bounds on every repeated coordinate derivative. -/
/-- Factorial analytic bounds for positive-order coordinate derivatives in L¹. -/
def HasCoordinateAnalyticL1Bounds {d : ℕ} (f : Vec d → ℂ)
    (Cf r : ℝ) : Prop :=
  ∀ (i : Fin d) (n : ℕ), 0 < n →
    (∫ x in unitCell d, ‖coordDerivIter i n f x‖) ≤
      Cf * (n.factorial : ℝ) / r ^ n

/-- Repeatedly applying the coordinate Fourier multiplier bounds a Fourier
coefficient by the averaged derivative of the same order. -/
theorem smoothFourierCoeff_le_derivative_average
    {d : ℕ} (hd : 0 < d) (i : Fin d) (n : ℕ)
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    (M : ℝ) (hM :
      (∫ x in unitCell d, ‖coordDerivIter i n f x‖) ≤ M)
    (k : Fin d → ℤ) (hki : k i ≠ 0) :
    ‖smoothFourierCoeff f k‖ ≤ M / (2 * Real.pi * ‖k i‖) ^ n := by
  have hmult := smoothFourierCoeff_coordDerivIter hd i n hf hper k
  have hkiPos : 0 < ‖k i‖ := norm_pos_iff.mpr hki
  have hc : ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ =
      2 * Real.pi * ‖k i‖ := by
    simp [Complex.norm_intCast, Int.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le]
  have hderivCoeff :
      (2 * Real.pi * ‖k i‖) ^ n * ‖smoothFourierCoeff f k‖ ≤ M := by
    calc
      _ = ‖smoothFourierCoeff (coordDerivIter i n f) k‖ := by
        rw [hmult, norm_mul, norm_pow, hc]
      _ ≤ ∫ x in unitCell d, ‖coordDerivIter i n f x‖ :=
        smoothFourierCoeff_norm_le_integral_norm k
      _ ≤ M := hM
  have hden : 0 < (2 * Real.pi * ‖k i‖) ^ n := by positivity
  rw [le_div_iff₀ hden]
  simpa [mul_comm] using hderivCoeff

theorem FourierDecay.factorial_fourier_decay_optimization {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, 0 < n ∧
      (n.factorial : ℝ) / (2 * Real.pi * x) ^ n ≤
        512 * Real.exp (-x / 512) := by
  let e : ℝ := Real.exp 1
  let α : ℝ := (2 * Real.pi / e) * x
  let n : ℕ := ⌊α⌋₊
  have hepos : 0 < e := by dsimp [e]; positivity
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπlower : 2 ≤ Real.pi := Real.two_le_pi
  have heupper : e < 3 := by
    dsimp [e]
    exact Real.exp_one_lt_three
  have hαlower : 1 ≤ α := by
    dsimp [α]
    rw [div_mul_eq_mul_div]
    have hmul : 2 * Real.pi * x ≥ 4 := by nlinarith
    rw [le_div_iff₀ hepos]
    nlinarith [heupper]
  have hn : 0 < n := by
    have : 1 ≤ n := Nat.le_floor (by exact_mod_cast hαlower)
    omega
  have hnle : (n : ℝ) ≤ α := Nat.floor_le (by positivity)
  have hlt : α < (n : ℝ) + 1 := Nat.lt_floor_add_one α
  have hden : 0 < 2 * Real.pi * x := by positivity
  have hnle' : (n : ℝ) * e ≤ 2 * Real.pi * x := by
    calc
      (n : ℝ) * e ≤ α * e := mul_le_mul_of_nonneg_right hnle hepos.le
      _ = 2 * Real.pi * x := by
        dsimp [α]
        field_simp
  have hratio : (n : ℝ) / (2 * Real.pi * x) ≤ 1 / e := by
    rw [div_le_div_iff₀ hden hepos]
    nlinarith [hnle']
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hquot : (n.factorial : ℝ) / (2 * Real.pi * x) ^ n ≤
      Real.exp (-(n : ℝ)) := by
    have hpow : ((n : ℝ) / (2 * Real.pi * x)) ^ n ≤ (1 / e) ^ n :=
      pow_le_pow_left₀ (by positivity) hratio n
    have hfac' : (n.factorial : ℝ) / (2 * Real.pi * x) ^ n ≤
        ((n : ℝ) / (2 * Real.pi * x)) ^ n := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right hfac (by positivity)
    calc
      _ ≤ ((n : ℝ) / (2 * Real.pi * x)) ^ n := hfac'
      _ ≤ (1 / e) ^ n := hpow
      _ = Real.exp (-(n : ℝ)) := by
        calc
          (1 / e) ^ n = (Real.exp (-1)) ^ n := by simp [e, Real.exp_neg]
          _ = Real.exp ((n : ℝ) * (-1)) := by rw [← Real.exp_nat_mul (-1) n]
          _ = Real.exp (-(n : ℝ)) := by
            congr 1
            ring
  have hexp : Real.exp (-(n : ℝ)) ≤
      Real.exp 1 * Real.exp (-(x / 512)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlt' := hlt
    dsimp [α] at hlt'
    have hcoef : (1 / 512 : ℝ) ≤ 2 * Real.pi / e := by
      rw [le_div_iff₀ hepos]
      nlinarith [hπlower]
    have hx0 : 0 ≤ x := by linarith
    have hxle : x / 512 ≤ (2 * Real.pi / e) * x := by
      calc
        x / 512 = (1 / 512) * x := by ring
        _ ≤ (2 * Real.pi / e) * x := mul_le_mul_of_nonneg_right hcoef hx0
    linarith
  have hfactor : Real.exp 1 ≤ 512 := by
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
  refine ⟨n, hn, ?_⟩
  calc
    _ ≤ Real.exp (-(n : ℝ)) := hquot
    _ ≤ Real.exp 1 * Real.exp (-(x / 512)) := hexp
    _ ≤ 512 * Real.exp (-(x / 512)) := by
      exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ = 512 * Real.exp (-x / 512) := by
      congr 1
      congr 1
      ring

/-- The factorial optimization used to pass from iterated derivative bounds
to exponential decay; exported for Parseval tail estimates. -/
theorem factorial_fourier_decay_optimization_exists {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, 0 < n ∧
      (n.factorial : ℝ) / (2 * Real.pi * x) ^ n ≤
        512 * Real.exp (-x / 512) :=
  FourierDecay.factorial_fourier_decay_optimization hx

/-- Exponential decay of nonzero Fourier modes from averaged bounds on every
positive-order repeated coordinate derivative. The lower-frequency condition
is the one used in `l.averages`: `r * ‖k‖ ≥ 1`. -/
theorem smoothFourierCoeff_expDecay_of_coordinateAnalyticL1Bounds
    {d : ℕ} (hd : 0 < d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (_hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL1Bounds f Cf r)
    (k : Fin d → ℤ) (hk : k ≠ 0) (hlarge : 1 ≤ r * ‖k‖) :
    ‖smoothFourierCoeff f k‖ ≤
      512 * Cf * Real.exp (-r * ‖k‖ / 512) := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin d)).Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hd
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin d)) (fun j => ‖k j‖) hnonempty
  have hmax' : ∀ j : Fin d, ‖k j‖ ≤ ‖k i‖ := by
    intro j
    exact hmax j (Finset.mem_univ j)
  have hle : ‖k‖ ≤ ‖k i‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg (k i))).2 hmax'
  have hge : ‖k i‖ ≤ ‖k‖ := norm_le_pi_norm k i
  have hnorm : ‖k i‖ = ‖k‖ := le_antisymm hge hle
  have hki : k i ≠ 0 := by
    intro hzero
    have hall : ∀ j : Fin d, k j = 0 := by
      intro j
      have hj : ‖k j‖ ≤ ‖k i‖ := hmax' j
      rw [hzero, norm_zero] at hj
      have hjzero : ‖k j‖ = 0 := le_antisymm hj (norm_nonneg _)
      exact norm_eq_zero.mp hjzero
    apply hk
    funext j
    exact hall j
  have hmpos : 0 < ‖k i‖ := norm_pos_iff.mpr hki
  have hx : 1 ≤ r * ‖k i‖ := by simpa [hnorm] using hlarge
  obtain ⟨n, hn, hopt⟩ := FourierDecay.factorial_fourier_decay_optimization hx
  have hcoef : ‖smoothFourierCoeff f k‖ ≤
      Cf * (n.factorial : ℝ) / (2 * Real.pi * (r * ‖k i‖)) ^ n := by
    have hcomponent := smoothFourierCoeff_le_derivative_average hd i n hf hper
      (Cf * (n.factorial : ℝ) / r ^ n) (hderiv i n hn) k hki
    convert hcomponent using 1
    ring
  calc
    ‖smoothFourierCoeff f k‖ ≤
        Cf * (n.factorial : ℝ) / (2 * Real.pi * (r * ‖k i‖)) ^ n := hcoef
    _ = Cf * ((n.factorial : ℝ) / (2 * Real.pi * (r * ‖k i‖)) ^ n) := by ring
    _ ≤ Cf * (512 * Real.exp (-(r * ‖k i‖) / 512)) :=
      mul_le_mul_of_nonneg_left hopt hCf
    _ = 512 * Cf * Real.exp (-r * ‖k‖ / 512) := by
      rw [hnorm]
      rw [show -(r * ‖k‖) / 512 = -r * ‖k‖ / 512 by ring]
      ring

end

end AVenhance.Infra.Ergodic
