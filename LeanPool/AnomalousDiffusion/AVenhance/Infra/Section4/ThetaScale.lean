/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.BarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Scale bookkeeping for conditional uses of the stream-function and diffusivity bounds
    conclusions.

The hypotheses below deliberately retain the expressions in the conclusions. In particular, `a *
    epsilon^(2 + gamma)` is not silently
replaced in an input hypothesis; its equivalent power form is proved here.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace AVenhance.Infra.Section4

/-- For continuous scalar functions, an `L∞` bound holds at every point,
since Lebesgue measure on `Vec 2` is positive on nonempty open sets. -/
theorem theta_continuous_norm_le_of_eLpNorm_bound {f : Homogenization.Vec 2 → ℝ}
    {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (hbound : eLpNorm f ⊤ volume ≤ ENNReal.ofReal B) :
    ∀ x, ‖f x‖ ≤ B := by
  have hess : eLpNormEssSup f volume ≤ ENNReal.ofReal B := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hbound
  have hae : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ ENNReal.ofReal B := by
    exact (enorm_ae_le_eLpNormEssSup f volume).mono fun x hx => hx.trans hess
  have hnot : ∀ᵐ x ∂volume, x ∉ {x | B < ‖f x‖} := by
    filter_upwards [hae] with x hx
    have hreal : ‖f x‖ ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).mp (by
        simpa [Real.enorm_eq_ofReal_abs] using hx)
    exact not_lt.mpr hreal
  have hzero : volume {x | B < ‖f x‖} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hnot
  have hopen : IsOpen {x : Homogenization.Vec 2 | B < ‖f x‖} :=
    isOpen_lt continuous_const (hf.norm)
  have hempty : {x : Homogenization.Vec 2 | B < ‖f x‖} = ∅ :=
    hopen.eq_empty_of_measure_zero hzero
  intro x
  by_contra hnotle
  have hx : x ∈ {x : Homogenization.Vec 2 | B < ‖f x‖} := by
    change B < ‖f x‖
    exact lt_of_not_ge hnotle
  rw [hempty] at hx
  exact hx

/-- The defining recursion for an admitted stream makes the preceding stream
an admissible smooth periodic potential, which is the drift used by θ. -/
theorem theta_prev_stream_admissible {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hΦ : AVenhance.IsStreamSeq I Φ) (hm : 2 ≤ m) :
    AVenhance.IsAdmissibleStream (Φ (m - 1)) := by
  obtain ⟨h, _⟩ := hΦ.2 m (by omega)
  exact h

/-- Unpack the `iSup` in `barNorm` one ordered coordinate derivative at a
time. This is the `L∞` coefficient input used by the differentiated energy
argument. -/
theorem barNorm_coordinate_eLpNorm_le {n : ℕ} {R B : ℝ}
    {f : Homogenization.Vec 2 → ℝ} (hR : 0 < R)
    (hbar : AVenhance.barNorm n R f ≤ ENNReal.ofReal B) :
    ∀ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume ≤
        ENNReal.ofReal B /
          (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
            (ENNReal.ofReal R)⁻¹ ^ n) := by
  let K : ENNReal := ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
    (ENNReal.ofReal R)⁻¹ ^ n
  have hK0 : K ≠ 0 := by
    dsimp [K]
    have hcoef : 0 < ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) := by positivity
    have hcoef' : ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hcoef
    have hRtop : ENNReal.ofReal R ≠ ⊤ := by simp
    exact mul_ne_zero hcoef' (pow_ne_zero n (ENNReal.inv_ne_zero.mpr hRtop))
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    have hR' : ENNReal.ofReal R ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hR
    have hcoefTop : ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) ≠ ⊤ := by simp
    have hRinvtop : (ENNReal.ofReal R)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hR'
    exact ENNReal.mul_ne_top hcoefTop (ENNReal.pow_ne_top hRinvtop)
  have hsup : K * (⨆ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume) ≤ ENNReal.ofReal B := by
    simpa [K, AVenhance.barNorm, mul_assoc] using hbar
  have hsup' : (⨆ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume) * K ≤
      (ENNReal.ofReal B / K) * K := by
    rw [ENNReal.div_mul_cancel hK0 hKtop]
    simpa [mul_comm] using hsup
  have hsup_le := (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp hsup'
  intro i
  exact (le_iSup (fun i : Fin n → Fin 2 =>
      eLpNorm (fun x => iteratedFDeriv ℝ n f x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume) i).trans <| by
    simpa [K] using hsup_le

/-- The high-order stream derivative conclusion of the stream-function estimates, copied at scale
`m - 1`, supplies each coordinate derivative's `L∞` seminorm. -/
theorem theta_stream_deriv_eLpNorm_of_A3 {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, ∀ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n (Φ (m - 1) t) x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) /
        (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal
            (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹))⁻¹ ^ n) := by
  intro n hn t i
  have hmpos : 1 ≤ m - 1 := by omega
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hR : 0 < 2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹ := by
    positivity
  exact (barNorm_coordinate_eLpNorm_le hR (hA3 (m - 1) hmpos t n hn)) i

/-- The factorial and radius weights in barNorm cancel to give a direct
coordinate derivative bound. This is the coefficient form used in the
differentiated energy estimate. -/
theorem theta_stream_deriv_eLpNorm_numeric_of_A3 {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, ∀ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n (Φ (m - 1) t) x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) *
        ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n) := by
  intro n hn t i
  let r : ℝ := 2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹
  let c : ℝ := ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)
  let K : ℝ := 2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
    AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
    (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)
  let B : ℝ := K * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * r ^ n
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hr : 0 < r := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
    rw [AVenhance.a]
    exact Real.rpow_pos_of_pos he _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscale : B * c * r⁻¹ ^ n = K := by
    have hfac : (n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2 *
        (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) = 1 := by
      field_simp
    have hrpow : r ^ n * r⁻¹ ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hr), one_pow]
    dsimp [B, c]
    calc
      K * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * r ^ n *
          (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * r⁻¹ ^ n =
        K * (((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
          (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ))) * (r ^ n * r⁻¹ ^ n) := by ring
      _ = K := by rw [hfac, hrpow]; ring
  have hden : ENNReal.ofReal c * (ENNReal.ofReal r)⁻¹ ^ n ≠ 0 := by
    apply mul_ne_zero
    · exact ENNReal.ofReal_ne_zero_iff.mpr hc
    · have hrTop : ENNReal.ofReal r ≠ ⊤ := by simp
      exact pow_ne_zero n (ENNReal.inv_ne_zero.mpr hrTop)
  have hdenTop : ENNReal.ofReal c * (ENNReal.ofReal r)⁻¹ ^ n ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · apply ENNReal.pow_ne_top
      exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hr)
  have hprod : ENNReal.ofReal B *
      (ENNReal.ofReal c * (ENNReal.ofReal r)⁻¹ ^ n) = ENNReal.ofReal K := by
    have hinvpow : (ENNReal.ofReal r)⁻¹ ^ n = ENNReal.ofReal (r⁻¹ ^ n) := by
      rw [← ENNReal.ofReal_inv_of_pos hr]
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hr.le)]
    rw [hinvpow]
    rw [← ENNReal.ofReal_mul hc.le]
    rw [← ENNReal.ofReal_mul hB]
    congr 1
    calc
      B * (c * r⁻¹ ^ n) = B * c * r⁻¹ ^ n := by ring
      _ = K := hscale
  have hratio : ENNReal.ofReal K /
      (ENNReal.ofReal c * (ENNReal.ofReal r)⁻¹ ^ n) ≤ ENNReal.ofReal B :=
    (ENNReal.div_le_iff hden hdenTop).2 hprod.symm.le
  have hraw := theta_stream_deriv_eLpNorm_of_A3 I Φ hm hA3 n hn t i
  dsimp [r, c, K, B] at hraw hratio ⊢
  exact hraw.trans hratio

theorem ThetaScale.theta_A3_factorial_weight_le {n : ℕ} (hn : 2 ≤ n) :
    (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) *
      ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) ≤ (n.factorial : ℝ) := by
  let z : ℝ := (n : ℝ) + 1
  have hz1 : 1 ≤ z := by
    dsimp [z]
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hz3 : 3 ≤ z := by
    dsimp [z]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlin : z + 1 ≤ z ^ 2 := by nlinarith [sq_nonneg z]
  have hsq : (z + 1) ^ 2 ≤ z ^ 4 := by
    calc
      (z + 1) ^ 2 = (z + 1) * (z + 1) := by ring
      _ ≤ z ^ 2 * z ^ 2 := mul_le_mul hlin hlin (by positivity) (by positivity)
      _ = z ^ 4 := by ring
  have hpow : z ^ 4 ≤ z ^ 5 := by
    calc
      z ^ 4 = z ^ 4 * 1 := by ring
      _ ≤ z ^ 4 * z := mul_le_mul_of_nonneg_left hz1 (by positivity)
      _ = z ^ 5 := by ring
  have hpoly : ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 1) ^ 5 := by
    calc
      ((n : ℝ) + 2) ^ 2 = (z + 1) ^ 2 := by dsimp [z]; ring
      _ ≤ z ^ 5 := hsq.trans hpow
      _ = ((n : ℝ) + 1) ^ 5 := by dsimp [z]
  have hrewrite :
      (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) *
        ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) =
      ((n.factorial : ℝ) * ((n : ℝ) + 2) ^ 2) / ((n : ℝ) + 1) ^ 5 := by
    field_simp
  rw [hrewrite]
  apply (div_le_iff₀ (by positivity)).2
  calc
    (n.factorial : ℝ) * ((n : ℝ) + 2) ^ 2 ≤
        (n.factorial : ℝ) * ((n : ℝ) + 1) ^ 5 :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (n.factorial : ℝ) * ((n : ℝ) + 1) ^ 5 := rfl

/-- The stream-function derivative estimate in the simple factorial-radius form used by
the energy recursion. -/
theorem theta_stream_deriv_eLpNorm_simple_of_A3 {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, ∀ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n (Φ (m - 1) t) x
        (fun j => Homogenization.basisVec (i j))) ⊤ volume ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 * (n.factorial : ℝ) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n) := by
  intro n hn t i
  have hraw := theta_stream_deriv_eLpNorm_numeric_of_A3 I Φ hm hA3 n hn t i
  have hfac := ThetaScale.theta_A3_factorial_weight_le hn
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 ≤ AVenhance.a β I.Λ (m - 1) := by
    rw [AVenhance.a]
    positivity
  have hreal :
      2 ^ 5 * AVenhance.a β I.Λ (m - 1) * AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) *
        ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n ≤
      2 ^ 5 * AVenhance.a β I.Λ (m - 1) * AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        (n.factorial : ℝ) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
    have hcoef : 0 ≤ 2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 := by positivity
    calc
      _ = (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2) *
          ((((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) *
            ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2)) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by ring
      _ ≤ (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2) * (n.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfac hcoef)
              (pow_nonneg (by positivity) n)
  exact hraw.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The stream-function coordinate bound is pointwise for the smooth stream potential,
not merely an essential-supremum statement. -/
theorem theta_stream_deriv_pointwise_of_A3 {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hΦ : AVenhance.IsStreamSeq I Φ) (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, ∀ i : Fin n → Fin 2, ∀ x : Homogenization.Vec 2,
      ‖iteratedFDeriv ℝ n (Φ (m - 1) t) x
        (fun j => Homogenization.basisVec (i j))‖ ≤
      2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        (n.factorial : ℝ) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
  intro n hn t i x
  let f : Homogenization.Vec 2 → ℝ := Φ (m - 1) t
  let g : Homogenization.Vec 2 → ℝ := fun y =>
    iteratedFDeriv ℝ n f y (fun j => Homogenization.basisVec (i j))
  have hprev : AVenhance.IsAdmissibleStream (Φ (m - 1)) :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Homogenization.Vec 2 => (t, y)) := contDiff_const.prodMk contDiff_id
    have hcomp := hprev.1.comp hmap
    simpa [f, Function.uncurry, Function.comp_def] using hcomp
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  have hderiv : Continuous (fun y : Homogenization.Vec 2 => iteratedFDeriv ℝ n f y) :=
    hfN.continuous_iteratedFDeriv (m := n) le_rfl
  have heval : Continuous
      (fun p : (ContinuousMultilinearMap ℝ (fun _ : Fin n => Homogenization.Vec 2) ℝ) ×
        (Fin n → Homogenization.Vec 2) => p.1 p.2) := continuous_eval
  have hg : Continuous g := by
    change Continuous (fun y => iteratedFDeriv ℝ n f y
      (fun j => Homogenization.basisVec (i j)))
    exact heval.comp (hderiv.prodMk continuous_const)
  have hLp := theta_stream_deriv_eLpNorm_simple_of_A3 I Φ hm hA3 n hn t i
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
    rw [AVenhance.a]
    exact Real.rpow_pos_of_pos he _
  have hB : 0 ≤ 2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
      (n.factorial : ℝ) *
      (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by positivity
  have hpoint := theta_continuous_norm_le_of_eLpNorm_bound hg hB hLp x
  simpa [g, Real.norm_eq_abs] using hpoint

theorem theta_kappa_power_identity {β : ℝ} {Λ m : ℕ}
    (hε : 0 < AVenhance.epsilon β Λ m) :
    AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ (2 + AVenhance.gamma β) =
      AVenhance.epsilon β Λ m ^ (β + AVenhance.gamma β) := by
  rw [AVenhance.a]
  rw [← Real.rpow_add hε]
  congr 1
  ring

/-- The diffusivity bounds control the coefficient ratio generated by the twice differentiated
stream potential. This is the `epsilon^(-2-gamma)` scale before the analytic
radius normalization. -/
theorem theta_second_stream_derivative_over_kappa
    {β c κ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^
      (2 + AVenhance.gamma β)) ≤ κ) :
    (AVenhance.epsilon β I.Λ m ^ (β - 2)) / κ ≤
      c⁻¹ * AVenhance.epsilon β I.Λ m ^ (-2 - AVenhance.gamma β) := by
  let e := AVenhance.epsilon β I.Λ m
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hpow := theta_kappa_power_identity (β := β) (Λ := I.Λ) (m := m) he
  have hκ' : c * e ^ (β + AVenhance.gamma β) ≤ κ := by
    simpa [e, hpow] using hκ
  have hden : 0 < c * e ^ (β + AVenhance.gamma β) := by positivity
  have hκpos : 0 < κ := lt_of_lt_of_le hden hκ'
  have hinv : κ⁻¹ ≤ (c * e ^ (β + AVenhance.gamma β))⁻¹ :=
    inv_le_inv₀ hκpos hden |>.2 hκ'
  have hnum : 0 ≤ e ^ (β - 2) := Real.rpow_nonneg he.le _
  have hmul := mul_le_mul_of_nonneg_left hinv hnum
  have hpowSub : e ^ (β - 2) / e ^ (β + AVenhance.gamma β) =
      e ^ (-2 - AVenhance.gamma β) := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  calc
    e ^ (β - 2) / κ = e ^ (β - 2) * κ⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ e ^ (β - 2) * (c * e ^ (β + AVenhance.gamma β))⁻¹ := hmul
    _ = c⁻¹ * (e ^ (β - 2) / e ^ (β + AVenhance.gamma β)) := by ring
    _ = c⁻¹ * e ^ (-2 - AVenhance.gamma β) := by rw [hpowSub]

end AVenhance.Infra.Section4
