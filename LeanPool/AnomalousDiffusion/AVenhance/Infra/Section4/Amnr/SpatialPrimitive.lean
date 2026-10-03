/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSize
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.ExplicitBarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds

/-! Extraction of pointwise primitive spatial bounds from the source seminorm. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The source seminorm bounds each actual ordered coordinate derivative.
The factorial and radius factors are retained exactly. -/
theorem amnr_partial_norm_le_of_barNorm (f : Vec 2 → ℝ) (n : ℕ)
    (hf : ContDiff ℝ n f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : AVenhance.barNorm n R f ≤ ENNReal.ofReal B)
    (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤
      B * (n.factorial : ℝ) * R ^ n / ((n : ℝ) + 1) ^ 2 := by
  let c : ℝ := ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : 0 < c * R⁻¹ ^ n := by positivity
  have he : ENNReal.ofReal (c * R⁻¹ ^ n *
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖) ≤ AVenhance.barNorm n R f := by
    rw [AVenhance.Infra.Construction.barNorm_eq_pointwise f n R hf]
    rw [ENNReal.ofReal_mul (show 0 ≤ c * R⁻¹ ^ n from by positivity),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow (show 0 ≤ R⁻¹ from by positivity),
      ENNReal.ofReal_inv_of_pos hR]
    apply mul_le_mul_right
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
      (le_iSup_of_le J (le_iSup_of_le x le_rfl) :
        ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ ≤
          ⨆ K : Fin n → Fin 2, ⨆ y : Vec 2,
            ‖iteratedFDeriv ℝ n f y (fun j => basisVec (K j))‖ₑ)
  have hr := (ENNReal.ofReal_le_ofReal_iff hB).mp (he.trans hb)
  have hd : ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤ B / (c * R⁻¹ ^ n) :=
    (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hr)
  have hident : B / (c * R⁻¹ ^ n) =
      B * (n.factorial : ℝ) * R ^ n / ((n : ℝ) + 1) ^ 2 := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
    dsimp [c]
    rw [inv_div]
    ring
  exact hident ▸ hd

/-- The precise second-order stream-regularity seminorm gives a universal Hessian bound on
an actual stream. This conditional helper consumes the stream-regularity data. -/
theorem amnr_stream_hessian_le_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) (J : Fin 2 → Fin 2) :
    ‖iteratedFDeriv ℝ 2 (Φ m t) x (fun j => basisVec (J j))‖ ≤
      (2 : ℝ) ^ 19 * AVenhance.a β I.Λ m := by
  let E := AVenhance.epsilon β I.Λ m
  let A := AVenhance.a β I.Λ m
  have hE : 0 < E := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 < A := AVenhance.Infra.Cutoff.a_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hs : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
    have ha := (AVenhance.streamSeq_isAdmissible hΦ m).1
    exact ha.comp (contDiff_const.prodMk contDiff_id)
  have hb := (hreg m hm t).2.1 2 le_rfl
  have hp := amnr_partial_norm_le_of_barNorm (Φ m t) 2 (hs.of_le (by simp))
    (R := (2 : ℝ) ^ 8 * E⁻¹) (B := (2 : ℝ) ^ 5 * A * E ^ 2 * (4 ^ 2 / 3 ^ 3))
    (by positivity) (by positivity) (by norm_num [E, A] at hb ⊢; exact hb) x J
  have heq : ((2 : ℝ) ^ 5 * A * E ^ 2 * (4 ^ 2 / 3 ^ 3)) *
      (Nat.factorial 2 : ℝ) * ((2 : ℝ) ^ 8 * E⁻¹) ^ 2 / ((2 : ℝ) + 1) ^ 2 =
      ((2 : ℝ) ^ 26 / 243) * A := by
    norm_num [Nat.factorial]
    field_simp
    ring
  simp only [Nat.cast_ofNat] at hp
  refine hp.trans ?_
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by norm_num) hA.le

end AVenhance.Infra.Section4
