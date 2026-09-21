/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Quadratic.Polynomial
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.R
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.QuadraticSeries

/-! # Native integral quadratic transformations -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

private lemma pochhammer_ne_zero_of_re_pos {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval c ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨k, _, hk⟩
  have h := congrArg Complex.re hk
  simp only [natCast_re, neg_re] at h
  linarith

private lemma Gamma_mul_regRPolynomial (n : ℕ) (p q x y : ℂ)
    (hc : 0 < (p + q).re) :
    Gamma (p + q) * regRPolynomial n p q x y =
      carlsonRPolynomialNumerator₂ n p q x y /
        (ascPochhammer ℂ n).eval (p + q) := by
  have hreg (k : ℕ) : p + q ≠ -(k : ℂ) := by
    intro h
    have h' := congrArg Complex.re h
    simp only [neg_re, natCast_re] at h'
    linarith
  have hG := Gamma_add_nat_div_Gamma_eq (n := n) (p + q) hreg
  have hG0 := Gamma_ne_zero_of_re_pos hc
  have hp0 := pochhammer_ne_zero_of_re_pos hc n
  have hG' : Gamma (p + q + n) =
      (ascPochhammer ℂ n).eval (p + q) * Gamma (p + q) :=
    (div_eq_iff hG0).mp hG
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma, hG']
  field_simp

private lemma Gamma_mul_regRPolynomial_even_opposite
    (n : ℕ) {β : ℂ} (hβ : 0 < β.re) (w : ℂ) :
    Gamma (β + β) * regRPolynomial (2 * n) β β w (-w) =
      (ascPochhammer ℂ n).eval (1 / 2) /
        (ascPochhammer ℂ n).eval (β + 1 / 2) * w ^ (2 * n) := by
  have hb : 0 < (β + β).re := by simpa using add_pos hβ hβ
  rw [Gamma_mul_regRPolynomial _ _ _ _ _ hb,
    numerator₂_even_opposite, show β + β = 2 * β by ring,
    ascPochhammer_eval_double]
  have hp := pochhammer_ne_zero_of_re_pos hβ n
  have hq := pochhammer_ne_zero_of_re_pos (c := β + 1 / 2) (by
    simp only [add_re, div_ofNat_re, one_re]; linarith) n
  field_simp

private lemma rIntegral_firstQuadratic_near_one (t β w : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hw : ‖w‖ < 1) :
    rIntegral (2 * t) β β (1 - w) (1 + w) =
      rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) := by
  let L : ℕ → ℂ := fun n => Gamma (β + β) *
    ((ascPochhammer ℂ n).eval (-(2 * t)) / (n.factorial : ℂ) *
      regRPolynomial n β β w (-w))
  let R : ℕ → ℂ := fun n => Gamma ((β + t) + (1 / 2 - t)) *
    ((ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) *
      regRPolynomial n (β + t) (1 / 2 - t) 0 (w ^ 2))
  have hl : HasSum L (rIntegral (2 * t) β β (1 - w) (1 + w)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-(2 * t))
      (pair β β) (pair w (-w)) hbleft (by
        intro i; fin_cases i <;> simpa [pair] using hw)).mul_left (Gamma (β + β))
    have hnodes : (fun i => 1 - pair w (-w) i) = pair (1 - w) (1 + w) := by
      ext i; fin_cases i <;> simp [pair]
    simpa only [hnodes, neg_neg, carlsonRIntegral, sum_pair, L] using H
  have hr : HasSum R (rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-t)
      (pair (β + t) (1 / 2 - t)) (pair 0 (w ^ 2)) hbright (by
        intro i; fin_cases i
        · simp [pair]
        · simpa [pair, norm_pow] using pow_lt_one₀ (norm_nonneg w) hw (by decide : 2 ≠ 0)
      )).mul_left (Gamma ((β + t) + (1 / 2 - t)))
    have hnodes : (fun i => 1 - pair 0 (w ^ 2) i) = pair 1 (1 - w ^ 2) := by
      ext i; fin_cases i <;> simp [pair]
    simpa only [hnodes, neg_neg, carlsonRIntegral, sum_pair, R] using H
  have hodd (n : ℕ) (hn : n ∉ Set.range (fun m : ℕ => 2 * m)) : L n = 0 := by
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · exact (hn ⟨m, hm.symm⟩).elim
    · subst n
      simp [L, regRPolynomial_eq_zero_of_odd _ (by exact ⟨m, rfl⟩)]
  have hi : Function.Injective (fun m : ℕ => 2 * m) := by
    intro i j h
    dsimp only at h
    omega
  have he := (hi.hasSum_iff hodd).mpr hl
  have hβ : 0 < β.re := hbleft 0
  have hc : 0 < (β + 1 / 2).re := by
    simp only [add_re, div_ofNat_re, one_re]; linarith
  have heq (n : ℕ) : L (2 * n) = R n := by
    have hfac : ((2 * n).factorial : ℂ) =
        4 ^ n * (ascPochhammer ℂ n).eval (1 / 2) * (n.factorial : ℂ) := by
      have H := ascPochhammer_eval_double (1 / 2 : ℂ) n
      norm_num [ascPochhammer_eval_one] at H ⊢
      exact H
    have hhalf := pochhammer_ne_zero_of_re_pos (c := (1 / 2 : ℂ)) (by norm_num) n
    have hsum : β + t + (1 / 2 - t) = β + 1 / 2 := by ring
    have hsingle : Gamma ((β + t) + (1 / 2 - t)) *
        regRPolynomial n (β + t) (1 / 2 - t) 0 (w ^ 2) =
        (ascPochhammer ℂ n).eval (1 / 2 - t) * (w ^ 2) ^ n /
          (ascPochhammer ℂ n).eval (β + 1 / 2) := by
      rw [Gamma_mul_regRPolynomial _ _ _ _ _ (by rwa [hsum]), hsum,
        ← carlsonRPolynomialNumerator₂_swap, numerator₂_zero_right]
    dsimp only [L, R]
    rw [show Gamma (β + β) *
        ((ascPochhammer ℂ (2 * n)).eval (-(2 * t)) / ((2 * n).factorial : ℂ) *
          regRPolynomial (2 * n) β β w (-w)) =
        (ascPochhammer ℂ (2 * n)).eval (-(2 * t)) / ((2 * n).factorial : ℂ) *
          (Gamma (β + β) * regRPolynomial (2 * n) β β w (-w)) by ring]
    rw [Gamma_mul_regRPolynomial_even_opposite n hβ w,
      show -(2 * t) = 2 * (-t) by ring, ascPochhammer_eval_double, hfac]
    have hrw := congrArg (fun v : ℂ => (ascPochhammer ℂ n).eval (-t) /
      (n.factorial : ℂ) * v) hsingle
    rw [show -t + (1 : ℂ) / 2 = 1 / 2 - t by ring]
    convert! hrw.symm using 1 <;> field_simp
    all_goals ring
  have hs : HasSum R (rIntegral (2 * t) β β (1 - w) (1 + w)) := by
    simpa only [Function.comp_def, heq] using he
  exact hs.unique hr

private lemma rIntegral_smul_of_re_pos (t p q x y : ℂ) {m : ℂ} (hm : 0 < m.re)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    rIntegral t p q (m * x) (m * y) = m ^ t * rIntegral t p q x y := by
  change carlsonRIntegral t (pair p q) (pair (m * x) (m * y)) = _
  rw [show pair (m * x) (m * y) = (fun i => m * pair x y i) by
    ext i; fin_cases i <;> rfl]
  exact carlsonRIntegral_smul_of_re_pos t hm hz

/-- Equal parameters eliminate odd powers in the expansion around equal nodes. -/
private lemma hasSum_rIntegral_opposite (t β v : ℂ)
    (hb : pair β β ∈ mvBetaConvergent) (hv : ‖v‖ < 1) :
    HasSum (fun m => (ascPochhammer ℂ (2 * m)).eval (-t) / ((2 * m).factorial : ℂ) *
      ((ascPochhammer ℂ m).eval (1 / 2) / (ascPochhammer ℂ m).eval (β + 1 / 2) * v ^ (2 * m)))
      (rIntegral t β β (1 - v) (1 + v)) := by
  let L : ℕ → ℂ := fun n => Gamma (β + β) *
    ((ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) * regRPolynomial n β β v (-v))
  have hl : HasSum L (rIntegral t β β (1 - v) (1 + v)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-t) (pair β β) (pair v (-v)) hb
      (by intro i; fin_cases i <;> simpa [pair] using hv)).mul_left (Gamma (β + β))
    have hnodes : (fun i => 1 - pair v (-v) i) = pair (1 - v) (1 + v) := by
      ext i; fin_cases i <;> simp [pair]
    simpa only [hnodes, neg_neg, carlsonRIntegral, sum_pair, L] using H
  have hodd (n : ℕ) (hn : n ∉ Set.range (fun m : ℕ => 2 * m)) : L n = 0 := by
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · exact (hn ⟨m, hm.symm⟩).elim
    · subst n
      simp [L, regRPolynomial_eq_zero_of_odd _ (by exact ⟨m, rfl⟩)]
  have hi : Function.Injective (fun m : ℕ => 2 * m) := by intro i j h; dsimp at h; omega
  have H := (hi.hasSum_iff hodd).mpr hl
  convert! H using 1
  ext m
  dsimp [L, Function.comp_def]
  rw [show Gamma (β + β) *
      ((ascPochhammer ℂ (2 * m)).eval (-t) / ((2 * m).factorial : ℂ) *
        regRPolynomial (2 * m) β β v (-v)) =
      (ascPochhammer ℂ (2 * m)).eval (-t) / ((2 * m).factorial : ℂ) *
        (Gamma (β + β) * regRPolynomial (2 * m) β β v (-v)) by ring,
    Gamma_mul_regRPolynomial_even_opposite m (β := β) (hb 0)]

/-- Carlson's double-series proof of 6.10-1 near equal nodes. -/
private lemma rIntegral_secondQuadratic_near_one (t β : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent) :
    (fun w => rIntegral t β β ((1 - w) ^ 2) ((1 + w) ^ 2)) =ᶠ[𝓝 0]
      (fun w => rIntegral t (2 * β + t) (1 / 2 - β - t) 1 (1 - w ^ 2)) := by
  have hc : 0 < (β + 1 / 2).re := by
    have hβ := hbleft 0
    change 0 < β.re at hβ
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have hc' : 1 / 2 ≤ (β + 1 / 2).re := by
    have hβ := hbleft 0
    change 0 < β.re at hβ
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have hw : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < 1 :=
    continuous_norm.continuousAt.eventually_lt_const (by simp)
  have hdcont : ContinuousAt (fun w : ℂ => (1 + w ^ 2 : ℂ).re) 0 := by fun_prop
  have hd : ∀ᶠ w : ℂ in 𝓝 0, 0 < (1 + w ^ 2 : ℂ).re :=
    hdcont.eventually_const_lt (by simp)
  have hv : ∀ᶠ w : ℂ in 𝓝 0, ‖2 * w / (1 + w ^ 2)‖ < 1 :=
    (show ContinuousAt (fun w : ℂ => ‖2 * w / (1 + w ^ 2)‖) 0 by
      fun_prop (disch := norm_num)).eventually_lt_const (by simp)
  have hs : ∀ᶠ w : ℂ in 𝓝 0, 4 * (‖-t‖ + 1) * ‖w‖ < 1 / 2 :=
    (show ContinuousAt (fun w : ℂ => 4 * (‖-t‖ + 1) * ‖w‖) 0 by fun_prop).eventually_lt_const (by simp)
  filter_upwards [hw, hd, hv, hs] with w hw hd hv hs
  let d := 1 + w ^ 2
  let v := 2 * w / d
  have hd0 : d ≠ 0 := ne_zero_of_re_pos hd
  have hnodes : pair (1 - v) (1 + v) ∈ carlsonRVariableDomain := by
    have h := abs_re_le_norm v
    intro i; fin_cases i
    · change 0 < (1 - v).re
      simp only [sub_re, one_re]; linarith [le_abs_self v.re]
    · change 0 < (1 + v).re
      simp only [add_re, one_re]; linarith [neg_le_abs v.re]
  have hx : d * (1 - v) = (1 - w) ^ 2 := by dsimp [v]; field_simp; dsimp [d]; ring
  have hy : d * (1 + v) = (1 + w) ^ 2 := by dsimp [v]; field_simp; dsimp [d]; ring
  have H := (hasSum_rIntegral_opposite t β v hbleft hv).mul_left (d ^ t)
  have hscale := rIntegral_smul_of_re_pos t β β (1 - v) (1 + v) hd hnodes
  rw [hx, hy] at hscale
  rw [← hscale] at H
  have hrows : HasSum (fun m => ∑' k, quadraticSeriesCoeff (-t) (β + 1 / 2) m k *
      w ^ (2 * (m + k))) (rIntegral t β β ((1 - w) ^ 2) ((1 + w) ^ 2)) := by
    convert! H using 1
    ext m
    rw [(hasSum_quadraticSeries_row (-t) (β + 1 / 2) w m hw).tsum_eq]
    change _ / d ^ (-t + (2 * m : ℕ)) = _
    rw [cpow_add _ _ hd0, cpow_neg, cpow_natCast]
    have hfac : ((2 * m).factorial : ℂ) =
        4 ^ m * (ascPochhammer ℂ m).eval (1 / 2) * (m.factorial : ℂ) := by
      have H := ascPochhammer_eval_double (1 / 2 : ℂ) m
      norm_num [ascPochhammer_eval_one] at H ⊢
      exact H
    have hfactorial (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [hfac]
    dsimp [v]
    rw [div_pow, mul_pow, show (2 : ℂ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp [hd0, hfactorial, pochhammer_ne_zero_of_re_pos hc m,
      pochhammer_ne_zero_of_re_pos (c := (1 / 2 : ℂ)) (by norm_num) m]
    rw [mul_div_mul_right _ _ (pochhammer_ne_zero_of_re_pos (c := (1 / 2 : ℂ)) (by norm_num) m)]
  have hsum : (2 * β + t) + (1 / 2 - β - t) = β + 1 / 2 := by ring
  have hright : HasSum (fun n =>
      ((ascPochhammer ℂ n).eval (-t) * (ascPochhammer ℂ n).eval (-t + 1 - (β + 1 / 2)) /
        ((ascPochhammer ℂ n).eval (β + 1 / 2) * n.factorial)) * w ^ (2 * n))
      (rIntegral t (2 * β + t) (1 / 2 - β - t) 1 (1 - w ^ 2)) := by
    have H := (hasSum_regCarlsonRIntegral_near_one (-t)
      (pair (2 * β + t) (1 / 2 - β - t)) (pair 0 (w ^ 2)) hbright (by
        intro i; fin_cases i
        · simp [pair]
        · simpa [pair, norm_pow] using pow_lt_one₀ (norm_nonneg w) hw (by decide : 2 ≠ 0)
      )).mul_left (Gamma ((2 * β + t) + (1 / 2 - β - t)))
    have hnodes : (fun i => 1 - pair 0 (w ^ 2) i) = pair 1 (1 - w ^ 2) := by
      ext i; fin_cases i <;> simp [pair]
    simp only [hnodes, neg_neg] at H
    convert! H using 1
    ext n
    have hp : Gamma ((2 * β + t) + (1 / 2 - β - t)) *
        regRPolynomial n (2 * β + t) (1 / 2 - β - t) 0 (w ^ 2) =
        (ascPochhammer ℂ n).eval (1 / 2 - β - t) * (w ^ 2) ^ n /
          (ascPochhammer ℂ n).eval (β + 1 / 2) := by
      rw [Gamma_mul_regRPolynomial _ _ _ _ _ (by rwa [hsum]), hsum,
        ← carlsonRPolynomialNumerator₂_swap, numerator₂_zero_right]
    rw [show -t + 1 - (β + 1 / 2) = 1 / 2 - β - t by ring, pow_mul]
    linear_combination -(ascPochhammer ℂ n).eval (-t) / (n.factorial : ℂ) * hp
    all_goals simp only [rIntegral, carlsonRIntegral, sum_pair]
  rw [← hrows.tsum_eq, tsum_quadraticSeries_eq (-t) (β + 1 / 2) w hc' hs]
  exact hright.tsum_eq

private lemma rIntegral_firstQuadratic_of_normalized (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hm : 0 < ((x + y) / 2).re) (hm2 : 0 < (arithmeticMeanSq x y).re)
    (hw : ‖(y - x) / (x + y)‖ < 1) :
    rIntegral (2 * t) β β x y =
      rIntegral t (β + t) (1 / 2 - t) (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  let m := (x + y) / 2
  let w := (y - x) / (x + y)
  have hsub {v : ℂ} (hv : ‖v‖ < 1) : 0 < (1 - v).re := by
    have h := re_le_norm v
    simp only [sub_re, one_re]
    linarith
  have hl : pair (1 - w) (1 + w) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hsub hw
    · change 0 < (1 + w).re
      simpa only [sub_neg_eq_add] using
        hsub (v := -w) (by simpa only [norm_neg] using (hw : ‖w‖ < 1))
  have hr : pair 1 (1 - w ^ 2) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · norm_num [pair, carlsonRightHalfPlane]
    · exact hsub (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw (by decide))
  have hsum : x + y ≠ 0 := by
    intro h
    simp [h] at hm
  have hx : m * (1 - w) = x := by dsimp [m, w]; field_simp; ring
  have hy : m * (1 + w) = y := by dsimp [m, w]; field_simp; ring
  have hg : m ^ 2 * (1 - w ^ 2) = geometricMeanSq x y := by
    dsimp [m, w, geometricMeanSq]; field_simp; ring
  have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hm))
  have hpow : (m ^ (2 : ℕ)) ^ t = m ^ (2 * t) := by
    symm
    exact cpow_ofNat_mul' (by linarith [harg.1]) (by linarith [harg.2]) t
  have H := rIntegral_firstQuadratic_near_one t β w hbleft hbright hw
  have Hleft := rIntegral_smul_of_re_pos (2 * t) β β (1 - w) (1 + w) hm hl
  have Hright := rIntegral_smul_of_re_pos t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) hm2 hr
  rw [hx, hy, H] at Hleft
  change rIntegral t (β + t) (1 / 2 - t) (m ^ 2 * 1) (m ^ 2 * (1 - w ^ 2)) =
    (m ^ (2 : ℕ)) ^ t * rIntegral t (β + t) (1 / 2 - t) 1 (1 - w ^ 2) at Hright
  rw [mul_one, hg, hpow] at Hright
  exact Hleft.trans Hright.symm

/-- Homogeneity transports the normalized local identity to a neighborhood of `(1,1)`. -/
private lemma rIntegral_secondQuadratic_eventually (t β : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent) :
    (fun z : Fin 2 → ℂ => rIntegral t β β (z 0 ^ 2) (z 1 ^ 2)) =ᶠ[𝓝 (fun _ => 1)]
      (fun z => rIntegral t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq (z 0) (z 1)) (geometricMeanSq (z 0) (z 1))) := by
  let o : Fin 2 → ℂ := fun _ => 1
  let m : (Fin 2 → ℂ) → ℂ := fun z => (z 0 + z 1) / 2
  let w : (Fin 2 → ℂ) → ℂ := fun z => (z 1 - z 0) / (z 0 + z 1)
  have hm : ContinuousAt m o := by dsimp [m]; fun_prop
  have hw : ContinuousAt w o := by dsimp [w]; fun_prop (disch := norm_num [o])
  have hw0 : w o = 0 := by simp [w, o]
  have hpos (f : (Fin 2 → ℂ) → ℂ) (hf : ContinuousAt f o) (ho : f o = 1) :
      ∀ᶠ z in 𝓝 o, 0 < (f z).re :=
    (Complex.continuous_re.continuousAt.comp hf).eventually_const_lt (by
      change 0 < (f o).re
      rw [ho]; norm_num)
  have hM := hpos (fun z => m z ^ 2) (hm.pow 2) (by norm_num [m, o])
  have hL₀ := hpos (fun z => (1 - w z) ^ 2) (hw.const_sub 1 |>.pow 2) (by simp [hw0])
  have hL₁ := hpos (fun z => (1 + w z) ^ 2) (hw.const_add 1 |>.pow 2) (by simp [hw0])
  have hR := hpos (fun z => 1 - w z ^ 2)
    (by fun_prop : ContinuousAt (fun z => 1 - w z ^ 2) o) (by simp [hw0])
  have hlocal := (show Tendsto w (𝓝 o) (𝓝 0) by simpa only [hw0] using hw.tendsto).eventually
    (rIntegral_secondQuadratic_near_one t β hbleft hbright)
  filter_upwards [hM, hL₀, hL₁, hR, hlocal] with z hM hL₀ hL₁ hR hlocal
  have hden : z 0 + z 1 ≠ 0 := by
    intro h
    simp [m, h] at hM
  have hleft : pair ((1 - w z) ^ 2) ((1 + w z) ^ 2) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hL₀
    · exact hL₁
  have hright : pair 1 (1 - w z ^ 2) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · norm_num [pair, carlsonRightHalfPlane]
    · exact hR
  have hx : m z ^ 2 * (1 - w z) ^ 2 = z 0 ^ 2 := by dsimp [m, w]; field_simp; ring
  have hy : m z ^ 2 * (1 + w z) ^ 2 = z 1 ^ 2 := by dsimp [m, w]; field_simp; ring
  have hg : m z ^ 2 * (1 - w z ^ 2) = geometricMeanSq (z 0) (z 1) := by
    dsimp [m, w, geometricMeanSq]; field_simp; ring
  have HL := rIntegral_smul_of_re_pos t β β ((1 - w z) ^ 2) ((1 + w z) ^ 2) hM hleft
  have HR := rIntegral_smul_of_re_pos t (2 * β + t) (1 / 2 - β - t) 1 (1 - w z ^ 2) hM hright
  rw [hx, hy, hlocal] at HL
  rw [mul_one, hg] at HR
  exact HL.trans HR.symm

/-- Carlson's first quadratic transformation 6.9-3 on a common native integral domain.

The extra convergence hypotheses make both sides genuine Dirichlet integrals. The larger
parameter domain is treated separately in `QuadraticContinuation` and `EqualParameter`. -/
theorem rIntegral_firstQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (β + t) (1 / 2 - t) ∈ mvBetaConvergent)
    (hz : FirstQuadraticDomain x y) :
    rIntegral (2 * t) β β x y =
      rIntegral t (β + t) (1 / 2 - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  let X : ℂ → ℂ := fun s => 1 - s + s * x
  let Y : ℂ → ℂ := fun s => 1 - s + s * y
  let S : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hX (s : ℂ) : AnalyticAt ℂ X s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hY (s : ℂ) : AnalyticAt ℂ Y s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hpath (s : ℂ) (hs : s ∈ S) : FirstQuadraticDomain (X s) (Y s) := by
    obtain ⟨r, hr, rfl⟩ := hs
    exact hz.affine hr
  have hleft : AnalyticOnNhd ℂ (fun s => rIntegral (2 * t) β β (X s) (Y s)) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral (2 * t) hbleft _ (hpath s hs).1).comp
      (f := fun u => pair (X u) (Y u))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact hX s
    · exact hY s
  have hright : AnalyticOnNhd ℂ (fun s => rIntegral t (β + t) (1 / 2 - t)
      (arithmeticMeanSq (X s) (Y s)) (geometricMeanSq (X s) (Y s))) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral t hbright _ (hpath s hs).2).comp
      (f := fun u => pair (arithmeticMeanSq (X u) (Y u)) (geometricMeanSq (X u) (Y u)))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (((hX s).add (hY s)).div_const (c := 2)).pow 2
    · exact (hX s).mul (hY s)
  have hS : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have h0 : (0 : ℂ) ∈ S := ⟨0, by norm_num, by simp⟩
  have h1 : (1 : ℂ) ∈ S := ⟨1, by norm_num, by simp⟩
  have hlocal : (fun s => rIntegral (2 * t) β β (X s) (Y s)) =ᶠ[𝓝 0]
      (fun s => rIntegral t (β + t) (1 / 2 - t)
        (arithmeticMeanSq (X s) (Y s)) (geometricMeanSq (X s) (Y s))) := by
    have hm := (Complex.continuous_re.continuousAt.comp
      (((hX 0).continuousAt.add (hY 0).continuousAt).div_const 2)).eventually_const_lt
      (by norm_num [X, Y] : (0 : ℝ) < (((X 0 + Y 0) / 2 : ℂ)).re)
    have hm2 := (Complex.continuous_re.continuousAt.comp
      ((((hX 0).continuousAt.add (hY 0).continuousAt).div_const 2).pow 2)).eventually_const_lt
      (by norm_num [X, Y] : (0 : ℝ) < ((((X 0 + Y 0) / 2 : ℂ) ^ 2)).re)
    have hw := ((((hY 0).continuousAt.sub (hX 0).continuousAt).div
      ((hX 0).continuousAt.add (hY 0).continuousAt) (by norm_num [X, Y])).norm).eventually_lt_const
      (by norm_num [X, Y] : ‖(Y 0 - X 0) / (X 0 + Y 0)‖ < 1)
    filter_upwards [hm, hm2, hw] with s hs hs2 hw
    exact rIntegral_firstQuadratic_of_normalized t β (X s) (Y s) hbleft hbright hs hs2 hw
  have H := hleft.eqOn_of_preconnected_of_eventuallyEq hright hS h0 hlocal h1
  simpa [X, Y] using H

private lemma rIntegral_secondQuadratic_of_re_pos (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent)
    (hz : SecondQuadraticDomain x y) (hx : 0 < x.re) (hy : 0 < y.re) :
    rIntegral t β β (x ^ 2) (y ^ 2) =
      rIntegral t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  let X : ℂ → ℂ := fun s => 1 - s + s * x
  let Y : ℂ → ℂ := fun s => 1 - s + s * y
  let S : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hX (s : ℂ) : AnalyticAt ℂ X s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hY (s : ℂ) : AnalyticAt ℂ Y s :=
    (analyticAt_const.sub analyticAt_id).add (analyticAt_id.mul analyticAt_const)
  have hpath (s : ℂ) (hs : s ∈ S) : SecondQuadraticDomain (X s) (Y s) := by
    obtain ⟨r, hr, rfl⟩ := hs
    exact hz.affine hx hy hr
  have hleft : AnalyticOnNhd ℂ (fun s => rIntegral t β β (X s ^ 2) (Y s ^ 2)) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral t hbleft _ (hpath s hs).1).comp
      (f := fun u => pair (X u ^ 2) (Y u ^ 2))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (hX s).pow 2
    · exact (hY s).pow 2
  have hright : AnalyticOnNhd ℂ (fun s => rIntegral t (2 * β + t) (1 / 2 - β - t)
      (arithmeticMeanSq (X s) (Y s)) (geometricMeanSq (X s) (Y s))) S := by
    intro s hs
    apply (analyticOnNhd_carlsonRIntegral t hbright _ (hpath s hs).2).comp
      (f := fun u => pair (arithmeticMeanSq (X u) (Y u)) (geometricMeanSq (X u) (Y u)))
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (((hX s).add (hY s)).div_const (c := 2)).pow 2
    · exact (hX s).mul (hY s)
  have hS : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have h0 : (0 : ℂ) ∈ S := ⟨0, by norm_num, by simp⟩
  have h1 : (1 : ℂ) ∈ S := ⟨1, by norm_num, by simp⟩
  have hnodes : Tendsto (fun s => pair (X s) (Y s)) (𝓝 (0 : ℂ)) (𝓝 (fun _ => 1)) := by
    have hcont : ContinuousAt (fun s => pair (X s) (Y s)) (0 : ℂ) := by
      apply continuousAt_pi.mpr
      intro i; fin_cases i
      · exact (hX 0).continuousAt
      · exact (hY 0).continuousAt
    convert! hcont.tendsto using 1
    congr 1
    ext i; fin_cases i <;> simp [pair, X, Y]
  have hlocal := hnodes.eventually (rIntegral_secondQuadratic_eventually t β hbleft hbright)
  have H := hleft.eqOn_of_preconnected_of_eventuallyEq hright hS h0 hlocal h1
  simpa [X, Y] using H

/-- Carlson's second quadratic transformation 6.10-1 on a common native integral domain. -/
theorem rIntegral_secondQuadratic (t β x y : ℂ)
    (hbleft : pair β β ∈ mvBetaConvergent)
    (hbright : pair (2 * β + t) (1 / 2 - β - t) ∈ mvBetaConvergent)
    (hz : SecondQuadraticDomain x y) :
    rIntegral t β β (x ^ 2) (y ^ 2) =
      rIntegral t (2 * β + t) (1 / 2 - β - t)
        (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  rcases hz.same_sign with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact rIntegral_secondQuadratic_of_re_pos t β x y hbleft hbright hz hx hy
  · have hA : arithmeticMeanSq (-x) (-y) = arithmeticMeanSq x y := by
      dsimp [arithmeticMeanSq]; ring
    have hG : geometricMeanSq (-x) (-y) = geometricMeanSq x y := by
      dsimp [geometricMeanSq]; ring
    have hz' : SecondQuadraticDomain (-x) (-y) := by
      simpa only [SecondQuadraticDomain, neg_sq, hA, hG] using hz
    simpa only [neg_sq, hA, hG] using
      rIntegral_secondQuadratic_of_re_pos t β (-x) (-y) hbleft hbright hz' hx hy

end DirichletTransform.TwoVariable
