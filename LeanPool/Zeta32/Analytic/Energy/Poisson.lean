/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Component

/-! Potential of the component `ρ_c` (the proof notes (8′), per component):

    2 L_c(x) = kC a c + wC c x   (|x| ≤ a),        2 L_c(x) ≤ kC a c + wC c x   (all x).

Proof: with `t = a cos θ`, `x − a cos θ = −(a/(2e))(e − q₁)(e − q₂)` on the unit circle, `q₁q₂ = 1`,
`q₁ + q₂ = 2x/a`; the Poisson formula for `log|· − q|` evaluates the balayage part and Jensen's
formula the
arcsine part. Outside `[-a, a]` the inequality reduces to `ψ(q) ≥ 0` for `q ≥ 1`, proved by `ψ′
≥ 0`. -/

public section

open Real MeasureTheory Set Filter
open scoped Interval

namespace Zeta32.Analytic.EnergyI
noncomputable section

theorem circleMap_zero_one_eq (θ : ℝ) : circleMap 0 1 θ = ⟨Real.cos θ, Real.sin θ⟩ := by
  apply Complex.ext <;> simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- On the unit circle, `|e − q₁||e − q₂| = 2|cos θ − ξ|` when `q₁ + q₂ = 2ξ`, `q₁q₂ = 1`. -/
theorem norm_mul_norm_circle (q1 q2 : ℂ) (ξ : ℝ) (hs : q1 + q2 = 2 * (ξ : ℂ)) (hp : q1 * q2 = 1)
    (θ : ℝ) : ‖circleMap 0 1 θ - q1‖ * ‖circleMap 0 1 θ - q2‖ = 2 * |Real.cos θ - ξ| := by
  have he := circleMap_zero_one_eq θ
  have hprod : (circleMap 0 1 θ - q1) * (circleMap 0 1 θ - q2) =
      circleMap 0 1 θ * (2 * ((Real.cos θ - ξ : ℝ) : ℂ)) := by
    have : (circleMap 0 1 θ - q1) * (circleMap 0 1 θ - q2) =
        circleMap 0 1 θ ^ 2 - (q1 + q2) * circleMap 0 1 θ + q1 * q2 := by ring
    rw [this, hs, hp, he]
    have hsc := Real.sin_sq_add_cos_sq θ
    apply Complex.ext
    · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
        Complex.re_ofNat, Complex.im_ofNat]
      nlinarith
    · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_im,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
      ring
  rw [← norm_mul, hprod, norm_mul]
  have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
  rw [h1, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp

section decomposition
variable {a : ℝ} (x : ℝ) (q1 q2 : ℂ)

theorem log_abs_decomp (ha : 0 < a) (hs : q1 + q2 = 2 * ((x / a : ℝ) : ℂ)) (hp : q1 * q2 = 1)
    {θ : ℝ} (hθ : a * Real.cos θ ≠ x) :
    Real.log |x - a * Real.cos θ| =
      Real.log (a / 2) + Real.log ‖circleMap 0 1 θ - q1‖ + Real.log ‖circleMap 0 1 θ - q2‖ := by
  have hn := norm_mul_norm_circle q1 q2 (x / a) hs hp θ
  have hne : Real.cos θ - x / a ≠ 0 := by
    intro h; apply hθ; field_simp at h; linarith
  have habs : |x - a * Real.cos θ| = (a / 2) * (‖circleMap 0 1 θ - q1‖ * ‖circleMap 0 1 θ - q2‖)
    := by
    rw [hn]
    rw [show x - a * Real.cos θ = -(a * (Real.cos θ - x / a)) by field_simp; ring, abs_neg, abs_mul,
      abs_of_pos ha]
    ring
  have hpos : 0 < ‖circleMap 0 1 θ - q1‖ * ‖circleMap 0 1 θ - q2‖ := by
    rw [hn]; have := abs_pos.mpr hne; positivity
  have h1 : 0 < ‖circleMap 0 1 θ - q1‖ := by
    rcases (norm_nonneg (circleMap 0 1 θ - q1)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
  have h2 : 0 < ‖circleMap 0 1 θ - q2‖ := by
    rcases (norm_nonneg (circleMap 0 1 θ - q2)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  rw [habs, Real.log_mul (by positivity) hpos.ne', Real.log_mul h1.ne' h2.ne']
  ring

theorem ae_log_abs_decomp (ha : 0 < a) (hs : q1 + q2 = 2 * ((x / a : ℝ) : ℂ)) (hp : q1 * q2 = 1) :
    ∀ᵐ θ ∂(volume : Measure ℝ), Real.log |x - a * Real.cos θ| =
      Real.log (a / 2) + Real.log ‖circleMap 0 1 θ - q1‖ + Real.log ‖circleMap 0 1 θ - q2‖ := by
  have hnull : volume (circleMap 0 1 ⁻¹' {q1, q2}) = 0 :=
    ((Set.toFinite _).countable.preimage_circleMap 0 one_ne_zero).measure_zero _
  have : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ circleMap 0 1 ⁻¹' {q1, q2} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [this] with θ hθ
  apply log_abs_decomp x q1 q2 ha hs hp
  intro h
  apply hθ
  have hn := norm_mul_norm_circle q1 q2 (x / a) hs hp θ
  have : Real.cos θ - x / a = 0 := by rw [← h]; field_simp; ring
  rw [this, abs_zero, mul_zero] at hn
  rcases mul_eq_zero.mp hn with h' | h'
  · left; exact sub_eq_zero.mp (norm_eq_zero.mp h')
  · right; exact sub_eq_zero.mp (norm_eq_zero.mp h')

end decomposition

/-- `L_x(θ) = log|x − a cos θ|`. -/
def Lx (a x θ : ℝ) : ℝ := Real.log |x - a * Real.cos θ|

section formulas
variable {a c : ℝ}

theorem PK_betaC_norm (ha : 0 < a) (hc : 0 < c) (b : ℝ) (hb : b = betaC a c ∨ b = -betaC a c) :
    ‖Complex.I * (b : ℂ)‖ < 1 := by
  have h0 := betaC_pos ha hc.le
  have h1 := betaC_lt_one ha hc
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases hb with h | h <;> subst h <;> simp [abs_of_pos h0] <;> linarith

/-- `L_c` in angular form. -/
theorem potC_eq_theta (ha : 0 < a) (hc : 0 < c) (x : ℝ)
    (hL : IntervalIntegrable (Lx a x) volume 0 (2 * π)) :
    potC a c x = ∫ θ in (0:ℝ)..2 * π, Lx a x θ * fC a c θ := by
  unfold potC
  have hint : IntervalIntegrable (fun θ => Lx a x θ * fC a c θ) volume 0 (2 * π) :=
    hL.mul_continuousOn (continuous_fC ha hc).continuousOn
  have hint' : IntervalIntegrable (fun θ => Lx a x θ * fC a c θ) volume 0 π :=
    hint.mono_set (by
      rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le (by positivity)]
      exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  exact integral_rhoC_eq ha hc (fun t => Real.log |x - t|) hint'

/-- Linear decomposition of `∫ L_x fC` through the Poisson form of `fC`. -/
theorem integral_Lx_fC (ha : 0 < a) (hc : 0 < c) (x : ℝ)
    (hL : IntervalIntegrable (Lx a x) volume 0 (2 * π)) :
    ∫ θ in (0:ℝ)..2 * π, Lx a x θ * fC a c θ =
      (1 / (8 * π)) * (∫ θ in (0:ℝ)..2 * π, Lx a x θ * PK (Complex.I * (betaC a c : ℝ)) θ) +
      (1 / (8 * π)) * (∫ θ in (0:ℝ)..2 * π, Lx a x θ * PK (Complex.I * ((-betaC a c : ℝ))) θ) -
      (c / uC a c / (4 * π)) * ∫ θ in (0:ℝ)..2 * π, Lx a x θ := by
  have hp1 := continuous_PK (PK_betaC_norm ha hc _ (Or.inl rfl))
  have hp2 := continuous_PK (PK_betaC_norm ha hc _ (Or.inr rfl))
  have i1 := hL.mul_continuousOn hp1.continuousOn
  have i2 := hL.mul_continuousOn hp2.continuousOn
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hpt : ∀ θ, Lx a x θ * fC a c θ =
      (1 / (8 * π)) * (Lx a x θ * PK (Complex.I * (betaC a c : ℝ)) θ) +
      (1 / (8 * π)) * (Lx a x θ * PK (Complex.I * ((-betaC a c : ℝ))) θ) -
      (c / uC a c / (4 * π)) * Lx a x θ := by
    intro θ
    have h := fC_eq_PK ha hc θ
    have : fC a c θ = ((PK (Complex.I * (betaC a c : ℝ)) θ + PK (Complex.I * ((-betaC a c : ℝ)))
      θ) / 2
      - c / uC a c) / (4 * π) := by rw [← h]; field_simp
    rw [this]; field_simp; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((i1.const_mul _).add (i2.const_mul _)) (hL.const_mul _),
    intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- `log‖w − q₁‖ + log‖w − q₂‖ = ½ log|w² − 2ξw + 1|²` evaluated at `w = ±iβ`. -/
theorem log_norm_pair_iβ (β ξ : ℝ) (q1 q2 : ℂ) (hs : q1 + q2 = 2 * (ξ : ℂ)) (hp : q1 * q2 = 1)
    (b : ℝ) (hb : b = β ∨ b = -β) (hβ : β ^ 2 < 1) :
    Real.log ‖Complex.I * (b : ℂ) - q1‖ + Real.log ‖Complex.I * (b : ℂ) - q2‖ =
      Real.log ((1 - β^2)^2 + 4 * β^2 * ξ^2) / 2 := by
  have hb2 : b^2 = β^2 := by
    rcases hb with h | h
    · rw [h]
    · rw [h]; ring
  have hprod : (Complex.I * (b : ℂ) - q1) * (Complex.I * (b : ℂ) - q2) = ⟨1 - β^2, -(2 * b * ξ)⟩
    := by
    have : (Complex.I * (b : ℂ) - q1) * (Complex.I * (b : ℂ) - q2) =
        (Complex.I * (b : ℂ))^2 - (q1 + q2) * (Complex.I * (b : ℂ)) + q1 * q2 := by ring
    rw [this, hs, hp]
    apply Complex.ext <;> simp [pow_two] <;> nlinarith
  have hQ : 0 < (1 - β^2)^2 + 4 * β^2 * ξ^2 := by
    have : 0 < 1 - β^2 := by linarith
    positivity
  have hne : (Complex.I * (b : ℂ) - q1) * (Complex.I * (b : ℂ) - q2) ≠ 0 := by
    rw [hprod]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : Complex.I * (b : ℂ) - q1 ≠ 0 := left_ne_zero_of_mul hne
  have h2 : Complex.I * (b : ℂ) - q2 ≠ 0 := right_ne_zero_of_mul hne
  rw [← Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ← norm_mul, hprod,
    Complex.norm_def, Complex.normSq_mk,
    Real.log_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
  congr 1
  rw [show -(2 * b * ξ) * -(2 * b * ξ) = 4 * b^2 * ξ^2 by ring, hb2]
  simp only [pow_two]

end formulas

section psi

/-- `ψ(q) = κ log q − ½ log(q² + β²) + ½ log(β²q² + 1) ≥ 0` for `q ≥ 1` when `κ(1+β²) = 1 − β²`. -/
theorem psi_nonneg {κ β q : ℝ} (hβ : 0 < β) (hκ0 : 0 ≤ κ) (hκ : κ * (1 + β ^ 2) = 1 - β ^ 2) (hq :
  1 ≤ q) :
    Real.log (q^2 + β^2) / 2 - Real.log (β^2 * q^2 + 1) / 2 ≤ κ * Real.log q := by
  let ψ : ℝ → ℝ := fun q => κ * Real.log q - Real.log (q^2 + β^2) / 2 + Real.log (β^2 * q^2 + 1) / 2
  have hderiv : ∀ q : ℝ, 0 < q → HasDerivAt ψ
      (κ / q - q / (q^2 + β^2) + β^2 * q / (β^2 * q^2 + 1)) q := by
    intro q hq
    have h1 := (Real.hasDerivAt_log hq.ne').const_mul κ
    have h2 := ((hasDerivAt_pow 2 q).add_const (β^2)).log (by positivity)
    have h3 := (((hasDerivAt_pow 2 q).const_mul (β^2)).add_const 1).log (by positivity)
    have := (h1.sub (h2.div_const 2)).add (h3.div_const 2)
    convert this using 1
    field_simp
    ring
  have hmono : MonotoneOn ψ (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun q => κ / q - q / (q^2 + β^2) + β^2 * q / (β^2 * q^2 + 1))
    · intro q hq
      exact (hderiv q (by linarith [mem_Ici.mp hq])).continuousAt.continuousWithinAt
    · intro q hq
      rw [interior_Ici] at hq
      exact (hderiv q (by linarith [mem_Ioi.mp hq])).hasDerivWithinAt
    · intro q hq
      rw [interior_Ici] at hq
      have hq0 : 0 < q := by linarith [mem_Ioi.mp hq]
      have hA : 0 < q^2 + β^2 := by positivity
      have hB : 0 < β^2 * q^2 + 1 := by positivity
      have e : κ / q - q / (q^2 + β^2) + β^2 * q / (β^2 * q^2 + 1) =
          κ * β^2 * (q^2 - 1)^2 / (q * (q^2 + β^2) * (β^2 * q^2 + 1)) := by
        field_simp
        linear_combination (q^2 * (1 + β^2)) * hκ
      rw [e]
      positivity
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hq) hq
  simp only [ψ, Real.log_one, mul_zero, one_pow, mul_one] at h
  have : Real.log (1 + β^2) = Real.log (β^2 + 1) := by rw [add_comm]
  linarith

end psi

section potC
variable {a c : ℝ}

theorem rhoC_neg (a c t : ℝ) : rhoC a c (-t) = rhoC a c t := by
  unfold rhoC; rw [neg_sq]

theorem potC_neg (a c x : ℝ) : potC a c (-x) = potC a c x := by
  unfold potC
  have := intervalIntegral.integral_comp_neg (a := -a) (b := a)
    (fun t => Real.log |x - t| * rhoC a c t)
  simp only [neg_neg] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [rhoC_neg]
  rw [show -x - t = -(x - -t) by ring, abs_neg]

theorem wC_neg (c x : ℝ) : wC c (-x) = wC c x := by unfold wC; rw [neg_sq]

/-- Inside the support: `2 L_c(x) = kC + wC`. -/
theorem two_potC_inside (ha : 0 < a) (hc : 0 < c) {x : ℝ} (hx : |x| ≤ a) :
    2 * potC a c x = kC a c + wC c x := by
  set ξ := x / a with hξdef
  have hξ1 : ξ^2 ≤ 1 := by
    rw [hξdef, div_pow, div_le_one (by positivity)]
    nlinarith [abs_nonneg x, sq_abs x]
  set η := √(1 - ξ^2) with hηdef
  have hη2 : η^2 = 1 - ξ^2 := Real.sq_sqrt (by linarith)
  set q1 : ℂ := ⟨ξ, η⟩
  set q2 : ℂ := ⟨ξ, -η⟩
  have hs : q1 + q2 = 2 * ((x / a : ℝ) : ℂ) := by apply Complex.ext <;> simp [q1, q2, ξ]; ring
  have hp : q1 * q2 = 1 := by apply Complex.ext <;> simp [q1, q2] <;> nlinarith
  have hn1 : ‖q1‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]; rw [show ξ * ξ + η * η = 1 by nlinarith]; simp
  have hn2 : ‖q2‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]; rw [show ξ * ξ + -η * -η = 1 by nlinarith]; simp
  have hdec := ae_log_abs_decomp x q1 q2 ha hs hp
  -- integrability of `L_x`
  have hsumint : IntervalIntegrable (fun θ => Real.log (a / 2) + Real.log ‖circleMap 0 1 θ - q1‖ +
      Real.log ‖circleMap 0 1 θ - q2‖) volume 0 (2 * π) :=
    (intervalIntegrable_const.add (intervalIntegrable_log_circle q1)).add
      (intervalIntegrable_log_circle q2)
  have hL : IntervalIntegrable (Lx a x) volume 0 (2 * π) :=
    hsumint.congr_ae (ae_restrict_of_ae (hdec.mono fun θ h => h.symm))
  -- the two families of integrals
  have hI1 : ∫ θ in (0:ℝ)..2 * π, Lx a x θ = 2 * π * Real.log (a / 2) := by
    unfold Lx
    rw [intervalIntegral.integral_congr_ae (hdec.mono fun θ h _ => h),
      intervalIntegral.integral_add (intervalIntegrable_const.add (intervalIntegrable_log_circle
        q1))
        (intervalIntegrable_log_circle q2),
      intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_log_circle q1),
      integral_log_circle, integral_log_circle, hn1, hn2, intervalIntegral.integral_const]
    simp
  have hIP : ∀ w : ℂ, ‖w‖ < 1 → ∫ θ in (0:ℝ)..2 * π, Lx a x θ * PK w θ =
      2 * π * (Real.log (a / 2) + Real.log ‖w - q1‖ + Real.log ‖w - q2‖) := by
    intro w hw
    have hc := (continuous_PK hw).continuousOn (s := uIcc 0 (2 * π))
    have e : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) → Lx a x θ * PK w θ =
        Real.log (a / 2) * PK w θ + PK w θ * Real.log ‖circleMap 0 1 θ - q1‖ +
          PK w θ * Real.log ‖circleMap 0 1 θ - q2‖ := by
      filter_upwards [hdec] with θ h _
      unfold Lx; rw [h]; ring
    rw [intervalIntegral.integral_congr_ae e,
      intervalIntegral.integral_add (((continuous_PK hw).intervalIntegrable _ _).const_mul _ |>.add
        (intervalIntegrable_PK_log_circle hw q1)) (intervalIntegrable_PK_log_circle hw q2),
      intervalIntegral.integral_add (((continuous_PK hw).intervalIntegrable _ _).const_mul _)
        (intervalIntegrable_PK_log_circle hw q1),
      intervalIntegral.integral_const_mul, integral_PK hw, integral_PK_log_sphere hw hn1,
      integral_PK_log_sphere hw hn2]
    ring
  have hβ0 := betaC_pos ha hc.le
  have hβ1 := betaC_lt_one ha hc
  have hβ2 : betaC a c ^ 2 < 1 := by nlinarith
  rw [potC_eq_theta ha hc x hL, integral_Lx_fC ha hc x hL, hI1,
    hIP _ (PK_betaC_norm ha hc _ (Or.inl rfl)), hIP _ (PK_betaC_norm ha hc _ (Or.inr rfl))]
  have hq : ∀ b : ℝ, b = betaC a c ∨ b = -betaC a c →
      Real.log (a / 2) + Real.log ‖Complex.I * (b : ℂ) - q1‖ + Real.log ‖Complex.I * (b : ℂ) - q2‖ =
        Real.log (a / 2) + Real.log ((1 - betaC a c ^ 2)^2 + 4 * betaC a c ^ 2 * ξ^2) / 2 := by
    intro b hb
    rw [add_assoc, log_norm_pair_iβ (betaC a c) ξ q1 q2 (by rw [hs]) hp b hb hβ2]
  rw [hq _ (Or.inl rfl), hq _ (Or.inr rfl)]
  -- the final algebra
  set u := uC a c with hu
  set β := betaC a c with hβ
  have hu0 : 0 < u := uC_pos ha c
  have hm : β * (u + c) = a := betaC_mul ha hc.le
  have h1 : 1 - β^2 = 2 * c / (u + c) := one_sub_betaC_sq ha hc.le
  have hQ : (1 - β^2)^2 + 4 * β^2 * ξ^2 = 4 * (c^2 + x^2) / (u + c)^2 := by
    rw [h1]
    have hβ' : β = a / (u + c) := by rw [hβ]; rfl
    rw [hβ', hξdef]
    have : u + c ≠ 0 := by linarith
    field_simp
    ring
  rw [hQ]
  unfold kC wC
  rw [← hu]
  have hpi : (0:ℝ) < π := Real.pi_pos
  -- logs
  have hl1 : Real.log (4 * (c^2 + x^2) / (u + c)^2) =
      2 * Real.log 2 + Real.log (c^2 + x^2) - 2 * Real.log (u + c) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log (a * c / (u + c)) = Real.log a + Real.log c - Real.log (u + c) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha.ne' hc.ne']
  have hl3 : Real.log (1 + x^2 / c^2) = Real.log (c^2 + x^2) - 2 * Real.log c := by
    rw [show 1 + x^2 / c^2 = (c^2 + x^2) / c^2 by field_simp, Real.log_div (by positivity)
      (by positivity), Real.log_pow]
    push_cast; ring
  have hl4 : Real.log (a / 2) = Real.log a - Real.log 2 := Real.log_div ha.ne' (by norm_num)
  rw [hl1, hl2, hl3, hl4]
  field_simp
  ring

theorem key_alg_out (L Lq Lb κ : ℝ) :
    2 * ((1 / (8 * π)) * (2 * π * (L - Lq + 2 * (Lb / 2))) + (1 / (8 * π)) * (2 * π * (L - Lq + 2 *
      (Lb / 2))) - κ / (4 * π) * (2 * π * (L + Lq))) = L - Lq + Lb - κ * (L + Lq) := by
  field_simp; ring

/-- Outside the support (`x > a`): `2 L_c(x) ≤ kC + wC`. -/
theorem two_potC_outside_pos (ha : 0 < a) (hc : 0 < c) {x : ℝ} (hx : a < x) :
    2 * potC a c x ≤ kC a c + wC c x := by
  set ξ := x / a with hξdef
  have hξ1 : 1 < ξ := by rw [hξdef, one_lt_div ha]; exact hx
  set r := √(ξ^2 - 1) with hrdef
  have hr2 : r^2 = ξ^2 - 1 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set q := ξ + r with hqdef
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  set q1 : ℂ := (q : ℂ)
  set q2 : ℂ := ((ξ - r : ℝ) : ℂ)
  have hqq : q * (ξ - r) = 1 := by rw [hqdef]; nlinarith
  have hs : q1 + q2 = 2 * ((x / a : ℝ) : ℂ) := by
    simp only [q1, q2, hqdef, ← hξdef]; push_cast; ring
  have hp : q1 * q2 = 1 := by simp only [q1, q2]; rw [← Complex.ofReal_mul, hqq]; simp
  have hnq1 : ‖q1‖ = q := by simp only [q1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  -- `|e − q₂| = |e − q₁| / q` on the circle
  have hrel : ∀ θ, q * ‖circleMap 0 1 θ - q2‖ = ‖circleMap 0 1 θ - q1‖ := by
    intro θ
    have hsc := Real.sin_sq_add_cos_sq θ
    have hsq : (q * ‖circleMap 0 1 θ - q2‖)^2 = ‖circleMap 0 1 θ - q1‖^2 := by
      rw [mul_pow, circleMap_zero_one_eq, Complex.sq_norm, Complex.sq_norm]
      simp only [q1, q2, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero]
      have hunit : q^2 * (ξ - r)^2 = 1 := by rw [← mul_pow, hqq]; norm_num
      linear_combination (q^2 - 1) * hsc - 2 * q * Real.cos θ * hqq + hunit
    exact (pow_left_inj₀ (by positivity) (norm_nonneg _) (by norm_num)).mp hsq
  have hpos1 : ∀ θ, 0 < ‖circleMap 0 1 θ - q1‖ := by
    intro θ
    apply norm_pos_iff.mpr
    intro h
    have : ‖circleMap 0 1 θ‖ = ‖q1‖ := by rw [sub_eq_zero.mp h]
    rw [hnq1] at this; simp at this; linarith
  have hdec : ∀ θ, Lx a x θ =
      Real.log (a / 2) - Real.log q + 2 * Real.log ‖circleMap 0 1 θ - q1‖ := by
    intro θ
    have hθ : a * Real.cos θ ≠ x := by
      intro h; have := Real.cos_le_one θ; nlinarith
    unfold Lx
    rw [log_abs_decomp x q1 q2 ha hs hp hθ]
    have h2 : ‖circleMap 0 1 θ - q2‖ = ‖circleMap 0 1 θ - q1‖ / q := by
      rw [← hrel θ]; field_simp
    rw [h2, Real.log_div (hpos1 θ).ne' hq0.ne']
    ring
  have hLfun : Lx a x = fun θ => Real.log (a / 2) - Real.log q +
      2 * Real.log ‖circleMap 0 1 θ - q1‖ := funext hdec
  have hL : IntervalIntegrable (Lx a x) volume 0 (2 * π) := by
    rw [hLfun]; exact intervalIntegrable_const.add ((intervalIntegrable_log_circle q1).const_mul 2)
  have hI1 : ∫ θ in (0:ℝ)..2 * π, Lx a x θ = 2 * π * (Real.log (a / 2) + Real.log q) := by
    rw [hLfun, intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_log_circle q1).const_mul 2), intervalIntegral.integral_const_mul,
      integral_log_circle, hnq1, intervalIntegral.integral_const, posLog_eq_log (by
        rw [abs_of_pos hq0]
        exact hq1.le)]
    simp; ring
  have hIP : ∀ w : ℂ, ‖w‖ < 1 → ∫ θ in (0:ℝ)..2 * π, Lx a x θ * PK w θ =
      2 * π * (Real.log (a / 2) - Real.log q + 2 * Real.log ‖w - q1‖) := by
    intro w hw
    have e : (fun θ => Lx a x θ * PK w θ) = fun θ => (Real.log (a / 2) - Real.log q) * PK w θ +
        2 * (PK w θ * Real.log ‖circleMap 0 1 θ - q1‖) := by
      funext θ; rw [hdec θ]; ring
    rw [e, intervalIntegral.integral_add (((continuous_PK hw).intervalIntegrable _ _).const_mul _)
      ((intervalIntegrable_PK_log_circle hw q1).const_mul 2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_PK hw,
      integral_PK_log_out hw (by rw [hnq1]; exact hq1)]
    ring
  have hβ0 := betaC_pos ha hc.le
  have hβ1 := betaC_lt_one ha hc
  rw [potC_eq_theta ha hc x hL, integral_Lx_fC ha hc x hL, hI1,
    hIP _ (PK_betaC_norm ha hc _ (Or.inl rfl)), hIP _ (PK_betaC_norm ha hc _ (Or.inr rfl))]
  have hnorm : ∀ b : ℝ, b = betaC a c ∨ b = -betaC a c →
      Real.log ‖Complex.I * (b : ℂ) - q1‖ = Real.log (q^2 + betaC a c ^ 2) / 2 := by
    intro b hb
    have hb2 : b^2 = betaC a c ^ 2 := by rcases hb with h | h <;> subst h <;> ring
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    congr 2
    simp only [q1, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  rw [hnorm _ (Or.inl rfl), hnorm _ (Or.inr rfl)]
  -- the final inequality
  set u := uC a c with hu
  set β := betaC a c with hβ
  have hu0 : 0 < u := uC_pos ha c
  have hu2 : u^2 = c^2 + a^2 := uC_sq a c
  have hm : β * (u + c) = a := betaC_mul ha hc.le
  have h1 : 1 - β^2 = 2 * c / (u + c) := one_sub_betaC_sq ha hc.le
  have h2 : 1 + β^2 = 2 * u / (u + c) := one_add_betaC_sq ha hc.le
  have hκ : c / u * (1 + β^2) = 1 - β^2 := by
    rw [h1, h2]; field_simp
  have hpsi := psi_nonneg hβ0 (by positivity) hκ hq1.le
  -- `c² + x² = (a/2)²(q²+β²)(β²q²+1)/(β²q²)`
  have hx2 : x = (a / 2) * (q + 1 / q) := by
    have : 1 / q = ξ - r := by rw [eq_comm, ← hqq]; field_simp
    rw [this]; simp only [hqdef]
    rw [show (a / 2) * (ξ + r + (ξ - r)) = a * ξ by ring, hξdef]; field_simp
  have hcx : c^2 + x^2 = (a / 2)^2 * (q^2 + β^2) * (β^2 * q^2 + 1) / (β^2 * q^2) := by
    rw [hx2]
    have hβa : a = β * (u + c) := hm.symm
    have hua : u^2 = c^2 + (β * (u + c))^2 := by rw [← hβa]; exact hu2
    have hc' : (1 - β^2) * (u + c) = 2 * c := by rw [h1]; field_simp
    field_simp
    rw [hβa]
    linear_combination (-(q^2 * β * (β * (u + c) * (1 - β^2) + 2 * β * c))) * hc'
  unfold kC wC
  rw [← hu]
  have hl2 : Real.log (a * c / (u + c)) = Real.log β + Real.log c := by
    rw [show a * c / (u + c) = β * c by rw [← hm]; field_simp, Real.log_mul hβ0.ne' hc.ne']
  have hl3 : Real.log (1 + x^2 / c^2) = Real.log (c^2 + x^2) - 2 * Real.log c := by
    rw [show 1 + x^2 / c^2 = (c^2 + x^2) / c^2 by field_simp, Real.log_div (by positivity)
      (by positivity), Real.log_pow]
    push_cast; ring
  have hl4 : Real.log (c^2 + x^2) = 2 * Real.log (a / 2) + Real.log (q^2 + β^2) +
      Real.log (β^2 * q^2 + 1) - 2 * Real.log β - 2 * Real.log q := by
    rw [hcx, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by
      positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hl2, hl3, hl4]
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [key_alg_out (Real.log (a / 2)) (Real.log q) (Real.log (q^2 + β^2)) (c / u)]
  linarith

theorem two_potC_le (ha : 0 < a) (hc : 0 < c) (x : ℝ) : 2 * potC a c x ≤ kC a c + wC c x := by
  rcases le_or_gt |x| a with hx | hx
  · exact (two_potC_inside ha hc hx).le
  rcases lt_abs.mp hx with h | h
  · exact two_potC_outside_pos ha hc h
  · have := two_potC_outside_pos ha hc h
    rwa [potC_neg, wC_neg] at this

end potC

end
end Zeta32.Analytic.EnergyI

end
