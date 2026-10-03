/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Contour.Moments
public import LeanPool.Zeta32.Analytic.Contour.PartialFractions

/-! the proof notes, §5.1: logistic integral representation of `U_r`.

With `t = 1/2 + iy`, `ρ(y) = (π/2) sech²(πy)` and `w = 2rρ + iρ'` (`wfun` of `Interfaces.lean`),
integration by parts gives `∫ G(t) w(y) dy = 2r E[G] + E[G']`, i.e. `U_r(f) = B((tf)') + 2r B(tf)`
for `G = t f`. Together with the moments of `Contour/Moments.lean` this identifies every entry:

    ∫ (t · t^e R_n)(1/2 + iy) w(y) dy = C_r · slope n e + intercept r n e.
-/

public section

open MeasureTheory Set Filter Topology Finset Polynomial

namespace Zeta32.Analytic.Contour

noncomputable section

/-- `U_r(G) := ∫ G(1/2 + iy) w(y) dy`. -/
def Uint (r : ℚ) (G : ℂ → ℂ) : ℂ := ∫ y : ℝ, G (tpt y) * wfun r y

lemma hasDerivAt_tpt (y : ℝ) : HasDerivAt tpt Complex.I y := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have := (h.const_mul Complex.I).const_add (1/2 : ℂ)
  unfold tpt
  simpa using this

/-- **Integration by parts**: `∫ G(t) w = 2r E[G] + E[G']`. -/
theorem Uint_eq (r : ℚ) {G G' : ℂ → ℂ} (hG : ∀ y : ℝ, HasDerivAt G (G' (tpt y)) (tpt y))
    (hc' : Continuous fun y => G' (tpt y))
    {C C' : ℝ} {N N' : ℕ} (hb : ∀ y, ‖G (tpt y)‖ ≤ C * (1 + |y|) ^ N)
    (hb' : ∀ y, ‖G' (tpt y)‖ ≤ C' * (1 + |y|) ^ N') :
    Uint r G = 2 * (r : ℂ) * Erho G + Erho G' := by
  have hc : Continuous fun y => G (tpt y) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hG y).continuousAt.comp continuous_tpt.continuousAt
  have hu : ∀ y, HasDerivAt (fun y => G (tpt y)) (G' (tpt y) * Complex.I) y :=
    fun y => (hG y).comp y (hasDerivAt_tpt y)
  have hv : ∀ y, HasDerivAt (fun y => (rho y : ℂ)) (rhoDeriv y : ℂ) y :=
    fun y => (hasDerivAt_rho y).ofReal_comp
  have i1 := integrable_mul_rho hc hb
  have i2 := integrable_mul_rhoDeriv hc hb
  have i3 : Integrable (fun y => G' (tpt y) * Complex.I * (rho y : ℂ)) :=
    integrable_mul_rho (hc'.mul continuous_const) (fun y => by
      rw [norm_mul, Complex.norm_I, mul_one]; exact hb' y)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun y => G (tpt y)) (v := fun y => (rho y : ℂ))
    (u' := fun y => G' (tpt y) * Complex.I) (v' := fun y => (rhoDeriv y : ℂ))
    (fun y _ => hu y) (fun y _ => hv y) i2 i3 i1
  unfold Uint Erho
  have hsplit : ∀ y, G (tpt y) * wfun r y = 2 * (r : ℂ) * (G (tpt y) * (rho y : ℂ)) +
      Complex.I * (G (tpt y) * (rhoDeriv y : ℂ)) := by
    intro y; rw [wfun_eq]; ring
  simp_rw [hsplit]
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, hibp]
  have h3 : ∫ y, G' (tpt y) * Complex.I * (rho y : ℂ) =
      Complex.I * ∫ y, G' (tpt y) * (rho y : ℂ) := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [h3]
  linear_combination (-(∫ y, G' (tpt y) * (rho y : ℂ))) * Complex.I_mul_I

lemma Erho_const_mul (c : ℂ) (φ : ℂ → ℂ) : Erho (fun t => c * φ t) = c * Erho φ := by
  unfold Erho
  simp_rw [mul_assoc]
  rw [integral_const_mul]

lemma norm_pow_tpt_le (m : ℕ) (y : ℝ) : ‖tpt y ^ m‖ ≤ 1 * (1 + |y|) ^ m := by
  rw [norm_pow, one_mul]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_tpt_le y) m

/-- `U_r(t^m) = (m+1)B_m + 2r B_{m+1}`, i.e. `∫ t^{m+1} w = moment r m`. -/
theorem Uint_pow (r : ℚ) (m : ℕ) : Uint r (fun t => t ^ (m + 1)) = (moment r m : ℂ) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun t : ℂ => t ^ (m + 1))
      ((fun t : ℂ => ((m + 1 : ℕ) : ℂ) * t ^ m) (tpt y)) (tpt y) := by
    intro y
    have := hasDerivAt_pow (m + 1) (tpt y)
    rwa [Nat.add_sub_cancel] at this
  rw [Uint_eq r (G := fun t : ℂ => t ^ (m + 1)) (G' := fun t : ℂ => ((m + 1 : ℕ) : ℂ) * t ^ m)
    hd (continuous_const.mul (continuous_tpt.pow m)) (norm_pow_tpt_le (m + 1))
    (C' := (m + 1 : ℕ)) (N' := m) (fun y => by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left ((norm_pow_tpt_le m y).trans (by rw [one_mul]))
        (Nat.cast_nonneg _))]
  rw [Erho_const_mul, Erho_pow, Erho_pow]
  unfold moment
  push_cast
  ring

lemma inv_add_nat_eq_invPow (j : ℕ) (t : ℂ) : (t + j)⁻¹ = invPow j 0 t := by
  unfold invPow; rw [zero_add, pow_one]

lemma norm_inv_add_nat_tpt_le (j : ℕ) (y : ℝ) : ‖(tpt y + j)⁻¹‖ ≤ 2 := by
  rw [inv_add_nat_eq_invPow]
  have := norm_invPow_le (t := tpt y) (by rw [tpt_re]) j 0
  simpa using this

lemma norm_pole_tpt_le (j : ℕ) (y : ℝ) : ‖tpt y * (tpt y + j)⁻¹‖ ≤ 2 * (1 + |y|) ^ 1 := by
  rw [norm_mul, pow_one, mul_comm 2]
  exact mul_le_mul (norm_tpt_le y) (norm_inv_add_nat_tpt_le j y) (norm_nonneg _) (by positivity)

lemma continuous_pole_tpt (j : ℕ) : Continuous fun y => tpt y * (tpt y + j)⁻¹ := by
  refine continuous_tpt.mul (Continuous.inv₀ (continuous_tpt.add continuous_const) fun y => ?_)
  exact add_nat_ne_zero (by rw [tpt_re]; norm_num) j

lemma Erho_invPow_zero (j : ℕ) :
    Erho (invPow j 0) = ((zeta2val - ((H 2 j : ℚ) : ℝ) : ℝ) : ℂ) := by
  rw [Erho_invPow]
  unfold zeta2val
  norm_num

lemma Erho_invPow_one (j : ℕ) :
    Erho (invPow j 1) = 2 * ((zeta3val - ((H 3 j : ℚ) : ℝ) : ℝ) : ℂ) := by
  rw [Erho_invPow]
  unfold zeta3val
  norm_num

/-- `U_r((t+j)^{-1}) = 2j C_r + β_j`, i.e. `∫ t/(t+j) w = 2j C_r + beta r j`. -/
theorem Uint_pole (r : ℚ) (j : ℕ) :
    Uint r (fun t => t * (t + j)⁻¹) = 2 * (j : ℂ) * ((Cr r : ℝ) : ℂ) + (beta r j : ℂ) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun t : ℂ => t * (t + j)⁻¹)
      ((fun t : ℂ => (j : ℂ) * invPow j 1 t) (tpt y)) (tpt y) := by
    intro y
    have hne : tpt y + j ≠ 0 := add_nat_ne_zero (by rw [tpt_re]; norm_num) j
    have h1 : HasDerivAt (fun t : ℂ => t + j) 1 (tpt y) := (hasDerivAt_id _).add_const _
    have h := (hasDerivAt_id' (tpt y)).fun_mul (h1.fun_inv hne)
    convert h using 1
    unfold invPow
    field_simp
    ring
  have hc' : Continuous fun y => (j : ℂ) * invPow j 1 (tpt y) :=
    continuous_const.mul ((differentiableOn_invPow j 1).continuousOn.comp_continuous continuous_tpt
      tpt_mem_strip)
  rw [Uint_eq r (G := fun t : ℂ => t * (t + j)⁻¹) (G' := fun t : ℂ => (j : ℂ) * invPow j 1 t)
    hd hc' (norm_pole_tpt_le j) (C' := (j : ℝ) * 2 ^ (1 + 1)) (N' := 0) (fun y => by
      rw [norm_mul, Complex.norm_natCast, pow_zero, mul_one]
      exact mul_le_mul_of_nonneg_left (norm_invPow_le (by rw [tpt_re]) j 1) (Nat.cast_nonneg _))]
  rw [Erho_const_mul, Erho_invPow_one]
  have hG : Erho (fun t => t * (t + j)⁻¹) = 1 - (j : ℂ) * Erho (invPow j 0) := by
    have h0 := Erho_pow 0
    rw [bernoulli'_zero, Rat.cast_one] at h0
    rw [← h0, ← Erho_const_mul]
    have i0 : Integrable (fun y : ℝ => tpt y ^ 0 * (rho y : ℂ)) := integrable_pow_rho 0
    have i1 : Integrable (fun y : ℝ => (j : ℂ) * invPow j 0 (tpt y) * (rho y : ℂ)) := by
      simpa only [mul_assoc] using (integrable_invPow_rho j 0).const_mul (j : ℂ)
    unfold Erho
    beta_reduce
    rw [← integral_sub i0 i1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hne : tpt y + j ≠ 0 := add_nat_ne_zero (by rw [tpt_re]; norm_num) j
    simp only [invPow, zero_add, pow_one, pow_zero]
    field_simp
    ring
  rw [hG, Erho_invPow_zero]
  unfold Cr beta
  push_cast
  ring

lemma integrable_pow_wfun (r : ℚ) (m : ℕ) : Integrable (fun y => tpt y ^ m * wfun r y) :=
  integrable_mul_wfun r (continuous_tpt.pow m) (norm_pow_tpt_le m)

lemma integrable_pole_wfun (r : ℚ) (j : ℕ) :
    Integrable (fun y => tpt y * (tpt y + j)⁻¹ * wfun r y) :=
  integrable_mul_wfun r (continuous_pole_tpt j) (norm_pole_tpt_le j)

lemma mul_aeval_eq_sum (q : ℚ[X]) (t : ℂ) :
    t * aeval t q = ∑ e ∈ q.support, (q.coeff e : ℂ) * t ^ (e + 1) := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [eq_ratCast]
  ring

end

end Zeta32.Analytic.Contour

namespace Zeta32.Analytic

open Zeta32.Analytic.Contour

noncomputable section

/-- The entry integrand, decomposed along the partial fractions of `t^e R_n`. -/
lemma logistic_entry_integrand_eq (r : ℚ) (n e : ℕ) (y : ℝ) :
    tpt y * (tpt y ^ e * Rfun n (tpt y)) * wfun r y =
      (∑ e' ∈ (polynomialPart n e).support,
          ((polynomialPart n e).coeff e' : ℂ) * (tpt y ^ (e' + 1) * wfun r y)) +
        ∑ j ∈ Icc 1 (5*n), (residue n e j : ℂ) * (tpt y * (tpt y + j)⁻¹ * wfun r y) := by
  rw [pow_mul_Rfun_eq n e (by rw [tpt_re]; norm_num), mul_add, mul_aeval_eq_sum, add_mul,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => by rw [div_eq_mul_inv]; ring

lemma logistic_integrable_entry (r : ℚ) (n e : ℕ) :
    Integrable (fun y => tpt y * (tpt y ^ e * Rfun n (tpt y)) * wfun r y) := by
  simp_rw [logistic_entry_integrand_eq]
  exact (integrable_finsetSum _ fun e' _ => (integrable_pow_wfun r (e' + 1)).const_mul _).add
    (integrable_finsetSum _ fun j _ => (integrable_pole_wfun r j).const_mul _)

/-- **Entry identity** (the proof notes, 5.1): `U_r(t^e R_n) = C_r · slope + intercept`. -/
theorem logistic_representation (r : ℚ) (n e : ℕ) :
    ∫ y : ℝ, tpt y * (tpt y ^ e * Rfun n (tpt y)) * wfun r y =
      ((Cr r : ℝ) : ℂ) * (slope n e : ℂ) + (intercept r n e : ℂ) := by
  simp_rw [logistic_entry_integrand_eq]
  rw [integral_add (integrable_finsetSum _ fun e' _ => (integrable_pow_wfun r (e' + 1)).const_mul _)
    (integrable_finsetSum _ fun j _ => (integrable_pole_wfun r j).const_mul _),
    integral_finsetSum _ fun e' _ => (integrable_pow_wfun r (e' + 1)).const_mul _,
    integral_finsetSum _ fun j _ => (integrable_pole_wfun r j).const_mul _]
  simp_rw [integral_const_mul]
  have hp : ∀ e', ∫ y, tpt y ^ (e' + 1) * wfun r y = (moment r e' : ℂ) :=
    fun e' => Uint_pow r e'
  have hq : ∀ j : ℕ, ∫ y, tpt y * (tpt y + j)⁻¹ * wfun r y =
      2 * (j : ℂ) * ((Cr r : ℝ) : ℂ) + (beta r j : ℂ) := fun j => Uint_pole r j
  simp_rw [hp, hq]
  unfold intercept slope polynomialMoment
  rw [Polynomial.sum_def]
  push_cast
  rw [Finset.mul_sum]
  have hs : ∑ j ∈ Icc 1 (5*n), (residue n e j : ℂ) * (2 * (j : ℂ) * ((Cr r : ℝ) : ℂ) + (beta r j
    : ℂ)) =
      ∑ j ∈ Icc 1 (5*n), ((Cr r : ℝ) : ℂ) * ((residue n e j : ℂ) * (2 * (j : ℂ))) +
        ∑ j ∈ Icc 1 (5*n), (residue n e j : ℂ) * (beta r j : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs]
  ring

end

end Zeta32.Analytic

end
