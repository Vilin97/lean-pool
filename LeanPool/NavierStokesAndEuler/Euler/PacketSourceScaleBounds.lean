/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-!
Pointwise bounds for the literal scale expressions in (37)--(39).  They
exhibit a finite list of exponential costs to which the existing uniform
scale-choice theorem applies.  The estimates here contain no field data.
-/

noncomputable section


namespace EulerPacketSourceScaleBounds

open Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales EulerPacketSourceTime

def monomialCost (J d B : ℕ) (a b c C : ℝ) (p q : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * ((J + n : ℕ) : ℝ)^p * (x n)^q *
    exp (-b * (x n / ((J + n : ℕ) : ℝ)^a) +
      c * (x n / ((J - d + n : ℕ) : ℝ)^B))

theorem monomialCost_nonneg (J d B : ℕ) (a b c C : ℝ) (p q : ℕ)
    (x : ℕ → ℝ) (n : ℕ) (hC : 0 ≤ C) (hx : 0 ≤ x n) :
    0 ≤ monomialCost J d B a b c C p q x n := by
  unfold monomialCost
  positivity

theorem monomialCost_eq_exp (J d B : ℕ) (a b c C : ℝ) (p q : ℕ)
    (x : ℕ → ℝ) (n : ℕ) (hJ : 1 ≤ J) (hC : 0 < C) (hx : 0 < x n) :
    monomialCost J d B a b c C p q x n =
      exp (-b * (x n / ((J + n : ℕ) : ℝ)^a) +
        c * (x n / ((J - d + n : ℕ) : ℝ)^B) +
        log C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)) := by
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  simp only [monomialCost, exp_add, exp_log hC, exp_nat_mul, exp_log hj, exp_log hx]
  ring

theorem theta_weighted_monomial_bound
    (J d B : ℕ) (a b c D C : ℝ) (p q A : ℕ) (x : ℕ → ℝ) (n : ℕ)
    (hJ : 1 ≤ J) (hC : 1 ≤ C) (hD : 0 ≤ D) (hx : ∀ n, 1 ≤ x n) :
    monomialCost J d B a b c D p q x n * sourceTheta J C x n^A ≤
      monomialCost J d B a b c (D*(2*C)^A) (p+2*A) (q+2*A) x n := by
  have hθ := pow_le_pow_left₀ (le_trans zero_le_one (sourceTheta_bounds hJ hC hx n).1)
    (sourceTheta_bounds hJ hC hx n).2 A
  have hh := mul_le_mul_of_nonneg_left hθ
    (monomialCost_nonneg J d B a b c D p q x n hD (le_trans zero_le_one (hx n)))
  convert! hh using 1
  simp only [monomialCost, mul_pow, pow_add, ← pow_mul]
  ring

theorem sourcePriorError_bound (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (n : ℕ)
    (hx : 0 ≤ x n) :
    sourcePriorError J x n ≤ exp (-(1/4)*(x n/((J+n : ℕ) : ℝ)^4)) := by
  have hp : (0 : ℝ) < (J-1+n : ℕ) := by exact_mod_cast (show 0 < J-1+n by omega)
  have hpj : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hd := div_le_div_of_nonneg_left hx
    (show 0 < 4*((J-1+n : ℕ) : ℝ)^4 by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hpj 4) (by norm_num : (0:ℝ) ≤ 4))
  apply exp_le_exp.mpr
  change -x n/(4*((J-1+n : ℕ) : ℝ)^4) ≤ _
  convert! neg_le_neg hd using 1 <;> ring

theorem sourceNeighborError_bound (J : ℕ) (hJ : 3 ≤ J) (c : ℝ) (hc : 0 ≤ c)
    (x : ℕ → ℝ) (n : ℕ) (hx : 0 ≤ x n) :
    sourceNeighborError J c x n ≤
      exp (-(x n/((J+n : ℕ) : ℝ)^(7/2 : ℝ)) +
        (2*c)*(x n/((J-1+n : ℕ) : ℝ)^4)) := by
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hd := div_le_div_of_nonneg_left (mul_nonneg hc hx)
    (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^4)
    (pow_le_pow_right₀ hp (by decide : 4 ≤ 7))
  unfold sourceNeighborError
  apply exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hd ⊢
  nlinarith only [hd]

/-- The complete coefficient error is controlled by three explicit costs,
with exactly the preceding-stage powers and the real support exponent 7/2. -/
theorem sourceCoefficientError_bound (J : ℕ) (hJ : 3 ≤ J) (C c : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ) :
    sourceCoefficientError J C c x n * sourceTheta J C x n^A ≤
      monomialCost J 2 9 7 (1/2) 2 (128*(2*C)^(A+1)) (2*(A+1)) (2*(A+1)) x n +
      monomialCost J 0 5 4 (1/4) 0 (16*(2*C)^A) (2*A) (2*A) x n +
      monomialCost J 1 4 (7/2) 1 (2*c) (16*(2*C)^A) (2*A) (2*A) x n := by
  have hJ1 : 1 ≤ J := by omega
  have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx n).1
  have hxp : ∀ n, 0 ≤ x n := fun n => le_trans zero_le_one (hx n)
  have hs := mul_le_mul_of_nonneg_right
    (source_shear_gradient_bound J hJ x hxp n) (pow_nonneg hθ (A+1))
  have hs16 := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 16)
  have hsm := theta_weighted_monomial_bound J 2 9 7 (1/2) 2 128 C 0 0 (A+1) x n hJ1 hC
    (by norm_num) hx
  have hshear : 16*(sourceEpsilon J x n*sourceTheta J C x n*sourceOlderGradient J x n^2)*
      sourceTheta J C x n^A ≤
      monomialCost J 2 9 7 (1/2) 2 (128*(2*C)^(A+1)) (2*(A+1)) (2*(A+1)) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hsm)
    convert! hs16 using 1 <;> simp only [monomialCost, rpow_ofNat, pow_zero, mul_one, pow_succ] <;>
      ring
  have hp := mul_le_mul_of_nonneg_right
    (sourcePriorError_bound J hJ x n (hxp n)) (pow_nonneg hθ A)
  have hp16 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 16)
  have hpm := theta_weighted_monomial_bound J 0 5 4 (1/4) 0 16 C 0 0 A x n hJ1 hC
    (by norm_num) hx
  have hprior : 16*sourcePriorError J x n*sourceTheta J C x n^A ≤
      monomialCost J 0 5 4 (1/4) 0 (16*(2*C)^A) (2*A) (2*A) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hpm)
    simpa only [monomialCost, rpow_ofNat, zero_mul, add_zero, pow_zero, mul_one, mul_assoc] using
      hp16
  have hn := mul_le_mul_of_nonneg_right
    (sourceNeighborError_bound J hJ c hc x n (hxp n)) (pow_nonneg hθ A)
  have hn16 := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ) ≤ 16)
  have hnm := theta_weighted_monomial_bound J 1 4 (7/2) 1 (2*c) 16 C 0 0 A x n hJ1 hC
    (by norm_num) hx
  have hneighbor : 16*sourceNeighborError J c x n*sourceTheta J C x n^A ≤
      monomialCost J 1 4 (7/2) 1 (2*c) (16*(2*C)^A) (2*A) (2*A) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hnm)
    simpa only [monomialCost, neg_one_mul, pow_zero, mul_one, mul_assoc] using hn16
  have hh := add_le_add (add_le_add hshear hprior) hneighbor
  convert! hh using 1
  unfold sourceCoefficientError
  ring

theorem sourceExtraTime_bound (J : ℕ) (hJ : 1 ≤ J) (C : ℝ) (hC : 1 ≤ C)
    (A : ℕ) (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ)
    (a : ℝ) (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2*sqrt (a*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J x n*
      sourceTheta J C x n^A ≤
      monomialCost J 1 7 5 (1/2) (1/2) (48*(2*C)^A) (6+2*A) (2+2*A) x n := by
  have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ hC hx n).1
  have hh := mul_le_mul_of_nonneg_right (source_extra_time_bound J hJ x n ha ha₂) (pow_nonneg hθ A)
  have hm := theta_weighted_monomial_bound J 1 7 5 (1/2) (1/2) 48 C 6 2 A x n hJ hC (by norm_num) hx
  apply le_trans hh
  simpa only [monomialCost, rpow_ofNat] using hm

theorem sourceTimeRatio_bound (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) :
    sourceTimeRatio J x n ≤ monomialCost J 1 7 5 (1/2) (1/2) 4 4 0 x n := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  have hp : (((J+n : ℕ) : ℝ)+1)^2 ≤ 4*((J+n : ℕ) : ℝ)^2 := by nlinarith only [hj]
  have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ((J+n : ℕ) : ℝ))
  have he := mul_le_mul_of_nonneg_right hh
    (exp_pos (-x n/(2*((J+n : ℕ) : ℝ)^5)+x n/(2*((J-1+n : ℕ) : ℝ)^7))).le
  have hexp : exp (-x n/(2*((J+n : ℕ) : ℝ)^5)+x n/(2*((J-1+n : ℕ) : ℝ)^7)) =
      exp (-(1/2)*(x n/((J+n : ℕ) : ℝ)^5)+(1/2)*(x n/((J-1+n : ℕ) : ℝ)^7)) := by
    congr 1
    ring
  rw [hexp] at he
  convert! he using 1 <;> simp only [sourceTimeRatio, monomialCost, rpow_ofNat, pow_zero, mul_one]
  · rw [hexp]
  · ring

theorem sourceParentSquareRatio_eq (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5) =
      monomialCost J 1 7 5 1 2 1 0 0 x n := by
  rw [← exp_sub]
  simp only [monomialCost, pow_zero, mul_one, one_mul, neg_one_mul, rpow_ofNat]
  congr 1
  ring

theorem sourceGoodCost_bound (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (n : ℕ) (hx : 0 ≤ x n) :
    exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5)*
      exp (x n/((J-1+n : ℕ) : ℝ)^7) ≤ monomialCost J 1 5 3 1 2 1 0 0 x n := by
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hpj : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hd₁ := div_le_div_of_nonneg_left hx (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^5)
    (pow_le_pow_left₀ (le_trans zero_le_one hp) hpj 5)
  have hd₂ := div_le_div_of_nonneg_left hx (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^5)
    (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))
  rw [← exp_add, ← exp_add]
  simp only [monomialCost, pow_zero, mul_one, one_mul, neg_one_mul, rpow_ofNat]
  apply exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hd₁ hd₂ ⊢
  nlinarith only [hd₁, hd₂]

end EulerPacketSourceScaleBounds
