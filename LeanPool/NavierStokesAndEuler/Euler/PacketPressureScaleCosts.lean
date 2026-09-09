/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketBadRatioPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

@[expose] public section

/-! Literal good- and bad-interval upper-Hessian costs fit the existing
summable scale family. The good contribution retains its factor delta. -/

noncomputable section

namespace EulerPacketPressureScale

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketSourceScaleGuards EulerPacketGeometryLowBounds
  EulerParentBadRatio
open scoped Topology

def badCoefficient (Cθ CM CMn CHn : ℝ) : ℝ :=
  1+2*CM*badConstant*(4+CMn+CHn)^degree*(2*Cθ)^5

theorem badCoefficient_pos (Cθ CM CMn CHn : ℝ) (hθ : 0 ≤ Cθ)
    (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) : 0 < badCoefficient Cθ CM CMn CHn := by
  unfold badCoefficient
  positivity [badConstant_pos]

def badCost (J : ℕ) (Cθ CM CMn CHn c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  monomialCost J 1 4 0 (1/8) ((degree : ℝ)*c+2)
    (badCoefficient Cθ CM CMn CHn) 10 10 x n

def badCostSpec (Cθ CM CMn CHn c : ℝ) (hθ : 0 ≤ Cθ)
    (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) : CostSpec where
  d := 1
  B := 4
  N := 0
  a := 0
  b := 1/8
  c := (degree : ℝ)*c+2
  C := badCoefficient Cθ CM CMn CHn
  p := 10
  q := 10
  d_le_two := by norm_num
  a_nonneg := le_rfl
  a_lt_B := by norm_num
  a_le_N := by norm_num
  b_pos := by norm_num
  C_pos := badCoefficient_pos Cθ CM CMn CHn hθ hM hMn hHn

theorem sigma_exponential_bound (σ x : ℝ) (hσ : 0 < σ) (hσx : σ*x ≤ 2) :
    exp (-(1/(4*σ))) ≤ exp (-x/8) := by
  have hdiv : x/8 ≤ 1/(4*σ) := (le_div_iff₀ (by positivity : 0 < 4*σ)).2 (by nlinarith)
  apply exp_le_exp.mpr
  linarith only [hdiv]

theorem parameter_sum_le (K Ti Hi cm ch CMn CHn E : ℝ)
    (hE : 1 ≤ E) (hK : K ≤ E) (hTi : Ti ≤ E) (hHi : Hi ≤ 1)
    (hcm : cm ≤ CMn) (hch : ch ≤ CHn) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) :
    1+K+Ti+Hi+cm+ch ≤ (4+CMn+CHn)*E := by
  nlinarith only [hE,hK,hTi,hHi,hcm,hch,
    mul_nonneg (sub_nonneg.mpr hE) hMn,mul_nonneg (sub_nonneg.mpr hE) hHn]

theorem badCost_bound (J : ℕ) (hJ : 3 ≤ J) (Cθ CM CMn CHn c : ℝ)
    (hθ : 1 ≤ Cθ) (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn)
    (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ)
    (M hchild r Q Θ σ : ℝ) (hh0 : 0 ≤ hchild) (hr0 : 0 ≤ r)
    (hQ0 : 0 ≤ Q) (hΘ0 : 0 ≤ Θ) (hσ : 0 < σ)
    (hMb : M ≤ CM*exp (x n/((J-1+n : ℕ) : ℝ)^7))
    (hhb : hchild ≤ exp (x n/((J+n : ℕ) : ℝ)^5))
    (hQ : Q ≤ (4+CMn+CHn)*exp (c*(x n/((J-1+n : ℕ) : ℝ)^4)))
    (hΘ : Θ ≤ sourceTheta J Cθ x n) (hσx : σ*x n ≤ 2)
    (hr : r ≤ badConstant*Q^degree*Θ^5*exp (-(1/(4*σ)))) :
    2*M*hchild*r ≤ badCost J Cθ CM CMn CHn c x n := by
  let j : ℝ := (J+n : ℕ)
  let p : ℝ := (J-1+n : ℕ)
  let z : ℝ := x n/p^4
  have hj : 1 ≤ j := by dsimp [j]; exact_mod_cast (show 1 ≤ J+n by omega)
  have hp : 1 ≤ p := by dsimp [p]; exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hpj : p ≤ j := by dsimp [p,j]; exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hj0 := zero_le_one.trans hj
  have hp0 := zero_le_one.trans hp
  have hxp := zero_le_one.trans (hx n)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hp4 : p^4 ≤ p^7 := pow_le_pow_right₀ hp (by decide)
  have hj5 : p^4 ≤ j^5 := (pow_le_pow_left₀ hp0 hpj 4).trans (pow_le_pow_right₀ hj (by decide))
  have hmexp : exp (x n/p^7) ≤ exp z := exp_le_exp.mpr
    (div_le_div_of_nonneg_left hxp (by positivity) hp4)
  have hhexp : exp (x n/j^5) ≤ exp z := exp_le_exp.mpr
    (div_le_div_of_nonneg_left hxp (by positivity) hj5)
  have hM' : M ≤ CM*exp z := hMb.trans (mul_le_mul_of_nonneg_left hmexp hM)
  have hh' : hchild ≤ exp z := hhb.trans hhexp
  have hΘ' : Θ ≤ 2*Cθ*j^2*(x n)^2 := hΘ.trans (sourceTheta_bounds (by omega) hθ hx n).2
  have hσ' := sigma_exponential_bound σ (x n) hσ hσx
  have hcθ := zero_le_one.trans hθ
  have hbad := badConstant_pos.le
  have hQ' : Q ≤ (4+CMn+CHn)*exp (c*z) := hQ
  have hr' : r ≤ badConstant*((4+CMn+CHn)*exp (c*z))^degree*
      (2*Cθ*j^2*(x n)^2)^5*exp (-x n/8) := by
    apply hr.trans
    gcongr
  have hfirst : 2*M*hchild*r ≤ 2*(CM*exp z)*exp z*
      (badConstant*((4+CMn+CHn)*exp (c*z))^degree*(2*Cθ*j^2*(x n)^2)^5*exp (-x n/8)) := by
    gcongr
  have hexp : (exp z)^2*(exp (c*z))^degree*exp (-x n/8) =
      exp (-(1/8)*(x n/j^0)+((degree : ℝ)*c+2)*z) := by
    rw [← exp_nat_mul,← exp_nat_mul,← exp_add,← exp_add]
    congr 1
    simp only [pow_zero,div_one]
    ring
  let B := 2*CM*badConstant*(4+CMn+CHn)^degree*(2*Cθ)^5
  calc
    _ ≤ 2*(CM*exp z)*exp z*
        (badConstant*((4+CMn+CHn)*exp (c*z))^degree*(2*Cθ*j^2*(x n)^2)^5*exp (-x n/8)) := hfirst
    _ = B*j^10*(x n)^10*((exp z)^2*(exp (c*z))^degree*exp (-x n/8)) := by
      dsimp [B]
      simp only [mul_pow,← pow_mul]
      ring
    _ = B*j^10*(x n)^10*exp (-(1/8)*(x n/j^0)+((degree : ℝ)*c+2)*z) := by rw [hexp]
    _ ≤ badCoefficient Cθ CM CMn CHn*j^10*(x n)^10*
        exp (-(1/8)*(x n/j^0)+((degree : ℝ)*c+2)*z) := by
      gcongr
      change B ≤ 1+B
      linarith
    _ = badCost J Cθ CM CMn CHn c x n := by
      simp only [badCost,monomialCost,j,z,p,rpow_zero,pow_zero,div_one]

theorem goodCost_bound (J : ℕ) (hJ : 1 ≤ J) (X CM M δ hchild : ℝ)
    (hM : 0 ≤ CM) (hδ : 0 ≤ δ) (hh : 0 ≤ hchild)
    (hbase : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7)) (n : ℕ)
    (hMb : M ≤ CM*previousShear J X n) (hδb : δ ≤ spike J X n) (hhb : hchild ≤ shear J X n) :
    2*M*hchild*(δ*goodRatio) ≤ 2*CM*goodRatio*goodCost J (scaleSequence J X) n := by
  have hg := goodRatio_pos.le
  have hsp := (exp_pos (-scaleSequence J X n/((J+n : ℕ) : ℝ)^3)).le
  have hsh := (exp_pos (scaleSequence J X n/((J+n : ℕ) : ℝ)^5)).le
  have hprev : 0 ≤ previousShear J X n := by
    cases n with
    | zero => change 0 ≤ X^1000; positivity
    | succ n => exact (exp_pos _).le
  calc
    _ ≤ 2*(CM*previousShear J X n)*shear J X n*(spike J X n*goodRatio) := by gcongr
    _ = (2*CM*goodRatio)*(spike J X n*shear J X n*previousShear J X n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (actualGoodCost_le J hJ X hbase n) (by positivity)

theorem parameters_le_source_exponential (J D : ℕ) (hJ : 3 ≤ J) (X c : ℝ)
    (hX : 1 ≤ X) (hc : 1 ≤ c)
    (hbaseH : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7))
    (hbaseK : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4))
    (n : ℕ) (K Ti Hi cm ch CMn CHn : ℝ)
    (hK : K ≤ previousFrequency J D X n^c) (hTi : Ti ≤ previousShear J X n)
    (hHi : Hi ≤ 1) (hcm : cm ≤ CMn) (hch : ch ≤ CHn)
    (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) :
    1+K+Ti+Hi+cm+ch ≤ (4+CMn+CHn)*exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)) := by
  let z := scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4
  have hxp := quadratic_growth_pos J (by omega) (scaleSequence J X)
    (lt_of_lt_of_le zero_lt_one hX) (scaleSequence_succ J X) n
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hK' : K ≤ exp (c*z) := by
    apply hK.trans
    calc
      _ ≤ (exp z)^c := rpow_le_rpow
        (previousFrequency_pos J D (lt_of_lt_of_le zero_lt_one hX) n).le
        (previousFrequency_le_normal J D (by omega) X hbaseK n) (zero_le_one.trans hc)
      _ = _ := by rw [← exp_mul]; congr 1; ring
  have hTi' : Ti ≤ exp (c*z) := by
    apply hTi.trans
    apply (previousShear_le_normal J (by omega) X hbaseH n).trans
    apply exp_le_exp.mpr
    calc
      _ ≤ z := div_le_div_of_nonneg_left hxp.le (by positivity)
        (pow_le_pow_right₀ hp (by decide : 4 ≤ 7))
      _ ≤ c*z := by nlinarith only [mul_le_mul_of_nonneg_right hc hz]
  exact parameter_sum_le K Ti Hi cm ch CMn CHn (exp (c*z))
    (one_le_exp (mul_nonneg (zero_le_one.trans hc) hz)) hK' hTi' hHi hcm hch hMn hHn

end EulerPacketPressureScale
