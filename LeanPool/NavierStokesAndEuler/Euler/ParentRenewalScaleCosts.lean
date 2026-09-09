/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalParameters
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSeries
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

/-! Fixed summable envelopes for actual geometric renewal. The analytic
envelope uses the constant sequence a=2, so its summability does not assume
bounds for the future, not-yet-constructed geometric couplings. -/

@[expose] public section


noncomputable section

namespace EulerParentRenewalScale

open Set Real Filter EulerScale EulerPacketMovingFrame EulerPacketSourceScales
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketSourceScaleGuards EulerPacketSourceScaleBounds EulerPacketPressureScale
open scoped Topology

/-- Maximum error, given by `geometryErrorCost J D C c X (fun _ => 2)`. -/
def maximumError (J D : ℕ) (C c X : ℝ) : ℕ → ℝ :=
  geometryErrorCost J D C c X (fun _ => 2)

/-- Error constant, given by `30000000*neighborStabilityConstant*CF^2`. -/
def errorConstant (CF : ℝ) : ℝ := 30000000*neighborStabilityConstant*CF^2

/-- Renewal cost, given by `3000/scaleSequence J X n+errorConstant CF*maximumError J D C c X n`. -/
def renewalCost (J D : ℕ) (C c CF X : ℝ) (n : ℕ) : ℝ :=
  3000/scaleSequence J X n+errorConstant CF*maximumError J D C c X n

theorem errorConstant_nonneg (CF : ℝ) : 0 ≤ errorConstant CF := by
  unfold errorConstant
  positivity [neighborStabilityConstant_ge]

theorem maximumError_series {J D : ℕ} {C c X δ : ℝ}
    (hb : ActualBounds J D C c X δ) : SmallSeries (maximumError J D C c X) δ :=
  hb.coefficient (fun _ => 2) (fun _ => by norm_num) (fun _ => le_rfl)

theorem scaleSequence_double (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 < X) (n : ℕ) :
    2*scaleSequence J X n ≤ scaleSequence J X (n+1) := by
  have hx := quadratic_growth_pos J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X) n
  have hj : (2 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 2 ≤ J+n by omega)
  have hs : (2 : ℝ) ≤ ((J+n : ℕ) : ℝ)^2 := by nlinarith only [hj]
  rw [scaleSequence_succ]
  exact mul_le_mul_of_nonneg_right hs hx.le

theorem reciprocal_geometric (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 < X) (n : ℕ) :
    1/scaleSequence J X n ≤ (1/X)*(1/2 : ℝ)^n := by
  have hx := quadratic_growth_pos J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  induction n with
  | zero => simp only [scaleSequence_zero,pow_zero,mul_one,le_refl]
  | succ n ih =>
    have hrec := one_div_le_one_div_of_le (by positivity [hx n] : 0 < 2*scaleSequence J X n)
      (scaleSequence_double J hJ X hX n)
    calc
      _ ≤ 1/(2*scaleSequence J X n) := hrec
      _ = (1/2)*(1/scaleSequence J X n) := by ring
      _ ≤ (1/2)*((1/X)*(1/2 : ℝ)^n) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem reciprocal_series (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 < X) :
    SmallSeries (fun n => 1/scaleSequence J X n) (2/X) := by
  have hs : SmallSeries (fun n => (1/X)*(1/2 : ℝ)^n) (2/X) := by
    refine ⟨fun n => by positivity,summable_geometric_two.mul_left (1/X),?_⟩
    rw [tsum_mul_left,tsum_geometric_two]
    exact le_of_eq (by ring)
  apply hs.mono
  · intro n
    have hx := quadratic_growth_pos J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X) n
    positivity
  · exact reciprocal_geometric J hJ X hX

theorem scale_series {f : ℕ → ℝ} {δ : ℝ} (hf : SmallSeries f δ) (C : ℝ) (hC : 0 ≤ C) :
    SmallSeries (fun n => C*f n) (C*δ) := by
  refine ⟨fun n => mul_nonneg hC (hf.nonneg n),hf.summable.mul_left C,?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hf.total_le hC

theorem renewal_series {J D : ℕ} (hJ : 2 ≤ J) {C c CF X δ : ℝ} (hX : 0 < X)
    (hb : ActualBounds J D C c X δ) :
    SmallSeries (renewalCost J D C c CF X) (6000/X+errorConstant CF*δ) := by
  have h := add_series (scale_series (reciprocal_series J hJ X hX) 3000 (by norm_num))
    (scale_series (maximumError_series hb) (errorConstant CF) (errorConstant_nonneg CF))
  convert h using 1
  · funext n
    unfold renewalCost
    ring
  · ring

/-- Enlarge only the final base scale; the starting index and every
previously chosen cost specification remain unchanged. -/
theorem renewal_series_small {J D : ℕ} (hJ : 2 ≤ J) {C c CF X δ η : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hη : 0 < η) (hb : ActualBounds J D C c X δ)
    (hfloor : 12000 / η ≤ X) (hsmall : 2 * (1 + errorConstant CF) * δ ≤ η) :
    SmallSeries (renewalCost J D C c CF X) η := by
  have hf := (div_le_iff₀ hη).mp hfloor
  have hfirst : 6000/X ≤ η/2 := (div_le_iff₀ hX).mpr (by nlinarith only [hf])
  have hc : errorConstant CF*δ ≤ η/2 := by nlinarith only [hsmall,hδ]
  exact (renewal_series hJ hX hb).weaken (by linarith only [hfirst,hc])

/-- This uses only the coupling at the present stage. -/
theorem physical_error_le_maximum {ι : Type*} (G : PhysicalGeometryData ι)
    (J D : ℕ) (hJ : 1 ≤ J) (C c CF X a : ℝ) (hC : 1 ≤ C) (hCF : 1 ≤ CF)
    (hX : 1 ≤ X) (ha : a ≤ 2) (n : ℕ)
    (heps : G.ε = epsilon J X a n)
    (htheta : G.Θ ≤ sourceTheta J C (scaleSequence J X) n)
    (hG : G.G ≤ CF * (1 + olderShear J X n))
    (hd : G.d ≤ priorError J D X n + neighborError J D X c n) :
    G.error*G.Θ^40 ≤ CF^2*maximumError J D C c X n := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hx := quadratic_growth_one_le J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  have hthetaOne := (sourceTheta_bounds hJ hC hx n).1
  have htheta0 : 0 ≤ sourceTheta J C (scaleSequence J X) n := zero_le_one.trans hthetaOne
  have he : G.ε ≤ epsilon J X 2 n := by
    rw [heps]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right ha (previousShear_pos J hXp n).le
  have he0 : 0 ≤ epsilon J X 2 n := Real.sqrt_nonneg _
  have hmain : G.ε*G.Θ*(4*G.G)^2 ≤
      CF^2*(epsilon J X 2 n*sourceTheta J C (scaleSequence J X) n *
        (4*(1+olderShear J X n))^2) := by
    calc
      _ ≤ epsilon J X 2 n*sourceTheta J C (scaleSequence J X) n *
          (4*(CF*(1+olderShear J X n)))^2 :=
        mul_le_mul (mul_le_mul he htheta G.Theta_pos.le he0)
          (pow_le_pow_left₀ (by positivity [G.G_lower])
            (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 4)) 2)
          (sq_nonneg _) (mul_nonneg he0 htheta0)
      _ = _ := by ring
  have hds : G.d ≤ CF^2*(priorError J D X n+neighborError J D X c n) :=
    hd.trans (le_mul_of_one_le_left (G.d_nonneg.trans hd) (one_le_pow₀ hCF))
  have herr : G.error ≤ CF^2*geometryError J D C c X (fun _ => 2) n := by
    unfold PhysicalGeometryData.error geometryError
    dsimp only
    nlinarith only [hmain,hds]
  have hpow : G.Θ^40 ≤ sourceTheta J C (scaleSequence J X) n^60 :=
    (pow_le_pow_left₀ G.Theta_pos.le htheta 40).trans (pow_le_pow_right₀ hthetaOne (by omega))
  have hmax0 := geometryError_nonneg J D C c X (fun _ => 2) n (zero_le_one.trans hC) hXp
  have hm := mul_le_mul herr hpow (pow_nonneg G.Theta_pos.le 40) (mul_nonneg (sq_nonneg CF) hmax0)
  simpa only [maximumError,geometryErrorCost,mul_assoc] using hm

theorem coupling_polynomial_le {ι : Type*} (G : PhysicalGeometryData ι) :
    G.y^4+G.σ^2*G.y^2+8*G.σ*G.y^3 ≤ 10*G.y := by
  have hy1 : G.y ≤ 1 := G.y_small.trans (by norm_num)
  have hs1 : G.σ ≤ 1 := G.sigma_small.trans (by norm_num)
  have hy2 : G.y^2 ≤ G.y := by nlinarith only [G.y_pos,hy1]
  have hy3 : G.y^3 ≤ G.y := by
    have h := mul_le_mul_of_nonneg_right (pow_le_one₀ G.y_pos.le hy1 (n := 2)) G.y_pos.le
    simpa only [pow_succ,one_mul] using h
  have hy4 : G.y^4 ≤ G.y := by
    have h := mul_le_mul_of_nonneg_right (pow_le_one₀ G.y_pos.le hy1 (n := 3)) G.y_pos.le
    simpa only [pow_succ,one_mul] using h
  have hs2 : G.σ^2 ≤ 1 := pow_le_one₀ G.sigma_pos.le hs1
  have h2 := mul_le_mul hs2 hy2 (sq_nonneg G.y) (by norm_num : (0 : ℝ) ≤ 1)
  have h3 := mul_le_mul hs1 hy3 (pow_nonneg G.y_pos.le 3) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith only [hy4,h2,h3]

theorem actual_errors_le_cost {ι : Type*} (G : PhysicalGeometryData ι)
    (J D : ℕ) (hJ : 2 ≤ J) (C c CF X a : ℝ) (hC : 1 ≤ C) (hCF : 1 ≤ CF)
    (hX : 1 ≤ X) (ha : a ≤ 2) (n : ℕ)
    (heps : G.ε = epsilon J X a n)
    (htheta : G.Θ ≤ sourceTheta J C (scaleSequence J X) n)
    (hG : G.G ≤ CF * (1 + olderShear J X n))
    (hd : G.d ≤ priorError J D X n + neighborError J D X c n)
    (hy : G.y = (scaleSequence J X (n + 1))⁻¹)
    (hsigma : G.σ * scaleSequence J X n ≤ 2) :
    G.couplingError ≤ renewalCost J D C c CF X n ∧
      G.tiltError ≤ renewalCost J D C c CF X n := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hx := quadratic_growth_pos J (by omega) (scaleSequence J X) hXp (scaleSequence_succ J X) n
  have hxx : scaleSequence J X n ≤ scaleSequence J X (n+1) :=
    (by linarith only [hx] : scaleSequence J X n ≤ 2*scaleSequence J X n).trans
      (scaleSequence_double J hJ X hXp n)
  have hy' : G.y ≤ 1/scaleSequence J X n := by
    rw [hy,← one_div]
    exact one_div_le_one_div_of_le hx hxx
  have hs : G.σ ≤ 2/scaleSequence J X n := (le_div_iff₀ hx).mpr hsigma
  have herr := physical_error_le_maximum G J D (by omega) C c CF X a hC hCF hX ha n
    heps htheta hG hd
  have hK : 0 ≤ 30000000*neighborStabilityConstant := by positivity [neighborStabilityConstant_ge]
  have hm := mul_le_mul_of_nonneg_left herr hK
  have hnorm : 30000000*neighborStabilityConstant*G.error*G.Θ^40 ≤
      errorConstant CF*maximumError J D C c X n := by
    unfold errorConstant
    nlinarith only [hm]
  have hp := coupling_polynomial_le G
  have hyp := mul_le_mul_of_nonneg_left hy' (by norm_num : (0 : ℝ) ≤ 10)
  have hsp := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1500)
  have hi : 0 ≤ 1/scaleSequence J X n := (one_div_pos.mpr hx).le
  constructor
  · unfold PhysicalGeometryData.couplingError renewalCost
    simp only [div_eq_mul_inv,one_mul] at hyp hi ⊢
    nlinarith only [hp,hyp,hnorm,hi]
  · unfold PhysicalGeometryData.tiltError renewalCost
    simp only [div_eq_mul_inv] at hsp ⊢
    nlinarith only [hsp,hnorm]

/-- Optional explicit extra cost for the next activation. The existing
parent-square cost also controls it after multiplication by 2*CF+1. -/
def activationCostSpec (CF : ℝ) (hCF : 1 ≤ CF) : CostSpec where
  d := 1
  B := 7
  N := 5
  a := 5
  b := 1
  c := 2
  C := 2*CF+1
  p := 0
  q := 0
  d_le_two := by norm_num
  a_nonneg := by norm_num
  a_lt_B := by norm_num
  a_le_N := by norm_num
  b_pos := zero_lt_one
  C_pos := by linarith

theorem activationCost_eq (J : ℕ) (CF : ℝ) (hCF : 1 ≤ CF) (x : ℕ → ℝ) (n : ℕ) :
    (activationCostSpec CF hCF).cost J x n=(2*CF+1)*parentSquareRatio J x n := by
  unfold parentSquareRatio
  rw [sourceParentSquareRatio_eq]
  simp only [activationCostSpec,CostSpec.cost,monomialCost,pow_zero,mul_one,one_mul]

theorem previousShear_one_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    1 ≤ previousShear J X n := by
  cases n with
  | zero => exact one_le_pow₀ hX
  | succ n =>
    apply Real.one_le_exp
    have hx := quadratic_growth_one_le J hJ (scaleSequence J X) hX (scaleSequence_succ J X) n
    exact div_nonneg (zero_le_one.trans hx) (pow_nonneg (Nat.cast_nonneg _) 5)

theorem activation_ratio_le {J D : ℕ} (hJ : 1 ≤ J) {C c CF X δ : ℝ}
    (hCF : 1 ≤ CF) (hX : 1 ≤ X) (hb : ActualBounds J D C c X δ)
    (e : ℝ) (he : e ≤ 1) (n : ℕ) :
    (CF*(1+previousShear J X n)+e)/shear J X n ≤
      (activationCostSpec CF hCF).cost J (scaleSequence J X) n := by
  have hp := previousShear_one_le J hJ X hX n
  have h1 : 1+previousShear J X n ≤ 2*(previousShear J X n)^2 := by
    nlinarith only [hp,sq_nonneg (previousShear J X n-1)]
  have h2 := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans hCF)
  have he' : e ≤ (previousShear J X n)^2 := he.trans (one_le_pow₀ hp)
  have hn : CF*(1+previousShear J X n)+e ≤ (2*CF+1)*(previousShear J X n)^2 := by
    nlinarith only [h2,he']
  have hd := div_le_div_of_nonneg_right hn (show 0 ≤ shear J X n from (Real.exp_pos _).le)
  have hb' := mul_le_mul_of_nonneg_left
    (actualParentRatio_le J hJ X (zero_lt_one.trans_le hX) hb.initial_shear n)
    (by positivity : 0 ≤ 2*CF+1)
  rw [activationCost_eq]
  have heq : (2*CF+1)*(previousShear J X n)^2/shear J X n =
      (2*CF+1)*((previousShear J X n)^2/shear J X n) := by ring
  rw [heq] at hd
  exact hd.trans hb'

theorem activation_smallness {J D : ℕ} (hJ : 1 ≤ J) {C c CF X δ ζ : ℝ}
    (hCF : 1 ≤ CF) (hX : 1 ≤ X) (hb : ActualBounds J D C c X δ)
    (hs : SmallSeries ((activationCostSpec CF hCF).cost J (scaleSequence J X)) ζ)
    (e : ℝ) (he : e ≤ 1) (n : ℕ) :
    CF*(1+previousShear J X n)+e ≤ ζ*shear J X n := by
  have h := (activation_ratio_le hJ hCF hX hb e he n).trans (hs.term_le n)
  exact (div_le_iff₀ (Real.exp_pos _)).mp h

end EulerParentRenewalScale
