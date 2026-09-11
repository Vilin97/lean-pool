/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleSequence
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentHistoryCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryNeighbor
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryProfileEnvelope
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryPolynomial

/-! Literal good- and bad-interval upper-Hessian costs fit the existing
summable scale family. The good contribution retains its factor delta. -/

section

/-! The actual history contribution to the early-time size ratio is
polynomial in the parent labels and reciprocal history length. The good
interval keeps its absolute size constant. -/

@[expose] public section

noncomputable section

namespace EulerTransverseHistoryBounds

open EulerTimeH1GeneratorBounds EulerTransverseEndpointBounds EulerTransverseGeneratorDifference
  EulerTransverseEndpointDifference

theorem historyCost_le_differenceCost (T c q q1 d a r x y z : ℝ)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hq : 0 ≤ q) (hq1 : 0 ≤ q1)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hx : q ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    historyCost T c q q1 d a r ≤ historyDifferenceCost T c q q1 d a r x y z := by
  have hx0 := hq.trans hx
  have ht : 0 ≤ traceCost T (2*c⁻¹*q*q1) := by unfold traceCost; positivity
  have hs : 0 ≤ slopeCost T d a r := by unfold slopeCost affineCost; positivity
  have hg : 0 ≤ generatorDifferenceCost c q q1 x y := by unfold generatorDifferenceCost; positivity
  have hsd : 0 ≤ slopeDifferenceCost T d a r (T*y+x) (T^2*z) := by
    unfold slopeDifferenceCost endpointDifferenceCost affineCost
    positivity
  unfold historyCost historyDifferenceCost
  apply le_trans _ (le_add_of_nonneg_right (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx ht) hs

end EulerTransverseHistoryBounds

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketParentLabelBounds EulerGevrey
  EulerTimeIntervalRestriction EulerTransversePacketProvider EulerPacketActivationHistory
  EulerTransverseHistoryBounds EulerParentHistoryCost

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)

omit [CompleteSpace U] in
theorem initial_history_size_le_difference :
    historyLabelSizeCost (G.historyOn H m hm R S hS τ hτ hτT) ≤
      L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT := by
  let D := (G.transverseData m hm R S hS).initial τ hτ hτT.le
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude L.K := by
    intro t x
    change ‖G.frame.field (initialInclusion G.T τ hτT.le t) x‖ ≤ frameAmplitude L.K
    have h := L.frame_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hq := D.frame_norm_le (frameAmplitude L.K) (frameAmplitude_nonneg L.K) hF
  have hR : 1 ≤ coefficientRadius L.K :=
    (by norm_num : (1 : ℝ) ≤ 1024).trans (le_max_left _ _)
  have hx : ‖D.frame.field‖ ≤ L.frameDifferenceCost := by
    apply hq.trans
    unfold frameDifferenceCost
    linarith only [mul_le_mul_of_nonneg_left hR (frameAmplitude_nonneg L.K)]
  apply historyCost_le_differenceCost τ D.frameLower _ _ _ _ _ _ _ _ hτ.le D.frameLower_pos.le
    (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity)
    (historyTransportCost_nonneg (D := D)) hx
  · unfold firstDifferenceCost
    positivity [gradientAmplitude_nonneg L.K,coefficientRadius_nonneg L.K]
  · unfold strainDifferenceCost
    positivity [gradientAmplitude_nonneg L.K,coefficientRadius_nonneg L.K]

omit [CompleteSpace U] in
theorem initial_history_size_polynomial (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) :
    historyLabelSizeCost (G.historyOn H m hm R S hS τ hτ hτT) ≤
      labelHistoryConstant*(1+L.K+Ti)^labelHistoryPower :=
  (L.initial_history_size_le_difference m hm R S hS H τ hτ hτT).trans
    ((L.initialHistoryDifferenceScaleCost_bound m hm R S hS H τ hτ hτT Ti hτ1 hTi).trans
      (labelHistoryEnvelope_power L.K Ti (zero_le_one.trans L.K_one) ((inv_pos.mpr hτ).le.trans
          hTi)))

end EulerParentPacketFrames.LabelData

namespace EulerParentBadRatio

open EulerPacketParentLabelBounds EulerParentHistoryCost EulerPolynomialCost
    EulerPacketGeometryLowBounds

/-- Formula, given by `8*(5+64*CM^2+2*CH)*(1+3*F^2)^2*(1+F)*Hist*Hi`. -/
def formula (F Hist Hi CM CH : ℝ) : ℝ :=
  8*(5+64*CM^2+2*CH)*(1+3*F^2)^2*(1+F)*Hist*Hi

/-- Envelope, given by `formula (frameAmplitude K)
(labelHistoryConstant*(1+K+Ti)^labelHistoryPower) Hi CM CH`. -/
def envelope (K Ti Hi CM CH : ℝ) : ℝ :=
  formula (frameAmplitude K) (labelHistoryConstant*(1+K+Ti)^labelHistoryPower) Hi CM CH

/-- Polynomial as an element of `Polynomial ℝ`. -/
def polynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let F := 1+Polynomial.C embeddingCost*X^2
  8*(5+64*X^2+2*X)*(1+3*F^2)^2*(1+F)*(Polynomial.C labelHistoryConstant*X^labelHistoryPower)*X

/-- Bound constant, given by `coefficientCost polynomial`. -/
def boundConstant : ℝ := coefficientCost polynomial
/-- Degree, given by `polynomial.natDegree`. -/
def degree : ℕ := polynomial.natDegree

theorem constant_pos : 0 < boundConstant := coefficientCost_pos _

theorem polynomial_eval (X : ℝ) :
    polynomial.eval X=formula (frameAmplitude X) (labelHistoryConstant*X^labelHistoryPower) X X X
        := by
  simp only [polynomial, formula, frameAmplitude, gradientAmplitude, Polynomial.eval_add,
      Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_C,
        Polynomial.eval_X]

theorem envelope_power (K Ti Hi CM CH : ℝ) (hK : 0 ≤ K) (hTi : 0 ≤ Ti)
    (hHi : 0 ≤ Hi) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) :
    envelope K Ti Hi CM CH ≤ boundConstant*(1+K+Ti+Hi+CM+CH)^degree := by
  let X := 1+K+Ti+Hi+CM+CH
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hKX : K ≤ X := by dsimp [X]; linarith
  have hbase : 1+K+Ti ≤ X := by dsimp [X]; linarith
  have hHiX : Hi ≤ X := by dsimp [X]; linarith
  have hCMX : CM ≤ X := by dsimp [X]; linarith
  have hCHX : CH ≤ X := by dsimp [X]; linarith
  have hemb := embeddingCost_nonneg
  have hhistory := labelHistoryConstant_pos
  have hF : frameAmplitude K ≤ frameAmplitude X := by
    unfold frameAmplitude gradientAmplitude
    gcongr
  have hf0 := frameAmplitude_nonneg K
  have hX0 := zero_le_one.trans hX
  have hHist : labelHistoryConstant*(1+K+Ti)^labelHistoryPower ≤
      labelHistoryConstant*X^labelHistoryPower := by
      gcongr
  have hpoly : envelope K Ti Hi CM CH ≤ polynomial.eval X := by
    rw [polynomial_eval]
    unfold envelope formula
    gcongr
    all_goals positivity [frameAmplitude_nonneg X]
  exact hpoly.trans ((le_abs_self _).trans (eval_bound polynomial X hX))

/-- Bad constant, given by `cutoffBound*(8232*Real.exp 9+4*boundConstant)`. -/
def badConstant : ℝ := cutoffBound*(8232*Real.exp 9+4*boundConstant)

theorem badConstant_pos : 0 < badConstant := by
  unfold badConstant
  positivity [cutoffBound_pos,constant_pos]

theorem prefactor_bound (X Θ : ℝ) (hX : 1 ≤ X) (hΘ : 1 ≤ Θ) :
    cutoffBound*(8232*Real.exp 9*Θ^5+4*Θ*(boundConstant*X^degree)) ≤ badConstant*X^degree*Θ^5 := by
  have hx0 := zero_le_one.trans hX
  have hθ0 := zero_le_one.trans hΘ
  have hp : 1 ≤ X^degree := one_le_pow₀ hX
  have hθ : Θ ≤ Θ^5 := by simpa only [pow_one] using pow_le_pow_right₀ hΘ (by decide : 1 ≤ 5)
  have hfirst : 8232*Real.exp 9*Θ^5 ≤ 8232*Real.exp 9*(X^degree*Θ^5) := by
    calc
      _ = 8232*Real.exp 9*(1*Θ^5) := by ring
      _ ≤ _ := by gcongr
  have hsecond : 4*Θ*(boundConstant*X^degree) ≤ 4*boundConstant*(X^degree*Θ^5) := by
    calc
      _ ≤ 4*Θ^5*(boundConstant*X^degree) := by gcongr; positivity [constant_pos]
      _ = _ := by ring
  calc
    _ ≤ cutoffBound*(8232*Real.exp 9*(X^degree*Θ^5)+4*boundConstant*(X^degree*Θ^5)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) cutoffBound_pos.le
    _ = _ := by unfold badConstant; ring

end EulerParentBadRatio

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerPacketParentLabelBounds EulerParentHistoryCost
  EulerPacketActivationHistory EulerPacketSourceGeometry EulerGevrey EulerParentBadRatio

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (A : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)

include hτ1 hTi

theorem historySizeRatio_envelope :
    A.historySizeCost/(P.rayScale hτ hτT) ≤ envelope L.K Ti P.shear⁻¹ A.CM A.CH := by
  let D := G.transverseData m hm R S hS
  let B := G.historyOn H m hm R S hS τ hτ hτT
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude L.K := by
    intro t x
    change ‖G.frame.field t x‖ ≤ frameAmplitude L.K
    have h := L.frame_scaled_bound 0 t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hf0 := frameAmplitude_nonneg L.K
  have hInv0 := D.inverseBound_pos.le
  have hInv := D.inverseBound_le_of_frame (frameAmplitude L.K) hf0 G.frame_det hF
  have hRay := (P.rayScale_inv_le_frameBound hτ hτT).trans
    (D.frameBound_le_of_frame (frameAmplitude L.K) hf0 hF)
  have hRay0 := (inv_pos.mpr (Guards.rayScale_pos hτ hτT P)).le
  have hHi := (inv_pos.mpr A.shear_pos).le
  have hHist := L.initial_history_size_polynomial m hm R S hS H τ hτ hτT Ti hτ1 hTi
  have hHist0 : 0 ≤ historyLabelSizeCost B := (norm_nonneg (B.coefficients.labelVelocity 0)).trans
      (labelVelocity_norm B 0)
  have hEq : A.historySizeCost/(P.rayScale hτ hτT) =
      8*(5+64*A.CM^2+2*A.CH)*D.inverseBound^2*(P.rayScale hτ hτT)⁻¹ *
        historyLabelSizeCost B*P.shear⁻¹ := by
    unfold Guards.historySizeCost ParentFrame.terminalBound
        EulerTransverseActivationSelection.activationConstant
    simp only [div_eq_mul_inv]
    ring
  rw [hEq]
  unfold envelope formula
  gcongr
  all_goals positivity [A.CH_nonneg]

theorem historySizeRatio_polynomial :
    A.historySizeCost/(P.rayScale hτ hτT) ≤
      boundConstant*(1+L.K+Ti+P.shear⁻¹+A.CM+A.CH)^degree :=
  (L.historySizeRatio_envelope m hm R S hS H τ hτ hτT P A Ti hτ1 hTi).trans
    (envelope_power L.K Ti P.shear⁻¹ A.CM A.CH (zero_le_one.trans L.K_one)
      ((inv_pos.mpr hτ).le.trans hTi) (inv_pos.mpr A.shear_pos).le A.CM_nonneg A.CH_nonneg)

theorem badRatio_polynomial :
    A.badRatio ≤ badConstant*(1+L.K+Ti+P.shear⁻¹+A.CM+A.CH)^degree *
      P.horizon^5*Real.exp (-(1/(4*P.sigma))) := by
  have hX : 1 ≤ 1+L.K+Ti+P.shear⁻¹+A.CM+A.CH := by
    have ht := (inv_pos.mpr hτ).le.trans hTi
    have hi := (inv_pos.mpr A.shear_pos).le
    linarith only [L.K_one,ht,hi,A.CM_nonneg,A.CH_nonneg]
  have hh := L.historySizeRatio_polynomial m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
  rw [A.badRatio_formula]
  calc
    _ = EulerPacketGeometryLowBounds.cutoffBound*(8232*Real.exp 9*P.horizon^5 +
        4*P.horizon*(A.historySizeCost/(P.rayScale hτ hτT)))*Real.exp (-(1/(4*P.sigma))) := by ring
    _ ≤ EulerPacketGeometryLowBounds.cutoffBound*(8232*Real.exp 9*P.horizon^5 +
        4*P.horizon*(boundConstant*(1+L.K+Ti+P.shear⁻¹+A.CM+A.CH)^degree))*Real.exp
            (-(1/(4*P.sigma))) := by
      gcongr
      · exact EulerPacketGeometryLowBounds.cutoffBound_pos.le
      · positivity [A.horizon_lower]
    _ ≤ _ := mul_le_mul_of_nonneg_right (prefactor_bound _ P.horizon hX A.horizon_lower)
        (Real.exp_pos _).le

end EulerParentPacketFrames.LabelData

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPressureScale

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketSourceScaleGuards EulerPacketGeometryLowBounds
  EulerParentBadRatio
open scoped Topology

/-- Bad coefficient, given by `1+2*CM*badConstant*(4+CMn+CHn)^degree*(2*Cθ)^5`. -/
def badCoefficient (Cθ CM CMn CHn : ℝ) : ℝ :=
  1+2*CM*badConstant*(4+CMn+CHn)^degree*(2*Cθ)^5

theorem badCoefficient_pos (Cθ CM CMn CHn : ℝ) (hθ : 0 ≤ Cθ)
    (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) : 0 < badCoefficient Cθ CM CMn CHn := by
  unfold badCoefficient
  positivity [badConstant_pos]

/-- Bad cost, given by `monomialCost J 1 4 0 (1/8) ((degree : ℝ)*c+2) (badCoefficient Cθ CM CMn
CHn) 10 10 x n`. -/
def badCost (J : ℕ) (Cθ CM CMn CHn c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  monomialCost J 1 4 0 (1/8) ((degree : ℝ)*c+2)
    (badCoefficient Cθ CM CMn CHn) 10 10 x n

/-- Bad cost spec, bundling `d`, `B`, `N`, `a` and the required compatibility proofs. -/
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

theorem sigma_exponential_bound (σ x : ℝ) (hσ : 0 < σ) (hσx : σ * x ≤ 2) :
    exp (-(1/(4*σ))) ≤ exp (-x/8) := by
  have hdiv : x/8 ≤ 1/(4*σ) := (le_div_iff₀ (by positivity : 0 < 4*σ)).2 (by linarith)
  apply exp_le_exp.mpr
  linarith only [hdiv]

theorem parameter_sum_le (K Ti Hi cm ch CMn CHn E : ℝ)
    (hE : 1 ≤ E) (hK : K ≤ E) (hTi : Ti ≤ E) (hHi : Hi ≤ 1)
    (hcm : cm ≤ CMn) (hch : ch ≤ CHn) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) :
    1+K+Ti+Hi+cm+ch ≤ (4+CMn+CHn)*E := by
  linarith only [hE,hK,hTi,hHi,hcm,hch,
    mul_nonneg (sub_nonneg.mpr hE) hMn,mul_nonneg (sub_nonneg.mpr hE) hHn]

theorem badCost_bound (J : ℕ) (hJ : 3 ≤ J) (Cθ CM CMn CHn c : ℝ)
    (hθ : 1 ≤ Cθ) (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn)
    (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ)
    (M hchild r Q Θ σ : ℝ) (hh0 : 0 ≤ hchild) (hr0 : 0 ≤ r)
    (hQ0 : 0 ≤ Q) (hΘ0 : 0 ≤ Θ) (hσ : 0 < σ)
    (hMb : M ≤ CM * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7))
    (hhb : hchild ≤ exp (x n / ((J + n : ℕ) : ℝ) ^ 5))
    (hQ : Q ≤ (4 + CMn + CHn) * exp (c * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 4)))
    (hΘ : Θ ≤ sourceTheta J Cθ x n) (hσx : σ * x n ≤ 2)
    (hr : r ≤ badConstant * Q ^ degree * Θ ^ 5 * exp (-(1 / (4 * σ)))) :
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
  have hr' : r ≤ badConstant*((4+CMn+CHn)*exp (c*z))^degree *
      (2*Cθ*j^2*(x n)^2)^5*exp (-x n/8) := by
    apply hr.trans
    gcongr
  have hfirst : 2*M*hchild*r ≤ 2*(CM*exp z)*exp z *
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
    _ ≤ 2*(CM*exp z)*exp z *
        (badConstant*((4+CMn+CHn)*exp (c*z))^degree*(2*Cθ*j^2*(x n)^2)^5*exp (-x n/8)) := hfirst
    _ = B*j^10*(x n)^10*((exp z)^2*(exp (c*z))^degree*exp (-x n/8)) := by
      dsimp [B]
      simp only [mul_pow,← pow_mul]
      ring
    _ = B*j^10*(x n)^10*exp (-(1/8)*(x n/j^0)+((degree : ℝ)*c+2)*z) := by rw [hexp]
    _ ≤ badCoefficient Cθ CM CMn CHn*j^10*(x n)^10 *
        exp (-(1/8)*(x n/j^0)+((degree : ℝ)*c+2)*z) := by
      gcongr
      change B ≤ 1+B
      linarith
    _ = badCost J Cθ CM CMn CHn c x n := by
      simp only [badCost,monomialCost,j,z,p,rpow_zero,pow_zero,div_one]

theorem goodCost_bound (J : ℕ) (hJ : 1 ≤ J) (X CM M δ hchild : ℝ)
    (hM : 0 ≤ CM) (hδ : 0 ≤ δ) (hh : 0 ≤ hchild)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ)
    (hMb : M ≤ CM * previousShear J X n) (hδb : δ ≤ spike J X n) (hhb : hchild ≤ shear J X n) :
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
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (n : ℕ) (K Ti Hi cm ch CMn CHn : ℝ)
    (hK : K ≤ previousFrequency J D X n ^ c) (hTi : Ti ≤ previousShear J X n)
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
      _ ≤ c*z := by linarith only [mul_le_mul_of_nonneg_right hc hz]
  exact parameter_sum_le K Ti Hi cm ch CMn CHn (exp (c*z))
    (one_le_exp (mul_nonneg (zero_le_one.trans hc) hz)) hK' hTi' hHi hcm hch hMn hHn

end EulerPacketPressureScale
