/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryProfileEnvelope

@[expose] public section

/-! The actual history contribution to the early-time size ratio is
polynomial in the parent labels and reciprocal history length. The good
interval keeps its absolute size constant. -/

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
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
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
    nlinarith only [mul_le_mul_of_nonneg_left hR (frameAmplitude_nonneg L.K)]
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

def formula (F Hist Hi CM CH : ℝ) : ℝ :=
  8*(5+64*CM^2+2*CH)*(1+3*F^2)^2*(1+F)*Hist*Hi

def envelope (K Ti Hi CM CH : ℝ) : ℝ :=
  formula (frameAmplitude K) (labelHistoryConstant*(1+K+Ti)^labelHistoryPower) Hi CM CH

def polynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let F := 1+Polynomial.C embeddingCost*X^2
  8*(5+64*X^2+2*X)*(1+3*F^2)^2*(1+F)*(Polynomial.C labelHistoryConstant*X^labelHistoryPower)*X

def boundConstant : ℝ := coefficientCost polynomial
def degree : ℕ := polynomial.natDegree

theorem constant_pos : 0 < boundConstant := coefficientCost_pos _

theorem polynomial_eval (X : ℝ) :
    polynomial.eval X=formula (frameAmplitude X) (labelHistoryConstant*X^labelHistoryPower) X X X
      := by
  simp only [polynomial,formula,frameAmplitude,gradientAmplitude,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X]

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
    labelHistoryConstant*X^labelHistoryPower := by gcongr
  have hpoly : envelope K Ti Hi CM CH ≤ polynomial.eval X := by
    rw [polynomial_eval]
    unfold envelope formula
    gcongr
    all_goals positivity [frameAmplitude_nonneg X]
  exact hpoly.trans ((le_abs_self _).trans (eval_bound polynomial X hX))

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
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
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
      8*(5+64*A.CM^2+2*A.CH)*D.inverseBound^2*(P.rayScale hτ hτT)⁻¹*
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
    A.badRatio ≤ badConstant*(1+L.K+Ti+P.shear⁻¹+A.CM+A.CH)^degree*
      P.horizon^5*Real.exp (-(1/(4*P.sigma))) := by
  have hX : 1 ≤ 1+L.K+Ti+P.shear⁻¹+A.CM+A.CH := by
    have ht := (inv_pos.mpr hτ).le.trans hTi
    have hi := (inv_pos.mpr A.shear_pos).le
    nlinarith only [L.K_one,ht,hi,A.CM_nonneg,A.CH_nonneg]
  have hh := L.historySizeRatio_polynomial m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
  rw [A.badRatio_formula]
  calc
    _ = EulerPacketGeometryLowBounds.cutoffBound*(8232*Real.exp 9*P.horizon^5+
        4*P.horizon*(A.historySizeCost/(P.rayScale hτ hτT)))*Real.exp (-(1/(4*P.sigma))) := by ring
    _ ≤ EulerPacketGeometryLowBounds.cutoffBound*(8232*Real.exp 9*P.horizon^5+
        4*P.horizon*(boundConstant*(1+L.K+Ti+P.shear⁻¹+A.CM+A.CH)^degree))*Real.exp
          (-(1/(4*P.sigma))) := by
      gcongr
      · exact EulerPacketGeometryLowBounds.cutoffBound_pos.le
      · positivity [A.horizon_lower]
    _ ≤ _ := mul_le_mul_of_nonneg_right (prefactor_bound _ P.horizon hX A.horizon_lower)
      (Real.exp_pos _).le

end EulerParentPacketFrames.LabelData
