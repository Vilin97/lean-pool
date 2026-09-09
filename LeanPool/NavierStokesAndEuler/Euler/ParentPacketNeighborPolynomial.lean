/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentHistoryCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryNeighbor
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationSourceData
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryPolynomial

/-! A fixed polynomial controls the full actual neighboring-label cost,
including the normal normalization and the selected terminal datum. The
small label scale is kept outside this polynomial. -/

@[expose] public section


noncomputable section

namespace EulerParentNeighborCost

open EulerPacketParentLabelBounds EulerParentHistoryCost EulerPolynomialCost
  EulerTransverseActivationSelection

/-- Formula, given by `27*F^2*V*R+27*F^2*R*(1+F)*Ei + 16*Hist*(5+64*CM^2+2*CH)*(1+3*F^2)*Hi*Ei`. -/
def formula (F V R Hist Ei Hi CM CH : ℝ) : ℝ :=
  27*F^2*V*R+27*F^2*R*(1+F)*Ei +
    16*Hist*(5+64*CM^2+2*CH)*(1+3*F^2)*Hi*Ei

/-- Envelope, constructed using `formula`. -/
def envelope (K Ti Ei Hi CM CH : ℝ) : ℝ :=
  formula (frameAmplitude K) (gradientAmplitude K) (coefficientRadius K)
    (labelHistoryConstant*(1+K+Ti)^labelHistoryPower) Ei Hi CM CH

/-- Polynomial as an element of `Polynomial ℝ`. -/
def polynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let V := Polynomial.C embeddingCost*X^2
  let F := 1+V
  let R := 1024+4*X
  let Hist := Polynomial.C labelHistoryConstant*X^labelHistoryPower
  27*F^2*V*R+27*F^2*R*(1+F)*X +
    16*Hist*(5+64*X^2+2*X)*(1+3*F^2)*X*X

/-- Bound constant, given by `coefficientCost polynomial`. -/
def boundConstant : ℝ := coefficientCost polynomial
/-- Degree, given by `polynomial.natDegree`. -/
def degree : ℕ := polynomial.natDegree

theorem constant_pos : 0 < boundConstant := coefficientCost_pos _

theorem polynomial_eval (P : ℝ) :
    polynomial.eval P = formula (frameAmplitude P) (gradientAmplitude P) (1024+4*P)
      (labelHistoryConstant*P^labelHistoryPower) P P P P := by
  simp [polynomial,formula,frameAmplitude,gradientAmplitude]

theorem formula_mono {F V R Hist Ei Hi CM CH F' V' R' Hist' Ei' Hi' CM' CH' : ℝ}
    (hF : 0 ≤ F) (hV : 0 ≤ V) (hR : 0 ≤ R) (hHist : 0 ≤ Hist)
    (hEi : 0 ≤ Ei) (hHi : 0 ≤ Hi) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (hFF : F ≤ F') (hVV : V ≤ V') (hRR : R ≤ R') (hHH : Hist ≤ Hist')
    (hEE : Ei ≤ Ei') (hII : Hi ≤ Hi') (hMM : CM ≤ CM') (hCC : CH ≤ CH') :
    formula F V R Hist Ei Hi CM CH ≤ formula F' V' R' Hist' Ei' Hi' CM' CH' := by
  have hF0 := hF.trans hFF
  have hV0 := hV.trans hVV
  have hR0 := hR.trans hRR
  have hH0 := hHist.trans hHH
  have hE0 := hEi.trans hEE
  have hI0 := hHi.trans hII
  have hM0 := hCM.trans hMM
  have hC0 := hCH.trans hCC
  unfold formula
  gcongr

theorem envelope_power (K Ti Ei Hi CM CH : ℝ)
    (hK : 0 ≤ K) (hTi : 0 ≤ Ti) (hEi : 0 ≤ Ei) (hHi : 0 ≤ Hi)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) :
    envelope K Ti Ei Hi CM CH ≤ boundConstant*(1+K+Ti+Ei+Hi+CM+CH)^degree := by
  let P := 1+K+Ti+Ei+Hi+CM+CH
  have hP : 1 ≤ P := by dsimp [P]; linarith
  have hKP : K ≤ P := by dsimp [P]; linarith
  have hbase : 1+K+Ti ≤ P := by dsimp [P]; linarith
  have hEP : Ei ≤ P := by dsimp [P]; linarith
  have hIP : Hi ≤ P := by dsimp [P]; linarith
  have hMP : CM ≤ P := by dsimp [P]; linarith
  have hHP : CH ≤ P := by dsimp [P]; linarith
  have hEmbedding := embeddingCost_nonneg
  have hHistory := labelHistoryConstant_pos
  have hV : gradientAmplitude K ≤ gradientAmplitude P := by
    unfold gradientAmplitude
    gcongr
  have hF : frameAmplitude K ≤ frameAmplitude P := add_le_add (le_refl (1 : ℝ)) hV
  have hR : coefficientRadius K ≤ 1024+4*P := by
    unfold coefficientRadius
    apply max_le <;> linarith
  have hHist : labelHistoryConstant*(1+K+Ti)^labelHistoryPower ≤
      labelHistoryConstant*P^labelHistoryPower := by gcongr
  have he : envelope K Ti Ei Hi CM CH ≤ polynomial.eval P := by
    rw [polynomial_eval]
    exact formula_mono (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
      (coefficientRadius_nonneg K) (by positivity) hEi hHi hCM hCH
      hF hV hR hHist hEP hIP hMP hHP
  exact he.trans ((le_abs_self _).trans (eval_bound polynomial P hP))

end EulerParentNeighborCost

namespace EulerPacketSourceGeometry.ParentFrame

open EulerSmoothLimit EulerTransversePacketProvider

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {τ : ℝ} (P : ParentFrame D τ)

theorem epsilon_inv_le_twice_shear (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear) :
    P.epsilon⁻¹ ≤ 2*P.shear := by
  have ha0 : 0 < P.a := by linarith only [ha]
  have hH0 : 0 ≤ P.shear := zero_le_one.trans hH
  rw [epsilon,← Real.sqrt_inv,inv_div]
  calc
    _ ≤ Real.sqrt (2*P.shear) := Real.sqrt_le_sqrt ((div_le_iff₀ ha0).2
      (by nlinarith only [mul_le_mul_of_nonneg_left ha hH0]))
    _ ≤ 2*P.shear := Real.sqrt_le_iff.mpr ⟨by positivity,
      by nlinarith only [hH,sq_nonneg (P.shear-1)]⟩

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketParentLabelBounds EulerGevrey EulerTransverseFrameCoordinates
  EulerTransversePacketProvider EulerPacketActivationHistory EulerPacketNormalizedPrimary
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketCrossProduct
  EulerTransverseActivationSelection EulerParentHistoryCost EulerParentNeighborCost

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (Ti CM CH : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hshear : 0 < P.shear) (heps : 0 < P.epsilon)

include hτ1 hTi hCH hshear heps in
theorem neighborScaleCost_envelope :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH ≤
      envelope L.K Ti P.epsilon⁻¹ P.shear⁻¹ CM CH := by
  let D := G.transverseData m hm R S hS
  have hK : 0 ≤ L.K := zero_le_one.trans L.K_one
  have hTi0 : 0 ≤ Ti := (inv_pos.mpr hτ).le.trans hTi
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude L.K := by
    intro t x
    change ‖G.frame.field t x‖ ≤ frameAmplitude L.K
    have h := L.frame_scaled_bound 0 t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hFn := frameAmplitude_nonneg L.K
  have hFnorm := D.frameBound_le_of_frame (frameAmplitude L.K) hFn hF
  have hInv0 := D.inverseBound_pos
  have hInv := D.inverseBound_le_of_frame (frameAmplitude L.K) hFn G.frame_det hF
  have hn : ‖cross (unit (P.m τ)) (unit (P.v τ))‖=1 := by
    exact (frame_orthonormal (unit (P.m τ)) (unit (P.v τ))
      (unit_inner_self (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩))
      (unit_inner_self (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩))
      (unit_inner_zero (P.tangent τ ⟨le_rfl,hτT.le⟩))).norm_eq_one 2
  have hray : (P.rayScale hτ hτT)⁻¹ ≤ 1+frameAmplitude L.K :=
    ((D.activationRayScale_bounds ⟨τ,hτ.le,hτT.le⟩ _ hn).2.2).trans hFnorm
  have hHistory := (L.initialHistoryDifferenceScaleCost_bound m hm R S hS H τ hτ hτT
    Ti hτ1 hTi).trans (labelHistoryEnvelope_power L.K Ti hK hTi0)
  have hHistory0 : 0 ≤ L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT := by
    have h0 := historyLabelDifferenceCost_nonneg (G.historyOn H m hm R S hS τ hτ hτT)
    have hb := L.initial_history_derivative_scale m hm R S hS H τ hτ hτT
    have hell := G.ell_pos
    nlinarith only [h0,hb,hell]
  have hR := coefficientRadius_nonneg L.K
  have hV := gradientAmplitude_nonneg L.K
  have hRayPos := Guards.rayScale_pos hτ hτT P
  have hHistConst := labelHistoryConstant_pos
  have heq : L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH =
      L.strainDifferenceCost+3*L.normalDifferenceCost*(P.rayScale hτ hτT)⁻¹*P.epsilon⁻¹ +
      16*(L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT) *
        (5+64*CM^2+2*CH)*D.inverseBound*P.shear⁻¹*P.epsilon⁻¹ := by
    unfold neighborScaleCost ParentFrame.terminalBound activationConstant
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq]
  unfold envelope formula strainDifferenceCost normalDifferenceCost
  calc
    _ ≤ 27*(frameAmplitude L.K)^2*gradientAmplitude L.K*coefficientRadius L.K +
        3*(9*(frameAmplitude L.K)^2*coefficientRadius L.K)*(1+frameAmplitude L.K)*P.epsilon⁻¹ +
        16*(labelHistoryConstant*(1+L.K+Ti)^labelHistoryPower) *
          (5+64*CM^2+2*CH)*(1+3*(frameAmplitude L.K)^2)*P.shear⁻¹*P.epsilon⁻¹ := by
      gcongr
    _ = _ := by ring

include hτ1 hTi hCM hCH hshear heps in
theorem neighborScaleCost_polynomial :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH ≤
      EulerParentNeighborCost.boundConstant *
        (1+L.K+Ti+P.epsilon⁻¹+P.shear⁻¹+CM+CH)^EulerParentNeighborCost.degree :=
  (L.neighborScaleCost_envelope m hm R S hS H τ hτ hτT P Ti CM CH hτ1 hTi hCH hshear heps).trans
    (envelope_power L.K Ti P.epsilon⁻¹ P.shear⁻¹ CM CH (zero_le_one.trans L.K_one)
      ((inv_pos.mpr hτ).le.trans hTi) (inv_nonneg.mpr heps.le) (inv_nonneg.mpr hshear.le) hCM hCH)

include hτ1 hTi hCM hCH hshear heps in
theorem source_neighbor_polynomial :
    P.neighborCost hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ≤
      (EulerParentNeighborCost.boundConstant *
        (1+L.K+Ti+P.epsilon⁻¹+P.shear⁻¹+CM+CH)^EulerParentNeighborCost.degree)*G.ell :=
  (L.source_neighbor_scale m hm R S hS H τ hτ hτT P CM CH hCM hCH hshear heps).trans
    (mul_le_mul_of_nonneg_right
      (L.neighborScaleCost_polynomial m hm R S hS H τ hτ hτT P Ti CM CH hτ1 hTi hCM hCH hshear heps)
      G.ell_pos.le)

include hτ1 hTi hCM hCH in
/-- With the actual activation scales, only the positive shear itself is
needed as a polynomial variable. CM and CH remain fixed low constants. -/
theorem neighborScaleCost_low_polynomial (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH ≤
      (EulerParentNeighborCost.boundConstant*(2*(1+CM+CH))^EulerParentNeighborCost.degree) *
        (1+L.K+Ti+P.shear)^EulerParentNeighborCost.degree := by
  have hK : 0 ≤ L.K := zero_le_one.trans L.K_one
  have hTi0 : 0 ≤ Ti := (inv_pos.mpr hτ).le.trans hTi
  have hHp : 0 < P.shear := zero_lt_one.trans_le hH
  have ha0 : 0 < P.a := by linarith only [ha]
  have hEp : 0 < P.epsilon := Real.sqrt_pos.mpr (div_pos ha0 hHp)
  have hEi := P.epsilon_inv_le_twice_shear ha hH
  have hHi : P.shear⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hH
  have hbase : 1 ≤ 1+L.K+Ti+P.shear := by linarith only [hK,hTi0,hH]
  have hab : 1+L.K+Ti+P.epsilon⁻¹+P.shear⁻¹+CM+CH ≤
      2*(1+CM+CH)*(1+L.K+Ti+P.shear) := by
    have hc := mul_le_mul_of_nonneg_left hbase (show 0 ≤ CM+CH by positivity)
    nlinarith only [hEi,hHi,hK,hTi0,hc,hCM,hCH]
  have hA0 : 0 ≤ 1+L.K+Ti+P.epsilon⁻¹+P.shear⁻¹+CM+CH := by positivity
  have hC := EulerParentNeighborCost.constant_pos
  calc
    _ ≤ EulerParentNeighborCost.boundConstant *
        (1+L.K+Ti+P.epsilon⁻¹+P.shear⁻¹+CM+CH)^EulerParentNeighborCost.degree :=
      L.neighborScaleCost_polynomial m hm R S hS H τ hτ hτT P Ti CM CH hτ1 hTi hCM hCH hHp hEp
    _ ≤ EulerParentNeighborCost.boundConstant *
        (2*(1+CM+CH)*(1+L.K+Ti+P.shear))^EulerParentNeighborCost.degree := by gcongr
    _ = _ := by rw [mul_pow]; ring

include hτ1 hTi hCM hCH in
theorem source_neighbor_low_polynomial (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear) :
    P.neighborCost hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ≤
      ((EulerParentNeighborCost.boundConstant*(2*(1+CM+CH))^EulerParentNeighborCost.degree) *
        (1+L.K+Ti+P.shear)^EulerParentNeighborCost.degree)*G.ell := by
  have hHp : 0 < P.shear := zero_lt_one.trans_le hH
  have ha0 : 0 < P.a := by linarith only [ha]
  have hEp : 0 < P.epsilon := Real.sqrt_pos.mpr (div_pos ha0 hHp)
  exact (L.source_neighbor_scale m hm R S hS H τ hτ hτT P CM CH hCM hCH hHp hEp).trans
    (mul_le_mul_of_nonneg_right
      (L.neighborScaleCost_low_polynomial m hm R S hS H τ hτ hτT P Ti CM CH hτ1 hTi hCM hCH ha hH)
      G.ell_pos.le)

end EulerParentPacketFrames.LabelData
