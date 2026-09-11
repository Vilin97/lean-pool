/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryNeighbor
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHessianSymmetry

/-! The scalar induction guards apply to the actual parent source data.
History norms and symmetry are derived from the parent fields, and the
neighbor error is the computed, ell-scaled coefficient expression. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketNormalizedPrimary EulerPacketMovingFrame EulerTransversePacketProvider

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {τ : ℝ} (P : ParentFrame D τ)

theorem activation_normal_le (hτ : 0 < τ) (hτT : τ < D.T) :
    ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (P.m τ)),unit (P.m τ)⟫_ℝ ≤
      ⟪P.B τ (unit (P.m τ)),unit (P.m τ)⟫_ℝ+P.error := by
  let t : Icc (0 : ℝ) D.T := ⟨τ,hτ.le,hτT.le⟩
  let E := D.M.field t 0-P.B τ -
    P.shear • rankOne ℝ (unit (P.v τ)) (unit (P.m τ))
  have hn : ‖unit (P.m τ)‖=1 := unit_norm (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩)
  have ht : ⟪unit (P.v τ),unit (P.m τ)⟫_ℝ=0 := by
    rw [real_inner_comm]
    exact unit_inner_zero (P.tangent τ ⟨le_rfl,hτT.le⟩)
  have hE : ‖E‖ ≤ P.error := by
    have h := P.remainder_bound τ ⟨le_rfl,hτT.le⟩
    rw [Data.clamp_coe D t] at h
    exact h
  have hu : ‖E (unit (P.m τ))‖ ≤ P.error :=
    (E.le_opNorm _).trans (by simpa only [hn,mul_one] using hE)
  have habs : |⟪E (unit (P.m τ)),unit (P.m τ)⟫_ℝ| ≤ ‖E (unit (P.m τ))‖ := by
    simpa only [Real.norm_eq_abs,hn,mul_one] using
      norm_inner_le_norm (𝕜 := ℝ) (E (unit (P.m τ))) (unit (P.m τ))
  have hi := (le_abs_self ⟪E (unit (P.m τ)),unit (P.m τ)⟫_ℝ).trans (habs.trans hu)
  have he : ⟪E (unit (P.m τ)),unit (P.m τ)⟫_ℝ =
      ⟪D.M.field t 0 (unit (P.m τ)),unit (P.m τ)⟫_ℝ -
      ⟪P.B τ (unit (P.m τ)),unit (P.m τ)⟫_ℝ := by
    simp only [E,sub_apply,smul_apply,rankOne_apply,inner_sub_left,
      real_inner_smul_left,ht,mul_zero,sub_zero]
  rw [he] at hi
  linarith only [hi]

theorem activation_compression_of_previous (hτ : 0 < τ) (hτT : τ < D.T)
    (e : ℝ) (he : P.error ≤ e)
    (hprevious : ⟪P.B τ (unit (P.m τ)), unit (P.m τ)⟫_ℝ + e < 0) :
    ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (P.m τ)),unit (P.m τ)⟫_ℝ < 0 :=
  (P.activation_normal_le hτ hτT).trans_lt ((add_le_add_right he _).trans_lt hprevious)

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketParentLabelBounds EulerGevrey EulerTransverseFrameCoordinates
  EulerTransversePacketProvider EulerPacketActivationHistory EulerTimeIntervalRestriction
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerTransverseActivationSelection EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScaleActual EulerPacketSourceScaleGuards EulerPacketSourceScales
open scoped BoundedContinuousFunction ContDiff

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)

/-- One explicit parent coefficient amplitude controls both the actual
strain and pressure Hessian throughout the history interval. -/
def historyAmplitude : ℝ := 27*(frameAmplitude L.K)^2*gradientAmplitude L.K

theorem historyAmplitude_nonneg : 0 ≤ L.historyAmplitude := by
  unfold historyAmplitude
  positivity [gradientAmplitude_nonneg L.K]

omit [CompleteSpace U] in
theorem history_strain_norm (t : Icc (0 : ℝ) τ) (x : Space) :
    ‖((G.transverseData m hm R S hS).initial τ hτ hτT.le).M.field t x‖ ≤
      L.historyAmplitude := by
  change ‖G.strain.field (initialInclusion G.T τ hτT.le t) x‖ ≤
    27*(frameAmplitude L.K)^2*gradientAmplitude L.K
  have h := L.strain_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using h

omit [CompleteSpace U] in
theorem history_hessian_norm (x : Space) :
    ‖(G.historyOn H m hm R S hS τ hτ hτT).coefficients.labelHessian x‖ ≤
      L.historyAmplitude := by
  apply (ContinuousMap.norm_le _ L.historyAmplitude_nonneg).2
  intro t
  change ‖G.curvature.field (initialInclusion G.T τ hτT.le t) x‖ ≤
    27*(frameAmplitude L.K)^2*gradientAmplitude L.K
  have h := L.curvature_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using h

/-- Apply the manuscript's scalar stage bounds to the literal source
coefficients. The remaining inputs are older-stage center data, the
chosen normal, and scalar comparisons with explicit source costs. -/
def geometryGuardsOfStage
    (P : ParentFrame (G.transverseData m hm R S hS) τ)
    (p : Icc (0 : ℝ) G.T → Space → ℝ) (hp : ∀ t, ContDiff ℝ ∞ (p t))
    (hacc : ∀ t x, G.acceleration.field t x = -(gradient (p t) (G.position t x)))
    (J D : ℕ) (C c X : ℝ) (a β : ℕ → ℝ) (n : ℕ) (hX : 0 < X)
    (CF : ℝ) (hCF : 1 ≤ CF)
    (stage : StageGuards J D C c X (neighborStabilityConstant * CF ^ 2) a β n)
    (ha : 1 / 2 ≤ a n) (ha_match : P.a = a n)
    (hshear : P.shear = previousShear J X n)
    (hsigma : P.sigma = Real.sqrt (β n))
    (htime : P.horizon = EulerPacketSourceScaleGuards.horizon J X (a n) (β n) n)
    (hG : P.G ≤ CF * (1 + olderShear J X n))
    (herr : P.error ≤ priorError J D X n)
    (CM CH ζ ρ δ hchild : ℝ)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hζ : 0 ≤ ζ) (hρ : 0 ≤ ρ)
    (hδ : 0 ≤ δ) (hhchild : 0 ≤ hchild)
    (hneighbor : L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH * G.ell * ρ ≤
      neighborError J D X c n)
    (hnormal : m =
 activationDirection
      ((G.transverseData m hm R S hS).deformationEquiv ⟨τ, hτ.le, hτT.le⟩ 0)
      (EulerPacketCrossProduct.cross (unit (P.m τ)) (unit (P.v τ))))
    (hlayer : 1 ≤ previousShear J X n * τ)
    (hstrain : ‖EulerTransverseSourceCoefficientPath.pathEvaluation 0
      ((G.transverseData m hm R S hS).initial τ hτ hτT.le).M.field‖ ≤ CM * previousShear J X n)
    (hhessian : ‖(G.historyOn H m hm R S hS τ hτ hτT).coefficients.labelHessian 0‖ ≤
      CH * (previousShear J X n) ^ 2)
    (hactivation : 16 * (activationConstant CM CH + 1) * ζ ≤ 1)
    (hactivationError : CF * (1 + olderShear J X n) + priorError J D X n ≤ ζ * previousShear J X n)
    (hpreviousCompression :
      ⟪P.B τ (unit (P.m τ)), unit (P.m τ)⟫_ℝ + priorError J D X n < 0) :
    Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT) := by
  have hshearPos : 0 < P.shear := by
    simpa only [hshear] using previousShear_pos J hX n
  have hepsilon : P.epsilon=epsilon J X (a n) n := by
    simp only [ParentFrame.epsilon,epsilon,ha_match,hshear]
  have hepsPos : 0 < P.epsilon := by simpa only [hepsilon] using stage.epsilon_pos
  have hsigmaPos : 0 < P.sigma := by simpa only [hsigma] using stage.sigma_pos
  have htarget : ((scaleSequence J X (n+1))⁻¹)⁻¹/P.sigma=targetTime J X (β n) n := by
    simp only [inv_inv,hsigma,targetTime]
  have htarget_ge : 1 ≤ targetTime J X (β n) n := by
    have hfirst : 1 ≤ 1/Real.sqrt (β n) :=
      (le_div_iff₀ stage.sigma_pos).2 (by linarith only [stage.sigma_small])
    exact hfirst.trans stage.target_from_sigma
  have htarget_le : targetTime J X (β n) n ≤ P.horizon := by
    rw [htime]
    exact stage.target_le_horizon
  have hhor : 1 ≤ P.horizon := htarget_ge.trans htarget_le
  have hhorθ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n := by
    rw [htime]
    exact stage.horizon_le_Theta
  have hθ : 1 ≤ sourceTheta J C (scaleSequence J X) n := hhor.trans hhorθ
  have hshort : P.horizon-targetTime J X (β n) n ≤ 1 := by
    rw [htime]
    apply stage.extra_time.trans
    exact (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hθ) 60)).2
      (by simpa only [one_mul] using one_le_pow₀ hθ (n := 60))
  have herror := L.source_totalError_bound m hm R S hS H τ hτ hτT P CM CH ρ
    (priorError J D X n) (neighborError J D X c n) hCM hCH hshearPos hepsPos hρ herr hneighbor
  have hray := Guards.rayScale_pos hτ hτT P
  have hterminal : 0 ≤ P.terminalBound CM CH := by
    unfold ParentFrame.terminalBound activationConstant
    positivity [(G.transverseData m hm R S hS).inverseBound_pos]
  have hhistory := historyLabelDifferenceCost_nonneg (G.historyOn H m hm R S hS τ hτ hτT)
  have hcost : 0 ≤ P.neighborCost hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH := by
    unfold ParentFrame.neighborCost
    positivity
  have herror0 : 0 ≤ P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ :=
    add_nonneg P.error_nonneg (mul_nonneg hcost hρ)
  have hcoef :
      16*(P.epsilon*P.horizon*(4*P.G)^2 +
        P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ) ≤
      CF^2*geometryError J D C c X a n := by
    have hmain : P.epsilon*P.horizon*(4*P.G)^2 ≤
        CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
          (4*(1+olderShear J X n))^2) := by
      rw [hepsilon]
      calc
        _ ≤ epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
            (4*(CF*(1+olderShear J X n)))^2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hhorθ stage.epsilon_pos.le)
            (pow_le_pow_left₀ (by positivity [P.G_lower])
              (mul_le_mul_of_nonneg_left hG (by norm_num : (0:ℝ) ≤ 4)) 2)
            (sq_nonneg _) (mul_nonneg stage.epsilon_pos.le (zero_le_one.trans hθ))
        _ = _ := by ring
    have hE := herror.trans (le_mul_of_one_le_left (herror0.trans herror)
      (one_le_pow₀ hCF : 1 ≤ CF^2))
    calc
      _ ≤ 16*(CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n *
          (4*(1+olderShear J X n))^2)+CF^2*(priorError J D X n+neighborError J D X c n)) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain hE) (by norm_num)
      _ = _ := by unfold geometryError; ring
  have hcoef0 : 0 ≤ 16*(P.epsilon*P.horizon*(4*P.G)^2 +
      P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ) := by
    positivity
  have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by
    have he : 1 ≤ Real.exp 6 := Real.one_le_exp_iff.mpr (by norm_num)
    unfold neighborStabilityConstant
    linarith only [he]
  have hN : 0 ≤ 1000000*neighborStabilityConstant := zero_le_one.trans hN1
  have hsmall :
      1000000*neighborStabilityConstant *
        (16*(P.epsilon*P.horizon*(4*P.G)^2 +
          P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ))*P.horizon^40 ≤ 1 := by
    calc
      _ ≤ 1000000*neighborStabilityConstant*(CF^2*geometryError J D C c X a n) *
          sourceTheta J C (scaleSequence J X) n^40 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef hN)
          (pow_le_pow_left₀ (zero_le_one.trans hhor) hhorθ 40)
          (pow_nonneg (zero_le_one.trans hhor) 40) (mul_nonneg hN (hcoef0.trans hcoef))
      _ = 1000000*(neighborStabilityConstant*CF^2)*geometryError J D C c X a n *
          sourceTheta J C (scaleSequence J X) n^40 := by ring
      _ ≤ 1 := stage.geometry_small
  have hplain : 16*(P.epsilon*P.horizon*(4*P.G)^2 +
      P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ) ≤ 1 := by
    have hh : 1 ≤ 1000000*neighborStabilityConstant*P.horizon^40 :=
      one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hhor)
    have hb := mul_le_mul_of_nonneg_right hh hcoef0
    linarith only [hb,hsmall]
  have hcompress :
      60*(P.G+P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ) *
        (targetTime J X (β n) n)*P.epsilon < P.a :=
    compression_of_error_small (by simpa only [ha_match] using ha) hepsPos.le
      (zero_le_one.trans hhor) htarget_le P.G_lower herror0 hplain
  refine {
    CM := CM, CH := CH, ζ := ζ, radius := ρ, y := (scaleSequence J X (n+1))⁻¹,
    δ := δ, hchild := hchild,
    CM_nonneg := hCM, CH_nonneg := hCH, zeta_nonneg := hζ, radius_nonneg := hρ,
    delta_nonneg := hδ, child_nonneg := hhchild,
    coupling_lower := by simpa only [ha_match] using ha,
    shear_pos := hshearPos,
    sigma_pos := hsigmaPos,
    sigma_small := by simpa only [hsigma] using stage.sigma_small,
    epsilon_small := by simpa only [hepsilon] using stage.epsilon_small,
    y_pos := stage.reciprocal_pos,
    y_small := stage.reciprocal_small,
    target_le_horizon := by simpa only [htarget] using htarget_le,
    horizon_lower := hhor,
    short_extension := by simpa only [htarget] using hshort,
    small := hsmall,
    compression_guard := by simpa only [htarget] using hcompress,
    normal_choice := hnormal,
    history_symmetric := fun t => G.initial_history_symmetric p hp hacc m hm R S hS H
      τ hτ hτT.le t 0,
    history_layer := by simpa only [hshear] using hlayer,
    history_strain := fun t => ((EulerTransverseSourceCoefficientPath.pathEvaluation 0
      ((G.transverseData m hm R S hS).initial τ hτ hτT.le).M.field).norm_coe_le_norm t).trans
      (by simpa only [hshear] using hstrain),
    history_hessian := by simpa only [hshear] using hhessian,
    activation_small := hactivation,
    activation_error := (add_le_add hG herr).trans (by simpa only [hshear] using hactivationError),
    activation_compression := P.activation_compression_of_previous hτ hτT
      (priorError J D X n) herr hpreviousCompression }

end EulerParentPacketFrames.LabelData
