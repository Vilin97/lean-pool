/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixNormalization
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedResidualEquation
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency

@[expose] public section

/-! The actual derivative of the initialized normalized approximation
has a source-dependent Gevrey bound uniform in the truncation frequency.
The time derivative of the inverse deformation is included explicitly. -/

noncomputable section


namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerPacketSourceFrequency EulerParameterWordGevrey
  EulerPacketCoordinates EulerPacketCorrectionCoefficients
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedNormalizedDerivativeField (N : ℕ) (k : ℝ) :=
  coordinateTimeField D
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹) k

theorem initializedNormalizedField_time (N : ℕ) (k : ℝ) :
    TimeDerivative D.T_pos.le
      (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
      (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k) := by
  have h := coordinateField_time D
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹) k
    (initializedVelocityField_time M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
  intro t
  change HasDerivWithinAt
    (EulerVolterraConvolution.extendPath D.T D.T_pos.le
      (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).path) _ _ _
  rw [initializedNormalizedField_path_eq M D hTime τ hτ hτT B δ hδ ξ hs α N k]
  exact h t

variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedNormalizedDerivativeField_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k).WordBound
      6 (4*L.R) (6*NB.blockAmplitude*
        (fixedVelocityGradeCost L.R S.H0 1+fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let G : ∀ i, i ≤ N → ProfileRegularity period M.T M.T_pos.le D.support
      (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α i) :=
    fun i _ => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have hzero : initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 0 = 0 := profiles_zero _ _
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase L.R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase L.R S.H0 BC.termCost N) hk hbase
  have hv := (ProfileRegularity.velocity_bound M.T_pos G hG L.radius_bounds.1 hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have ht := (ProfileRegularity.velocityDerivative_bound M.T_pos G hG L.radius_bounds.1 hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have hKR : sobolevCoefficientRadius (Fin 4) NB.coefficientRadius ≤ 4*L.R :=
    NB.radius.trans (by have := L.radius_bounds.1; linarith)
  have hlow1 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_bounds.1) 1
  have hlow2 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_bounds.1) 2
  have ha := (inverseTimeCoefficient D).normalized_approximation_bound
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).2.1) hv
    (by have := L.radius_bounds.1; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hb := (inverseCoefficient D).normalized_approximation_bound
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).1) ht
    (by have := L.radius_bounds.1; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hh := (ha.add hb).of_raw_eq
    (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
    (fun _ _ _ => smul_add _ _ _)
  convert hh using 1
  dsimp [EulerTransversePacketJoin.NormalBudget.blockAmplitude]
  ring

end EulerPacketTerminalDatum
