/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedResidualEquation
public import LeanPool.NavierStokesAndEuler.Euler.PacketRemainderBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2

@[expose] public section

/-! The literal forward finite packet is its actual primary plus a
remainder with a proved physical C1 bound. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerPacketPrimaryShear EulerPacketForwardFactorization EulerPacketForwardPrimary
  EulerCylinderCoordinates
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedProfiles_zero : forwardInitializedProfiles M D δ hδ ξ hs α 0 = 0 :=
  profiles_zero _ _

theorem forwardInitializedProfiles_one_high :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).high =
      vector D (initialData D δ hδ (α • ξ) hs) := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

theorem forwardInitializedProfiles_one_mean :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).mean = 0 := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

def forwardInitializedPrimaryRemainder (N : ℕ) (κ : ℝ) : VectorField :=
  forwardInitializedVelocity M D δ hδ ξ hs α N κ -
    κ • vector D (initialData D δ hδ (α • ξ) hs)

def forwardInitializedPrimaryRemainderField (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) :
    Field period D.T (forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N κ) :=
  ((ProfileRegularity.primaryRemainderField M.T_pos
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    hN (forwardInitializedProfiles_zero M D δ hδ ξ hs α)
    (forwardInitializedProfiles_one_mean M D δ hδ ξ hs α) κ).changeTime hTime).congr
      (fun _ _ _ => by rw [forwardInitializedProfiles_one_high]; rfl)

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.g)

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem forwardInitializedPrimaryRemainder_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (forwardInitializedPrimaryRemainderField M D hTime δ hδ ξ hs α N hN k⁻¹).WordBound
      6 (4*L.R) ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) 0 := by
  let G := fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have h := ProfileRegularity.primaryRemainder_bound M.T_pos G hG L.radius_one
    (forwardInitializedProfiles_zero M D δ hδ ξ hs α)
    (forwardInitializedProfiles_one_mean M D δ hδ ξ hs α) hN BC k hk hbase
  exact (h.changeTime hTime).of_raw_eq _ (fun _ _ _ => by rw [forwardInitializedProfiles_one_high];
    rfl)

theorem forwardInitializedPrimaryRemainder_physical_norm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) :
    ‖forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
      (t,(Y x,k*inner ℝ D.m₀ (Y x)))‖ ≤
      sobolevEmbeddingConstant period 3*((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) :=
  (forwardInitializedPrimaryRemainder_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).raw_graph_norm_le
      (by norm_num) t k D.m₀ (Y x)

theorem forwardInitializedPrimaryRemainder_physical_fderiv (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : DifferentiableAt ℝ Y x) :
    ‖fderiv ℝ (fun y => forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x‖ ≤
      (frequencyFactor k D.m₀*(sobolevEmbeddingConstant period 3*
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ :=
  (forwardInitializedPrimaryRemainder_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).raw_physical_fderiv_le
      (by norm_num) t k D.m₀ Y x hY

omit NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth in
/-- The constant contains no packet frequency or derivative of the inverse flow. -/
def forwardInitializedRemainderDerivativeCost (R H0 : ℝ) : ℝ :=
  8*‖coordinateEquiv.symm.toContinuousLinearMap‖*sobolevEmbeddingConstant period 3*
    R*(fixedVelocityGradeCost R H0 2+2)

theorem forwardInitializedPrimaryRemainder_physical_fderiv_inv (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : DifferentiableAt ℝ Y x) :
    ‖fderiv ℝ (fun y => forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x‖ ≤
      (forwardInitializedRemainderDerivativeCost L.R S.H0/k)*‖fderiv ℝ Y x‖ := by
  have hk0 : k ≠ 0 := by linarith
  have hc := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_one) 2
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hr : 0 ≤ L.R := zero_le_one.trans L.radius_one
  have hb : 0 ≤ sobolevEmbeddingConstant period 3*
      ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R) := by positivity
  have hf := frequencyFactor_le_linear k (by linarith) D.m₀
  rw [D.m₀_unit] at hf
  norm_num only at hf
  have h := forwardInitializedPrimaryRemainder_physical_fderiv M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY
  calc
    _ ≤ (frequencyFactor k D.m₀*(sobolevEmbeddingConstant period 3*
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ := h
    _ ≤ ((‖coordinateEquiv.symm.toContinuousLinearMap‖*2*k)*(sobolevEmbeddingConstant period 3*
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf hb) (norm_nonneg _)
    _ = _ := by unfold forwardInitializedRemainderDerivativeCost; field_simp; ring

end EulerPacketTerminalDatum
