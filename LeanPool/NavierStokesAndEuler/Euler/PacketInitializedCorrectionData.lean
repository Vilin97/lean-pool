/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionConstants
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer

/-! The fully initialized finite packet supplies the actual all-order data
of the correction equation, with its derived word estimates. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized normalized field, given by `((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ
hs α N k⁻¹).smul k).changeTime hTime`. -/
def initializedNormalizedField (N : ℕ) (k : ℝ) :=
  ((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).changeTime hTime

/-- Initialized normalized residual field used in packet initialized correction data. -/
def initializedNormalizedResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :=
  (((joinedSourceCoefficientData period M D τ hτ hτT B hTime).inverse.multiply
    (initializedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k⁻¹
      (inv_ne_zero (by linarith)))).smul k).changeTime hTime

/-- Initialized correction data, constructed using
`EulerPacketCorrectionCoefficients.correctionDataOfFields`. -/
def initializedCorrectionData (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    EulerAllOrderCorrectionData.Data period D.T :=
  EulerPacketCorrectionCoefficients.correctionDataOfFields D period k⁻¹
    (by rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
        exact inv_le_one_of_one_le₀ (by linarith))
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
    (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)

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
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedNormalizedField_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).WordBound
      6 (4*L.R) (velocity L.R S.H0 BC.multiplierCost) 0 :=
  (initializedPacket_normalized_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).changeTime hTime

theorem initializedNormalizedField_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R) (normal L.R S.H0 BC.multiplierCost/k) 0 := by
  have hh := (initializedPacket_normal_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).changeTime hTime
  exact hh.ofRawEq _ (fun _ _ _ => rfl)

theorem initializedNormalizedResidualField_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk).WordBound
      6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 :=
  (initializedResidual_normalized_bound M D hTime τ hτ hτT B δ hδ ξ hs α L H NB W LM WM BC
    hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k X hk hbase hcoef hX hNX).changeTime hTime

end EulerPacketTerminalDatum
