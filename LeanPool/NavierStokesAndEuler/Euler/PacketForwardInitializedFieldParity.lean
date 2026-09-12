/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldParityAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketReflection
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteParity
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfilesParity
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParity

/-! The literal zero-history initialized packet and its exact residual tail are odd
as actual cylinder L² paths, before and after coordinate normalization. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerCylinderFieldReflection

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)

include hTime eM hSym hF hDM

theorem forwardInitializedVelocity_odd (N : ℕ) (κ : ℝ) :
    JointOdd M.T (fieldSum (N+1) κ
      (assembledVelocity N (forwardInitializedProfiles M D δ hδ ξ hs α))) :=
  ProfileParity.velocity_odd
    (fun i _ => forwardInitializedProfiles_parity M D hTime δ hδ ξ hs α
      eM hSym hF hDM i) κ

theorem forwardInitializedPacketField_odd (N : ℕ) (κ : ℝ) :
    (forwardInitializedPacketField M D hTime δ hδ ξ hs α N κ).ReflectionOdd := by
  apply Field.reflectionOdd_of_raw
  exact (forwardInitializedVelocity_odd M D hTime δ hδ ξ hs α
    eM hSym hF hDM N κ).matrix_apply _
    (sourceCoefficientEven period M D (InitialData.zero period D) hF hDM).inverse

theorem forwardInitializedNormalizedField_odd (N : ℕ) (k : ℝ) :
    (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k).ReflectionOdd :=
  ((forwardInitializedPacketField_odd M D hTime δ hδ ξ hs α
    eM hSym hF hDM N k⁻¹).smul k).changeTime hTime

theorem forwardInitializedResidualField_odd (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :
    (forwardInitializedResidualField M D hTime δ hδ ξ hs α Cagree N hN κ hκ).ReflectionOdd := by
  let a := forwardInitializedProfiles M D δ hδ ξ hs α
  let G := fun (i : ℕ) (_ : i ≤ N) =>
    forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i
  have H : ∀ i, i ≤ N → ProfileParity M.T (a i) :=
    fun i _ => forwardInitializedProfiles_parity M D hTime δ hδ ξ hs α
      eM hSym hF hDM i
  have ha : a 0 = 0 := profiles_zero _ _
  have htail := ProfileRegularity.residualTail_odd M.T_pos G H
    (sourceCoefficientData period M D (InitialData.zero period D) hTime)
    (sourceCoefficientEven period M D (InitialData.zero period D) hF hDM) ha κ
  intro t
  exact (ProfileRegularity.tailSumField M.T_pos G
    (sourceCoefficientData period M D (InitialData.zero period D) hTime) ha
        κ).reflection_neg_of_raw_odd
    t (htail t)

theorem forwardInitializedNormalizedResidualField_odd (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    (forwardInitializedNormalizedResidualField M D hTime δ hδ ξ hs α
      Cagree N hN k hk).ReflectionOdd := by
  have h := forwardInitializedResidualField_odd M D hTime δ hδ ξ hs α
    eM hSym hF hDM Cagree N hN k⁻¹ (inv_ne_zero (by linarith))
  exact ((h.multiply (sourceCoefficientData period M D (InitialData.zero period D) hTime).inverse
    (sourceCoefficientEven period M D (InitialData.zero period D) hF hDM).inverse).smul
        k).changeTime hTime

end EulerPacketTerminalDatum
