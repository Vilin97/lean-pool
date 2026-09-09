/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudgetTimeChange

/-! All-grade bounds for the actual zero-history source recursion, initialized
by the literal compact periodic wave.  Every later forcing and solution is
constructed, and the primary budget is discharged from its actual datum. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
      EulerParameterWordGevrey

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Forward initialized profiles, given by `sourceProfiles period M D (InitialData.zero period
D) (initialData D δ hδ (α • ξ) hs)`. -/
def forwardInitializedProfiles : ℕ → Profile :=
  sourceProfiles period M D (InitialData.zero period D) (initialData D δ hδ (α • ξ) hs)

/-- Forward initialized profile witness, given by `sourceProfileWitness period M D hTime
(InitialData.zero period D) (initialData D δ hδ (α • ξ) hs) p`. -/
def forwardInitializedProfileWitness (p : ℕ) :
    ProfileRegularity period M.T M.T_pos.le D.support (forwardInitializedProfiles M D δ hδ ξ hs α
        p) :=
  sourceProfileWitness period M D hTime (InitialData.zero period D) (initialData D δ hδ (α • ξ) hs)
      p

variable (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

include NB hδ1 hα hR WP hgrowth in
theorem forwardInitialized_primary_budget :
    ProfileBudget (forwardSourcePrimaryWitness period M D hTime (initialData D δ hδ (α • ξ) hs))
      S L.R 1 := by
  have hg : (S.changeTime hTime).growth=α • L.g := (S.growth_changeTime hTime).trans hgrowth
  have hD := forwardPrimary_profile_budget L NB δ hδ hδ1 ξ hs α hα hR WP
    (sourceOperators period M D (InitialData.zero period D)) rfl (S.changeTime hTime) hg
  have hM := hD.changeTime hTime.symm M.T_pos.le
  rw [Scales.changeTime_roundtrip] at hM
  exact hM

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth in
theorem forwardInitialized_profile_budgets (p : ℕ) (hp : 1 ≤ p) :
    ProfileBudget (forwardInitializedProfileWitness M D hTime δ hδ ξ hs α p) S L.R p :=
  forwardSource_profile_budgets period M D hTime (initialData D δ hδ (α • ξ) hs)
    L NB W LM WM BC hRc hcost S α hα hgrowth
    (forwardInitialized_primary_budget M D hTime δ hδ ξ hs α L NB hδ1 hα hR WP S hgrowth) p hp

end EulerPacketTerminalDatum
