/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardHessianError
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields

@[expose] public section

/-! The canonical pressure Hessian of the exact forward packet differs
from the literal primary normal tensor by its proved finite tail and
the Hessian of the same actual correction. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerPacketForwardPrimary EulerPeriodicProfile
  EulerPacketInverseFlowGevrey EulerPacketPhysicalGevrey EulerGevrey
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderDriftCorrection
  EulerPacketCoordinates EulerGraphPressurePotential
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk))

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x)=x) (hY : Continuous (Function.uncurry Y))

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

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth hX hXY hY in
theorem forwardInitializedExactPhysicalPressure_hessian_error
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t))) x -
      (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
      rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤
        forwardInitializedPressureHessianCost NB L.R S.H0 L.Rc L.C₀/k +
          ‖fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x‖ := by
  rw [forwardInitializedExactPhysicalPressure_hessian M D hTime δ hδ ξ hs α
    Cagree N hN k hk Q X Y hX hXY hY t x]
  have he : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (forwardInitializedPressure_hessian_bound M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
      X Y hX hXY hY hdet t x) le_rfl)

end EulerPacketTerminalDatum
