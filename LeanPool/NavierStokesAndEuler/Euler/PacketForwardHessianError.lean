/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPressureRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! The actual finite pressure Hessian is its primary normal tensor plus
a uniform inverse-frequency error. No derivative or remainder estimate
is assumed for a solved field. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerPacketForwardPrimary EulerPeriodicProfile
  EulerPacketInverseFlowGevrey EulerPacketPhysicalGevrey EulerGevrey
  EulerLiftedGradientSpace EulerCylinderSobolevSpace
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Forward initialized pressure hessian cost, constructed using `fastHessianCost`. -/
def forwardInitializedPressureHessianCost {D : Data U} {q : ℕ} {R₀ : ℝ}
    (NB : EulerTransversePacketJoin.NormalBudget D q R₀) (R H0 Rc C : ℝ) : ℝ :=
  fastHessianCost (P := period) NB (4*R) (fixedVelocityGradeCost R H0 1) +
    9*C*physicalFixedCost D Rc C (4*R) 1*sobolevEmbeddingConstant period 3 *
      (fixedVelocityGradeCost R H0 2+2)

variable (M : EulerMeanPacketProvider.Data) (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedAngularPressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z)) := by
  have hq := pressure_smooth D (initialData D δ hδ (α • ξ) hs) t
  simp only [forwardInitializedAngularPressure,pressureJet_angle]
  change ContDiff ℝ ∞ (angularDerivative (fun y =>
    scalar D (initialData D δ hδ (α • ξ) hs) (t,y)))
  exact angularDerivative_contDiff hq

theorem forwardInitializedAngularPressure_second (t : Icc (0 : ℝ) D.T) (z : LiftTangent) :
    angularDerivative (fun w => forwardInitializedAngularPressure D δ hδ ξ hs α (t,w)) z =
      EulerPacketForwardShear.pressureCoefficient D ξ α t z.1 * deriv (profile δ) z.2 := by
  have hq := pressure_smooth D (initialData D δ hδ (α • ξ) hs) t
  simp only [forwardInitializedAngularPressure,pressureJet_angle]
  change angularDerivative (angularDerivative (fun w =>
    scalar D (initialData D δ hδ (α • ξ) hs) (t,w))) z = _
  rw [angularSecond_eq_deriv hq]
  exact EulerPacketForwardShear.scalar_second_deriv D δ hδ ξ hs α t z.1 z.2

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
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem forwardInitializedPressure_hessian_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ)))) x -
      (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
      rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤
        forwardInitializedPressureHessianCost NB L.R S.H0 L.Rc L.C₀/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_one
  let AF := forwardInitializedAngularPressureField M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  let RF := forwardInitializedCovectorRemainderField M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹
  let a : LiftTangent → ℝ := fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z)
  let J : Space → Space →L[ℝ] Space := fun y => D.FInv.field t (Y t y)
  have hYd := continuousInverse_differentiable D X Y hX hXY hY
  have hYder := continuousInverse_hasFDerivAt D X Y hX hXY hY
  have hJ : DifferentiableAt ℝ J x :=
    ((D.FInv.smooth t).differentiable (by simp) (Y t x)).comp x (hYd t x)
  have ha : ContDiff ℝ ∞ a := forwardInitializedAngularPressure_smooth D δ hδ ξ hs α t
  have hf := fastForce_hasFDerivAt a k hk0.ne' D.m₀ (Y t) J x (hYder t x) hJ
    (ha.differentiable (by simp) _)
  have hsecond : angularDerivative a (graphMap k D.m₀ (Y t x)) =
      EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ) :=
    forwardInitializedAngularPressure_second D δ hδ ξ hs α t _
  have hn : transportedNormal D.m₀ J x = D.normal.field t (Y t x) := rfl
  rw [hsecond,hn] at hf
  have hRF := forwardInitializedCovectorRemainder_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hAF := forwardInitializedAngularPressure_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  have hfast := fastHessianRemainder_bound NB
    (forwardInitializedAngularPressure D δ hδ ξ hs α) AF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 1) (by positivity)
    (fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1) hAF k hk0 t (Y t) x (hYder t x)
    (ha.differentiable (by simp) _)
  have htail := physicalCovector_error_bound D RF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 2+2) (by positivity)
    (by have h := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 2; linarith)
    k (by linarith) hRF L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg hdet L.frame_bound
    X Y hX hYd hXY t x
  have htaild : DifferentiableAt ℝ (physicalCovector D RF k Y t) x := by
    have hI := (adjoint.differentiableAt.comp x hJ)
    have hR := (RF.raw_graph_contDiff t k D.m₀).differentiable (by simp) (Y t x)
    have hRg := hR.comp x (hYd t x)
    exact hI.clm_apply hRg
  have he : gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
      (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) =
      fastForce a k D.m₀ (Y t) J + physicalCovector D RF k Y t := by
    funext y
    exact forwardInitializedPressure_gradient_decomposition M D hTime δ hδ ξ hs α
      N k hk0.ne' t (Y t) y (hYder t y)
  calc
    _ = ‖fastHessianRemainder a k D.m₀ (Y t) J x +
        fderiv ℝ (physicalCovector D RF k Y t) x‖ := by
      rw [he,fderiv_add hf.differentiableAt htaild,hf.fderiv]
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hfast htail).trans_eq (by
      unfold forwardInitializedPressureHessianCost
      ring))

end EulerPacketTerminalDatum
