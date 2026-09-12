/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedHessianError
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCorrectionPotential
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! The canonical scalar pressure of the actual exact packet has the
finite pressure's Hessian plus the Hessian of its actual correction.
The normalization of the scalar potential does not affect this identity. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerTransversePacketPrimary EulerPeriodicProfile
  EulerPacketInverseFlowGevrey EulerPacketPhysicalGevrey EulerGevrey
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderDriftCorrection
  EulerPacketCoordinates EulerGraphPressurePotential
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))

/-- Initialized exact physical pressure, given by `(initializedExactPacket M D hTime τ hτ hτT B
δ hδ ξ hs α Cagree N hN k hk Q).graphPotential k t ∘ Y`. -/
def initializedExactPhysicalPressure (t : Icc (0 : ℝ) D.T) (Y : Space → Space) : Space → ℝ :=
  (initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q).graphPotential k t ∘
      Y

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem initializedExactPhysicalPressure_gradient
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t)) x =
      gradient (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) x +
      gradient (Q.physicalPotential D period k Y t) x := by
  have hk0 : k ≠ 0 := by linarith
  have hkk : k*(initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk).κ=1 := mul_inv_cancel₀ hk0
  let S := initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q
  let R := initializedApproximationResidual M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk
  have hpressure : S.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) =
      R.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) +
        Q.pointPressure period t (cylinderGraph period k D.m₀ (Y t x)) :=
    exactPacketOfResidual_pressure_pointField period Q R t _
  have hactual : R.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) =
      coordinatePressure D k (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
        (t,(Y t x,k*⟪D.m₀,Y t x⟫_ℝ)) :=
    (initializedCoordinatePressureField M D hTime τ hτ hτT B δ hδ ξ hs α N k
        hk0).toFieldTower_pointField_raw
      t (Y t x) (k*⟪D.m₀,Y t x⟫_ℝ)
  have hp := ((initializedPressureWitness M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).changeTime
      hTime).smooth t
  change gradient (S.graphPotential k t ∘ Y t) x = _
  rw [EulerLagrangian.gradient_pullback _ _ _ _
    (continuousInverse_hasFDerivAt D X Y hX hXY hY t x)
    ((S.graphPotential_smooth k hkk t).differentiable (by simp) (Y t x)),
    S.graphPotential_gradient k hkk t (Y t x),map_smul]
  change k⁻¹ • (D.FInv.field t (Y t x)).adjoint
    (S.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x))) = _
  rw [hpressure,hactual,map_add,smul_add,
    Q.physicalPotential_gradient D period X Y hX hXY hY k hkk t x,
    gradient_physical_covector k D.m₀ _ t (Y t) _ x
      (continuousInverse_hasFDerivAt D X Y hX hXY hY t x) (hp.differentiable (by simp) _)]
  congr 1
  simp only [coordinatePressure,covector,angularPressure,Pi.add_apply,Pi.smul_apply,
    map_add,map_smul,smul_add,smul_smul]
  match_scalars <;> field_simp

include hX hXY hY in
theorem initializedExactPhysicalPressure_hessian
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    fderiv ℝ (gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t))) x =
      fderiv ℝ (gradient (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ)))) x +
      fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x := by
  have hk0 : k ≠ 0 := by linarith
  have hkk : k*(initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk).κ=1 := mul_inv_cancel₀ hk0
  have hp := ((initializedPressureWitness M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).changeTime
      hTime).smooth t
  have hYc := continuousInverse_contDiff D X Y hX hXY hY t
  have hfinite : ContDiff ℝ ∞ (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) := hp.comp ((graphMap k D.m₀).contDiff.comp hYc)
  have hc := Q.physicalPotential_smooth D period X Y hX hXY hY k hkk t
  have he := funext (initializedExactPhysicalPressure_gradient M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q X Y hX hXY hY t)
  rw [he]
  exact fderiv_fun_add
    ((EulerMeanSolenoidal.contDiff_gradient hfinite).differentiable (by simp) x)
    ((EulerMeanSolenoidal.contDiff_gradient hc).differentiable (by simp) x)

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

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth hX hXY hY in
theorem initializedExactPhysicalPressure_hessian_error
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t))) x -
      (EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
      rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤
        initializedPressureHessianCost NB L.R S.H0 L.Rc L.C₀/k +
          ‖fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x‖ := by
  rw [initializedExactPhysicalPressure_hessian M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q X Y hX hXY hY t x]
  have he : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (initializedPressure_hessian_bound M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
      X Y hX hXY hY hdet t x) le_rfl)

end EulerPacketTerminalDatum
