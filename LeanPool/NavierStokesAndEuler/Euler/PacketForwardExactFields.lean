/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedExactLifted
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCorrectionPotential
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureCovector
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalGevrey

@[expose] public section

/-! The exact zero-history packet has its literal finite velocity and scalar
pressure plus the actual correction. These identities use the canonical
pressure potential and therefore also identify its Hessian. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPacketCoordinates EulerPacketCorrectionCoefficients EulerPacketPhysicalGevrey
  EulerPacketPressure EulerPacketGraphHessian EulerGraphPullback EulerPacketInverseFlowGevrey
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk))

def forwardInitializedExactPhysicalVelocity (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) :
  Space :=
  k⁻¹ • D.F.field t (Y x)
    ((forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q).velocity.pointField
      t (cylinderGraph period k D.m₀ (Y x)))

/-- The approximation is exactly the finite physical velocity after
undoing its true normalized coordinate transformation. -/
theorem forwardInitializedExactPhysicalVelocity_eq (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x :
  Space) :
    forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α Cagree N hN k hk Q t Y x =
      forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
        (t,(Y x,k*inner ℝ D.m₀ (Y x))) +
      k⁻¹ • D.F.field t (Y x) (Q.pointField period t (cylinderGraph period k D.m₀ (Y x))) := by
  have hk0 : k ≠ 0 := by linarith
  have ha : (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).approximation
    =
      (coordinateField D (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
        k).toFieldTower :=
    forwardInitializedNormalizedField_tower_eq M D hTime δ hδ ξ hs α N k
  change k⁻¹ • D.F.field t (Y x)
    ((exactPacketOfResidual period Q
      (forwardInitializedApproximationResidual M D hTime δ hδ ξ hs α Cagree N hN k
        hk)).velocity.pointField
        t (cylinderGraph period k D.m₀ (Y x))) = _
  rw [exactPacketOfResidual_velocity_pointField,ha,map_add,smul_add]
  congr 1
  have he := (coordinateField D (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
    k).toFieldTower_pointField_raw
    t (Y x) (k*inner ℝ D.m₀ (Y x))
  rw [show cylinderGraph period k D.m₀ (Y x) =
      (Y x,((k*inner ℝ D.m₀ (Y x) : ℝ) : AddCircle period)) from rfl,he]
  simp only [coordinate,rawInverse,Data.clamp_coe,map_smul,D.inverse_right,
    smul_smul,inv_mul_cancel₀ hk0,one_smul]

theorem forwardInitializedExactPhysicalVelocity_fderiv (t : Icc (0 : ℝ) D.T)
    (Y : Space → Space) (x : Space) (hY : DifferentiableAt ℝ Y x) :
    fderiv ℝ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x =
      fderiv ℝ (fun y => forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x +
      fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
        (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x := by
  have hw : DifferentiableAt ℝ (fun y => forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x := by
    simpa only [Function.comp_def] using
      (((forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹).raw_graph_contDiff
        t k D.m₀).differentiable (by simp) (Y x)).comp x hY
  have he : DifferentiableAt ℝ (fun y => k⁻¹ • D.F.field t (Y y)
      (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x := by
    simpa only [Function.comp_def,graphReconstruction,physicalField] using
      ((graphReconstruction_contDiff D period k⁻¹ k (Q.pointField period)
        (Q.pointField_smooth period) t).differentiable (by simp) (Y x)).comp x hY
  have hfun := funext (forwardInitializedExactPhysicalVelocity_eq M D hTime δ hδ ξ hs α
    Cagree N hN k hk Q t Y)
  rw [hfun]
  exact fderiv_fun_add hw he

def forwardInitializedExactPhysicalPressure (t : Icc (0 : ℝ) D.T) (Y : Space → Space) : Space → ℝ :=
  (forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q).graphPotential k t ∘ Y

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x)=x) (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem forwardInitializedExactPhysicalPressure_gradient
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t)) x =
      gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) x +
      gradient (Q.physicalPotential D period k Y t) x := by
  have hk0 : k ≠ 0 := by linarith
  have hkk : k*(forwardInitializedCorrectionData M D hTime δ hδ ξ hs α
      Cagree N hN k hk).κ=1 := mul_inv_cancel₀ hk0
  let S := forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q
  let R := forwardInitializedApproximationResidual M D hTime δ hδ ξ hs α Cagree N hN k hk
  have hpressure : S.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) =
      R.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) +
        Q.pointPressure period t (cylinderGraph period k D.m₀ (Y t x)) :=
    exactPacketOfResidual_pressure_pointField period Q R t _
  have hactual : R.pressure.pointField t (cylinderGraph period k D.m₀ (Y t x)) =
      coordinatePressure D k (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)
        (t,(Y t x,k*⟪D.m₀,Y t x⟫_ℝ)) :=
    (forwardInitializedCoordinatePressureField M D hTime δ hδ ξ hs α N k
      hk0).toFieldTower_pointField_raw
      t (Y t x) (k*⟪D.m₀,Y t x⟫_ℝ)
  have hp := ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).changeTime
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
theorem forwardInitializedExactPhysicalPressure_hessian
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q t (Y t))) x =
      fderiv ℝ (gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ)))) x +
      fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x := by
  have hk0 : k ≠ 0 := by linarith
  have hkk : k*(forwardInitializedCorrectionData M D hTime δ hδ ξ hs α
      Cagree N hN k hk).κ=1 := mul_inv_cancel₀ hk0
  have hp := ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).changeTime
    hTime).smooth t
  have hYc := continuousInverse_contDiff D X Y hX hXY hY t
  have hfinite : ContDiff ℝ ∞ (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
      (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) := hp.comp ((graphMap k D.m₀).contDiff.comp hYc)
  have hc := Q.physicalPotential_smooth D period X Y hX hXY hY k hkk t
  have he := funext (forwardInitializedExactPhysicalPressure_gradient M D hTime δ hδ ξ hs α
    Cagree N hN k hk Q X Y hX hXY hY t)
  rw [he]
  exact fderiv_fun_add
    ((EulerMeanSolenoidal.contDiff_gradient hfinite).differentiable (by simp) x)
    ((EulerMeanSolenoidal.contDiff_gradient hc).differentiable (by simp) x)

end EulerPacketTerminalDatum
