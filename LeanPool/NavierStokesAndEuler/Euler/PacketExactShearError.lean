/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalGevrey
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedExactLifted
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! The exact corrected packet has the same primary shear, with the
literal finite-tail and correction derivatives as its only errors. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
   EulerPacketPrimaryFactorization EulerTransversePacketPrimary
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPacketCoordinates EulerPacketCorrectionCoefficients EulerPacketPhysicalGevrey
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))

/-- Initialized exact physical velocity as an element of `Space`. -/
def initializedExactPhysicalVelocity (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) : Space
    :=
  k⁻¹ • D.F.field t (Y x)
    ((initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk
        Q).velocity.pointField
      t (cylinderGraph period k D.m₀ (Y x)))

/-- The approximation is exactly the finite physical velocity after
undoing its true normalized coordinate transformation. -/
theorem initializedExactPhysicalVelocity_eq (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) :
    initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q t Y x =
      initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y x,k*inner ℝ D.m₀ (Y x))) +
      k⁻¹ • D.F.field t (Y x) (Q.pointField period t (cylinderGraph period k D.m₀ (Y x))) := by
  have hk0 : k ≠ 0 := by linarith
  have ha : (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
      hk).approximation =
      (coordinateField D (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
          k).toFieldTower :=
    initializedNormalizedField_tower_eq M D hTime τ hτ hτT B δ hδ ξ hs α N k
  change k⁻¹ • D.F.field t (Y x)
    ((exactPacketOfResidual period Q
      (initializedApproximationResidual M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
          hk)).velocity.pointField
        t (cylinderGraph period k D.m₀ (Y x))) = _
  rw [exactPacketOfResidual_velocity_pointField,ha,map_add,smul_add]
  congr 1
  have he := (coordinateField D (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
      k).toFieldTower_pointField_raw
    t (Y x) (k*inner ℝ D.m₀ (Y x))
  rw [show cylinderGraph period k D.m₀ (Y x) =
      (Y x,((k*inner ℝ D.m₀ (Y x) : ℝ) : AddCircle period)) from rfl,he]
  simp only [coordinate,rawInverse,Data.clamp_coe,map_smul,D.inverse_right,
    smul_smul,inv_mul_cancel₀ hk0,one_smul]

theorem initializedExactPhysicalVelocity_fderiv (t : Icc (0 : ℝ) D.T)
    (Y : Space → Space) (x : Space) (hY : DifferentiableAt ℝ Y x) :
    fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x =
      fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x +
      fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
        (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x := by
  have hw : DifferentiableAt ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x := by
    simpa only [Function.comp_def] using
      (((initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).raw_graph_contDiff
        t k D.m₀).differentiable (by simp) (Y x)).comp x hY
  have he : DifferentiableAt ℝ (fun y => k⁻¹ • D.F.field t (Y y)
      (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x := by
    simpa only [Function.comp_def,graphReconstruction,physicalField] using
      ((graphReconstruction_contDiff D period k⁻¹ k (Q.pointField period)
        (Q.pointField_smooth period) t).differentiable (by simp) (Y x)).comp x hY
  have hfun := funext (initializedExactPhysicalVelocity_eq M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q t Y)
  rw [hfun]
  exact fderiv_fun_add hw he

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

theorem initializedExactPhysicalVelocity_gradient_error
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t Y) (X 0) -
      (α/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0)‖ ≤
      (initializedRemainderDerivativeCost L.R S.H0/k)*‖D.FInv.field t 0‖ +
      ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
        (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) (X 0)‖ := by
  rw [initializedExactPhysicalVelocity_fderiv M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q t Y (X 0) hY]
  have he : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (initializedVelocity_gradient_error M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t X Y hX hY hleft) le_rfl)

end EulerPacketTerminalDatum
