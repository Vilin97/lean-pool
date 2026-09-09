/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! The actual finite and exact packets have the source shear at every
physical point. The slow primary derivative and finite tail contribute
only a fixed source constant divided by the frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderSobolevSpace EulerCylinderCoordinates
  EulerPacketPrimaryShear EulerPacketForwardFactorization EulerPacketForwardPrimary
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPeriodicProfile EulerGevrey
open scoped ContDiff

/-- Forward initialized global shear cost as an element of `ℝ`. -/
def forwardInitializedGlobalShearCost (R H0 C : ℝ) : ℝ :=
  ‖coordinateEquiv.symm.toContinuousLinearMap‖*
      (sobolevEmbeddingConstant period 3*fixedVelocityGradeCost R H0 1*(4*R))*C +
    |forwardInitializedRemainderDerivativeCost R H0| *C

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
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

theorem forwardInitializedPrimary_global_bound :
    ((forcing D).vectorField (initialData D δ hδ (α • ξ) hs)).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  have hG := forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1 le_rfl
  have hb := hG.high.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_one) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_one) S.H0_pos.le
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [forwardInitializedProfiles_one_high])

theorem forwardInitializedVelocity_global_gradient_error (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (fun y => forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity D ξ t (Y x)) (D.normal.field t (Y x))‖ ≤
      forwardInitializedGlobalShearCost L.R S.H0 NB.C/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_one
  have hc0 := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1
  have hinv : ‖D.FInv.field t (Y x)‖ ≤ NB.C := by
    simpa [majorant] using NB.inverse_bound 0 t (Y x)
  have hprimary := EulerPacketForwardShear.global_gradient_bound D δ hδ ξ hs α k hk0
    (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) NB.C (by positivity) hc0 NB.C_nonneg
    (forwardInitializedPrimary_global_bound M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth) t Y x hY hinv
  have htail := forwardInitializedPrimaryRemainder_physical_fderiv_inv M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY.differentiableAt
  rw [hY.fderiv] at htail
  have htail' : ‖fderiv ℝ (fun y => forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x‖ ≤ |forwardInitializedRemainderDerivativeCost L.R S.H0| *NB.C/k
          := by
    apply htail.trans
    calc
      _ ≤ (|forwardInitializedRemainderDerivativeCost L.R S.H0|/k)*‖D.FInv.field t (Y x)‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hk0.le) (norm_nonneg
            _)
      _ ≤ (|forwardInitializedRemainderDerivativeCost L.R S.H0|/k)*NB.C :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hp := ((((forcing D).vectorField (initialData D δ hδ (α • ξ) hs)).smul
      k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hpd : DifferentiableAt ℝ (fun y => k⁻¹ • vector D (initialData D δ hδ (α • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def,Pi.smul_apply] using hp.comp x hY.differentiableAt
  have hr := ((forwardInitializedPrimaryRemainderField M D hTime δ hδ ξ hs α N hN
      k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hrd : DifferentiableAt ℝ (fun y => forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def] using hr.comp x hY.differentiableAt
  have he : (fun y => forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) =
      (fun y => k⁻¹ • vector D (initialData D δ hδ (α • ξ) hs)
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) +
      (fun y => forwardInitializedPrimaryRemainder M D δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) := by
    funext y
    dsimp only [forwardInitializedPrimaryRemainder,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [he,fderiv_add hpd hrd]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans ((add_le_add hprimary htail').trans_eq (by
    unfold forwardInitializedGlobalShearCost
    ring))

theorem forwardInitializedExactPhysicalVelocity_global_gradient_error
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk))
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity D ξ t (Y x)) (D.normal.field t (Y x))‖ ≤
      forwardInitializedGlobalShearCost L.R S.H0 NB.C/k +
        ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
          (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x‖ := by
  rw [forwardInitializedExactPhysicalVelocity_fderiv M D hTime δ hδ ξ hs α
    Cagree N hN k hk Q t Y x hY.differentiableAt]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans (add_le_add
    (forwardInitializedVelocity_global_gradient_error M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY) le_rfl)

end EulerPacketTerminalDatum
