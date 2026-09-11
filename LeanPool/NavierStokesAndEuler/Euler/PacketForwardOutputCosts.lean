/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardHessianError
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCanonicalRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedFlowData
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketWeightedPhysicalErrors
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! The direct-forward physical output costs obey the same fixed
polynomial envelope, with no bound on extrema of the growth profile. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInitializedOutputCost

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketCorrectionCoefficients
  EulerPacketPhysicalCost EulerPacketFiveCost EulerAllOrderDriftCorrection
      EulerPacketCorrectionOutput

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

theorem forward_output_costs (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketForwardRadius.RadiusPrimitives L LM NB BC δ ξ W)
    (hH0 : 0 ≤ H0) (hHW : H0 ≤ W) :
    let R := forwardInitializedRadius LM L NB BC δ ξ
    let Kc := L.correctionCoefficients NB period
    let ρ := initialRadius R Kc.M Kc.Rc/4
    let Z := EulerPacketInitializedCost.envelope W
    EulerPacketInitializedCost.weightSize W ≤ extraEnvelope Z ∧
    physicalInputRadius (4*R) (4*R) ρ ≤ extraEnvelope Z ∧
    liftedInputConstant period*(velocity R H0 BC.multiplierCost+normal R H0 BC.multiplierCost) ≤
        extraEnvelope Z ∧
    2*liftedInputConstant period*EulerPacketInitializedCost.weightSize W ≤ extraEnvelope Z ∧
    2*liftedInputConstant period*(6*NB.blockAmplitude *
      (fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) +
      EulerPacketInitializedCost.weightSize W) ≤ extraEnvelope Z ∧
    weightedPhysicalGradientCost D period L.Rc L.C₀ ρ (EulerPacketInitializedCost.weightSize W) ≤
        extraEnvelope Z ∧
    forwardInitializedGlobalShearCost R H0 NB.C ≤ extraEnvelope Z ∧
    forwardInitializedPressureHessianCost NB R H0 L.Rc L.C₀ ≤ extraEnvelope Z := by
  let R := forwardInitializedRadius LM L NB BC δ ξ
  let Kc := L.correctionCoefficients NB period
  let ρ := initialRadius R Kc.M Kc.Rc/4
  let Z := EulerPacketInitializedCost.envelope W
  obtain ⟨hZ1,hRZ,hHZ,hCZ,hK⟩ := EulerPacketInitializedCost.forward_actual_parameters
    LM L NB BC δ ξ W H0 hδ H hHW
  change R ≤ Z at hRZ
  change H0 ≤ Z at hHZ
  change BC.multiplierCost ≤ Z at hCZ
  have hZ : 0 ≤ Z := zero_le_one.trans hZ1
  have hWZ := (EulerPacketInitializedCost.envelope_bounds W (zero_le_one.trans H.one)).2.1
  have hR0 : 0 ≤ R := zero_le_one.trans (forwardInitializedLinearBudget LM L NB BC δ ξ).radius_one
  have hC0 := BC.multiplierCost_nonneg
  have hLR := H.forward_radius.trans hWZ
  have hLC := H.forward_frame.trans hWZ
  have hNR := H.normal_radius.trans hWZ
  have hNC := H.normal_amplitude.trans hWZ
  have hNI := H.normal_inverse.trans hWZ
  have hρ0 : 0 < ρ := div_pos (initialRadius_bounds R Kc.M Kc.Rc hR0
    (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1 (by norm_num)
  have hiR : (initialRadius R Kc.M Kc.Rc)⁻¹ ≤ inverseRadiusEnvelope Z := by
    simp only [initialRadius,one_div,inv_inv]
    unfold inverseRadiusEnvelope
    have hm : Kc.M ≤ Z := hK.pressure
    have hr : Kc.Rc ≤ Z := hK.radius
    have hp := mul_le_mul hm hr Kc.Rc_nonneg hZ
    nlinarith only [hp,hRZ,hr]
  have hρinv : ρ⁻¹ ≤ 4*inverseRadiusEnvelope Z := by
    change (initialRadius R Kc.M Kc.Rc/4)⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    gcongr
  have hiZ : 0 ≤ inverseRadiusEnvelope Z := by unfold inverseRadiusEnvelope; positivity
  have hrf : physicalInputRadius (4*R) (4*R) ρ ≤ radiusEnvelope Z := by
    simp only [physicalInputRadius,max_self,liftedInputRadius]
    change 1+coordinateCost*(4*R+ρ⁻¹) ≤ 1+coordinateCost*(4*Z+4*inverseRadiusEnvelope Z)
    have hc : 0 ≤ coordinateCost := norm_nonneg _
    gcongr
  have hv := velocity_mono hR0 hH0 hC0 hRZ hHZ hCZ
  have ha1 := gradeCost_mono R H0 Z hR0 hH0 hRZ hHZ 1
  have ha2 := gradeCost_mono R H0 Z hR0 hH0 hRZ hHZ 2
  have hg1 := fixedVelocityGradeCost_nonneg R H0 hR0 1
  have hg2 := fixedVelocityGradeCost_nonneg R H0 hR0 2
  have hg1Z := hg1.trans ha1
  have hg2Z := hg2.trans ha2
  have hn : normal R H0 BC.multiplierCost ≤ normal Z Z Z := by unfold normal; gcongr
  have hl := zero_le_one.trans (liftedInputConstant_one_le period)
  have hav : liftedInputConstant period*(velocity R H0 BC.multiplierCost+normal R H0
      BC.multiplierCost) ≤
      velocityInputEnvelope Z := by unfold velocityInputEnvelope; gcongr
  have hb := EulerPacketRadiusPolynomial.normal_block_le NB Z hZ hNR hNC hNI
  have hb0 := NB.blockAmplitude_nonneg
  have hbZ := hb0.trans hb
  have ht : 6*NB.blockAmplitude*(fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) ≤
      timeEnvelope Z := by unfold timeEnvelope; gcongr
  have hat : 2*liftedInputConstant period*(6*NB.blockAmplitude *
      (fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) +
      EulerPacketInitializedCost.weightSize W) ≤ timeInputEnvelope Z := by
    unfold timeInputEnvelope EulerPacketInitializedCost.weightSize
    gcongr
  have hphys := physicalFixedCost_one_le D L.Rc L.C₀ ρ⁻¹ Z (4*inverseRadiusEnvelope Z)
    L.Rc_nonneg L.C₀_nonneg (inv_nonneg.mpr hρ0.le) hLR hLC hρinv
  have hphys0 := EulerPacketPhysicalGevrey.physicalFixedCost_nonneg D L.Rc L.C₀ ρ⁻¹ 1
    L.Rc_nonneg L.C₀_nonneg (inv_nonneg.mpr hρ0.le)
  have hphysZ := hphys0.trans hphys
  have he := EulerCylinderSobolevSpace.sobolevEmbeddingConstant_nonneg period 3
  have ho := zero_le_one.trans (output_components period Z hZ).1
  have herr : weightedPhysicalGradientCost D period L.Rc L.C₀ ρ
      (EulerPacketInitializedCost.weightSize W) ≤
      weightedErrorEnvelope Z := by
    calc
      _ = ((1+9*L.C₀)*EulerPacketPhysicalGevrey.physicalFixedCost D L.Rc L.C₀ ρ⁻¹ 1 *
          EulerCylinderSobolevSpace.sobolevEmbeddingConstant period 3)*outputEnvelope period Z := by
        unfold weightedPhysicalGradientCost EulerPacketInitializedCost.weightSize
        ring
      _ ≤ ((1+9*Z)*physicalEnvelope Z (4*inverseRadiusEnvelope Z) *
          EulerCylinderSobolevSpace.sobolevEmbeddingConstant period 3)*outputEnvelope period Z := by
              gcongr
      _ = _ := rfl
  have hshear := shearCost_le R H0 NB.C Z hR0 hH0 NB.C_nonneg hRZ hHZ hNC
  have hhess := hessianCost_le D NB R H0 L.Rc L.C₀ Z hR0 hH0 L.Rc_nonneg L.C₀_nonneg
    hRZ hHZ hLR hLC hNR hNC
  obtain ⟨hwe,hr,ha,hb,ht',he',hs,hp⟩ := extra_components Z hZ
  exact ⟨hwe,hrf.trans hr,hav.trans ha,hb,hat.trans ht',herr.trans he',hshear.trans hs,hhess.trans
      hp⟩

end EulerPacketInitializedOutputCost
