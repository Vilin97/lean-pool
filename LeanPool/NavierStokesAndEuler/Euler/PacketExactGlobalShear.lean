/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGlobalShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError

@[expose] public section

/-! The actual finite and exact packets have the source shear at every
physical point. The slow primary derivative and finite tail contribute
only a fixed source constant divided by the frequency. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderSobolevSpace EulerCylinderCoordinates
  EulerPacketPrimaryShear EulerPacketPrimaryFactorization EulerTransversePacketPrimary
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPeriodicProfile EulerGevrey
open scoped ContDiff

def initializedGlobalShearCost (R H0 C : ℝ) : ℝ :=
  ‖coordinateEquiv.symm.toContinuousLinearMap‖*
      (sobolevEmbeddingConstant period 3*fixedVelocityGradeCost R H0 1*(4*R))*C +
    |initializedRemainderDerivativeCost R H0| *C

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
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
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPrimary_global_bound :
    (vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  have hG := initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1 le_rfl
  have hb := hG.high.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_bounds.1) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_bounds.1) S.H0_pos.le
  exact (hc.changeTime hTime).of_raw_eq _
    (fun _ _ _ => by rw [initializedProfiles_one_high])

theorem initializedVelocity_global_gradient_error (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  have hc0 := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1
  have hinv : ‖D.FInv.field t (Y x)‖ ≤ NB.C := by
    simpa [majorant] using NB.inverse_bound 0 t (Y x)
  have hprimary := scaled_terminal_global_gradient_bound τ hτ hτT B δ hδ ξ hs α k hk0
    (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) NB.C (by positivity) hc0 NB.C_nonneg
    (initializedPrimary_global_bound M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth) t Y x hY hinv
  have htail := initializedPrimaryRemainder_physical_fderiv_inv M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY.differentiableAt
  rw [hY.fderiv] at htail
  have htail' : ‖fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x‖ ≤ |initializedRemainderDerivativeCost L.R S.H0| *NB.C/k := by
    apply htail.trans
    calc
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*‖D.FInv.field t (Y x)‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hk0.le) (norm_nonneg
          _)
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*NB.C :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hp := (((vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).smul k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hpd : DifferentiableAt ℝ (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def,Pi.smul_apply] using hp.comp x hY.differentiableAt
  have hr := ((initializedPrimaryRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α N hN
    k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hrd : DifferentiableAt ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N
    k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def] using hr.comp x hY.differentiableAt
  have he : (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) =
      (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) +
      (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) := by
    funext y
    dsimp only [initializedPrimaryRemainder,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [he,fderiv_add hpd hrd]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans ((add_le_add hprimary htail').trans_eq (by
    unfold initializedGlobalShearCost
    ring))

theorem initializedExactPhysicalVelocity_global_gradient_error
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k +
        ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
          (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x‖ := by
  rw [initializedExactPhysicalVelocity_fderiv M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q t Y x hY.differentiableAt]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans (add_le_add
    (initializedVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY) le_rfl)

end EulerPacketTerminalDatum
