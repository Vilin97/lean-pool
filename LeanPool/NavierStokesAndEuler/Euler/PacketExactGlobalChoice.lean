/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketExactGlobalShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedHessianChoice

@[expose] public section

/-! Both global identities in source (20) for one actual exact packet.
The velocity and canonical scalar pressure have uniform O(1/k) errors. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter Finset InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerSpatialCutoffs EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketTimeProfile EulerPacketCoarseMajorant
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerLiftedGradientSpace
  EulerPacketPrimaryFactorization EulerPacketInverseFlowGevrey EulerGevrey
  EulerGraphPressurePotential EulerPeriodicProfile
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t, ContDiff ℝ ∞ (X t))
  (hF : ∀ t x, fderiv ℝ (X t) x = D.F.field t x)
  (hXY : ∀ t x, X t (Y t x)=x)
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hX hF hXY hY hdet

theorem initialized_exact_global_shear_hessian_eventually :
    ∃ ρ0 G Cv Cp : ℝ, 0 < ρ0 ∧ 0 < G ∧ 0 < Cv ∧ 0 < Cp ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          (‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t)) x -
            (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
              rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y t x)) (D.normal.field t (Y t x))‖ <
                Cv/k) ∧
          (‖fderiv ℝ (gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t))) x -
            (EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
              deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
            rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ < Cp/k) := by
  classical
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  obtain ⟨L',H',N',M',hprofile,wj,wm,wp,hterminal,hcost,hrc⟩ :=
    exists_initialized_budgets LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile := by
    rw [hprofile]
    exact Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  let Kv := initializedGlobalShearCost L'.R S.H0 N'.C
  let Kp := initializedPressureHessianCost N' L'.R S.H0 L'.Rc L'.C₀
  let Cv := 1+|Kv|
  let Cp := 1+|Kp|
  have hCv : 0 < Cv := by dsimp only [Cv]; positivity
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  obtain ⟨ρ0,G,hρ,hG,hQ⟩ := initialized_correction_gradient_hessian_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree X Y hX hF hXY hY hdet
    L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg L.frame_bound 1
  have hXd : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hX t).differentiable (by simp) x).hasFDerivAt
  have hYd := continuousInverse_hasFDerivAt D X Y hXd hXY hY
  refine ⟨ρ0,G,Cv,Cp,hρ,hG,hCv,hCp,?_⟩
  filter_upwards [hQ,fixed_costs_eventually ({tailPolynomialConstant L'.R S.H0 BC.termCost} :
    Finset ℝ)]
    with k hQ hscalar
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hcorrection⟩ := hQ
  have hk0 : 0 < k := by linarith
  have hbase : tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 : ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg (by linarith)
      (hscalar.2.2.2 _ (by simp))
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro t x
  constructor
  · have he := initializedExactPhysicalVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ
    hs α
      L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth
      Cagree (truncation k) hn k hk Q hbase t (Y t) x (hYd t x)
    have hc : ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y t y)
        (Q.pointField period t (cylinderGraph period k D.m₀ (Y t y)))) x‖ < k⁻¹ := by
      simpa only [Real.rpow_neg_one] using (hcorrection t x).1
    have ht : Kv/k ≤ |Kv|/k := div_le_div_of_nonneg_right (le_abs_self Kv) hk0.le
    exact he.trans_lt ((add_lt_add_of_le_of_lt ht hc).trans_eq (by dsimp only [Cv]; ring))
  · have he := initializedExactPhysicalPressure_hessian_error M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree (truncation k) hn k hk Q X Y hXd hXY hY L' H' N' wj M' wm BC hrc hcost
      hδ1 hα hterminal wp S hgrowth hbase hdet t x
    have hc : ‖fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x‖ < k⁻¹ := by
      simpa only [Real.rpow_neg_one] using (hcorrection t x).2
    have ht : Kp/k ≤ |Kp|/k := div_le_div_of_nonneg_right (le_abs_self Kp) hk0.le
    exact he.trans_lt ((add_lt_add_of_le_of_lt ht hc).trans_eq (by dsimp only [Cp]; ring))

end EulerPacketTerminalDatum
