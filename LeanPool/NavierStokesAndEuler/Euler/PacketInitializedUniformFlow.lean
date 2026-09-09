/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowExplicitBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin

/-! A single polynomial comparison gives the actual canonical correction,
the physical shear and pressure errors, and the three flow fields. Only
the displayed numerical frequency margins are independent extra guards. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketGraphFlowFrequency EulerPacketPrimaryFactorization EulerPacketInverseFlowGevrey
  EulerGevrey EulerGraphPressurePotential EulerPeriodicProfile EulerSobolevGevreyOperators
  EulerLpTranslation.SmoothL2Field
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ W)
  (hprofile : ∀ t, α * L.fullProfile t ≤ W)
  (k : ℝ) (hk : 4 ≤ k) (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (hfrequency : EulerPacketInitializedOutputCost.uniformConstant *
    W ^ EulerPacketInitializedOutputCost.uniformPower ≤ smallPower k)
  (hdelta : delta (expansion k) ≤ k ^ (-(3 : ℝ)))
  (hroot : 16 ≤ k ^ (1 / 4 : ℝ))
  (htrace : max 71 (Real.sqrt (2 / period + 2 * period)) ≤ k ^ (1 / 24 : ℝ))
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hXs : ∀ t, ContDiff ℝ ∞ (X t))
  (hF : ∀ t x, fderiv ℝ (X t) x = D.F.field t x)
  (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)

include hδ1 hα L NB LM hW hprofile hX hlog hfrequency hdelta hroot htrace hXs hF hXY hY hdet

theorem initialized_uniform_flow_and_shear :
    ∃ (hn : 1 ≤ truncation k)
      (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
        (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
          (truncation k) hn k hk))
      (G : EulerPhysicalGraphFlowBounds.Data period D.T),
      Q.delta=delta (expansion k) ∧
      Q.initialRadius=initialRadius
        (initializedRadius LM L NB (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ)
        (L.correctionCoefficients NB period).M (L.correctionCoefficients NB period).Rc ∧
      G.A = Q.liftedPacketCoefficient period
        (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k) ∧
      G.A₁ = Q.liftedPacketDerivativeCoefficient period
        (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k) ∧
      (∀ t z, graphConstraint k D.m₀ (G.A.field t z)=0) ∧
      (∀ (s n : ℕ), n+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
        weightedNorm period 6 n (Q.initialRadius/4) ((Q.fieldTower period).realization s t) ≤
          EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
        weightedNorm period 6 n (Q.initialRadius/4) ((Q.pressureTower period).realization s t) ≤
          EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
        weightedNorm period 6 n (Q.initialRadius/4) ((Q.timeDerivativeTower period).realization s
            t) ≤
          EulerPacketInitializedCost.weightSize W*delta (expansion k)) ∧
      (∀ (t : Icc (0 : ℝ) D.T) (x : Space),
        ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
          Cagree (truncation k) hn k hk Q t (Y t)) x -
          (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
            rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y t x)) (D.normal.field t (Y t x))‖ ≤
          k^(-(1/4 : ℝ)) ∧
        ‖fderiv ℝ (gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
          Cagree (truncation k) hn k hk Q t (Y t))) x -
          (EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
            deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
          rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤ k^(-(1/4 : ℝ))) ∧
      (∀ (ell : ℝ) (hell : 0 < ell), ell ≤ 1 → ∀ t : Icc (0 : ℝ) D.T,
        (G.displacementField k D.m₀ ell hell t).HasJetBound
          (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
        (G.velocityField k D.m₀ ell hell t).HasJetBound
          (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
        (G.accelerationFieldL2 k D.m₀ ell hell t).HasJetBound
          (k^(1/4 : ℝ)) (ell⁻¹*k^(5/4 : ℝ)) ∧
        HasSupBound (G.displacementField k D.m₀ ell hell t).field
          (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
        HasSupBound (G.velocityField k D.m₀ ell hell t).field
          (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ))) := by
  classical
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let L' := initializedJoinedBudget LM L NB BC δ ξ
  let H' := initializedPrimaryBudget LM L NB BC δ ξ
  let N' := initializedNormalBudget LM L NB BC δ ξ
  let M' := initializedMeanBudget LM L NB BC δ ξ
  have guards := initializedRadius_guards LM L NB BC δ ξ
  have wj := guards.1
  have wm := guards.2.1
  have wp := guards.2.2.1
  have hterminal := guards.2.2.2.1
  have hcost := guards.2.2.2.2.1
  have hrc := guards.2.2.2.2.2
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile :=
    Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos
    hTime.symm α hα W hW.one hprofile
  have hW0 := zero_le_one.trans hW.one
  have hcomparison := (EulerPacketInitializedOutputCost.envelope_bound W hW.one).trans hfrequency
  have hold := (EulerPacketInitializedOutputCost.envelope_components W hW0).1.trans hcomparison
  have hout := (EulerPacketInitializedOutputCost.envelope_components W hW0).2.trans hcomparison
  have costs := EulerPacketInitializedOutputCost.actual_output_costs LM L NB BC δ ξ
    W S.H0 hδ hW S.H0_pos.le hH0
  have five := EulerPacketInitializedCost.initialized_five_costs_bound LM L NB BC δ ξ
    W S.H0 hδ hW S.H0_pos.le hH0
  let Q := initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM Cagree W hW hprofile k hk hX hlog hold X hXs hF hdet
  let Cw := EulerPacketInitializedCost.weightSize W
  let ρ0 := Q.initialRadius
  have hρ : 0 < ρ0 := Q.radius_pos
  have hCw : 0 < Cw := EulerPacketInitializedCost.weightSize_pos W hW0
  have hweighted := initializedUniformBudget_weighted M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM Cagree W hW hprofile k hk hX hlog hold X hXs hF hdet
  let C0 := velocity L'.R S.H0 BC.multiplierCost
  let Cn := normal L'.R S.H0 BC.multiplierCost
  let Ch := 6*N'.blockAmplitude *
    (fixedVelocityGradeCost L'.R S.H0 1+fixedVelocityGradeCost L'.R S.H0 2+1)
  let Rf := physicalInputRadius (4*L'.R) (4*L'.R) (ρ0/4)
  let Av := liftedInputConstant period*(C0+Cn)
  let Ev := 2*liftedInputConstant period*Cw
  let At := 2*liftedInputConstant period*(Ch+Cw)
  let Kerr := weightedPhysicalGradientCost D period L.Rc L.C₀ (ρ0/4) Cw
  let Kv := initializedGlobalShearCost L'.R S.H0 N'.C
  let Kp := initializedPressureHessianCost N' L'.R S.H0 L'.Rc L'.C₀
  have hRf_k : Rf ≤ smallPower k := costs.2.1.trans hout
  have hAv_k : Av ≤ smallPower k := costs.2.2.1.trans hout
  have hEv_k : Ev ≤ smallPower k := costs.2.2.2.1.trans hout
  have hAt_k : At ≤ smallPower k := costs.2.2.2.2.1.trans hout
  have hKerr_k : Kerr ≤ smallPower k := costs.2.2.2.2.2.1.trans hout
  have hKv_k : Kv ≤ smallPower k := costs.2.2.2.2.2.2.1.trans hout
  have hKp_k : Kp ≤ smallPower k := costs.2.2.2.2.2.2.2.trans hout
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hn := (truncation_bounds k hk1).1
  have hT_k : D.T ≤ smallPower k := hW.total_time.trans
    (Real.one_le_rpow hk1 (by norm_num [theta]))
  have hRv : 0 ≤ 4*L'.R := by have := L'.radius_bounds.1; linarith
  have hρ' : 0 < ρ0/4 := by positivity
  have hRf : 0 < Rf := (liftedInputRadius_pos (4*L'.R) (ρ0/4) hRv hρ').trans_le (le_max_left _ _)
  have hC0 : 0 ≤ C0 := velocity_nonneg L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_bounds.1) BC.multiplierCost_nonneg
  have hCn : 0 ≤ Cn := normal_nonneg L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_bounds.1) BC.multiplierCost_nonneg
  have hCh : 0 ≤ Ch := by
    have hN := N'.blockAmplitude_nonneg
    have h₁ := fixedVelocityGradeCost_nonneg L'.R S.H0 (zero_le_one.trans L'.radius_bounds.1) 1
    have h₂ := fixedVelocityGradeCost_nonneg L'.R S.H0 (zero_le_one.trans L'.radius_bounds.1) 2
    dsimp [Ch]
    positivity
  have hsmall := liftedAmplitude_small_of_costs Av Ev Rf D.T k hk1 hRf.le D.T_pos.le
    hAv_k hEv_k hRf_k hT_k hdelta hroot
  have hbase : tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 : ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg hk1 (five.1.trans hold)
  let V := initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k
  let Vt := initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k
  have hv := initializedNormalizedField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
  have hnrm := initializedNormalizedField_normal_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
  have hvt := initializedNormalizedDerivativeField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
  have he (n : ℕ) (t : Icc (0 : ℝ) D.T) : weightedNorm period 6 n (ρ0/4)
      ((Q.fieldTower period).realization (n+6) t) ≤ Cw*delta (expansion k) :=
    (hweighted (n+6) n le_rfl t).1
  have hp (n : ℕ) (t : Icc (0 : ℝ) D.T) : weightedNorm period 6 n (ρ0/4)
      ((Q.pressureTower period).realization (n+6) t) ≤ Cw*delta (expansion k) :=
    (hweighted (n+6) n le_rfl t).2.1
  have het (n : ℕ) (t : Icc (0 : ℝ) D.T) : weightedNorm period 6 n (ρ0/4)
      ((Q.timeDerivativeTower period).realization (n+6) t) ≤ Cw :=
    ((hweighted (n+6) n le_rfl t).2.2).trans
      ((mul_le_mul_of_nonneg_left (delta_le_one _) hCw.le).trans_eq (mul_one _))
  have hsize : physicalInputSize period k C0 Cn (Cw*delta (expansion k)) = liftedAmplitude Av Ev k
      := by
    dsimp [physicalInputSize,liftedAmplitude,Av,Ev]
    ring
  let G := Q.physicalFlowData period V Vt rfl
    (initializedNormalizedField_time M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k)
    k (4*L'.R) (4*L'.R) (ρ0/4) C0 Cn Ch (Cw*delta (expansion k)) Cw
    hk1 rfl D.m₀_unit.le hRv hRv hρ' hC0 hCn hCh
    (mul_nonneg hCw.le (delta_pos _).le) hCw.le hv hnrm hvt he het
    (by change physicalInputSize period k C0 Cn (Cw*delta (expansion k))*Rf*D.T ≤ 1/8
        rw [hsize]
        exact hsmall.2)
  have hGB : G.B ≤ 2*k^(-(1/2 : ℝ)) := by
    change physicalInputSize period k C0 Cn (Cw*delta (expansion k)) ≤ _
    rw [hsize]
    exact hsmall.1
  have hflow := data_field_bounds_explicit period D.T G k rfl rfl rfl hk1 htrace hroot
    hGB hRf_k hAt_k hT_k D.m₀ D.m₀_unit
  have hsup := data_sup_bounds_explicit period D.T G k hk1 ((le_max_left _ _).trans htrace)
    hroot hGB hRf_k hT_k D.m₀ D.m₀_unit
  have hXd : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hXs t).differentiable (by simp) x).hasFDerivAt
  have hYd := continuousInverse_hasFDerivAt D X Y hXd hXY hY
  have hcorrection (t : Icc (0 : ℝ) D.T) (x : Space) :=
    Q.physical_gradient_hessian_of_weighted D period X Y hXd hXY hY hdet
      L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg L.frame_bound k (ρ0/4) Cw (delta (expansion k))
      hk1 rfl rfl hρ' hCw.le (delta_pos _).le he hp t x
  have hroot2 : 2 ≤ k^(1/4 : ℝ) := by linarith
  have hvErr := physical_error_le_inverse_quarter Kv Kerr k hk1 hKv_k hKerr_k hdelta hroot2
  have hpErr := physical_error_le_inverse_quarter Kp Kerr k hk1 hKp_k hKerr_k hdelta hroot2
  refine ⟨hn,Q,G,rfl,rfl,rfl,rfl,?_,hweighted,?_,?_⟩
  · intro t z
    change graphConstraint k D.m₀
      (EulerMetricTransport.transportDirection k⁻¹ D.m₀ ((Q.packetCoefficient period V).field t
          z))=0
    exact graphConstraint_transport k k⁻¹ (mul_inv_cancel₀ hk0.ne') D.m₀ _
  · intro t x
    constructor
    · have h := initializedExactPhysicalVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ
        hs α
        L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth
        Cagree (truncation k) hn k hk Q hbase t (Y t) x (hYd t x)
      exact (h.trans (add_le_add le_rfl (hcorrection t x).1)).trans hvErr
    · have h := initializedExactPhysicalPressure_hessian_error M D hTime τ hτ hτT B δ hδ ξ hs α
        Cagree (truncation k) hn k hk Q X Y hXd hXY hY L' H' N' wj M' wm BC hrc hcost
        hδ1 hα hterminal wp S hgrowth hbase hdet t x
      exact (h.trans (add_le_add le_rfl (hcorrection t x).2)).trans hpErr
  · intro ell hell hell1 t
    exact ⟨(hflow ell hell hell1 t).1,(hflow ell hell hell1 t).2.1,
      (hflow ell hell hell1 t).2.2,(hsup ell hell hell1 t).1,(hsup ell hell hell1 t).2⟩

end EulerPacketTerminalDatum
