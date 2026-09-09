/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedFlowData
public import LeanPool.NavierStokesAndEuler.Euler.PacketWeightedPhysicalErrors
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowSupBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactGlobalChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedSmallness

@[expose] public section

/-! One constructed correction satisfies the source shear/Hessian
estimates and all physical graph-flow bounds simultaneously. The full
weighted correction, pressure and time-derivative estimates are retained. -/

noncomputable section


namespace EulerPacketTerminalDatum

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
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
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T=D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
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
  (hXY : ∀ t x, X t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hX hF hXY hY hdet

theorem initialized_flow_and_shear_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ0 γ Cw Cv Cp : ℝ, 0 < ρ0 ∧ 0 < γ ∧ 0 < Cw ∧ 0 < Cv ∧ 0 < Cp ∧
      ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period D.T),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=γ ∧
        G.A = Q.liftedPacketCoefficient period
          (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k) ∧
        G.A₁ = Q.liftedPacketDerivativeCoefficient period
          (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α (truncation k) k) ∧
        (∀ t z, graphConstraint k D.m₀ (G.A.field t z)=0) ∧
        (∀ (s n : ℕ), n+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          weightedNorm period 6 n (ρ0/4) ((Q.fieldTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.pressureTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.timeDerivativeTower period).realization s t) ≤
            Cw*delta (expansion k)) ∧
        (∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t)) x -
            (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
              rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y t x)) (D.normal.field t (Y t x))‖ <
                Cv/k ∧
          ‖fderiv ℝ (gradient (initializedExactPhysicalPressure M D hTime τ hτ hτT B δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t))) x -
            (EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
              deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
            rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ < Cp/k) ∧
        (∀ (ell : ℝ) (hell : 0 < ell), ell ≤ 1 → ∀ t : Icc (0 : ℝ) D.T,
          (G.displacementField k D.m₀ ell hell t).HasJetBound
            (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
          (G.velocityField k D.m₀ ell hell t).HasJetBound
            (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
          (G.accelerationFieldL2 k D.m₀ ell hell t).HasJetBound
            (k^ε) (ell⁻¹*k^(1+ε)) ∧
          HasSupBound (G.displacementField k D.m₀ ell hell t).field
            (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε)) ∧
          HasSupBound (G.velocityField k D.m₀ ell hell t).field
            (k^(-(1/2 : ℝ)+ε)) (ell⁻¹*k^(1+ε))) := by
  classical
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  obtain ⟨L',H',N',M',hprofile,wj,wm,wp,hterminal,hcost,hrc⟩ :=
    exists_initialized_budgets LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile := by
    rw [hprofile]
    exact Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  obtain ⟨ρ0,γ,Cw,hρ,hγ,hCw,hQ⟩ := initialized_correction_estimates_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree X hX hF hdet
  let C0 := velocity L'.R S.H0 BC.multiplierCost
  let Cn := normal L'.R S.H0 BC.multiplierCost
  let Ch := 6*N'.blockAmplitude*
    (fixedVelocityGradeCost L'.R S.H0 1+fixedVelocityGradeCost L'.R S.H0 2+1)
  let Rf := physicalInputRadius (4*L'.R) (4*L'.R) (ρ0/4)
  let Av := liftedInputConstant period*(C0+Cn)
  let Ev := 2*liftedInputConstant period*Cw
  let At := 2*liftedInputConstant period*(Ch+Cw)
  let Kerr := weightedPhysicalGradientCost D period L.Rc L.C₀ (ρ0/4) Cw
  let Kv := initializedGlobalShearCost L'.R S.H0 N'.C
  let Kp := initializedPressureHessianCost N' L'.R S.H0 L'.Rc L'.C₀
  let Cv := 1+|Kv|
  let Cp := 1+|Kp|
  have hRv : 0 ≤ 4*L'.R := by have := L'.radius_bounds.1; linarith
  have hρ' : 0 < ρ0/4 := by positivity
  have hRf : 0 < Rf := (liftedInputRadius_pos (4*L'.R) (ρ0/4) hRv hρ').trans_le (le_max_left _ _)
  have hK : 0 ≤ liftedInputConstant period := zero_le_one.trans (liftedInputConstant_one_le period)
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
  have hAv : 0 ≤ Av := mul_nonneg hK (add_nonneg hC0 hCn)
  have hEv : 0 ≤ Ev := by dsimp [Ev]; positivity
  have hEta := inputExponent_pos ε hε
  have hXd : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hX t).differentiable (by simp) x).hasFDerivAt
  have hYd := continuousInverse_hasFDerivAt D X Y hXd hXY hY
  refine ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,by dsimp [Cv]; positivity,by dsimp [Cp]; positivity,?_⟩
  filter_upwards [hQ,
    fixed_costs_eventually ({tailPolynomialConstant L'.R S.H0 BC.termCost} : Finset ℝ),
    liftedAmplitude_small_eventually Av Ev Rf D.T hAv hEv hRf.le D.T_pos.le,
    (_root_.tendsto_rpow_atTop hEta).eventually_ge_atTop Rf,
    (_root_.tendsto_rpow_atTop hEta).eventually_ge_atTop At,
    (_root_.tendsto_rpow_atTop hEta).eventually_ge_atTop D.T,
    correction_with_power_loss_eventually Kerr 1 1,
    data_field_bounds_eventually period D.T ε hε,
    data_sup_bounds_eventually period D.T ε hε]
    with k hQ hscalar hsmall hRf_k hAt_k hT_k hdecay hLp hSup
  obtain ⟨hk,hn,Q,hδQ,hρQ,hγQ,hweighted⟩ := hQ
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hbase : tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 : ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg hk1 (hscalar.2.2.2 _ (by simp))
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
        exact hsmall.2.2.2)
  have hGB : G.B ≤ 2*k^(-(1/2 : ℝ)) := by
    change physicalInputSize period k C0 Cn (Cw*delta (expansion k)) ≤ _
    rw [hsize]
    exact hsmall.2.2.1
  have hflow := hLp G rfl rfl rfl hGB hRf_k hAt_k hT_k D.m₀ D.m₀_unit
  have hsup := hSup G hGB hRf_k hT_k D.m₀ D.m₀_unit
  have hcorrection (t : Icc (0 : ℝ) D.T) (x : Space) :=
    Q.physical_gradient_hessian_of_weighted D period X Y hXd hXY hY hdet
      L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg L.frame_bound k (ρ0/4) Cw (delta (expansion k))
      hk1 rfl rfl hρ' hCw.le (delta_pos _).le he hp t x
  have hdecay' : Kerr*k*delta (expansion k) < k⁻¹ := by
    simpa only [Real.rpow_one,Real.rpow_neg_one] using hdecay
  refine ⟨hk,hn,Q,G,hδQ,hρQ,hγQ,rfl,rfl,?_,hweighted,?_,?_⟩
  · intro t z
    change graphConstraint k D.m₀
      (EulerMetricTransport.transportDirection k⁻¹ D.m₀ ((Q.packetCoefficient period V).field t z))
        = 0
    exact graphConstraint_transport k k⁻¹ (mul_inv_cancel₀ hk0.ne') D.m₀ _
  · intro t x
    constructor
    · have h := initializedExactPhysicalVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ
      hs α
        L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth
        Cagree (truncation k) hn k hk Q hbase t (Y t) x (hYd t x)
      have hc := ((hcorrection t x).1).trans_lt hdecay'
      have ht : Kv/k ≤ |Kv|/k := div_le_div_of_nonneg_right (le_abs_self Kv) hk0.le
      exact h.trans_lt ((add_lt_add_of_le_of_lt ht hc).trans_eq (by dsimp [Cv]; ring))
    · have h := initializedExactPhysicalPressure_hessian_error M D hTime τ hτ hτT B δ hδ ξ hs α
        Cagree (truncation k) hn k hk Q X Y hXd hXY hY L' H' N' wj M' wm BC hrc hcost
        hδ1 hα hterminal wp S hgrowth hbase hdet t x
      have hc := ((hcorrection t x).2).trans_lt hdecay'
      have ht : Kp/k ≤ |Kp|/k := div_le_div_of_nonneg_right (le_abs_self Kp) hk0.le
      exact h.trans_lt ((add_lt_add_of_le_of_lt ht hc).trans_eq (by dsimp [Cp]; ring))
  · intro ell hell hell1 t
    exact ⟨(hflow ell hell hell1 t).1,(hflow ell hell hell1 t).2.1,
      (hflow ell hell hell1 t).2.2,(hsup ell hell hell1 t).1,(hsup ell hell hell1 t).2⟩

end EulerPacketTerminalDatum
