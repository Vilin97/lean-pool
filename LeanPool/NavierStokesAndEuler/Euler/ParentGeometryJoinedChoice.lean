/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedState
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniversalFrequency
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSourceExponent
import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildSourceBound
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedResidualEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteApproximationBounds

/-! Actual activation geometry and one uniform frequency comparison
construct the joined packet, its physical state, and both source errors. -/

section

/-! The uniform source comparison gives the actual child label estimate
at exponent 10(q+2), retaining the same exact correction and its errors. -/

section

/-! The actual derivative of the initialized normalized approximation
has a source-dependent Gevrey bound uniform in the truncation frequency.
The time derivative of the inverse deformation is included explicitly. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant  EulerParameterWordGevrey
  EulerPacketCoordinates EulerPacketCorrectionCoefficients
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized normalized derivative field, constructed using `coordinateTimeField`. -/
def initializedNormalizedDerivativeField (N : ℕ) (k : ℝ) :=
  coordinateTimeField D
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹) k

theorem initializedNormalizedField_time (N : ℕ) (k : ℝ) :
    TimeDerivative D.T_pos.le
      (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
      (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k) := by
  have h := coordinateField_time D
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹) k
    (initializedVelocityField_time M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
  intro t
  change HasDerivWithinAt
    (EulerVolterraConvolution.extendPath D.T D.T_pos.le
      (initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).path) _ _ _
  rw [initializedNormalizedField_path_eq M D hTime τ hτ hτT B δ hδ ξ hs α N k]
  exact h t

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

theorem initializedNormalizedDerivativeField_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k).WordBound
      6 (4*L.R) (6*NB.blockAmplitude *
        (fixedVelocityGradeCost L.R S.H0 1+fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let G : ∀ i, i ≤ N → ProfileRegularity period M.T M.T_pos.le D.support
      (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α i) :=
    fun i _ => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have hzero : initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 0 = 0 := profiles_zero _ _
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase L.R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase L.R S.H0 BC.termCost N) hk hbase
  have hv := (ProfileRegularity.velocity_bound M.T_pos G hG L.radius_bounds.1 hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have ht := (ProfileRegularity.velocityDerivative_bound M.T_pos G hG L.radius_bounds.1 hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have hKR : sobolevCoefficientRadius (Fin 4) NB.coefficientRadius ≤ 4*L.R :=
    NB.radius.trans (by have := L.radius_bounds.1; linarith)
  have hlow1 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_bounds.1) 1
  have hlow2 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_bounds.1) 2
  have ha := (inverseTimeCoefficient D).normalized_approximation_bound
    (initializedVelocityField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).2.1) hv
    (by have := L.radius_bounds.1; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hb := (inverseCoefficient D).normalized_approximation_bound
    (initializedVelocityDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).1) ht
    (by have := L.radius_bounds.1; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hh := (ha.add hb).ofRawEq
    (initializedNormalizedDerivativeField M D hTime τ hτ hτT B δ hδ ξ hs α N k)
    (fun _ _ _ => smul_add _ _ _)
  convert hh using 1
  dsimp [EulerTransversePacketJoin.NormalBudget.blockAmplitude]
  ring

end EulerPacketTerminalDatum

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
   EulerPacketPrimaryFactorization EulerPacketInverseFlowGevrey
  EulerGevrey EulerGraphPressurePotential EulerPeriodicProfile EulerSobolevGevreyOperators
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanClassicalWordBounds
  EulerPacketParentLabelBounds EulerSobolevSourceExponent EulerSmoothBanachFlow
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
  (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (Dp Vp Wp : Icc (0 : ℝ) D.T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hDp : ∀ t, HasLabelBound K (Dp t))
  (hVp : ∀ t, HasLabelBound K (Vp t))
  (hWp : ∀ t, HasLabelBound K (Wp t))

include hδ1 hα L NB LM hW hprofile hX hlog hfrequency hdelta hroot htrace hXs hF hXY hY hdet
  hell1 hK hDp hVp hWp

theorem initialized_uniform_child_label_bounds (q : ℕ)
    (hk69 : 69 ≤ k) (hKk : K ≤ k)
    (hbig : 2 + 45 * embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hinv : ell⁻¹ ≤ k ^ (3 / 4 : ℝ)) :
    ∃ (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period D.T)
        (E : Icc (0 : ℝ) D.T → EulerChildParticleFieldBounds.Data),
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
              t) ≤ EulerPacketInitializedCost.weightSize W*delta (expansion k)) ∧
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
        (∀ t, (E t).parentDisplacement=Dp t ∧ (E t).parentVelocity=Vp t ∧ (E
            t).parentAcceleration=Wp t ∧
          (E t).displacement=G.displacementField k D.m₀ ell hell t ∧
          (E t).velocity=G.velocityField k D.m₀ ell hell t ∧
          (E t).acceleration=G.accelerationFieldL2 k D.m₀ ell hell t ∧
          (E t).inner=(flowData D.T G.time_nonneg (physicalCoefficient k D.m₀ D.T G.A ell)).forward
              t) ∧
        (∀ t n,
          classicalBlockSize direction q (E t).childDisplacement.toLp (E
              t).childDisplacement.translation_contDiff n +
          classicalBlockSize direction q (E t).childVelocity.toLp (E
              t).childVelocity.translation_contDiff n +
          classicalBlockSize direction q (E t).childAcceleration.toLp (E
              t).childAcceleration.translation_contDiff n ≤
            (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2) ∧
        (∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖(G.displacementField k D.m₀ ell hell t).field x‖ ≤ k^(-(1/4 : ℝ))) := by
  obtain ⟨hn,Q,G,hδQ,hρQ,hA,hA1,hgraph,hweighted,herror,hfields⟩ :=
    initialized_uniform_flow_and_shear M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
      L NB LM Cagree W hW hprofile k hk hX hlog hfrequency hdelta hroot htrace
      X Y hXs hF hXY hY hdet
  have hcoarse (t : Icc (0 : ℝ) D.T) :=
    EulerPhysicalChildFields.coarsen_graph_bounds k ell (by linarith) hell hinv
      (G.displacementField k D.m₀ ell hell t) (G.velocityField k D.m₀ ell hell t)
      (G.accelerationFieldL2 k D.m₀ ell hell t)
      (by convert (hfields ell hell hell1 t).1 using 1 <;> norm_num)
      (by convert (hfields ell hell hell1 t).2.1 using 1 <;> norm_num)
      (by convert (hfields ell hell hell1 t).2.2.1 using 1; norm_num)
      (by convert (hfields ell hell hell1 t).2.2.2.1 using 1 <;> norm_num)
      (by convert (hfields ell hell hell1 t).2.2.2.2 using 1 <;> norm_num)
  obtain ⟨E,hmatch,hlabel⟩ := EulerPhysicalChildFields.exists_source_child_fields
    G k D.m₀ hgraph ell hell Dp Vp Wp K hK hDp hVp hWp q hk69 hKk hbig hcost hcoarse
  refine ⟨hn,Q,G,E,hδQ,hρQ,hA,hA1,hgraph,hweighted,herror,hmatch,hlabel,?_⟩
  intro t x
  simpa only [norm_iteratedFDeriv_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,
    one_pow,mul_one] using (hfields ell hell hell1 t).2.2.2.1 0 x

end EulerPacketTerminalDatum

end
end

end

section

/-! The positive-history packet at the fixed frequency constructs the
actual next parent, with the same errors and the k^80 label bound. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketSourceFrequency EulerAllOrderDriftCorrection EulerGraphInvariantFlow
  EulerPacketPrimaryFactorization EulerPeriodicProfile EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
  (J : JoinedInputs (A.meanData H) (A.transverseData m hm R S hS) τ hτ hτT
    (A.historyOn H m hm R S hS τ hτ hτT))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives J.mean J.linear J.normal
    (joinedCoefficientBudget period (A.meanData H) (A.transverseData m hm R S hS)
      rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) J.normal) δ ξ W)
  (hprofile : ∀ t, α * J.linear.fullProfile t ≤ W)
  (k : ℝ) (hk : UniversalFrequency k)
  (hfrequency : EulerPacketInitializedOutputCost.uniformConstant *
    W ^ EulerPacketInitializedOutputCost.uniformPower ≤ smallPower k)
  (hKk : L.K ≤ k) (hinv : A.ell⁻¹ ≤ k ^ (3 / 4 : ℝ))
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

include hδ1 hα J hW hprofile hfrequency hKk hinv in
theorem joined_uniform_child :
    ∃ (hn : 1 ≤ truncation k)
      (Q : Budget period A.T_pos
        (initializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS)
          rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
          (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk.four))
      (G : EulerPhysicalGraphFlowBounds.Data period A.T)
      (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0),
      G.A=Q.liftedPacketCoefficient period
        (initializedNormalizedField (A.meanData H) (A.transverseData m hm R S hS)
          rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α (truncation k) k) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖fderiv ℝ (initializedExactPhysicalVelocity (A.meanData H)
          (A.transverseData m hm R S hS) rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
          δ hδ ξ hs α (A.sourceAgreement m hm R S hS H)
          (truncation k) hn k hk.four Q t (I.normalized t)) x -
          (α*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
            rankOne ℝ (canonicalVelocity τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
              ξ hs t (I.normalized t x))
              ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 : ℝ)) ∧
        ‖fderiv ℝ (gradient (initializedExactPhysicalPressure (A.meanData H)
          (A.transverseData m hm R S hS) rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
          δ hδ ξ hs α (A.sourceAgreement m hm R S hS H)
          (truncation k) hn k hk.four Q t (I.normalized t))) x -
          (EulerPacketPrimaryPressure.coefficient τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
            ξ hs α t (I.normalized t x)*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
              rankOne ℝ ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))
                ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 :
                    ℝ))) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖(G.displacementField k m A.ell A.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))) ∧
      ∃ LC : LabelData (A.child G k m hgraph nextEll hnext hnext1), LC.K=k^80 := by
  obtain ⟨hn,Q,G,E,_,_,hG,_,hgraph,_,herror,hmatch,hlabel,hdisplacement⟩ :=
    initialized_uniform_child_label_bounds (A.meanData H) (A.transverseData m hm R S hS) rfl
      τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
      δ hδ hδ1 ξ hs α hα J.linear J.normal (JoinedInputs.mean (U := U) J)
      (A.sourceAgreement m hm R S hS H) W hW hprofile k hk.four hk.expansion_bound hk.log_bound
      hfrequency hk.delta_bound hk.root_bound hk.trace_bound
      (fun t x => A.packetPosition (t,x)) I.normalized
      A.packetPosition_contDiff (fun t x => (A.packetPosition_spatial t x).fderiv)
      I.normalized_right I.normalized_continuous A.frame_det
      A.ell A.ell_pos A.ell_le_one L.displacement L.velocity L.acceleration L.K L.K_one
      L.displacement_bound L.velocity_bound L.acceleration_bound 6
      hk.child_bound hKk hk.embedding_bound hk.derivative_bound hinv
  let LC := L.child G k m hgraph nextEll hnext hnext1 E
    (fun t => (hmatch t).1) (fun t => (hmatch t).2.1) (fun t => (hmatch t).2.2.1)
    (fun t => (hmatch t).2.2.2.1) (fun t => (hmatch t).2.2.2.2.1)
    (fun t => (hmatch t).2.2.2.2.2.1)
    (k^80) (one_le_pow₀ hk.one_le) hlabel
  exact ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,rfl⟩

end EulerParentPacketFrames.LabelData

end
end

end

section

/-! Initial-data convergence for the very same correction witnesses used
in the exact packets. No correction is chosen again for this conclusion. -/

@[expose] public section

noncomputable section

namespace EulerPacketInitial

open Set Filter Finset EulerSmoothLimit EulerPhysicalL2Scaling EulerAllOrderDriftCorrection
  EulerPacketTerminalDatum EulerPacketSourceFrequency EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketUniformFrequencyScales EulerLpTranslation
open scoped Topology

namespace Input

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)

/-- Correction budget type used in packet initial exact limit. -/
abbrev correctionBudget (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) :=
  Budget period A.data.T_pos
    (initializedCorrectionData A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
        A.history
      A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation k) hn k
          hk)

/-- Exact initial, constructed using `scale`. -/
def exactInitial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : A.correctionBudget k hk hn) :
    Space → Space :=
  scale A.parent.ell
    (initializedExactPhysicalVelocity A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement
      (truncation k) hn k hk Q ⟨0,le_rfl,A.data.T_pos.le⟩ id)

theorem exactInitial_eq (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : A.correctionBudget k hk
    hn) :
    A.exactInitial k hk hn Q=A.high k+A.mean k := A.sameQ_initial k hk hn Q

end Input

variable {U : ℕ → Type} [∀ n, NormedAddCommGroup (U n)] [∀ n, InnerProductSpace ℝ (U n)]
  [∀ n, CompleteSpace (U n)] (A : ∀ n, Input (U n)) (J : ℕ) (X : ℝ)
  (hk : ∀ n, 4 ≤ frequency J X n) (hn : ∀ n, 1 ≤ truncation (frequency J X n))
  (Q : ∀ n, (A n).correctionBudget (frequency J X n) (hk n) (hn n))

/-- Exact partial, defined pointwise by `∑ n ∈ range N, (A n).exactInitial (frequency J X n) (hk
n) (hn n) (Q n) x`. -/
def exactPartial (N : ℕ) : Space → Space :=
  fun x => ∑ n ∈ range N, (A n).exactInitial (frequency J X n) (hk n) (hn n) (Q n) x

theorem exactPartial_eq (N : ℕ) : exactPartial A J X hk hn Q N=initialPartial A J X N := by
  funext x
  unfold exactPartial initialPartial
  apply sum_congr rfl
  intro n _
  rw [Input.exactInitial_eq]
  rfl

variable (hJ : 2 ≤ J) (C c : ℝ) (hC : 0 < C) (hc : 0 ≤ c)
  (p q : ℕ) (hX : 1 ≤ X)
  (hparameter : ∀ n, (A n).parameterSize ≤ parameterEnvelope J C c p q X n)
  (hscale : ∀ n, (A n).parent.ell = supportScale J X n)
  (hσ : ∀ n, (A n).frame.sigma * scaleSequence J X n ≤ 2)
  (hfrequency : ∀ n, (A n).frequencyGuard (frequency J X n))

local notation "V" => initialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency

theorem selectedQ_initial_Hm (s : ℕ) :
    Tendsto (fun N => derivativeSum s (exactPartial A J X hk hn Q N-(V).field)) atTop (𝓝 0) := by
  simpa only [exactPartial_eq] using
    initialLimit_Hm A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency s

theorem selectedQ_fullInitial_Hm (base : SmoothL2Field Space) (s : ℕ) :
    Tendsto (fun N => derivativeSum s ((base.field+exactPartial A J X hk hn Q N) -
      (fullInitialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base).field))
      atTop (𝓝 0) := by
  simpa only [exactPartial_eq] using
    fullInitialLimit_Hm A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base s

end EulerPacketInitial

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketTerminalDatum EulerPacketSourceFrequency EulerPacketUniformSource
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketPhysicalLowBounds

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section ConstructorInjectivity

attribute [local irreducible] Parent.child

/-- Geometry joined choice data, collecting `hn`, `Q`, `flow`, `graph`, `coefficient`, `labels`
and their compatibility conditions. -/
structure GeometryJoinedChoice where
  hn : 1 ≤ truncation k
  /-- Scale parameter of `GeometryJoinedChoice`, of type `I.correctionBudget k hk.four hn`. -/
  Q : I.correctionBudget k hk.four hn
  /-- Flow of `GeometryJoinedChoice`, of type `EulerPhysicalGraphFlowBounds.Data period
  I.parent.T`. -/
  flow : EulerPhysicalGraphFlowBounds.Data period I.parent.T
  graph : ∀ t q, graphConstraint k I.normal (flow.A.field t q)=0
  coefficient : flow.A=Q.liftedPacketCoefficient period
    (initializedNormalizedField I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
        I.history
      I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) k)
  /-- Label type of `GeometryJoinedChoice`, of type `LabelData (I.parent.child flow k I.normal
  graph nextEll hnext hnext1)`. -/
  labels : LabelData (I.parent.child flow k I.normal graph nextEll hnext hnext1)
  label_constant : labels.K=k^80
  displacement_bound : ∀ (t : Icc (0 : ℝ) I.parent.T) (x : Space),
    ‖(flow.displacementField k I.normal I.parent.ell I.parent.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))
  errors : S.evolution.SourceErrors I.normal I.normal_unit I.coordinates I.support
      I.support_compact Q
    (initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) hn k hk.four)
    k I.geometry I.halfBall I.cutoff_support (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ)))

end ConstructorInjectivity

theorem exists_geometryJoinedChoice
    (hterminal : I.terminal = I.geometry.terminal)
    (hfrequency : I.frequencyGuard k) (hK : I.label.K ≤ k)
    (hell : I.parent.ell⁻¹ ≤ k ^ (3 / 4 : ℝ)) :
    Nonempty (GeometryJoinedChoice I S k hk nextEll hnext hnext1) := by
  let J := I.label.geometryInputs I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.historyTime I.history_pos I.history_lt I.frame I.geometry
        I.halfBall
    I.historyTime⁻¹ I.parent.T⁻¹ (I.history_lt.le.trans I.total_le_one) le_rfl I.total_le_one le_rfl
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
        I.neighborhood_bound
  have hp := I.label.geometry_uniform_primitives I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.historyTime I.history_pos I.history_lt I.frame I.geometry
        I.halfBall
    I.historyTime⁻¹ I.parent.T⁻¹ (I.history_lt.le.trans I.total_le_one) le_rfl I.total_le_one le_rfl
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
        I.neighborhood_bound
    I.terminal I.delta_pos I.delta_le_one
  obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := I.label.joined_uniform_child
      S.evolution.inverse I.low
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    I.historyTime I.history_pos I.history_lt J I.geometry.δ I.delta_pos I.delta_le_one
    I.terminal I.cutoff_support I.alpha I.alpha_pos (profileEnvelope I.parameterSize) hp.1 hp.2.1
    k hk (hp.2.2.trans hfrequency) hK hell nextEll hnext hnext1
  refine ⟨⟨hn,Q,G,hgraph,hG,LC,hLC,hdisplacement,?_⟩⟩
  intro t x
  constructor
  · simp only [← hterminal]
    exact (herror t x).1
  · erw [pressureTerm_eq_coefficient]
    simp only [← hterminal]
    exact (herror t x).2

namespace GeometryJoinedChoice

variable (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

/-- Parent, given by `I.parent.child F.flow k I.normal F.graph nextEll hnext hnext1`. -/
def parent : Parent := I.parent.child F.flow k I.normal F.graph nextEll hnext hnext1

/-- State, constructed using `S.joinedChild`. -/
def state (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) : SmoothState F.parent :=
  S.joinedChild I.low I.normal I.normal_unit I.coordinates I.support I.support_compact hSym
    I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) F.hn k hk.four
    I.historyTime I.history_pos I.history_lt F.Q F.flow F.coefficient F.graph nextEll hnext hnext1
        F.labels

theorem state_label_constant (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) :
    (state I S k hk nextEll hnext hnext1 F hSym).labels.K=k^80 := F.label_constant

theorem initial_trace : I.exactInitial k hk.four F.hn F.Q=I.high k+I.mean k :=
  I.exactInitial_eq k hk.four F.hn F.Q

end GeometryJoinedChoice
end EulerParentPacketFrames
