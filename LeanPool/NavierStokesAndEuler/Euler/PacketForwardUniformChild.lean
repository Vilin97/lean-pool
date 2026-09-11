/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCanonicalRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSourceExponent
import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildSourceBound
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactPressureError
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardOutputCosts
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowExplicitBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedResidualEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteApproximationBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixNormalization

/-! The uniform source comparison gives the actual child label estimate
at exponent 10(q+2), retaining the same exact correction and its errors. -/

section

/-! The actual derivative of the zero-history initialized normalized approximation
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
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Forward initialized normalized derivative field, constructed using `coordinateTimeField`. -/
def forwardInitializedNormalizedDerivativeField (N : ℕ) (k : ℝ) :=
  coordinateTimeField D
    (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
    (forwardInitializedVelocityDerivativeField M D hTime δ hδ ξ hs α N k⁻¹) k

theorem forwardInitializedNormalizedField_time (N : ℕ) (k : ℝ) :
    TimeDerivative D.T_pos.le
      (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k)
      (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α N k) := by
  have h := coordinateField_time D
    (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
    (forwardInitializedVelocityDerivativeField M D hTime δ hδ ξ hs α N k⁻¹) k
    (forwardInitializedVelocityField_time M D hTime δ hδ ξ hs α N k⁻¹)
  intro t
  change HasDerivWithinAt
    (EulerVolterraConvolution.extendPath D.T D.T_pos.le
      (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k).path) _ _ _
  rw [forwardInitializedNormalizedField_path_eq M D hTime δ hδ ξ hs α N k]
  exact h t

variable
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

theorem forwardInitializedNormalizedDerivativeField_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α N k).WordBound
      6 (4*L.R) (6*NB.blockAmplitude *
        (fixedVelocityGradeCost L.R S.H0 1+fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let G : ∀ i, i ≤ N → ProfileRegularity period M.T M.T_pos.le D.support
      (forwardInitializedProfiles M D δ hδ ξ hs α i) :=
    fun i _ => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have hzero : forwardInitializedProfiles M D δ hδ ξ hs α 0 = 0 := profiles_zero _ _
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase L.R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase L.R S.H0 BC.termCost N) hk hbase
  have hv := (ProfileRegularity.velocity_bound M.T_pos G hG L.radius_one hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have ht := (ProfileRegularity.velocityDerivative_bound M.T_pos G hG L.radius_one hzero hN
    BC.termCost BC.one_le_termCost k⁻¹ (inv_nonneg.mpr hk0) hsmall).changeTime hTime
  have hKR : sobolevCoefficientRadius (Fin 4) NB.coefficientRadius ≤ 4*L.R :=
    NB.radius.trans (by have := L.radius_one; linarith)
  have hlow1 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_one) 1
  have hlow2 := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_one) 2
  have ha := (inverseTimeCoefficient D).normalized_approximation_bound
    (forwardInitializedVelocityField M D hTime δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).2.1) hv
    (by have := L.radius_one; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hb := (inverseCoefficient D).normalized_approximation_bound
    (forwardInitializedVelocityDerivativeField M D hTime δ hδ ξ hs α N k⁻¹)
    NB.coefficientRadius NB.coefficientAmplitude NB.coefficient_bounds.1 NB.coefficient_bounds.2.1
    (fun n a => (NB.coefficient_bounds.2.2 n a).1) ht
    (by have := L.radius_one; linarith) hKR hk
    (tailBase_nonneg L.R S.H0 BC.termCost BC.termCost_nonneg N) hbase hlow1 hlow2
  have hh := (ha.add hb).ofRawEq
    (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α N k)
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
  EulerPacketGraphFlowFrequency EulerPacketForwardFactorization EulerPacketInverseFlowGevrey
  EulerGevrey EulerGraphPressurePotential EulerPeriodicProfile EulerSobolevGevreyOperators
  EulerLpTranslation.SmoothL2Field
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (W : ℝ)
  (hW : EulerPacketForwardRadius.RadiusPrimitives L LM NB
    (forwardCoefficientBudget period M D hTime NB) δ ξ W)
  (hprofile : ∀ t, α * L.g t ≤ W)
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

theorem forward_uniform_flow_and_shear :
    ∃ (hn : 1 ≤ truncation k)
      (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
        (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
          (truncation k) hn k hk))
      (G : EulerPhysicalGraphFlowBounds.Data period D.T),
      Q.delta=delta (expansion k) ∧
      Q.initialRadius=initialRadius
        (forwardInitializedRadius LM L NB (forwardCoefficientBudget period M D hTime NB) δ ξ)
        (L.correctionCoefficients NB period).M (L.correctionCoefficients NB period).Rc ∧
      G.A = Q.liftedPacketCoefficient period
        (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α (truncation k) k) ∧
      G.A₁ = Q.liftedPacketDerivativeCoefficient period
        (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α (truncation k) k) ∧
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
        ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
          Cagree (truncation k) hn k hk Q t (Y t)) x -
          (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
            rankOne ℝ (canonicalVelocity D ξ t (Y t x)) (D.normal.field t (Y t x))‖ ≤
          k^(-(1/4 : ℝ)) ∧
        ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
          Cagree (truncation k) hn k hk Q t (Y t))) x -
          (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
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
  let BC := forwardCoefficientBudget period M D hTime NB
  let L' := forwardInitializedLinearBudget LM L NB BC δ ξ
  let N' := forwardInitializedNormalBudget LM L NB BC δ ξ
  let M' := forwardInitializedMeanBudget LM L NB BC δ ξ
  have guards := forwardInitializedRadius_guards LM L NB BC δ ξ
  have wj := guards.1
  have wm := guards.2.1
  have wp := guards.2.2.1
  have hterminal := guards.2.2.2.1
  have hcost := guards.2.2.2.2.1
  have hrc := guards.2.2.2.2.2
  let S := Scales.ofTimeProfile L.g L.positive hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.g :=
    Scales.ofTimeProfile_growth L.g L.positive hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.g L.positive
    hTime.symm α hα W hW.one hprofile
  have hW0 := zero_le_one.trans hW.one
  have hcomparison := (EulerPacketInitializedOutputCost.envelope_bound W hW.one).trans hfrequency
  have hold := (EulerPacketInitializedOutputCost.envelope_components W hW0).1.trans hcomparison
  have hout := (EulerPacketInitializedOutputCost.envelope_components W hW0).2.trans hcomparison
  have costs := EulerPacketInitializedOutputCost.forward_output_costs LM L NB BC δ ξ
    W S.H0 hδ hW S.H0_pos.le hH0
  have five := EulerPacketInitializedCost.forward_five_costs_bound LM L NB BC δ ξ
    W S.H0 hδ hW S.H0_pos.le hH0
  let Q := forwardUniformBudget M D hTime δ hδ hδ1 ξ hs α hα
    L NB LM Cagree W hW hprofile k hk hX hlog hold X hXs hF hdet
  let Cw := EulerPacketInitializedCost.weightSize W
  let ρ0 := Q.initialRadius
  have hρ : 0 < ρ0 := Q.radius_pos
  have hCw : 0 < Cw := EulerPacketInitializedCost.weightSize_pos W hW0
  have hweighted := forwardUniformBudget_weighted M D hTime δ hδ hδ1 ξ hs α hα
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
  let Kv := forwardInitializedGlobalShearCost L'.R S.H0 N'.C
  let Kp := forwardInitializedPressureHessianCost N' L'.R S.H0 L'.Rc L'.C₀
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
  have hRv : 0 ≤ 4*L'.R := by have := L'.radius_one; linarith
  have hρ' : 0 < ρ0/4 := by positivity
  have hRf : 0 < Rf := (liftedInputRadius_pos (4*L'.R) (ρ0/4) hRv hρ').trans_le (le_max_left _ _)
  have hC0 : 0 ≤ C0 := velocity_nonneg L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_one) BC.multiplierCost_nonneg
  have hCn : 0 ≤ Cn := normal_nonneg L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_one) BC.multiplierCost_nonneg
  have hCh : 0 ≤ Ch := by
    have hN := N'.blockAmplitude_nonneg
    have h₁ := fixedVelocityGradeCost_nonneg L'.R S.H0 (zero_le_one.trans L'.radius_one) 1
    have h₂ := fixedVelocityGradeCost_nonneg L'.R S.H0 (zero_le_one.trans L'.radius_one) 2
    dsimp [Ch]
    positivity
  have hsmall := liftedAmplitude_small_of_costs Av Ev Rf D.T k hk1 hRf.le D.T_pos.le
    hAv_k hEv_k hRf_k hT_k hdelta hroot
  have hbase : tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 : ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg hk1 (five.1.trans hold)
  let V := forwardInitializedNormalizedField M D hTime δ hδ ξ hs α (truncation k) k
  let Vt := forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α (truncation k) k
  have hv := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
  have hnrm := forwardInitializedNormalizedField_normal_bound M D hTime δ hδ ξ hs α
    L' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
  have hvt := forwardInitializedNormalizedDerivativeField_bound M D hTime δ hδ ξ hs α
    L' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth (truncation k) hn k hk hbase
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
    (forwardInitializedNormalizedField_time M D hTime δ hδ ξ hs α (truncation k) k)
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
    · have h := forwardInitializedExactPhysicalVelocity_global_gradient_error M D hTime δ hδ ξ hs α
        L' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth
        Cagree (truncation k) hn k hk Q hbase t (Y t) x (hYd t x)
      exact (h.trans (add_le_add le_rfl (hcorrection t x).1)).trans hvErr
    · have h := forwardInitializedExactPhysicalPressure_hessian_error M D hTime δ hδ ξ hs α
        Cagree (truncation k) hn k hk Q X Y hXd hXY hY L' N' wj M' wm BC hrc hcost
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
   EulerPacketForwardFactorization EulerPacketInverseFlowGevrey
  EulerGevrey EulerGraphPressurePotential EulerPeriodicProfile EulerSobolevGevreyOperators
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanClassicalWordBounds
  EulerPacketParentLabelBounds EulerSobolevSourceExponent EulerSmoothBanachFlow
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (W : ℝ)
  (hW : EulerPacketForwardRadius.RadiusPrimitives L LM NB
    (forwardCoefficientBudget period M D hTime NB) δ ξ W)
  (hprofile : ∀ t, α * L.g t ≤ W)
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

theorem forward_uniform_child_label_bounds (q : ℕ)
    (hk69 : 69 ≤ k) (hKk : K ≤ k)
    (hbig : 2 + 45 * embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hinv : ell⁻¹ ≤ k ^ (3 / 4 : ℝ)) :
    ∃ (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period D.T)
        (E : Icc (0 : ℝ) D.T → EulerChildParticleFieldBounds.Data),
        Q.delta=delta (expansion k) ∧
        Q.initialRadius=initialRadius
          (forwardInitializedRadius LM L NB (forwardCoefficientBudget period M D hTime NB) δ ξ)
          (L.correctionCoefficients NB period).M (L.correctionCoefficients NB period).Rc ∧
        G.A = Q.liftedPacketCoefficient period
          (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α (truncation k) k) ∧
        G.A₁ = Q.liftedPacketDerivativeCoefficient period
          (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α (truncation k) k) ∧
        (∀ t z, graphConstraint k D.m₀ (G.A.field t z)=0) ∧
        (∀ (s n : ℕ), n+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          weightedNorm period 6 n (Q.initialRadius/4) ((Q.fieldTower period).realization s t) ≤
              EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
          weightedNorm period 6 n (Q.initialRadius/4) ((Q.pressureTower period).realization s t) ≤
              EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
          weightedNorm period 6 n (Q.initialRadius/4) ((Q.timeDerivativeTower period).realization s
              t) ≤ EulerPacketInitializedCost.weightSize W*delta (expansion k)) ∧
        (∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t)) x -
            (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
              rankOne ℝ (canonicalVelocity D ξ t (Y t x)) (D.normal.field t (Y t x))‖ ≤ k^(-(1/4 :
                  ℝ)) ∧
          ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t))) x -
            (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
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
    forward_uniform_flow_and_shear M D hTime δ hδ hδ1 ξ hs α hα
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
