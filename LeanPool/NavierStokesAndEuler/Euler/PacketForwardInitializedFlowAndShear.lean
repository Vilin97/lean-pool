/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGlobalShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactPressureError

@[expose] public section

/-! One zero-history correction satisfies the source shear/Hessian
estimates and all physical graph-flow bounds simultaneously. The full
weighted correction, pressure and time-derivative estimates are retained. -/

noncomputable section


namespace EulerPacketTerminalDatum

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
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
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t, ContDiff ℝ ∞ (X t))
  (hF : ∀ t x, fderiv ℝ (X t) x = D.F.field t x)
  (hXY : ∀ t x, X t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hX hF hXY hY hdet

theorem forwardInitialized_flow_and_shear_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ0 γ Cw Cv Cp : ℝ, 0 < ρ0 ∧ 0 < γ ∧ 0 < Cw ∧ 0 < Cv ∧ 0 < Cp ∧
      ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period D.T),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=γ ∧
        G.A = Q.liftedPacketCoefficient period
          (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α (truncation k) k) ∧
        G.A₁ = Q.liftedPacketDerivativeCoefficient period
          (forwardInitializedNormalizedDerivativeField M D hTime δ hδ ξ hs α (truncation k) k) ∧
        (∀ t z, graphConstraint k D.m₀ (G.A.field t z)=0) ∧
        (∀ (s n : ℕ), n+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          weightedNorm period 6 n (ρ0/4) ((Q.fieldTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.pressureTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.timeDerivativeTower period).realization s t) ≤
            Cw*delta (expansion k)) ∧
        (∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t)) x -
            (α*deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
              rankOne ℝ (canonicalVelocity D ξ t (Y t x)) (D.normal.field t (Y t x))‖ < Cv/k ∧
          ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure M D hTime δ hδ ξ hs α
            Cagree (truncation k) hn k hk Q t (Y t))) x -
            (EulerPacketForwardShear.pressureCoefficient D ξ α t (Y t x) *
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
  let BC := forwardCoefficientBudget period M D hTime NB
  have hC : 0 ≤ wordCost (Fin 4) 6 δ*‖ξ‖ :=
    mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ)
  obtain ⟨R',hM,hL,wm,wf,wp,hcost,hrc,hterminal⟩ :=
    EulerPacketForwardCommonRadius.exists_common_radius LM L NB BC
      (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ) hC
  let L' := L.enlargeRadius R' hL
  let N' := NB.enlargeRadius R' hL
  let M' := LM.enlargeRadius R' hM
  let S := Scales.ofTimeProfile L.g L.positive hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.g :=
    Scales.ofTimeProfile_growth L.g L.positive hTime.symm α hα
  obtain ⟨ρ0,γ,Cw,hρ,hγ,hCw,hsource⟩ := forwardInitialized_flow_and_correction_eventually
    M D hTime δ hδ hδ1 ξ hs α hα L NB LM Cagree X Y hX hF hXY hY hdet ε hε
  let Kv := forwardInitializedGlobalShearCost L'.R S.H0 N'.C
  let Kp := forwardInitializedPressureHessianCost N' L'.R S.H0 L'.Rc L'.C₀
  let Cv := 1+|Kv|
  let Cp := 1+|Kp|
  have hXd : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hX t).differentiable (by simp) x).hasFDerivAt
  have hYd := continuousInverse_hasFDerivAt D X Y hXd hXY hY
  refine ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,by dsimp [Cv]; positivity,by dsimp [Cp]; positivity,?_⟩
  filter_upwards [hsource,
    fixed_costs_eventually ({tailPolynomialConstant L'.R S.H0 BC.termCost} : Finset ℝ)]
    with k hsource hscalar
  obtain ⟨hk,hn,Q,G,hδQ,hρQ,hγQ,hA,hA1,hgraph,hweighted,hcorrection,hflow⟩ := hsource
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hbase : tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 : ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg hk1 (hscalar.2.2.2 _ (by simp))
  refine ⟨hk,hn,Q,G,hδQ,hρQ,hγQ,hA,hA1,hgraph,hweighted,?_,hflow⟩
  intro t x
  constructor
  · have h := forwardInitializedExactPhysicalVelocity_global_gradient_error M D hTime δ hδ ξ hs α
      L' N' wf M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth
      Cagree (truncation k) hn k hk Q hbase t (Y t) x (hYd t x)
    have ht : Kv/k ≤ |Kv|/k := div_le_div_of_nonneg_right (le_abs_self Kv) hk0.le
    exact h.trans_lt ((add_lt_add_of_le_of_lt ht (hcorrection t x).1).trans_eq
      (by dsimp [Cv]; ring))
  · have h := forwardInitializedExactPhysicalPressure_hessian_error M D hTime δ hδ ξ hs α
      Cagree (truncation k) hn k hk Q X Y hXd hXY hY L' N' wf M' wm BC hrc hcost
      hδ1 hα hterminal wp S hgrowth hbase hdet t x
    have ht : Kp/k ≤ |Kp|/k := div_le_div_of_nonneg_right (le_abs_self Kp) hk0.le
    exact h.trans_lt ((add_lt_add_of_le_of_lt ht (hcorrection t x).2).trans_eq
      (by dsimp [Cp]; ring))

end EulerPacketTerminalDatum
