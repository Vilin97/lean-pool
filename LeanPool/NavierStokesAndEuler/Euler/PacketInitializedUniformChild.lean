/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSourceExponent
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformFlow
import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildSourceBound

/-! The uniform source comparison gives the actual child label estimate
at exponent 10(q+2), retaining the same exact correction and its errors. -/

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
