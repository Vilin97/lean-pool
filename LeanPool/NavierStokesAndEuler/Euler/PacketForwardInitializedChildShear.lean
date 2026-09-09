/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedFlowAndShear
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildSourceBound

@[expose] public section

/-! One actual zero-history initialized correction simultaneously satisfies the
global shear/Hessian estimates and the source C*=10(s+2) child-label
bound. The child fields are constructed from the actual graph flow and
the parent displacement, velocity and acceleration. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketForwardFactorization EulerGraphPressurePotential EulerPeriodicProfile
  EulerSobolevGevreyOperators EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds EulerSobolevSourceExponent
  EulerSmoothBanachFlow
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
  (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (Dp Vp Wp : Icc (0 : ℝ) D.T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hDp : ∀ t, HasLabelBound K (Dp t))
  (hVp : ∀ t, HasLabelBound K (Vp t))
  (hWp : ∀ t, HasLabelBound K (Wp t))

include hδ1 hα L NB LM hX hF hXY hY hdet hell1 hK hDp hVp hWp

theorem forwardInitialized_child_label_and_shear_eventually (q : ℕ) :
    ∃ ρ0 γ Cw Cv Cp : ℝ, 0 < ρ0 ∧ 0 < γ ∧ 0 < Cw ∧ 0 < Cv ∧ 0 < Cp ∧
      ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period D.T)
        (E : Icc (0 : ℝ) D.T → EulerChildParticleFieldBounds.Data),
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
        (∀ t, (E t).parentDisplacement=Dp t ∧ (E t).parentVelocity=Vp t ∧ (E
          t).parentAcceleration=Wp t ∧
          (E t).displacement=G.displacementField k D.m₀ ell hell t ∧
          (E t).velocity=G.velocityField k D.m₀ ell hell t ∧
          (E t).acceleration=G.accelerationFieldL2 k D.m₀ ell hell t ∧
          (E t).inner=(flowData D.T G.time_nonneg (physicalCoefficient k D.m₀ D.T G.A ell)).forward
            t) ∧
        (∀ t n,
          classicalBlockSize direction q (E t).childDisplacement.toLp (E
            t).childDisplacement.translation_contDiff n+
          classicalBlockSize direction q (E t).childVelocity.toLp (E
            t).childVelocity.translation_contDiff n+
          classicalBlockSize direction q (E t).childAcceleration.toLp (E
            t).childAcceleration.translation_contDiff n ≤
            (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2) := by
  obtain ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,hCv,hCp,hsource⟩ := forwardInitialized_flow_and_shear_eventually
    M D hTime δ hδ hδ1 ξ hs α hα L NB LM Cagree X Y hX hF hXY hY hdet
    (1/4) (by norm_num)
  refine ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,hCv,hCp,?_⟩
  filter_upwards [hsource,eventually_ge_atTop (69 : ℝ),eventually_ge_atTop K,
    eventually_ge_atTop (2+45*embeddingCost),eventually_ge_atTop (fixedCost q),
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).eventually_ge_atTop ell⁻¹]
    with k hsource hk69 hKk hbig hcost hinv
  obtain ⟨hk,hn,Q,G,hδQ,hρQ,hγQ,hA,hA1,hgraph,hweighted,herror,hfields⟩ := hsource
  have hcoarse (t : Icc (0 : ℝ) D.T) :=
    EulerPhysicalChildFields.coarsen_graph_bounds k ell (by linarith) hell hinv
      (G.displacementField k D.m₀ ell hell t) (G.velocityField k D.m₀ ell hell t)
      (G.accelerationFieldL2 k D.m₀ ell hell t)
      (hfields ell hell hell1 t).1 (hfields ell hell hell1 t).2.1 (hfields ell hell hell1 t).2.2.1
      (hfields ell hell hell1 t).2.2.2.1 (hfields ell hell hell1 t).2.2.2.2
  obtain ⟨E,hmatch,hlabel⟩ := EulerPhysicalChildFields.exists_source_child_fields
    G k D.m₀ hgraph ell hell Dp Vp Wp K hK hDp hVp hWp q hk69 hKk hbig hcost hcoarse
  exact ⟨hk,hn,Q,G,E,hδQ,hρQ,hγQ,hA,hA1,hgraph,hweighted,herror,hmatch,hlabel⟩

end EulerPacketTerminalDatum
