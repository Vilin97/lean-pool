/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialPhysical
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRemainder
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceInitialMean

/-! Source (22) for the literal initialized packet. The constants at
each fixed Sobolev order are independent of its truncation and frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set

theorem timeProfileChange_initial {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (g : C(Icc (0 : ℝ) T, ℝ)) (h : T = T') :
    timeProfileChange g h ⟨0,le_rfl,hT'⟩ = g ⟨0,le_rfl,hT⟩ := by
  subst T'
  rfl

end EulerPacketCylinderField

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
      EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPhysicalL2Scaling EulerCylinderCoordinates

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

/-- Initialized initial high, given by `scale M.ℓ (fun x => EulerPacketInitial.high N k⁻¹ 0
(initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))`. -/
def initializedInitialHigh (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.high N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))

/-- Initialized initial mean, given by `scale M.ℓ (fun x => EulerPacketInitial.mean N k⁻¹ 0
(initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))`. -/
def initializedInitialMean (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.mean N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))

include hTime in
theorem initializedInitialHigh_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 (M.ℓ/2) := by
  have h := EulerPacketInitial.high_scaled_support
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹ k D.m₀ M.ℓ M.ℓ_pos (1/2) hS
  simpa only [initializedInitialHigh,div_eq_mul_inv,one_mul] using h

include hTime in
theorem initializedInitialMean_support (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 2 := by
  apply EulerPacketInitial.mean_scaled_support k⁻¹ k D.m₀ M.ℓ M.ℓ_pos
  intro i _ θ
  exact joinedSource_mean_initial_support period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    rfl i θ

include hTime in
theorem initializedInitial_common_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 ∧
      tsupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 := by
  refine ⟨(initializedInitialHigh_support M D hTime τ hτ hτT B δ hδ ξ hs α hS N k).trans ?_,
    initializedInitialMean_support M D hTime τ hτ hτT B δ hδ ξ hs α N k⟩
  exact Metric.closedBall_subset_closedBall (by have := M.ℓ_le_one; linarith)

include hTime in
theorem initializedInitialMean_zero (hL : M.L = 0) (N : ℕ) (k : ℝ) :
    initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k = 0 := by
  funext x
  change M.ℓ • EulerPacketInitial.mean N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α)
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0
  rw [EulerPacketInitial.mean_eq]
  simp only [EulerPacketPointJets.fieldSum,EulerFiniteGrades.evaluate,EulerPacketInitial.timeSlice]
  have hz (i : ℕ) := joinedSource_mean_initial_zero period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    rfl hL i (M.ℓ⁻¹ • x) (k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))
  simp only [show ∀ i, (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α i).mean
      (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0 from hz,
    smul_zero,Finset.sum_const_zero]

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

include hgrowth in
theorem initialized_growth_initial : S.growth ⟨0,le_rfl,M.T_pos.le⟩=α := by
  have he := congrArg (fun g : C(Icc (0 : ℝ) D.T,ℝ) => g ⟨0,le_rfl,D.T_pos.le⟩) hgrowth
  rw [timeProfileChange_initial M.T_pos.le D.T_pos.le] at he
  have hp : L.fullProfile ⟨0,le_rfl,D.T_pos.le⟩=1 :=
    EulerElapsedTimePathGluing.profile_left D.T τ hτ.le hτT.le L.g L.initial_one ⟨0,le_rfl,hτ.le⟩
  simpa only [ContinuousMap.smul_apply,smul_eq_mul,hp,mul_one] using he

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedInitialHigh_Hm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ≤
      (M.ℓ⁻¹)^s*k^s*α*(EulerPacketInitial.highCost L.R S.H0 *
        physicalDerivativeCost period (4*L.R)
          (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖)) s) := by
  let G := fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have h := EulerPacketInitial.high_physical_bound G S L.R hG L.radius_bounds.1
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) ⟨0,le_rfl,M.T_pos.le⟩
    hN BC.termCost k BC.one_le_termCost hk hbase M.ℓ M.ℓ_pos M.ℓ_le_one D.m₀ s
  simpa only [initializedInitialHigh,initialized_growth_initial M D hTime τ hτ hτT B α L S hgrowth]
      using h

theorem initializedInitialMean_Hm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) (s : ℕ) :
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ≤
      (M.ℓ⁻¹)^s/k^2*(EulerPacketInitial.meanCost L.R S.H0 *
        physicalDerivativeCost period (4*L.R) ‖coordinateEquiv.symm.toContinuousLinearMap‖ s) := by
  let G := fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  exact EulerPacketInitial.mean_physical_bound G S L.R hG L.radius_bounds.1
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) ⟨0,le_rfl,M.T_pos.le⟩
    hN BC.termCost k BC.one_le_termCost hk hbase
    (initializedProfiles_one_mean M D τ hτ hτT B δ hδ ξ hs α)
    M.ℓ M.ℓ_pos M.ℓ_le_one D.m₀ s

end EulerPacketTerminalDatum
