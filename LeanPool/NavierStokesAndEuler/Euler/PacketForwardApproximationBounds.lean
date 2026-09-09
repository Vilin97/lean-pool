/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceSolenoidal
public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds

@[expose] public section

/-! The actual zero-history packet has a bounded normalized velocity and a
small normal drift, at a single radius inherited from the profile construction. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey EulerPacketCoarseMajorant
  EulerTransversePacketProvider

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (Y : InitialData P D)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := P) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData P M D (InitialData.zero P D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (S : Scales (Icc (0 : ℝ) M.T)) (α : ℝ) (hα : 0 < α)
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)
  (hprimaryBudget : ProfileBudget (forwardSourcePrimaryWitness P M D hTime Y) S L.R 1)

include NB W LM WM BC hRc hcost hα hgrowth hprimaryBudget

theorem forwardPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    ((sourcePacketPullbackField P M D hTime (InitialData.zero P D) Y N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1+
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let a := sourceProfiles P M D (InitialData.zero P D) Y
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => sourceProfileWitness P M D hTime (InitialData.zero P D) Y i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardSource_profile_budgets P M D hTime Y L NB W LM WM BC
      hRc hcost S α hα hgrowth hprimaryBudget i hi
  have h := ProfileRegularity.normalizedVelocity_bound M.T_pos G hG L.radius_one
    (profiles_zero _ _) hN BC hRc k hk hbase
  exact h.of_raw_eq _ (fun _ _ _ => rfl)

theorem forwardPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (((sourcePacketPullbackField P M D hTime (InitialData.zero P D) Y N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 := by
  let a := sourceProfiles P M D (InitialData.zero P D) Y
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => sourceProfileWitness P M D hTime (InitialData.zero P D) Y i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardSource_profile_budgets P M D hTime Y L NB W LM WM BC
      hRc hcost S α hα hgrowth hprimaryBudget i hi
  have hb : (a 1).mean = 0 := by
    simp only [a,sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
  have ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ D.m₀ ((sourceOperators P M D (InitialData.zero P D)).inverseFrame (t,(x,θ))
        ((a 1).high (t,(x,θ)))) = 0 := by
    intro t x θ
    have h := source_high_tangent P M D hTime (InitialData.zero P D) Y 1 t x θ
    change inner ℝ ((D.FInv.field (D.clamp t) x).adjoint D.m₀) ((a 1).high (t,(x,θ))) = 0 at h
    rw [ContinuousLinearMap.adjoint_inner_left] at h
    exact h
  have h := ProfileRegularity.normalizedNormal_bound M.T_pos G hG L.radius_one
    (profiles_zero _ _) hb hN BC hRc D.m₀ D.m₀_unit.le ht k hk hbase
  exact h.of_raw_eq _ (fun _ _ _ => rfl)

end EulerPacketCylinderField
