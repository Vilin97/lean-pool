/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceSolenoidal
public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketApproximationBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedUniformProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds

/-! The actual joined packet has a bounded normalized velocity and a small normal drift. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey EulerPacketCoarseMajorant

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := P) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData P M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (S : Scales (Icc (0 : ℝ) M.T)) (α : ℝ) (hα : 0 < α)
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryBudget : ProfileBudget hprimary S L.R 1)
  (hprimaryMean : primary.mean = 0)
  (hprimaryTangent : ∀ (t : Icc (0 : ℝ) M.T) x θ,
    inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)

include NB W LM WM BC hRc hcost hα hgrowth hprimaryBudget hprimaryMean hprimaryTangent

theorem joinedPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((joinedPacketPullbackField P M D hTime τ hτ hτT B primary hprimary N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1 +
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => joinedSource_profile_budgets P M D hTime τ hτ hτT B L NB W LM WM BC
      hRc hcost S α hα hgrowth primary hprimary hprimaryBudget hprimaryMean hprimaryTangent i hi
  have h := ProfileRegularity.normalizedVelocity_bound M.T_pos G hG L.radius_bounds.1
    (profiles_zero _ _) hN BC hRc k hk hbase
  exact h.ofRawEq _ (fun _ _ _ => rfl)

theorem joinedPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (((joinedPacketPullbackField P M D hTime τ hτ hτT B primary hprimary N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 := by
  let a := joinedSourceProfiles P M D τ hτ hτT B primary
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => joinedSource_profile_budgets P M D hTime τ hτ hτT B L NB W LM WM BC
      hRc hcost S α hα hgrowth primary hprimary hprimaryBudget hprimaryMean hprimaryTangent i hi
  have hb : (a 1).mean=0 := by
    simpa only [a,joinedSourceProfiles,profiles_one] using hprimaryMean
  have ht : ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ D.m₀ ((joinedSourceOperators P M D τ hτ hτT B).inverseFrame (t,(x,θ))
        ((a 1).high (t,(x,θ))))=0 := by
    intro t x θ
    have h := hprimaryTangent t x θ
    change inner ℝ ((D.FInv.field (D.clamp t) x).adjoint D.m₀) (primary.high (t,(x,θ)))=0 at h
    rw [ContinuousLinearMap.adjoint_inner_left] at h
    change inner ℝ D.m₀ (D.FInv.field (D.clamp t) x ((a 1).high (t,(x,θ))))=0
    simpa only [a,joinedSourceProfiles,profiles_one] using h
  have h := ProfileRegularity.normalizedNormal_bound M.T_pos G hG L.radius_bounds.1
    (profiles_zero _ _) hb hN BC hRc D.m₀ D.m₀_unit.le ht k hk hbase
  exact h.ofRawEq _ (fun _ _ _ => rfl)

end EulerPacketCylinderField
