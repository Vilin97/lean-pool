/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedStepBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudgetTransport
public import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceConstraints

@[expose] public section

/-! A single fixed radius bounds all recursively constructed joined-source profiles. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := P) L N)
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
    inner ℝ (D.normalField (t,(x,θ))) (primary.high (t,(x,θ))) = 0)

include N W LM WM BC hRc hcost hα hgrowth hprimaryBudget hprimaryMean hprimaryTangent

/-- The hypotheses are fixed source budgets and the primary estimate. No
later-grade forcing or solution estimate is assumed. -/
theorem joinedSource_profile_budgets (p : ℕ) : 1 ≤ p →
    ProfileBudget (joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary p) S L.R p :=
      by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp
    by_cases hp1 : p = 1
    · subst p
      apply hprimaryBudget.of_profile_eq M.T_pos
      simp only [joinedSourceProfiles,profiles_one]
    have hp2 : 2 ≤ p := by omega
    let a := joinedSourceProfiles P M D τ hτ hτT B primary
    let O := joinedSourceOperators P M D τ hτ hτT B
    let C := joinedSourceCoefficientData P M D τ hτ hτT B hTime
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
      fun i _ => joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary i
    have hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
      fun i hi hi1 => ih i hi hi1
    have he : a p = EulerPacketProfileRecursion.step O p a :=
      profiles_step O primary p hp2
    let H := (joinedSourceProfileWitness P M D hTime τ hτ hτT B primary hprimary p).congr he
    have hc₀ : (a 0).corrector = 0 := by simp only [a,joinedSourceProfiles,profiles_zero]; rfl
    have hB₁ : (a 1).mean = 0 := by simpa only [a,joinedSourceProfiles,profiles_one] using
      hprimaryMean
    have hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
        inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ))) = 0 := by
      intro i _ t x θ
      by_cases hi0 : i = 0
      · subst i
        simp only [a,joinedSourceProfiles,profiles_zero]
        exact inner_zero_right _
      · exact joinedSource_high_tangent_all P M D hTime τ hτ hτT B primary hprimary
          hprimaryTangent i (by omega) t x θ
    have hStep : ProfileBudget H S L.R p :=
      ProfileBudget.joinedStep M D hTime τ hτ hτT B L N W LM WM C BC rfl rfl rfl hRc hcost S
        hp2 G hG hc₀ hB₁ hA (α*meanScale S.H0 p) (S.gradeFactor_pos α hα p)
        (S.high_timeProfile_eq hTime L.fullProfile α hgrowth p) H
    exact hStep.of_profile_eq M.T_pos _ he.symm

end EulerPacketCylinderField
