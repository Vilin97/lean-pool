/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedProfilesRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedStepParity

@[expose] public section

/-! Every grade constructed with the joined inverse has the prescribed joint parity. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (E : CoefficientEven M.T O) (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryParity : ProfileParity M.T primary)

include hT τ hτ hτT B C hmean hhigh hcorrector E eM hSym hF hDM hBH hprimary hprimaryParity in
theorem joined_profiles_parity (p : ℕ) : ProfileParity M.T (profiles O primary p) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst p
      rw [profiles_zero]
      exact ProfileParity.zero M.T
    by_cases hp1 : p = 1
    · subst p
      rw [profiles_one]
      exact hprimaryParity
    have hp : 2 ≤ p := by omega
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
      fun i _ => joinedProfileWitness M D hT τ hτ hτT B C hmean hhigh hcorrector primary hprimary i
    rw [profiles_step O primary p hp]
    exact ProfileParity.joinedStep M D hT τ hτ hτT B C hmean hhigh hcorrector E eM
      hSym hF hDM hBH hp G ih

end EulerPacketCylinderField
