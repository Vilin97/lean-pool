/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileStepParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfilesRegularity

@[expose] public section

/-! Every profile in the literal recursively generated family has the source parity. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerLpCylinderTranslation EulerCylinderFieldReflection

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (E : CoefficientEven M.T O) (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hI : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryParity : ProfileParity M.T primary)

include hT I C hmean hhigh hcorrector E eM hSym hF hDM hI hprimary hprimaryParity in
theorem profiles_parity (p : ℕ) : ProfileParity M.T (profiles O primary p) := by
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
      fun i _ => profileWitness M D hT I C hmean hhigh hcorrector primary hprimary i
    rw [profiles_step O primary p hp]
    exact ProfileParity.step M D hT I C hmean hhigh hcorrector E eM hSym hF hDM hI hp G ih

end EulerPacketCylinderField
