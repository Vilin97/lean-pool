/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileStepRegularity

@[expose] public section

/-!
# Genuine regularity through the full literal profile recursion

Strong induction applies the constructed mean and high solvers at each grade.
Only the primary profile is supplied; later forcing admissibility is proved.
-/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

include hT I C hmean hhigh hcorrector hprimary in
theorem profiles_regular (p : ℕ) :
    Nonempty (ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p)) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst p
      rw [profiles_zero]
      exact ⟨ProfileRegularity.zero P M.T M.T_pos.le D.support⟩
    by_cases hp1 : p = 1
    · subst p
      rw [profiles_one]
      exact ⟨hprimary⟩
    have hp : 2 ≤ p := by omega
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
      fun i hi => Classical.choice (ih i hi)
    rw [profiles_step O primary p hp]
    exact ⟨ProfileRegularity.step M D hT I C hmean hhigh hcorrector hp G⟩

def profileWitness (p : ℕ) : ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p) :=
  Classical.choice (profiles_regular M D hT I C hmean hhigh hcorrector primary hprimary p)

/-- The literal mean forcing at every nonprimary grade has actual smooth spatial L² slices. -/
def profiles_meanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M (meanForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => profileWitness M D hT I C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure

/-- The actual supported zero-mean transverse input is built from the already generated profiles. -/
def profiles_highForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D (highForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => profileWitness M D hT I C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
    (ProfileRegularity.prefixLocality G) W.pressure_zero

end EulerPacketCylinderField
