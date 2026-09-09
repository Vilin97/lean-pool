/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGrade
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedStepBudget

@[expose] public section

/-! The angular derivative of the actual recursive high pressure retains
the unit grade budget. This is derived from the same source solve used by
the velocity recursion. -/

noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem angularPressure_step_exists
    {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (D : EulerTransversePacketProvider.Data U) (hTime : M.T = D.T)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
    (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
    (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
    (W : EulerTransversePacketJoin.Budget.GradeGuards (P := P) L N)
    (LM : EulerMeanPacketProvider.Budget M 6 L.R)
    (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
    {O : Operators} (C : CoefficientData P M.T O) (BC : CoefficientBudget C)
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
    (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
    (S : Scales (Icc (0 : ℝ) M.T))
    {p : ℕ} {a : ℕ → Profile} (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i))
    (hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i)
    (hc₀ : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ))) = 0)
    (c : ℝ) (hc : 0 < c)
    (hprofile : timeProfileChange (S.high p) hTime = c • L.fullProfile) :
    ∃ Q : Field P M.T (fun z => (pressureJet (step O p a).highPressure z).2 angleDirection • D.m₀),
      (Q.normalized M.T_pos.le (S.high p) (S.high_pos p)).WordBound 6 L.R 1 (highShift p) := by
  let F := ProfileRegularity.prefixFields G
  let V := G (p-1) (by omega)
  have hV := hG (p-1) (by omega) (by omega)
  have BF : PrefixBound F M.T_pos.le S L.R := {
    high := fun i hi hi1 => (hG i hi hi1).high
    mean := fun i hi hi2 => (hG i hi (by omega)).mean
    corrector := fun i hi hi1 => (hG i hi hi1).corrector
  }
  have hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)) := fun i hi => (G i hi).mean_angle
  let MF := F.meanForce C (by omega) M.T_pos V.correctorDerivative V.corrector_time V.pressure
  have hMF : (MF.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 L.R 1 (meanForceShift p) :=
    BF.meanForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure L.radius_bounds.1 hRc hcost hc₀ hB₁ hA hB
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (meanForce O p a)) :=
    ⟨F.meanForcing M C (by omega) V.correctorDerivative V.corrector_time V.pressure⟩
  let GM := Classical.choice hm
  have hMeanSolve : O.meanSolve (meanForce O p a) = (GM.vector,GM.scalar) := by
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
  let newMean : Field P M.T (meanResult O p a).1 := (GM.vectorCylinderField P).congr
    (fun t x θ => by change (O.meanSolve (meanForce O p a)).1 _ = _; rw [hMeanSolve])
  have hNew : (newMean.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 L.R 1 (meanShift p) := (LM.grade_bounds WM S GM MF p hp hMF).1.of_path_eq _ rfl
  let HF := F.highForce C hp M.T_pos V.correctorDerivative V.corrector_time V.pressure newMean
  have hHF : (HF.normalized M.T_pos.le (S.high p) (S.high_pos p)).WordBound
      6 L.R 1 (highForceShift p) :=
    BF.highForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure L.radius_bounds.1 hRc hcost hc₀ hB₁ hA hB newMean hNew
  let hh : Nonempty (EulerTransversePacketProvider.Forcing P D (highForce O p a)) :=
    ⟨F.highForcing M D hTime C hp V.correctorDerivative V.corrector_time V.pressure hmean
      (ProfileRegularity.prefixLocality G) V.pressure_zero⟩
  let GH := Classical.choice hh
  let hg := smul_profile_pos L.fullProfile L.fullProfile_pos c hc
  have hHFD : ((HF.changeTime hTime).normalized D.T_pos.le (c • L.fullProfile) hg).WordBound
      6 L.R 1 (highForceShift p) :=
    hHF.normalized_changeTime M.T_pos.le (S.high p) (S.high_pos p) hTime D.T_pos.le
      (c • L.fullProfile) hg hprofile
  have hj := L.angular_grade_bound N W GH (HF.changeTime hTime) c hc p hp hHFD
  have hback : timeProfileChange (c • L.fullProfile) hTime.symm = S.high p := by
    rw [← hprofile,timeProfileChange_roundtrip]
  have hbound := hj.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hHighSolve : O.highSolve (highForce O p a) =
      (EulerTransversePacketJoin.vector τ hτ hτT B GH,EulerTransversePacketJoin.scalar τ hτ hτT B
        GH) := by
    rw [hhigh]
    exact EulerTransversePacketJoin.highSolve_eq τ hτ hτT B GH
  have hscalar : (step O p a).highPressure = EulerTransversePacketJoin.scalar τ hτ hτT B GH :=
    congrArg Prod.snd hHighSolve
  let Q : Field P M.T (fun z => (pressureJet (step O p a).highPressure z).2 angleDirection • D.m₀)
    :=
    ((EulerTransversePacketJoin.angularField τ hτ hτT B GH).changeTime hTime.symm).congr
      (fun _ _ _ => by rw [hscalar])
  exact ⟨Q,hbound.of_path_eq _ rfl⟩

end EulerPacketCylinderField.ProfileBudget
