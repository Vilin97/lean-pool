/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalPrimaryFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceConstraints
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudgetTransport
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketForcingBounds

/-! Related estimates used together by the same construction modules. -/

section

/-! The literal compact terminal wave initializes the mean-time packet budget. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))

include hδ1 hα hR W

theorem joinedTerminalPrimary_budget (S : Scales (Icc (0 : ℝ) M.T))
    (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile) :
    ProfileBudget (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) S L.R 1 := by
  have hg : (S.changeTime hTime).growth=α • L.fullProfile :=
    (S.growth_changeTime hTime).trans hgrowth
  have hD := primary_profile_budget H NB δ hδ hδ1 ξ hs α hα hR W
    (joinedSourceOperators period M D τ hτ hτT B) rfl (S.changeTime hTime) hg
  have hM := hD.changeTime hTime.symm M.T_pos.le
  simpa only [Scales.changeTime_roundtrip, joinedTerminalPrimaryWitness, joinedTerminalPrimary]
      using hM

end EulerPacketTerminalDatum

end
end

end

section

/-! A single fixed radius bounds all recursively constructed joined-source profiles. -/

section

/-! One complete quantitative recursion step, using the actual mean and joined transverse solvers.
-/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem joinedStep
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
    (hcorrector : O.curlCorrector = D.curlCorrector P)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
    (S : Scales (Icc (0 : ℝ) M.T))
    {p : ℕ} {a : ℕ → Profile} (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i))
    (hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S L.R i)
    (hc₀ : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)
    (c : ℝ) (hc : 0 < c)
    (hprofile : timeProfileChange (S.high p) hTime = c • L.fullProfile)
    (H : ProfileRegularity P M.T M.T_pos.le D.support (EulerPacketProfileRecursion.step O p a)) :
    ProfileBudget H S L.R p := by
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
  have hmBounds := LM.grade_bounds WM S GM MF p hp hMF
  have hNew : (newMean.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 L.R 1 (meanShift p) := hmBounds.1.of_path_eq _ rfl
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
  have hj := L.grade_bounds N W GH (HF.changeTime hTime) c hc p hp hHFD
  have hback : timeProfileChange (c • L.fullProfile) hTime.symm = S.high p := by
    rw [← hprofile,timeProfileChange_roundtrip]
  have hv := hj.1.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hvt := hj.2.1.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hcv := hj.2.2.1.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hct := hj.2.2.2.1.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hpv := hj.2.2.2.2.normalized_changeTime D.T_pos.le (c • L.fullProfile) hg
    hTime.symm M.T_pos.le (S.high p) (S.high_pos p) hback
  have hHighSolve : O.highSolve (highForce O p a) =
      (EulerTransversePacketJoin.vector τ hτ hτT B GH,EulerTransversePacketJoin.scalar τ hτ hτT B
          GH) := by
    rw [hhigh]
    exact EulerTransversePacketJoin.highSolve_eq τ hτ hτT B GH
  have hHighVal : (EulerPacketProfileRecursion.step O p a).high =
      EulerTransversePacketJoin.vector τ hτ hτT B GH := congrArg Prod.fst hHighSolve
  have hMeanVal : (EulerPacketProfileRecursion.step O p a).mean = GM.vector := congrArg Prod.fst
      hMeanSolve
  have hCorrectorVal : (EulerPacketProfileRecursion.step O p a).corrector =
      D.curlCorrector P (EulerTransversePacketJoin.vector τ hτ hτT B GH) := by
    change O.curlCorrector (O.highSolve (highForce O p a)).1 = _
    rw [hcorrector,hHighSolve]
  have hPressureVal : pressureGradient (EulerPacketProfileRecursion.step O p a).highPressure =
      pressureGradient (EulerTransversePacketJoin.scalar τ hτ hτT B GH) :=
    congrArg pressureGradient (congrArg Prod.snd hHighSolve)
  let highBase : Field P M.T (EulerPacketProfileRecursion.step O p a).high :=
    ((EulerTransversePacketJoin.vectorField τ hτ hτT B GH).changeTime hTime.symm).congr
      (fun t x θ => congrFun hHighVal (t,(x,θ)))
  let meanBase : Field P M.T (EulerPacketProfileRecursion.step O p a).mean :=
    (GM.vectorCylinderField P).congr (fun t x θ => congrFun hMeanVal (t,(x,θ)))
  let correctorBase : Field P M.T (EulerPacketProfileRecursion.step O p a).corrector :=
    ((EulerTransversePacketJoin.correctorField τ hτ hτT B GH).changeTime hTime.symm).congr
      (fun t x θ => congrFun hCorrectorVal (t,(x,θ)))
  have hHighTime : TimeDerivative M.T_pos.le highBase
      ((EulerTransversePacketJoin.vectorDerivativeField τ hτ hτT B GH).changeTime hTime.symm) :=
    (EulerTransversePacketJoin.vectorField τ hτ hτT B GH).changeTime_derivative
      (EulerTransversePacketJoin.vectorDerivativeField τ hτ hτT B GH) hTime.symm D.T_pos.le
          M.T_pos.le
      (EulerTransversePacketJoin.vectorField_time τ hτ hτT B GH)
  have hMeanTime : TimeDerivative M.T_pos.le meanBase (GM.vectorDerivativeCylinderField P) :=
    GM.vectorCylinderField_time P
  have hCorrectorTime : TimeDerivative M.T_pos.le correctorBase
      ((EulerTransversePacketJoin.correctorDerivativeField τ hτ hτT B GH).changeTime hTime.symm) :=
    (EulerTransversePacketJoin.correctorField τ hτ hτT B GH).changeTime_derivative
      (EulerTransversePacketJoin.correctorDerivativeField τ hτ hτT B GH) hTime.symm D.T_pos.le
          M.T_pos.le
      (EulerTransversePacketJoin.correctorField_time τ hτ hτT B GH)
  exact {
    high := hv.normalized_of_raw_eq H.high M.T_pos.le (S.high p) (S.high_pos p)
      (fun t x θ => congrFun hHighVal (t,(x,θ)))
    highDerivative := hvt.normalized_of_raw_eq H.highDerivative M.T_pos.le (S.high p) (S.high_pos p)
      (TimeDerivative.raw_eq (hT := M.T_pos) H.high_time hHighTime)
    mean := hmBounds.1.normalized_of_raw_eq H.mean M.T_pos.le (S.mean p) (S.mean_pos p)
      (fun t x θ => congrFun hMeanVal (t,(x,θ)))
    meanDerivative := hmBounds.2.1.normalized_of_raw_eq H.meanDerivative M.T_pos.le (S.mean p)
        (S.mean_pos p)
      (TimeDerivative.raw_eq (hT := M.T_pos) H.mean_time hMeanTime)
    corrector := hcv.normalized_of_raw_eq H.corrector M.T_pos.le (S.high p) (S.high_pos p)
      (fun t x θ => congrFun hCorrectorVal (t,(x,θ)))
    correctorDerivative := hct.normalized_of_raw_eq H.correctorDerivative M.T_pos.le (S.high p)
        (S.high_pos p)
      (TimeDerivative.raw_eq (hT := M.T_pos) H.corrector_time hCorrectorTime)
    pressure := hpv.normalized_of_raw_eq H.pressure M.T_pos.le (S.high p) (S.high_pos p)
      (fun t x θ => congrFun hPressureVal (t,(x,θ)))
  }

end EulerPacketCylinderField.ProfileBudget

end
end

end

@[expose] public section

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
    inner ℝ (D.normalField (t, (x, θ))) (primary.high (t, (x, θ))) = 0)

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
    have hB₁ : (a 1).mean = 0 := by
        simpa only [a,joinedSourceProfiles,profiles_one] using hprimaryMean
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

end
end

end
