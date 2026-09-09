/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketForcingBounds

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
