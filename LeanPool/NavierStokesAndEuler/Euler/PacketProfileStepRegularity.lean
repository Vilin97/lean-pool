/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorSupport
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradientProperties

/-! One literal profile-recursion step carries genuine path, time-derivative and locality witnesses.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  {p : ℕ} {a : ℕ → Profile}

/-- The prefix hypotheses are regularity of known fields, never equations for the new profile. -/
def step (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i)) :
    ProfileRegularity P M.T M.T_pos.le D.support (EulerPacketProfileRecursion.step O p a) := by
  let F := prefixFields G
  let W := G (p-1) (by omega)
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (EulerPacketProfileRecursion.meanForce O p
      a)) :=
    ⟨F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure⟩
  let hh : Nonempty (EulerTransversePacketProvider.Forcing P D
      (EulerPacketProfileRecursion.highForce O p a)) :=
    ⟨F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
      (prefixLocality G) W.pressure_zero⟩
  let GM := Classical.choice hm
  let GH := Classical.choice hh
  let high : Field P M.T (EulerPacketProfileRecursion.step O p a).high :=
    ((GH.vectorField I).changeTime hT.symm).congr (fun _ _ _ => by
      change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 _ = _
      rw [hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh])
  let mean : Field P M.T (EulerPacketProfileRecursion.step O p a).mean :=
    (GM.vectorCylinderField P).congr (fun _ _ _ => by
      change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 _ = _
      rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm])
  let corrector : Field P M.T (EulerPacketProfileRecursion.step O p a).corrector :=
    ((GH.curlCorrectorField I).changeTime hT.symm).congr (fun _ _ _ => by
      change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 _ = _
      rw [hcorrector,hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh])
  let pressure : Field P M.T (pressureGradient (EulerPacketProfileRecursion.step O p
      a).highPressure) :=
    ((GH.scalarGradientField I).changeTime hT.symm).congr (fun _ _ _ => by
      change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 _ = _
      rw [hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh])
  refine {
    high := high
    mean := mean
    corrector := corrector
    pressure := pressure
    highT := GH.vectorDerivative I
    meanT := GM.vectorDerivative
    correctorT := GH.correctorDerivative I
    highDerivative := (GH.vectorDerivativeField I).changeTime hT.symm
    meanDerivative := GM.vectorDerivativeCylinderField P
    correctorDerivative := (GH.correctorDerivativeField I).changeTime hT.symm
    high_time := ?_
    mean_time := ?_
    corrector_time := ?_
    high_zero := ?_
    corrector_zero := ?_
    pressure_zero := ?_
    mean_angle := ?_
  }
  · exact (GH.vectorField I).changeTime_derivative (GH.vectorDerivativeField I) hT.symm
      D.T_pos.le M.T_pos.le (GH.vectorField_time I)
  · exact GM.vectorCylinderField_time P
  · exact (GH.curlCorrectorField I).changeTime_derivative (GH.correctorDerivativeField I) hT.symm
      D.T_pos.le M.T_pos.le (GH.curlCorrectorField_time I)
  · intro t x hx θ
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ)) = 0
    rw [hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh]
    exact GH.vector_zero_outside I t x hx θ
  · intro t x hx θ
    change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
        = 0
    rw [hcorrector,hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh]
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    exact (GH.curlCorrector_eq I td x θ).trans (GH.corrector_zero_outside I t x hx θ)
  · intro t x hx θ
    change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
        = 0
    rw [hhigh,EulerTransversePacketProvider.highSolve_of_admissible D I _ hh]
    exact GH.scalarGradient_zero_outside I t x hx θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,θ)) =
      (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,0))
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
    exact GM.vector_angle_independent t x θ 0

end EulerPacketCylinderField.ProfileRegularity
