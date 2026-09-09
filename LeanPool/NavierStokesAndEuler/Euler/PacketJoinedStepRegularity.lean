/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality

@[expose] public section

/-! A genuine recursion step using the full history/forward transverse inverse. -/

noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  {p : ℕ} {a : ℕ → Profile}

def joinedStep (hp : 2 ≤ p)
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
    ((EulerTransversePacketJoin.vectorField τ hτ hτT B GH).changeTime hT.symm).congr (fun _ _ _ =>
      by
      change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 _ = _
      rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh])
  let mean : Field P M.T (EulerPacketProfileRecursion.step O p a).mean :=
    (GM.vectorCylinderField P).congr (fun _ _ _ => by
      change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 _ = _
      rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm])
  let corrector : Field P M.T (EulerPacketProfileRecursion.step O p a).corrector :=
    ((EulerTransversePacketJoin.correctorField τ hτ hτT B GH).changeTime hT.symm).congr (fun _ _ _
      => by
      change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 _ = _
      rw [hcorrector,hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh])
  let pressure : Field P M.T (pressureGradient (EulerPacketProfileRecursion.step O p
    a).highPressure) :=
    ((EulerTransversePacketJoin.scalarGradientField τ hτ hτT B GH).changeTime hT.symm).congr
      (fun _ _ _ => by
        change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 _ = _
        rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh])
  refine {
    high := high
    mean := mean
    corrector := corrector
    pressure := pressure
    high_t := EulerTransversePacketJoin.vectorDerivative τ hτ hτT B GH
    mean_t := GM.vectorDerivative
    corrector_t := EulerTransversePacketJoin.correctorDerivative τ hτ hτT B GH
    highDerivative := (EulerTransversePacketJoin.vectorDerivativeField τ hτ hτT B GH).changeTime
      hT.symm
    meanDerivative := GM.vectorDerivativeCylinderField P
    correctorDerivative := (EulerTransversePacketJoin.correctorDerivativeField τ hτ hτT B
      GH).changeTime hT.symm
    high_time := ?_
    mean_time := ?_
    corrector_time := ?_
    high_zero := ?_
    corrector_zero := ?_
    pressure_zero := ?_
    mean_angle := ?_
  }
  · exact (EulerTransversePacketJoin.vectorField τ hτ hτT B GH).changeTime_derivative
      (EulerTransversePacketJoin.vectorDerivativeField τ hτ hτT B GH) hT.symm
      D.T_pos.le M.T_pos.le (EulerTransversePacketJoin.vectorField_time τ hτ hτT B GH)
  · exact GM.vectorCylinderField_time P
  · exact (EulerTransversePacketJoin.correctorField τ hτ hτT B GH).changeTime_derivative
      (EulerTransversePacketJoin.correctorDerivativeField τ hτ hτT B GH) hT.symm
      D.T_pos.le M.T_pos.le (EulerTransversePacketJoin.correctorField_time τ hτ hτT B GH)
  · intro t x hx θ
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ)) = 0
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.vector_zero_outside τ hτ hτT B GH t x hx θ
  · intro t x hx θ
    change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
      = 0
    rw [hcorrector,hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    exact (EulerTransversePacketJoin.curlCorrector_eq τ hτ hτT B GH td x θ).trans
      (EulerTransversePacketJoin.corrector_zero_outside τ hτ hτT B GH t x hx θ)
  · intro t x hx θ
    change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
      = 0
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    exact pressureGradient_zero_outside (EulerTransversePacketJoin.scalar τ hτ hτT B GH) t
      D.support D.support_compact.isClosed (EulerTransversePacketJoin.scalar_zero_outside τ hτ hτT
        B GH td) x hx θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,θ)) =
      (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,0))
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
    exact GM.vector_angle_independent t x θ 0

end EulerPacketCylinderField.ProfileRegularity
