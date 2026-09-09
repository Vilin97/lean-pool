/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality

@[expose] public section

/-! The complete history/forward high inverse preserves the actual recursive symmetries. -/

noncomputable section

namespace EulerPacketCylinderField.ProfileParity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerLpCylinderTranslation EulerCylinderFieldReflection

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
  {p : ℕ} {a : ℕ → Profile}

include hT τ hτ hτT B C hmean hhigh hcorrector E eM hSym hF hDM hBH in
theorem joinedStep (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i))
    (H : ∀ i, i < p → ProfileParity M.T (a i)) :
    ProfileParity M.T (EulerPacketProfileRecursion.step O p a) := by
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  have Hpre := prefixOdd H
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (EulerPacketProfileRecursion.meanForce O p
    a)) :=
    ⟨F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure⟩
  let hh : Nonempty (EulerTransversePacketProvider.Forcing P D
    (EulerPacketProfileRecursion.highForce O p a)) :=
    ⟨F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
      (ProfileRegularity.prefixLocality G) W.pressure_zero⟩
  let GH := Classical.choice hh
  have hmOdd := F.meanForce_odd Hpre C E (by omega) M.T_pos W.correctorDerivative
    W.corrector_time W.pressure (H (p-1) (by omega)).pressure
  have hm0 (t : Icc (0 : ℝ) M.T) (x : Space) :
      EulerPacketProfileRecursion.meanForce O p a (t,(-x,0)) =
        -EulerPacketProfileRecursion.meanForce O p a (t,(x,0)) := by
    simpa only [neg_zero] using hmOdd t x 0
  have hhOdd : JointOdd D.T (EulerPacketProfileRecursion.highForce O p a) :=
    (F.actualHighForce_odd M Hpre C E eM hp W.correctorDerivative W.corrector_time
      W.pressure (H (p-1) (by omega)).pressure hmean).changeTime hT
  refine { high := ?_, mean := ?_, corrector := ?_, pressure := ?_, highPressure := ?_,
    meanPressure := ?_ }
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(-x,-θ)) =
      -(O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.vector_odd τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(-x,-θ)) =
      -(O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,θ))
    rw [hmean]
    exact EulerMeanPacketProvider.meanSolve_odd M eM _ hm hm0 t x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1
      (t,(-x,-θ)) =
      -O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
    rw [hcorrector,hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.curlCorrector_odd τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2
      (t,(-x,-θ)) =
      -pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact pressureGradient_odd (EulerTransversePacketJoin.scalar τ hτ hτT B GH) t
      (EulerTransversePacketJoin.scalar_smooth τ hτ hτT B GH t)
      (EulerTransversePacketJoin.scalar_even τ hτ hτT B GH hSym hF hDM hBH hhOdd td) x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(-x,-θ)) =
      (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.scalar_even τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).2 (t,(-x,-θ)) =
      (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).2 (t,(x,θ))
    rw [hmean]
    exact EulerMeanPacketProvider.meanSolve_even M eM _ hm hm0 t x θ

end EulerPacketCylinderField.ProfileParity
