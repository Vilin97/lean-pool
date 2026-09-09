/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownForce
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighMean

/-! The recursive mean forcing is sent to the actual source inverse, then returned as a true
cylinder field. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (D : EulerMeanPacketProvider.Data)
  {O : Operators} {p : ℕ} {a : ℕ → Profile}

/-- Mean forcing as an element of `EulerMeanPacketProvider.Forcing D
(EulerPacketProfileRecursion.meanForce O p a)`. -/
def PrefixFields.meanForcing (F : PrefixFields P D.T p a) (C : CoefficientData P D.T O)
    (hp : 1 ≤ p) {correctorT : VectorField} (Ct : Field P D.T correctorT)
    (hCt : TimeDerivative D.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P D.T (pressureGradient (a (p - 1)).highPressure)) :
    EulerMeanPacketProvider.Forcing D (EulerPacketProfileRecursion.meanForce O p a) := by
  simpa only [EulerPacketProfileRecursion.meanForce,C.period_eq] using
    (F.knownForce C hp D.T_pos Ct hCt pressure).meanForcing D

/-- Mean result field as an element of `Field P D.T (meanResult O p a).1`. -/
def PrefixFields.meanResultField (F : PrefixFields P D.T p a) (C : CoefficientData P D.T O)
    (hp : 1 ≤ p) {correctorT : VectorField} (Ct : Field P D.T correctorT)
    (hCt : TimeDerivative D.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P D.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve D) :
    Field P D.T (meanResult O p a).1 :=
  (EulerMeanPacketProvider.meanSolveCylinderField P D (EulerPacketProfileRecursion.meanForce O p a)
    ⟨F.meanForcing D C hp Ct hCt pressure⟩).congr (fun _ _ _ => by rw [meanResult,hmean])

theorem PrefixFields.meanResult_angleIndependent (F : PrefixFields P D.T p a)
    (C : CoefficientData P D.T O) (hp : 1 ≤ p) {correctorT : VectorField}
    (Ct : Field P D.T correctorT)
    (hCt : TimeDerivative D.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P D.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve D)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    (meanResult O p a).1 (t,(x,θ)) = (meanResult O p a).1 (t,(x,0)) := by
  rw [meanResult,hmean]
  exact (EulerMeanPacketProvider.meanSolve_angle_independent D
    (EulerPacketProfileRecursion.meanForce O p a) ⟨F.meanForcing D C hp Ct hCt pressure⟩ t x θ 0).1

/-- The new mean in this witness is obtained from the constructed source mean inverse. -/
def PrefixFields.actualHighForce (F : PrefixFields P D.T p a) (C : CoefficientData P D.T O)
    (hp : 2 ≤ p) {correctorT : VectorField} (Ct : Field P D.T correctorT)
    (hCt : TimeDerivative D.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P D.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve D) :
    Field P D.T (EulerPacketProfileRecursion.highForce O p a) :=
  F.highForce C hp D.T_pos Ct hCt pressure
    (F.meanResultField D C (by omega) Ct hCt pressure hmean)

theorem PrefixFields.actualHighForce_mean_zero (F : PrefixFields P D.T p a)
    (C : CoefficientData P D.T O) (hp : 2 ≤ p) {correctorT : VectorField}
    (Ct : Field P D.T correctorT)
    (hCt : TimeDerivative D.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P D.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve D)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, EulerPacketProfileRecursion.highForce O p a (t,(x,θ))) = 0 :=
  F.highForce_mean_zero C hp D.T_pos Ct hCt pressure
    (F.meanResultField D C (by omega) Ct hCt pressure hmean)
    (F.meanResult_angleIndependent D C (by omega) Ct hCt pressure hmean) t x

end EulerPacketCylinderField
