/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderForcingParity
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketReflection
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanStep

/-! The actual mean step and literal high-force expression preserve joint odd parity. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

/-- Coefficient even data, collecting `inverse`, `strain`, `normal`. -/
structure CoefficientEven (T : ℝ) (O : Operators) : Prop where
  inverse : ∀ (t : Icc (0 : ℝ) T) x θ, O.inverseFrame (t,(-x,-θ)) = O.inverseFrame (t,(x,θ))
  strain : ∀ (t : Icc (0 : ℝ) T) x θ, O.strain (t,(-x,-θ)) = O.strain (t,(x,θ))
  normal : ∀ (t : Icc (0 : ℝ) T) x θ, O.normal (t,(-x,-θ)) = O.normal (t,(x,θ))

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixFields.meanForce_odd (F : PrefixFields P T p a) (H : PrefixOdd T p a)
    (C : CoefficientData P T O) (E : CoefficientEven T O) (hp : 1 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
    (hpressure : JointOdd T (pressureGradient (a (p - 1)).highPressure)) :
    JointOdd T (EulerPacketProfileRecursion.meanForce O p a) := by
  have hk := F.knownForce_odd H C hp hT Ct hCt hpressure E.inverse E.strain E.normal
  have hm := (F.knownForce C hp hT Ct hCt pressure).angleMean_odd hk
  simpa only [EulerPacketProfileRecursion.meanForce,C.period_eq] using hm

theorem PrefixFields.highForce_odd (F : PrefixFields P T p a) (H : PrefixOdd T p a)
    (C : CoefficientData P T O) (E : CoefficientEven T O) (hp : 2 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
    (hpressure : JointOdd T (pressureGradient (a (p - 1)).highPressure))
    (hnewMean : JointOdd T (meanResult O p a).1) :
    JointOdd T (EulerPacketProfileRecursion.highForce O p a) := by
  have hk := F.knownForce_odd H C (by omega) hT Ct hCt hpressure E.inverse E.strain E.normal
  have hm := F.meanForce_odd H C E (by omega) hT Ct hCt pressure hpressure
  have hB : JointOdd T (fun z => (slicedJet O.interval (meanResult O p a).1 z).1) := hnewMean
  have hA : JointOdd T (fun z => (slicedJet O.interval (a 1).high z).1) := H.high 1 (by omega)
  have ha := (SpatialJetField.ofField O.interval (F.high 1 (by omega))).fastAdvection_odd
    (J := slicedJet O.interval (meanResult O p a).1) O.normal E.normal hB hA
  exact (hk.sub hm).sub ha

theorem PrefixFields.actualMean_odd (M : EulerMeanPacketProvider.Data)
    (F : PrefixFields P M.T p a) (H : PrefixOdd M.T p a)
    (C : CoefficientData P M.T O) (E : CoefficientEven M.T O)
    (hM : EulerMeanPacketProvider.EvenData M) (hp : 1 ≤ p)
    {correctorT : VectorField} (Ct : Field P M.T correctorT)
    (hCt : TimeDerivative M.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P M.T (pressureGradient (a (p - 1)).highPressure))
    (hpressure : JointOdd M.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M) :
    JointOdd M.T (meanResult O p a).1 := by
  have hf := F.meanForce_odd H C E hp M.T_pos Ct hCt pressure hpressure
  intro t x θ
  rw [meanResult,hmean]
  exact EulerMeanPacketProvider.meanSolve_odd M hM _ ⟨F.meanForcing M C hp Ct hCt pressure⟩
    (fun s y => by simpa only [neg_zero] using hf s y 0) t x θ

theorem PrefixFields.actualHighForce_odd (M : EulerMeanPacketProvider.Data)
    (F : PrefixFields P M.T p a) (H : PrefixOdd M.T p a)
    (C : CoefficientData P M.T O) (E : CoefficientEven M.T O)
    (hM : EulerMeanPacketProvider.EvenData M) (hp : 2 ≤ p)
    {correctorT : VectorField} (Ct : Field P M.T correctorT)
    (hCt : TimeDerivative M.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P M.T (pressureGradient (a (p - 1)).highPressure))
    (hpressure : JointOdd M.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M) :
    JointOdd M.T (EulerPacketProfileRecursion.highForce O p a) :=
  F.highForce_odd H C E hp M.T_pos Ct hCt pressure hpressure
    (F.actualMean_odd M H C E hM (by omega) Ct hCt pressure hpressure hmean)

end EulerPacketCylinderField
