/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownJets
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderAngularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownForce

/-! The literal recursively constructed high forcing has zero angular mean. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerCylinderAngleAverage EulerCylinderSmoothOrbit

variable {P T : ℝ} [Fact (0 < P)]

theorem Field.average_zero_of_raw_integral {raw : VectorField} (G : Field P T raw)
    (h : ∀ (t : Icc (0 : ℝ) T) x, (∫ θ in (0 : ℝ)..P, raw (t, (x, θ))) = 0)
    (t : Icc (0 : ℝ) T) : average P (G.path t) = 0 := by
  apply (pointField_mean_zero_iff P G.path G.orbit t).mpr
  intro x
  convert h t x using 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact (G.raw_eq t x θ).symm

variable {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixFields.highForce_mean_zero (F : PrefixFields P T p a)
    (C : CoefficientData P T O) (hp : 2 ≤ p) (hT : 0 < T)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
    (newMean : Field P T (meanResult O p a).1)
    (hB : ∀ (t : Icc (0 : ℝ) T) x θ,
      (meanResult O p a).1 (t, (x, θ)) = (meanResult O p a).1 (t, (x, 0)))
    (t : Icc (0 : ℝ) T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, EulerPacketProfileRecursion.highForce O p a (t,(x,θ))) = 0 := by
  let K := F.knownForce C (by omega) hT Ct hCt pressure
  let A := SpatialJetField.fastAdvection C.normal
    (SpatialJetField.ofField O.interval newMean)
    (SpatialJetField.ofField O.interval (F.high 1 (by omega)))
  have hK : IntervalIntegrable (fun θ => EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) -
      EulerPacketProfileRecursion.meanForce O p a (t,(x,θ))) volume 0 P := by
    simpa only [EulerPacketProfileRecursion.meanForce,C.period_eq,Pi.sub_apply] using
      ((K.sub K.angleMean).raw_angle_continuous t x).intervalIntegrable 0 P
  have hA : IntervalIntegrable (fun θ => fastAdvection (O.normal (t,(x,θ)))
      (slicedJet O.interval (meanResult O p a).1 (t,(x,θ)))
      (slicedJet O.interval (a 1).high (t,(x,θ)))) volume 0 P :=
    (A.raw_angle_continuous t x).intervalIntegrable 0 P
  change (∫ θ in (0 : ℝ)..P, (EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) -
    EulerPacketProfileRecursion.meanForce O p a (t,(x,θ))) -
      fastAdvection (O.normal (t,(x,θ)))
        (slicedJet O.interval (meanResult O p a).1 (t,(x,θ)))
        (slicedJet O.interval (a 1).high (t,(x,θ)))) = 0
  rw [intervalIntegral.integral_sub hK hA]
  have hm : (∫ θ in (0 : ℝ)..P, EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) -
      EulerPacketProfileRecursion.meanForce O p a (t,(x,θ))) = 0 := by
    simpa only [EulerPacketProfileRecursion.meanForce,C.period_eq,Pi.sub_apply] using
      K.subtract_mean_integral t x
  rw [hm,mean_primary_integral_zero C.normal (F.high 1 (by omega)) O.interval hB t x,sub_self]

end EulerPacketCylinderField
