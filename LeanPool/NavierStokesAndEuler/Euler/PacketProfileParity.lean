/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderForcingParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity
import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly

/-! Joint parity carried by the actual profile fields and their true time derivatives. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

/-- Profile parity data, collecting `high`, `mean`, `corrector`, `pressure`, `highPressure`,
`meanPressure`. -/
structure ProfileParity (T : ℝ) (a : Profile) : Prop where
  high : JointOdd T a.high
  mean : JointOdd T a.mean
  corrector : JointOdd T a.corrector
  pressure : JointOdd T (pressureGradient a.highPressure)
  highPressure : ∀ (t : Icc (0 : ℝ) T) x θ, a.highPressure (t,(-x,-θ)) = a.highPressure (t,(x,θ))
  meanPressure : ∀ (t : Icc (0 : ℝ) T) x θ, a.meanPressure (t,(-x,-θ)) = a.meanPressure (t,(x,θ))

namespace ProfileParity

theorem zero (T : ℝ) : ProfileParity T (0 : Profile) where
  high := JointOdd.zero T
  mean := JointOdd.zero T
  corrector := JointOdd.zero T
  pressure := by
    intro t x θ
    change pressureGradient (0 : ScalarField) (t,(-x,-θ)) =
      -pressureGradient (0 : ScalarField) (t,(x,θ))
    simp [pressureGradient,pressureJet_zero]
  highPressure _ _ _ := rfl
  meanPressure _ _ _ := rfl

theorem prefixOdd {T : ℝ} {p : ℕ} {a : ℕ → Profile}
    (H : ∀ i, i < p → ProfileParity T (a i)) : PrefixOdd T p a where
  high i hi := (H i hi).high
  mean i hi := (H i hi).mean
  corrector i hi := (H i hi).corrector

theorem changeTime {T T' : ℝ} {a : Profile} (H : ProfileParity T a) (h : T = T') :
    ProfileParity T' a := by
  subst T'
  exact H

variable {P T : ℝ} [Fact (0 < P)] {S : Set Space} {a : Profile}
  (hT : 0 < T) (G : ProfileRegularity P T hT.le S a) (H : ProfileParity T a)

include H

theorem highDerivative_odd : JointOdd T G.highT :=
  G.high.timeDerivative_odd G.highDerivative hT G.high_time H.high

theorem meanDerivative_odd : JointOdd T G.meanT :=
  G.mean.timeDerivative_odd G.meanDerivative hT G.mean_time H.mean

theorem correctorDerivative_odd : JointOdd T G.correctorT :=
  G.corrector.timeDerivative_odd G.correctorDerivative hT G.corrector_time H.corrector

end ProfileParity

theorem JointOdd.changeTime {T T' : ℝ} {raw : VectorField} (H : JointOdd T raw) (h : T = T') :
    JointOdd T' raw := by
  subst T'
  exact H

end EulerPacketCylinderField
