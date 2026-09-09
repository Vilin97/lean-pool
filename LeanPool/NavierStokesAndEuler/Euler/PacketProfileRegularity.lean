/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly

@[expose] public section

/-! Genuine regularity and locality data carried by each recursively constructed profile. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

theorem Field.zero_time (hT : 0 ≤ T) :
    TimeDerivative hT (Field.zero P T) (Field.zero P T) := by
  intro t
  exact hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : LiftL2 P)

theorem raw_zero_changeTime {raw : VectorField} {T' : ℝ} (h : T = T') (S : Set Space)
    (hs : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0) :
    ∀ (t : Icc (0 : ℝ) T') x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0 := by
  subst T'
  exact hs

structure ProfileRegularity (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
    (S : Set Space) (a : Profile) where
  high : Field P T a.high
  mean : Field P T a.mean
  corrector : Field P T a.corrector
  pressure : Field P T (pressureGradient a.highPressure)
  high_t : VectorField
  mean_t : VectorField
  corrector_t : VectorField
  highDerivative : Field P T high_t
  meanDerivative : Field P T mean_t
  correctorDerivative : Field P T corrector_t
  high_time : TimeDerivative hT high highDerivative
  mean_time : TimeDerivative hT mean meanDerivative
  corrector_time : TimeDerivative hT corrector correctorDerivative
  high_zero : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, a.high (t,(x,θ)) = 0
  corrector_zero : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, a.corrector (t,(x,θ)) = 0
  pressure_zero : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ,
    pressureGradient a.highPressure (t,(x,θ)) = 0
  mean_angle : ∀ (t : Icc (0 : ℝ) T) x θ, a.mean (t,(x,θ)) = a.mean (t,(x,0))

namespace ProfileRegularity

variable {hT : 0 ≤ T} {S : Set Space} {a b : Profile}

def congr (G : ProfileRegularity P T hT S a) (h : a = b) : ProfileRegularity P T hT S b := h ▸ G

def zero (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T) (S : Set Space) :
    ProfileRegularity P T hT S (0 : Profile) where
  high := Field.zero P T
  mean := Field.zero P T
  corrector := Field.zero P T
  pressure := (Field.zero P T).congr (fun t x θ => by
    change pressureGradient (0 : ScalarField) (t,(x,θ)) = 0
    simp [pressureGradient,pressureJet_zero])
  high_t := 0
  mean_t := 0
  corrector_t := 0
  highDerivative := Field.zero P T
  meanDerivative := Field.zero P T
  correctorDerivative := Field.zero P T
  high_time := Field.zero_time hT
  mean_time := Field.zero_time hT
  corrector_time := Field.zero_time hT
  high_zero _ _ _ _ := rfl
  corrector_zero _ _ _ _ := rfl
  pressure_zero t x _ θ := by
    change pressureGradient (0 : ScalarField) (t,(x,θ)) = 0
    simp [pressureGradient,pressureJet_zero]
  mean_angle _ _ _ := rfl

def prefixFields {p : ℕ} {a : ℕ → Profile}
    (G : ∀ i, i < p → ProfileRegularity P T hT S (a i)) : PrefixFields P T p a where
  high i hi := (G i hi).high
  mean i hi := (G i hi).mean
  corrector i hi := (G i hi).corrector

theorem prefixLocality {p : ℕ} {a : ℕ → Profile}
    (G : ∀ i, i < p → ProfileRegularity P T hT S (a i)) : PrefixLocality T p a S where
  high_zero i hi := (G i hi).high_zero
  corrector_zero i hi := (G i hi).corrector_zero
  mean_angle i hi := (G i hi).mean_angle

end ProfileRegularity
end EulerPacketCylinderField
