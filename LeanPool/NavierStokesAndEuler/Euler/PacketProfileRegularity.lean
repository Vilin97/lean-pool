/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPrefixLocality
import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly

/-! Genuine regularity and locality data carried by each recursively constructed profile. -/

@[expose] public section


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

/-- Profile regularity data, collecting `high`, `mean`, `corrector`, `pressure`, `highT`,
`meanT` and their compatibility conditions. -/
structure ProfileRegularity (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
    (S : Set Space) (a : Profile) where
  /-- High-frequency field of `ProfileRegularity`, of type `Field P T a.high`. -/
  high : Field P T a.high
  /-- Mean field of `ProfileRegularity`, of type `Field P T a.mean`. -/
  mean : Field P T a.mean
  /-- Correction field of `ProfileRegularity`, of type `Field P T a.corrector`. -/
  corrector : Field P T a.corrector
  /-- Pressure field of `ProfileRegularity`, of type `Field P T (pressureGradient
  a.highPressure)`. -/
  pressure : Field P T (pressureGradient a.highPressure)
  /-- High T of `ProfileRegularity`, of type `VectorField`. -/
  highT : VectorField
  /-- Mean T of `ProfileRegularity`, of type `VectorField`. -/
  meanT : VectorField
  /-- Corrector T of `ProfileRegularity`, of type `VectorField`. -/
  correctorT : VectorField
  /-- High derivative of `ProfileRegularity`, of type `Field P T highT`. -/
  highDerivative : Field P T highT
  /-- Mean derivative of `ProfileRegularity`, of type `Field P T meanT`. -/
  meanDerivative : Field P T meanT
  /-- Corrector derivative of `ProfileRegularity`, of type `Field P T correctorT`. -/
  correctorDerivative : Field P T correctorT
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

/-- Congr, given by `h ▸ G`. -/
def congr (G : ProfileRegularity P T hT S a) (h : a = b) : ProfileRegularity P T hT S b := h ▸ G

/-- Zero, bundling `high`, `mean`, `corrector`, `pressure` and the required compatibility
proofs. -/
def zero (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T) (S : Set Space) :
    ProfileRegularity P T hT S (0 : Profile) where
  high := Field.zero P T
  mean := Field.zero P T
  corrector := Field.zero P T
  pressure := (Field.zero P T).congr (fun t x θ => by
    change pressureGradient (0 : ScalarField) (t,(x,θ)) = 0
    simp [pressureGradient,pressureJet_zero])
  highT := 0
  meanT := 0
  correctorT := 0
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

/-- Prefix fields, bundling `high`, `mean`, `corrector`. -/
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
