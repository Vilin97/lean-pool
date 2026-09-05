/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Statement.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.Definitions

/-!
# Counting definitions

The normalized slope form of the triple count, the Walsh coefficient of the
derivative image, and the admissible slopes.

The conjecture is stated in `Challenge.lean` in coefficient form, with
coefficients `v₁, v₂, v₁+v₂`.  Dividing through by `v₁` puts it in the slope
form used throughout the proof, indexed by `ρ = v₂/v₁`;
`Statement/CoefficientForm.lean`
relates the two.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `N(ρ) = #{(x,y,z) ∈ Δ³ : x + ρ y + σ z = 0}` with `σ = 1 + ρ`.  This is the
normalised form of the triple count of the conjecture, obtained from the
original `v₁ x + v₂ y + v₃ z = 0` by dividing through by `v₁` and setting
`ρ = v₂/v₁`. -/
def slopeTripleCount (k : ℕ) (ρ : K) : ℕ :=
  (((derivativeImage k K) ×ˢ (derivativeImage k K) ×ˢ (derivativeImage k K)).filter
    (fun p => p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0)).card

/-- The Walsh coefficient `S(a) = ∑_{x ∈ Δ} ψ(a x)`. -/
noncomputable def walshCoefficient (k : ℕ) (ψ : AddChar K ℂ) (a : K) : ℂ :=
  ∑ x ∈ derivativeImage k K, ψ (a * x)

/-- The admissible slopes `ρ ≠ 0, 1`. -/
def AdmissibleSlope (ρ : K) : Prop := ρ ≠ 0 ∧ ρ ≠ 1

/-- The finset of admissible slopes. -/
def slopes (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  Finset.univ.filter (fun r : K => r ≠ 0 ∧ r ≠ 1)

end KasamiCyclicAdditive
