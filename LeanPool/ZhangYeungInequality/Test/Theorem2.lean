/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/
module

public import LeanPool.ZhangYeungInequality.Theorem2

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Basic

/-!
# LeanPool.ZhangYeungInequality.Test.Theorem2

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.Theorem2`.
-/

@[expose] public section

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

universe u

section Signature

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Pinned signature: re-state `theorem2` verbatim. This guards against silent
drifts in the hypothesis shape (eq. 16) or the conclusion shape (eq. 17) as the
proof evolves. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ h₁ h₂

/- Downstream API usage: from Theorem 2 plus the extra vanishing hypothesis
`I[Z : U | ⟨X, Y⟩; μ] = 0`, deduce `I[X : Y | ⟨Z, U⟩; μ] ≤ I[X : Y | U; μ]`.
This closes by applying `theorem2` as a black box and then combining the
resulting inequality with `h₃` via `linarith`. It exercises the theorem's role
as a pluggable inequality in a larger Shannon chase. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0)
    (h₃ : I[Z : U|⟨X, Y⟩;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[X : Y | U; μ] := by
  have h := theorem2 hX hY hZ hU μ h₁ h₂
  linarith [h, h₃]

/- `X ↔ Y` swap via `mutualInfo_comm` and `condMutualInfo_comm`: a caller whose
hypotheses are stated as `I[Y : X; μ] = 0` and `I[Y : X | Z; μ] = 0` -- the
syntactic commute of the paper's eq. (16) -- still recovers the conclusion by
rebasing through the commutation lemmas before calling `theorem2`. This
exercises the theorem's interplay with the commutative structure of mutual
information. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[Y : X; μ] = 0)
    (h₂ : I[Y : X|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ ((mutualInfo_comm hY hX μ).symm.trans h₁)
    ((condMutualInfo_comm hY hX Z μ).symm.trans h₂)

end Signature

section ConcreteFintype

/- Smoke test: the theorem statement elaborates under concrete `Fin n` codomains
without any explicit instance-class plumbing. This checks that the default
`Finite`/`MeasurableSpace`/`MeasurableSingletonClass` instances on `Fin n` are
found by instance search in the theorem's hypothesis shape. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 3} {Z : Ω → Fin 4} {U : Ω → Fin 5}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ h₁ h₂

end ConcreteFintype

end ZhangYeungTest
