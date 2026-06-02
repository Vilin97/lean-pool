/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Delta

/-!
# LeanPool.ZhangYeungInequality.Test.Delta

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.Delta`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

section PureAlgebra

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = I[Z : U; μ] - I[Z : U|X;μ] - I[Z : U|Y;μ] := by
  simpa using delta_def Z U X Y μ

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta Z U Y X μ := by
  simpa using delta_comm_cond Z U X Y μ

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (μ : Measure Ω) :
    delta Z U X X μ = I[Z : U; μ] - 2 * I[Z : U|X;μ] := by
  simpa using delta_self Z U X μ

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    (2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
          + I[Z : U|X;μ] - I[Z : U|Y;μ]) ↔
      (2 * I[Z : U; μ] - 3 * I[Z : U|X;μ] - I[Z : U|Y;μ]
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]) := by
  simpa using delta_form21_iff Z U X Y μ

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    (2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
          - I[Z : U|X;μ] + I[Z : U|Y;μ]) ↔
      (2 * I[Z : U; μ] - I[Z : U|X;μ] - 3 * I[Z : U|Y;μ]
        ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  simpa using delta_form22_iff Z U X Y μ

example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω)
    (h21 : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Z : U|X;μ] - I[Z : U|Y;μ])
    (h22 : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ] - I[Z : U|X;μ] + I[Z : U|Y;μ]) :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  apply (delta_form23_iff Z U X Y μ).mp
  exact delta_form23_of_form21_form22 h21 h22

end PureAlgebra

section FiniteAlphabet

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

example {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta U Z X Y μ := by
  simpa using delta_comm_main hZ hU μ

example {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = (H[Z; μ] + H[U; μ] - H[⟨Z, U⟩; μ])
        - (H[Z | X; μ] + H[U | X; μ] - H[⟨Z, U⟩ | X; μ])
        - (H[Z | Y; μ] + H[U | Y; μ] - H[⟨Z, U⟩ | Y; μ]) := by
  simpa using delta_eq_entropy hZ hU hX hY μ

example {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ ≤ I[Z : U; μ] := by
  simpa using delta_le_mutualInfo hZ hU μ

end FiniteAlphabet

end ZhangYeungTest
