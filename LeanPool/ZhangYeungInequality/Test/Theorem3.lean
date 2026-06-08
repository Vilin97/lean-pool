/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Theorem3

/-!
# LeanPool.ZhangYeungInequality.Test.Theorem3

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.Theorem3`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

universe u

section Signatures

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Pinned signature: re-state `zhangYeung` verbatim, pinning the paper's
`(1/2)`-scaled right-hand side and the hypothesis order. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ]) :=
  zhangYeung hX hY hZ hU μ

/- Pinned signature: re-state `zhangYeung_dual` verbatim, pinning the
`X ↔ Y` dual (paper eq. 22) and the sign flips on the two conditional
MI terms. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ]) :=
  zhangYeung_dual hX hY hZ hU μ

/- Pinned signature: re-state `zhangYeung_averaged` verbatim, pinning
the `(1/2)`- and `(1/4)`-scaled averaged symmetric form of paper
eq. (23). -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) :=
  zhangYeung_averaged hX hY hZ hU μ

end Signatures

section IndependentSmokeTest

/- Independent-variable smoke test: if `I[Z : U; μ] = 0` (for example, when
`Z` and `U` are independent under `μ`), then `Δ(Z, U | X, Y) ≤ 0` —
sanity-checking that Theorem 3's bound remains consistent with the simple
bound `Δ ≤ I[Z : U]` from the M1 `delta_le_mutualInfo` lemma. Recoverable
directly from `delta_le_mutualInfo`, independent of the Theorem 3 chase;
kept here to pin the delta-vs-independence interaction the paper's eq. (23)
inherits. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) (hZU : I[Z : U; μ] = 0) :
    delta Z U X Y μ ≤ 0 := by
  have h := delta_le_mutualInfo (X := X) (Y := Y) hZ hU μ
  linarith [hZU]

end IndependentSmokeTest

section AveragedFromAsymmetric

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Theorem-application test: re-derive the averaged form `zhangYeung_averaged`
(paper eq. 23) from the two asymmetric public theorems `zhangYeung` (eq. 21)
and `zhangYeung_dual` (eq. 22) plus the M1 form-conversion machinery. This
cross-checks that `zhangYeung_averaged`'s proof route is reconstructible from
the two asymmetric theorems alone -- if a future refactor deletes
`zhangYeung_averaged`, this example shows callers have a working recipe to
rebuild eq. (23) from the public API. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  have h21 := zhangYeung hX hY hZ hU μ
  have h22 := zhangYeung_dual hX hY hZ hU μ
  have h21' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ] := by linarith
  have h22' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ] := by linarith
  exact (delta_form23_iff Z U X Y μ).mp (delta_form23_of_form21_form22 h21' h22')

end AveragedFromAsymmetric

section DownstreamUsage

/- Downstream-usage example: consume the public `zhangYeung` theorem in a
concrete `Fin 2`-valued setting and scale up to the integer `2 * delta ≤ ...`
bound via `linarith`. Exercises the full M2-to-M3 universe handling
end-to-end (all four codomains bound at a fixed universe via `copyLemma`'s
universe constraint). Analogous to the M2 downstream example at
`ZhangYeungTest/CopyLemma.lean`. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ] := by
  have h := zhangYeung hX hY hZ hU μ
  linarith

end DownstreamUsage

end ZhangYeungTest
