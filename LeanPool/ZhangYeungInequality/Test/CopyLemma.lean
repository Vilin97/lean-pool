/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.CopyLemma

/-!
# LeanPool.ZhangYeungInequality.Test.CopyLemma

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.CopyLemma`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

universe u

section Signature

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

/- Pinned signature: re-state `copyLemma` verbatim, exercising the six
projected random variables, the two `IdentDistrib` marginal-equality facts,
and the `CondIndepFun` conditional-independence fact. This guards against
silent drifts in the existential shape or the hypothesis order. -/
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν :=
  copyLemma hX hY hZ hU μ

end Signature

section LemmaTwoFormA

variable {Ω : Type*} [MeasurableSpace Ω]
  {α β γ δ : Type*}
  [Finite α] [Finite β] [Finite γ] [Finite δ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]

/- Pinned signature: re-state `delta_of_condMI_vanishes_eq` verbatim. Pins the
hypothesis order, the vanishing-CMI shape `I[A : D | ⟨B, C⟩; ν] = 0`, and the
right-hand-side argument order `delta B C A D` vs `I[A : D] - I[A : D | B] -
I[A : D | C] - I[B : C | ⟨A, D⟩]`. -/
example
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D|⟨B, C⟩;ν] = 0) :
    delta B C A D ν
      = I[A : D; ν] - I[A : D|B;ν] - I[A : D|C;ν]
        - I[B : C|⟨A, D⟩;ν] :=
  delta_of_condMI_vanishes_eq hA hB hC hD ν hVanish

end LemmaTwoFormA

section Consequences

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}

/- Pinned signature: `copyLemma_delta_identity_Y₁` (Form B, primary). -/
example
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' Y₁ ν
      = I[X' : Y₁; ν] - I[X' : Y₁|Z';ν] - I[X' : Y₁|U';ν]
        - I[Z' : U'|⟨X', Y₁⟩;ν] :=
  copyLemma_delta_identity_Y₁ hX' hY₁ hZ' hU' hCond

/- Pinned signature: `copyLemma_delta_identity_X_X₁` (Form B, symmetric). -/
example
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' X₁ ν
      = I[X' : X₁; ν] - I[X' : X₁|Z';ν] - I[X' : X₁|U';ν]
        - I[Z' : U'|⟨X', X₁⟩;ν] :=
  copyLemma_delta_identity_X_X₁ hX' hX₁ hZ' hU' hCond

/- Pinned signature: `copyLemma_delta_transport_Y_to_Y₁`. -/
example
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X Y μ = delta Z' U' X' Y₁ ν :=
  copyLemma_delta_transport_Y_to_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond

/- Pinned signature: `copyLemma_delta_transport_X_to_X₁`. -/
example
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X X μ = delta Z' U' X' X₁ ν :=
  copyLemma_delta_transport_X_to_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond

/- Pinned signature: `copyLemma_delta_le_mutualInfo_Y₁` (primary inequality). -/
example
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z U X Y μ ≤ I[X' : Y₁; ν] :=
  copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond

/- Pinned signature: `copyLemma_delta_le_mutualInfo_X_X₁` (symmetric inequality). -/
example
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[Z : U; μ] - 2 * I[Z : U|X;μ] ≤ I[X' : X₁; ν] :=
  copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond

end Consequences

section DownstreamUsage

/- Downstream-usage example: given four discrete random variables on an ambient
probability space, apply `copyLemma` to produce the two copies, then
`copyLemma_delta_le_mutualInfo_Y₁` to close a `delta ≤ I[X' : Y₁]` inequality.
Exercises the full M2-to-M3 flow in one shot. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → Fin 2) (Y₁ : Ω' → Fin 2),
      IsProbabilityMeasure ν ∧ delta Z U X Y μ ≤ I[X' : Y₁; ν] := by
  obtain ⟨Ω', _, ν, X', _, _, Y₁, Z', U',
      hν, hX', hY', hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  exact ⟨Ω', _, ν, X', Y₁, hν,
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond⟩

/- Shannon-chase smoke test: combine the two copy-lemma inequality corollaries
in one concrete `Fin n`-valued example. After `copyLemma` supplies the copies,
`copyLemma_delta_le_mutualInfo_Y₁` gives
`delta Z U X Y μ ≤ I[X' : Y₁; ν]` and
`copyLemma_delta_le_mutualInfo_X_X₁` gives
`I[Z : U; μ] - 2 * I[Z : U | X; μ] ≤ I[X' : X₁; ν]`; rewriting `delta` via
`delta_def` and closing with `linarith` produces the summed bound
`2 * I[Z : U; μ] - 3 * I[Z : U | X; μ] - I[Z : U | Y; μ] ≤
  I[X' : Y₁; ν] + I[X' : X₁; ν]`.

This exercises the two M2 inequality corollaries in a single Lean proof: no
`delta_form21_iff` and no extra Shannon-chase slack term, just the direct sum
once `delta` is unfolded. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → Fin 2) (X₁ : Ω' → Fin 2) (Y₁ : Ω' → Fin 2),
      2 * I[Z : U; μ] - 3 * I[Z : U|X;μ] - I[Z : U|Y;μ]
        ≤ I[X' : Y₁; ν] + I[X' : X₁; ν] := by
  obtain ⟨Ω', _, ν, X', _, X₁, Y₁, Z', U',
      hν, hX', hY', hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  refine ⟨Ω', _, ν, X', X₁, Y₁, ?_⟩
  have h1 : delta Z U X Y μ ≤ I[X' : Y₁; ν] :=
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
  have h2 : I[Z : U; μ] - 2 * I[Z : U|X;μ] ≤ I[X' : X₁; ν] :=
    copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
  rw [delta_def] at h1
  linarith

end DownstreamUsage

end ZhangYeungTest
