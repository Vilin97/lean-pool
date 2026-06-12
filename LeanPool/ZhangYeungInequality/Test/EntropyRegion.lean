/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.EntropyRegion
import LeanPool.ZhangYeungInequality.Theorem4

/-!
# LeanPool.ZhangYeungInequality.Test.EntropyRegion

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.EntropyRegion`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open scoped Topology
open ZhangYeung
open scoped ZhangYeungPFR

universe u

section EntropyFunction

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin n, Ω → S i) (μ : Measure Ω) :
    entropyFnN X μ = fun α : Finset (Fin n) => H[(fun ω : Ω => fun i : α => X i.1 ω); μ] :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) :
    entropyFn X μ = entropyFnN X μ :=
  rfl

end EntropyFunction

section Regions

example (n : ℕ) : shannonRegionN n = {F | shannonConeN F} :=
  rfl

example (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  entropyRegionN.{u} n

example (n : ℕ) :
    almostEntropicRegionN.{u} n = closure (entropyRegionN.{u} n) :=
  rfl

example
    {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} {S : Fin n → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Fintype (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    (X : ∀ i : Fin n, Ω → S i) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropyFnN X μ ∈ entropyRegionN.{u} n := by
  exact
    ⟨Ω, inferInstance, μ, inferInstance, S, inferInstance, inferInstance,
      inferInstance, X, hX, rfl⟩

example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn = fun F α => F (α.map (Fin.castLEEmb hn)) :=
  rfl

example (F : Finset (Fin 4) → ℝ) :
    shannonConeN F ↔ shannonCone F :=
  Iff.rfl

end Regions

section Restriction

example {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn (FWitnessN hn) = FWitness :=
  restrictFirstFour_witness_n hn

end Restriction

end ZhangYeungTest
