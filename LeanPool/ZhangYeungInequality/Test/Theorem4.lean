/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Theorem4

/-!
# LeanPool.ZhangYeungInequality.Test.Theorem4

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.Theorem4`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

universe u

/-! ### Signature pins for the set-function calculus and cone predicates -/

section SetFunctionCalculus

/- Pinned signature: `IF` is a three-argument real-valued function of `F`
and two `Finset (Fin 4)` arguments. -/
example (F : Finset (Fin 4) → ℝ) (α β : Finset (Fin 4)) :
    IF F α β = F α + F β - F (α ∪ β) :=
  rfl

/- Pinned signature: `condIF` is a four-argument real-valued function of `F`
and three `Finset (Fin 4)` arguments. -/
example (F : Finset (Fin 4) → ℝ) (α β γ : Finset (Fin 4)) :
    condIF F α β γ = F (α ∪ γ) + F (β ∪ γ) - F (α ∪ β ∪ γ) - F γ :=
  rfl

/- Pinned signature: `deltaF` is a five-argument real-valued function of `F`
and four `Fin 4` indices. -/
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    deltaF F i j k l = IF F {i} {j} - condIF F {i} {j} {k} - condIF F {i} {j} {l} :=
  rfl

end SetFunctionCalculus

section Predicates

/- Pinned signature: `shannonCone` is a three-clause conjunction (zero, monotone, submodular). -/
example (F : Finset (Fin 4) → ℝ) :
    shannonCone F ↔
      F ∅ = 0 ∧
      (∀ α β : Finset (Fin 4), α ⊆ β → F α ≤ F β) ∧
      (∀ α β : Finset (Fin 4), F (α ∪ β) + F (α ∩ β) ≤ F α + F β) :=
  Iff.rfl

/- Pinned signature: `zhangYeungAt F i j k l` is paper eq. (21) at the labeling `(i, j, k, l)`. -/
example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    zhangYeungAt F i j k l ↔
      deltaF F i j k l ≤ (1 / 2) * (IF F {k} {l} + IF F {k} ({i} ∪ {j})
        + condIF F {i} {j} {k} - condIF F {i} {j} {l}) :=
  Iff.rfl

/- Pinned signature: `zhangYeungHolds F` quantifies over `Equiv.Perm (Fin 4)`. -/
example (F : Finset (Fin 4) → ℝ) :
    zhangYeungHolds F ↔ ∀ π : Equiv.Perm (Fin 4), zhangYeungAt F (π 0) (π 1) (π 2) (π 3) :=
  Iff.rfl

end Predicates

/-! ### Witness signature pins -/

section Witness

/- Pinned signature: `FWitnessℚ` is a `Finset (Fin 4) → ℚ` five-case function. -/
example : FWitnessℚ (∅ : Finset (Fin 4)) = 0 := rfl

/- Pinned signature: `FWitness` is the `ℝ`-cast of `FWitnessℚ`. -/
example (S : Finset (Fin 4)) : FWitness S = (FWitnessℚ S : ℝ) :=
  FWitness_eq_cast S

end Witness

/-! ### Main statement pins -/

section MainStatements

example : shannonCone FWitness := shannonCone_of_witness

example : ¬ zhangYeungHolds FWitness := not_zhangYeungHolds_witness

example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete

example
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) :=
  zhangYeungHolds_of_entropy hX μ

example :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ :=
  theorem4_finite

example :
    ∃ F : Finset (Fin 4) → ℝ,
      F ∈ shannonRegionN 4 ∧ F ∉ almostEntropicRegionN.{u} 4 :=
  theorem4.{u}

end MainStatements

/-! ### Concrete evaluation of the `ℚ`-valued witness

The witness values at the 16 subsets of `Fin 4`, as a compile-time regression
against accidental edits to `FWitnessℚ`. Each value follows the paper's
table on lines 368-377 at `a = 1`. -/

section WitnessEvaluation

example : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({2} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({3} : Finset (Fin 4)) = 2 := by decide
example : FWitnessℚ ({0, 1} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 2} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({0, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({1, 2} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({1, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({2, 3} : Finset (Fin 4)) = 3 := by decide
example : FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 2, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({1, 2, 3} : Finset (Fin 4)) = 4 := by decide
example : FWitnessℚ ({0, 1, 2, 3} : Finset (Fin 4)) = 4 := by decide

end WitnessEvaluation

/-! ### Downstream usage

`shannon_incomplete` composes Parts (a) and (b) into a single existential;
`theorem4_finite` pins the literal non-entropic witness theorem; `theorem4`
pins the exact closure statement from the paper. -/

section DownstreamUsage

/- Extracting the separating set function from `shannon_incomplete`. -/
example : ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧ ¬ zhangYeungHolds F :=
  shannon_incomplete

/- From `zhangYeungHolds_of_entropy`, every permutation of a four-variable
entropy family satisfies `zhangYeungAt`. Exercising the composition on the
identity permutation pins the bridge's downstream shape. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {X : ∀ _ : Fin 4, Ω → Fin 2} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungAt (entropyFn X μ) 0 1 2 3 :=
  zhangYeungHolds_of_entropy hX μ (Equiv.refl _)

end DownstreamUsage

/-! ### Stretch: closure form pins -/

section ClosureStretch

open scoped Topology

/- Pinned signature: `zhangYeungHolds_of_tendsto` closes the Zhang-Yeung cone
under pointwise convergence. -/
example {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F :=
  zhangYeungHolds_of_tendsto h_seq h_lim

/- Pinned signature: `theorem4_seqClosure` shows `FWitness` is not even a
pointwise limit of `tildeΓ_4` members. -/
example :
    ∃ F : Finset (Fin 4) → ℝ, shannonCone F ∧
      ∀ (F_seq : ℕ → Finset (Fin 4) → ℝ),
        (∀ k, zhangYeungHolds (F_seq k)) →
        (∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) →
        False :=
  theorem4_seqClosure

end ClosureStretch

/-! ### Stretch: `n ≥ 4` extension pins -/

section NExtensionStretch

/- Pinned signature: `shannon_incomplete_ge_four` states the paper's `n ≥ 4`
separation in the `Fin n`-indexed cone predicates. -/
example (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ, shannonConeN F ∧ ¬ zhangYeungHoldsN F :=
  shannon_incomplete_ge_four n hn

/- Pinned signature: `theorem4_ge_four` states the exact paper-level `n ≥ 4`
closure separation. -/
example (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ,
      F ∈ shannonRegionN n ∧ F ∉ almostEntropicRegionN.{u} n :=
  theorem4_ge_four.{u} n hn

/- Pinned signature: `FWitnessN` is the lifted witness. -/
example {n : ℕ} (hn : 4 ≤ n) : shannonConeN (FWitnessN hn) :=
  shannonCone_of_witness_n hn

example {n : ℕ} (hn : 4 ≤ n) : ¬ zhangYeungHoldsN (FWitnessN hn) :=
  not_zhangYeungHolds_witness_n hn

/- Pinned signature: at `n = 4`, the generic predicates coincide with the
Fin-4 predicates by definition; checked here against `shannonCone` and an
arbitrary permutation's `zhangYeungAt` form. -/
example (F : Finset (Fin 4) → ℝ) :
    shannonConeN F ↔ shannonCone F := Iff.rfl

example (F : Finset (Fin 4) → ℝ) (i j k l : Fin 4) :
    zhangYeungAtN F i j k l ↔ zhangYeungAt F i j k l := Iff.rfl

end NExtensionStretch

end ZhangYeungTest
