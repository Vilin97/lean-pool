/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set Complex
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasureSpace ι where
  volume := Measure.count

variable {r : ℕ}

/-- The `k` tuple `j` consists of all distinct indices. -/
def all_distinct (k : ℕ) (j : Fin k → ι) := ∀ i i', i ≠ i' → j i ≠ j i'

/-- The product function `x ↦ ∏ i < r, f (j i) x * ∏ i ≥ r, conj f (j i) x` -/
abbrev cprod (f : ι → α → ℂ) {r : ℕ} (j : Fin (2 * r) → ι) :=
  fun x ↦ ∏ i : Fin (2 * r), if i < r then f (j i) x else star (f (j i) x)

/-- Type IV superorthogonality of a family of functions -/
structure TypeIVSuperorthogonal (f : ι → α → ℂ) (r : ℕ) : Prop where
  measurable : ∀ j, Measurable (f j)
  integrable_cprod : ∀ j : Fin (2 * r) → ι, all_distinct (2 * r) j → Integrable (cprod f j) μ
  superorthogonal : ∀ j : Fin (2 * r) → ι, all_distinct (2 * r) j → ∫ x, cprod f j x ∂μ = 0

/-- Square-function associated with the family of functions `f` -/
def sqfct (f : ι → α → ℂ) (x : α) := (∑' j, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹

section PointwiseEstimate

/-- Sum of a sequence. -/
abbrev s (a : ι → ℂ) := ∑' j, a j

/-- Set of  `k` tuples of all distinct indices. -/
abbrev set_all_distinct (k : ℕ) : Set (Fin k → ι) := fun j ↦ all_distinct k j

variable {k : ℕ}

/-- Auxiliary quantity Q from the pointwise estimate -/
abbrev Q (a : Fin k → ι → ℂ) := ∑' j : Fin k → ι,
  indicator (set_all_distinct k) (fun j ↦ ∏ i, a i (j i)) j

/-- Auxiliary quantity A from the pointwise estimate -/
abbrev A (hk : 2 ≤ k) (a : Fin k → ι → ℂ) := ENNReal.ofReal <|
  (Finset.univ.image fun i ↦ ‖s (a i)‖).max' ⟨‖s (a ⟨0, zero_lt_of_lt hk⟩)‖, by simp⟩

/-- Auxiliary quantity B from the pointwise estimate -/
abbrev B (hk : 2 ≤ k) (a : Fin k → ι → ℂ) := (Finset.univ.image
  fun i ↦ eLpNorm (a i) 2).max' ⟨eLpNorm (a ⟨0, zero_lt_of_lt hk⟩) 2, by simp⟩

end PointwiseEstimate

/-- Constant in the main theorem on Type IV superorthogonality -/
def C (r : ℕ) : ENNReal := match r with
  | 1 => 1
  | r => 2 ^ ((2: ℝ)⁻¹) * ((2 * r)! - 1) ^ ((2 : ℝ)⁻¹)

end Superorthogonal

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
