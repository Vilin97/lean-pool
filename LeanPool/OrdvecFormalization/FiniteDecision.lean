/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Finite ordered binary decisions

This file contains the combinatorial layer for finite monotone decision rules.
The support is `Fin (n + 1)`, and thresholds are encoded by a cut in
`Fin (n + 2)` so that both degenerate cuts are represented.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- The ordered finite support with `n + 1` points. -/
abbrev Support (n : ℕ) := Fin (n + 1)

/-- A strictly positive probability mass function on the finite support. -/
structure PosPMF (n : ℕ) where
  /-- The probability mass at each support point. -/
  mass : Support n → ℝ≥0
  /-- Every support point has strictly positive mass. -/
  pos : ∀ i, 0 < mass i
  /-- The mass function is normalized. -/
  sum_one : Finset.univ.sum mass = 1

/-- A prior probability on `H₁`, bundled with the proof that it is at most one. -/
structure Prior where
  /-- The prior probability of `H₁`. -/
  prob : ℝ≥0
  /-- The prior probability is at most one. -/
  le_one : prob ≤ 1

/--
False-decision costs for deterministic binary admission rules.

`falseAccept` is paid when the rule admits under `H₀`; `falseReject` is paid
when the rule rejects under `H₁`.
-/
structure DecisionCosts where
  /-- Cost of admitting a false candidate under `H₀`. -/
  falseAccept : ℝ≥0
  /-- Cost of rejecting a true candidate under `H₁`. -/
  falseReject : ℝ≥0

namespace Prior

/-- The prior probability on `H₀`. -/
def compl (prior : Prior) : ℝ≥0 :=
  1 - prior.prob

@[simp]
theorem compl_eq (prior : Prior) : prior.compl = 1 - prior.prob :=
  rfl

end Prior

/--
The threshold set associated to a cut.

`cut = 0` accepts every support point, while `cut = n + 1` accepts none.
-/
def thresholdSet (n : ℕ) (cut : Fin (n + 2)) : Set (Support n) :=
  {x | cut.val ≤ x.val}

/-- Threshold sets are upper sets in the finite support order. -/
theorem isUpperSet_thresholdSet (n : ℕ) (cut : Fin (n + 2)) :
    IsUpperSet (thresholdSet n cut) := by
  intro x y hxy hx
  exact le_trans hx (Fin.le_iff_val_le_val.mp hxy)

/-- Any upper set in the finite support is represented by a threshold cut. -/
theorem exists_threshold_of_isUpperSet (n : ℕ) (s : Set (Support n))
    (hs : IsUpperSet s) :
    ∃ cut : Fin (n + 2), s = thresholdSet n cut := by
  rcases hs.eq_empty_or_Ici with h | ⟨a, ha⟩
  · refine ⟨Fin.last (n + 1), ?_⟩
    rw [h]
    ext x
    simp [thresholdSet, Fin.val_last, not_le_of_gt x.isLt]
  · refine ⟨Fin.castSucc a, ?_⟩
    rw [ha]
    ext x
    change a ≤ x ↔ (Fin.castSucc a).val ≤ x.val
    exact Fin.le_iff_val_le_val

/-- A monotone predicate on the finite support is represented by a threshold cut. -/
theorem exists_threshold_of_monotone_pred (n : ℕ) (P : Support n → Prop)
    (hmon : Monotone P) :
    ∃ cut : Fin (n + 2), ∀ x : Support n, P x ↔ x ∈ thresholdSet n cut := by
  have hs : IsUpperSet {x : Support n | P x} := isUpperSet_setOf.mpr hmon
  rcases exists_threshold_of_isUpperSet n {x : Support n | P x} hs with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro x
  simpa using congrArg (fun t : Set (Support n) => x ∈ t) hcut

end OrdvecFormalization
