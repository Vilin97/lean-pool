/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib

/-!
# `NRR.EMP.WeightSpace` — finite‑dimensional algebra of normalized weights

This module packages the **pure, finite‑dimensional linear algebra** of weight vectors
`w : Fin n → ℝ`, independent of any optimal‑transport / power‑diagram machinery. It provides
the vocabulary used to pin down the additive‑constant freedom in equal‑area weights:

## Definitions

* `EMP.weightSum w = ∑ i, w i` — the total of a weight vector.
* `EMP.WeightNormalized w` — the affine normalization `EMP.weightSum w = 0` (equivalently
 `∑ i, w i = 0`).
* `EMP.weightMean w = EMP.weightSum w / n` — the arithmetic mean of a weight vector.
* `EMP.normalizeWeight w = fun i => w i - EMP.weightMean w` — subtract the mean, producing a
 zero‑sum weight vector.

## Main results

* `EMP.weightSum_zero`, `EMP.weightSum_add_const` — basic finite‑sum algebra.
* `EMP.WeightNormalized_normalizeWeight` — mean subtraction produces a normalized weight
 (for `0 < n`).
* `EMP.normalizeWeight_eq_sub_mean` — the definitional unfolding of `normalizeWeight`.
* `EMP.normalizeWeight_eq_self_of_normalized` — normalization is idempotent on already
 normalized weights.

This file must not depend on optimal transport; it imports only `Mathlib`.
-/

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Weight sum.** The total `∑ i, w i` of a weight vector. -/
noncomputable def weightSum (w : Fin n → ℝ) : ℝ :=
  ∑ i, w i

/-- **Normalized weights.** The affine normalization `∑ i, w i = 0`, used to remove the
additive‑constant freedom in the weights. -/
def WeightNormalized (w : Fin n → ℝ) : Prop :=
  EMP.weightSum w = 0

/-- **Weight mean.** The arithmetic mean `(∑ i, w i) / n` of a weight vector. -/
noncomputable def weightMean (w : Fin n → ℝ) : ℝ :=
  EMP.weightSum w / n

/-- **Mean‑subtraction normalization.** Subtract the mean from every weight, producing a
zero‑sum weight vector. -/
noncomputable def normalizeWeight (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i - EMP.weightMean w

@[simp] theorem normalizeWeight_apply (w : Fin n → ℝ) (i : Fin n) :
    normalizeWeight w i = w i - EMP.weightMean w := rfl

/-- `EMP.WeightNormalized w` unfolds to `∑ i, w i = 0`. -/
theorem WeightNormalized_iff (w : Fin n → ℝ) :
    EMP.WeightNormalized w ↔ ∑ i, w i = 0 := Iff.rfl

/-- The all‑zero weight has zero total. -/
@[simp] theorem weightSum_zero :
    EMP.weightSum (fun _ : Fin n => 0) = 0 := by
  simp [weightSum]

/-- Adding a constant `c` to every weight increases the total by `n * c`. -/
theorem weightSum_add_const
    (w : Fin n → ℝ) (c : ℝ) :
    EMP.weightSum (fun i => w i + c) =
      EMP.weightSum w + n * c := by
  simp only [weightSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **Mean subtraction normalizes.** For `0 < n`, the mean‑subtracted weight vector has
zero sum. -/
theorem WeightNormalized_normalizeWeight
    (w : Fin n → ℝ) (hn : 0 < n) :
    EMP.WeightNormalized (EMP.normalizeWeight w) := by
  unfold EMP.WeightNormalized EMP.weightSum
  simp only [EMP.normalizeWeight_apply, EMP.weightMean, EMP.weightSum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- Definitional unfolding of `normalizeWeight`. -/
theorem normalizeWeight_eq_sub_mean
    (w : Fin n → ℝ) :
    EMP.normalizeWeight w = fun i => w i - EMP.weightMean w := rfl

/-- Normalizing an already normalized weight leaves it unchanged. -/
theorem normalizeWeight_eq_self_of_normalized
    (w : Fin n → ℝ) (hw : EMP.WeightNormalized w) :
    EMP.normalizeWeight w = w := by
  have hmean : EMP.weightMean w = 0 := by
    unfold EMP.weightMean
    rw [EMP.WeightNormalized] at hw
    rw [hw, zero_div]
  funext i
  simp [EMP.normalizeWeight_apply, hmean]

/-- `Nat.cast` of the `Fin n` cardinality equals `(n : ℝ)`. -/
theorem natCast_card_fin : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
  simp

end EMP

end NRR
