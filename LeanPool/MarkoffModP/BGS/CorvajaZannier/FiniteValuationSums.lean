/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.LaurentSeries

/-! # Finite valuation arithmetic shared by the local Wronskian estimates -/

@[expose] public section

namespace BGS.CorvajaZannier.FiniteValuationSums

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The additive Laurent valuation sends a finite product to the sum of its valuations. -/
theorem laurent_product_valuation {ι : Type*}
    (s : Finset ι) (g : ι → LaurentSeries K) :
    HahnSeries.addVal ℤ K (∏ i ∈ s, g i) =
      ∑ i ∈ s, HahnSeries.addVal ℤ K (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, AddValuation.map_mul]

/-- Coercion from integers to `WithTop` preserves a sum over a finset. -/
theorem integer_sum_coercion {ι : Type*}
    (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

/-- Coercion from integers to `WithTop` preserves a sum over a finite type. -/
theorem integer_sum_coercion_univ {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    (((∑ i, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, ((g i : ℤ) : WithTop ℤ) := by
  classical
  exact integer_sum_coercion Finset.univ g

end BGS.CorvajaZannier.FiniteValuationSums
