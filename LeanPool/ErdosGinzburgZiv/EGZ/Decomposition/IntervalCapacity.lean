/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Termination

/-!
# Termination from bounds on least-color occurrences

A uniform capacity for each interval's least color turns the finite-color
interval lemma into a uniform bound on operation-sequence length. The bound
depends only on the number of colors and the capacity function.
-/

namespace EGZ

attribute [local instance] Classical.propDecidable

/-- Every interval before `N` has at most `capacity a` occurrences of any
color which is a lower bound for all colors on that interval. -/
def HasIntervalCapacity (χ capacity : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ a b l, a ≤ b → b < N → (∀ i ∈ Finset.Icc a b, l ≤ χ i) →
    ((Finset.Icc a b).filter fun i ↦ χ i = l).card ≤ capacity a

/-- The first length at which the interval lemma forces a capacity violation.
The requested occurrence threshold is exactly `capacity + 1`. -/
noncomputable def intervalCapacityBound (k : ℕ) (capacity : ℕ → ℕ) : ℕ :=
  Nat.find (exists_color_interval_bound k (fun a ↦ capacity a + 1))

theorem intervalCapacityBound_spec (k : ℕ) (capacity : ℕ → ℕ) :
    ∀ χ : ℕ → ℕ, (∀ i < intervalCapacityBound k capacity, χ i < k) →
      ∃ a b l, b < intervalCapacityBound k capacity ∧ l < k ∧
        HasColorInterval χ (fun a ↦ capacity a + 1) a b l :=
  Nat.find_spec (exists_color_interval_bound k (fun a ↦ capacity a + 1))

/-- The bound is uniform over operation sequences; no monotonicity of the
colors or of the capacity function is required. -/
theorem length_lt_intervalCapacityBound (k : ℕ) (capacity : ℕ → ℕ)
    (N : ℕ) (χ : ℕ → ℕ) (hχ : ∀ i < N, χ i < k)
    (hcapacity : HasIntervalCapacity χ capacity N) :
    N < intervalCapacityBound k capacity := by
  by_contra hN
  have hBN : intervalCapacityBound k capacity ≤ N := Nat.le_of_not_gt hN
  obtain ⟨a, b, l, hb, _, hab, hlow, hcount⟩ :=
    intervalCapacityBound_spec k capacity χ (fun i hi ↦ hχ i (hi.trans_le hBN))
  have hc := hcapacity a b l hab (hb.trans_le hBN) hlow
  change capacity a + 1 ≤ _ at hcount
  omega

/-- Existential formulation of the uniform termination bound. -/
theorem exists_length_bound_of_interval_capacity (k : ℕ) (capacity : ℕ → ℕ) :
    ∃ B, ∀ N χ, (∀ i < N, χ i < k) → HasIntervalCapacity χ capacity N → N < B :=
  ⟨intervalCapacityBound k capacity, length_lt_intervalCapacityBound k capacity⟩

end EGZ
