/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Geometric Series in Nonarchimedean Rings

We prove **Proposition 5.38** of [Wedhorn, *Adic Spaces*]: in a complete Hausdorff
nonarchimedean topological ring, every topologically nilpotent element `a` yields a unit
`1 - a` (via the geometric series `∑ aⁿ`).

## Main results

* `IsTopologicallyNilpotent.summable_pow` : The geometric series `∑ aⁿ` converges.
* `IsTopologicallyNilpotent.neg` : `-a` is topologically nilpotent.
* `IsTopologicallyNilpotent.isUnit_one_sub` : `1 - a` is a unit (**Prop 5.38**).
* `IsTopologicallyNilpotent.isUnit_one_add` : `1 + a` is a unit (corollary).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 5.38
-/

@[expose] public section

open Filter Topology

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]

omit [T2Space A] [IsTopologicalRing A] in
/-- The geometric series `∑ aⁿ` converges for a topologically nilpotent element `a`
in a complete nonarchimedean ring. -/
theorem IsTopologicallyNilpotent.summable_pow {a : A} (ha : IsTopologicallyNilpotent a) :
    Summable (a ^ · : ℕ → A) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact ha

/-- **Proposition 5.38** of Wedhorn: in a complete Hausdorff nonarchimedean ring,
`1 - a` is a unit for every topologically nilpotent `a`, with inverse `∑ aⁿ`. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 - a) :=
  .of_mul_eq_one _ ha.summable_pow.one_sub_mul_tsum_pow

omit [T2Space A] [CompleteSpace A] [IsTopologicalRing A] [IsUniformAddGroup A] in
/-- The negation of a topologically nilpotent element is topologically nilpotent. -/
theorem IsTopologicallyNilpotent.neg {a : A}
    (ha : IsTopologicallyNilpotent a) : IsTopologicallyNilpotent (-a) := by
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine (ha.eventually (V.isOpen.mem_nhds V.zero_mem')).mono fun n hn ↦ hVU ?_
  change (-a) ^ n ∈ (V : Set A)
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow]; exact hn
  · rw [ho.neg_pow]; exact V.neg_mem' hn

/-- Corollary of Prop 5.38: `1 + a` is a unit for topologically nilpotent `a`. -/
theorem IsTopologicallyNilpotent.isUnit_one_add {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 + a) := by
  rw [← sub_neg_eq_add]
  exact ha.neg.isUnit_one_sub
