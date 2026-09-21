/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

import Mathlib.Data.Fintype.BigOperators

/-!
# Aggregation of finite coordinates

This file develops aggregation of a function along the fibers of a map between finite types.
For Mathlib's intrinsic `Convexity.StdSimplex`, this operation is the finite-coordinate
realization of `Convexity.StdSimplex.map`.

The fiber-cardinality results are included because they describe the exponents and normalization
constants that occur when coordinate measures on standard simplices are pushed forward.

## Main definitions and results

* `stdSimplexAggregate`: aggregation of coordinates along a finite map.
* `Convexity.StdSimplex.weights_map_eq_stdSimplexAggregate`: compatibility with the intrinsic
  standard-simplex map.
* `stdSimplexAggregateFiberCard`: cardinality of a fiber of the aggregation map.
-/

@[expose] public noncomputable section StdSimplexAggregation

variable {ι : Type*} [Fintype ι]

open scoped Classical
open Convexity

/-- Coordinate aggregation sends `u : ι → R` to its block sums under a map `f : ι → κ`.
This is an application-oriented functional name for `FunOnFinite.linearMap`. -/
abbrev stdSimplexAggregate {κ R : Type*} [Finite κ] [Semiring R]
    (f : ι → κ) : (ι → R) → (κ → R) :=
  FunOnFinite.linearMap R R f

/-- Aggregation is continuous whenever addition in the coefficient semiring is continuous. -/
theorem continuous_stdSimplexAggregate {κ R : Type*} [Finite κ] [Semiring R]
    [TopologicalSpace R] [ContinuousAdd R] (f : ι → κ) :
    Continuous (stdSimplexAggregate (R := R) f) :=
  FunOnFinite.continuous_linearMap R R f

namespace Convexity.StdSimplex

variable {κ R : Type*} [Fintype κ]
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-- Mapping an intrinsic standard-simplex point and then reading its weights agrees with
aggregation of its finite coordinate function. -/
@[simp] theorem weights_map_eq_stdSimplexAggregate (f : ι → κ) (s : StdSimplex R ι) :
    (fun k ↦ (s.map f).weights k) =
      stdSimplexAggregate f (fun i ↦ s.weights i) := by
  change ⇑(Finsupp.mapDomain f s.weights) =
    FunOnFinite.map f (fun i ↦ s.weights i)
  rw [FunOnFinite.map, Finsupp.equivFunOnFinite_symm_coe]
  funext k
  exact (Finsupp.equivFunOnFinite_apply _ k).symm

end Convexity.StdSimplex

/-- Aggregating positive parameters along a surjective partition gives positive parameters. -/
theorem stdSimplexAggregate_pos {κ R : Type*} [Finite κ]
    [Semiring R] [PartialOrder R] [AddLeftStrictMono R] [IsOrderedCancelAddMonoid R]
    {f : ι → κ} (hf : Function.Surjective f)
    {u : ι → R} (hu : ∀ i, 0 < u i) :
    ∀ k, 0 < stdSimplexAggregate f u k := by
  classical
  intro k
  change 0 < (FunOnFinite.linearMap R R f u) k
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_pos
  · intro i _
    exact hu i
  · rcases hf k with ⟨i, hi⟩
    use i
    simp [hi]

/-- Cardinality of a fiber of an aggregation map. The codomain need not be finite because every
fiber is a subtype of the finite domain `ι`. -/
def stdSimplexAggregateFiberCard {κ : Type*} (f : ι → κ) (k : κ) : ℕ := by
  classical
  exact Fintype.card {i : ι // f i = k}

/-- Every fiber of a surjective aggregation map has positive cardinality. -/
theorem stdSimplexAggregateFiberCard_pos {κ : Type*} {f : ι → κ}
    (hf : Function.Surjective f) (k : κ) :
    0 < stdSimplexAggregateFiberCard f k := by
  unfold stdSimplexAggregateFiberCard
  exact Fintype.card_pos_iff.mpr <| by
    obtain ⟨i, hi⟩ := hf k
    exact ⟨⟨i, hi⟩⟩

/-- The cardinalities of all fibers of a map from a finite type sum to the cardinality of its
domain. -/
theorem sum_stdSimplexAggregateFiberCard {κ : Type*} [Fintype κ] (f : ι → κ) :
    ∑ k, stdSimplexAggregateFiberCard f k = Fintype.card ι := by
  let e : (Σ k, {i : ι // f i = k}) ≃ ι :=
    { toFun := fun x => x.2.1
      invFun := fun i => ⟨f i, i, rfl⟩
      left_inv := by rintro ⟨k, i, hi⟩; subst k; rfl
      right_inv := fun _ => rfl }
  unfold stdSimplexAggregateFiberCard
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr e

/-- Aggregating the constant-one vector records the cardinality of each fiber. -/
theorem stdSimplexAggregate_one {κ S : Type*} [Finite κ] [Semiring S]
    (f : ι → κ) (k : κ) :
    stdSimplexAggregate f (fun _ => (1 : S)) k =
      (stdSimplexAggregateFiberCard f k : S) := by
  classical
  change (FunOnFinite.linearMap S S f (fun _ => 1)) k = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [stdSimplexAggregateFiberCard, ← Fintype.card_subtype]

end StdSimplexAggregation
