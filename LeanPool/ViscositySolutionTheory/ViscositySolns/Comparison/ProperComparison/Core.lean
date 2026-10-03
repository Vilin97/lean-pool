/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.DoublingVariables

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Core declarations for proper comparison.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Interior comparison conclusion on a set `C`: for every `x ∈ C`, `u x ≤ v x`.

Boundary hypotheses and compactness/localization hypotheses are not included
in this predicate; they will appear in the theorem that proves it.
-/
def ComparisonConclusionOn (C : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C -> u x <= v x

theorem ComparisonConclusionOn.mono_spatial_set
    {C D : Set (Point n)} {u v : Point n -> Real}
    (h : ComparisonConclusionOn D u v) (hCD : C ⊆ D) :
    ComparisonConclusionOn C u v :=
  fun x hx => h x (hCD hx)

/--
Scalar range condition on a set `C`: for every `x ∈ C`, the value `u x`
belongs to the scalar set `R`.
-/
def ScalarRangeOn (C : Set (Point n)) (R : Set Real) (u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C -> u x ∈ R

/--
A scalar set is closed under subtracting nonnegative constants.

In quantified mathematical form, this predicate says: if `r ∈ R` and
`0 ≤ δ`, then `r - δ ∈ R`.
-/
def ClosedUnderSubNonneg (R : Set Real) : Prop :=
  ∀ r : Real, r ∈ R -> ∀ δ : Real, 0 <= δ -> r - δ ∈ R

/--
Boundedness of a real-valued function on a set `C`: there exist real numbers
`m` and `M` such that, for every `x ∈ C`, `m ≤ u x` and `u x ≤ M`.
-/
def ValueBoundedOn (C : Set (Point n)) (u : Point n -> Real) : Prop :=
  ∃ m M : Real, ∀ x : Point n, x ∈ C -> m <= u x ∧ u x <= M

/--
Upper boundedness of a real-valued function on a set `C`: there exists a real
number `M` such that, for every `x ∈ C`, `u x ≤ M`.
-/
def ValueUpperBoundedOn (C : Set (Point n)) (u : Point n -> Real) : Prop :=
  ∃ M : Real, ∀ x : Point n, x ∈ C -> u x <= M

/--
Lower boundedness of a real-valued function on a set `C`: there exists a real
number `m` such that, for every `x ∈ C`, `m ≤ u x`.
-/
def ValueLowerBoundedOn (C : Set (Point n)) (u : Point n -> Real) : Prop :=
  ∃ m : Real, ∀ x : Point n, x ∈ C -> m <= u x

/--
If `u` has a minimum and a maximum on `C`, then `u` is bounded above and
below on `C`.
-/
theorem ValueBoundedOn.of_isMinOn_isMaxOn
    {C : Set (Point n)} {u : Point n -> Real} {xmin xmax : Point n}
    (hmin : IsMinOn u C xmin) (hmax : IsMaxOn u C xmax) :
    ValueBoundedOn C u := by
  exact ⟨u xmin, u xmax, fun x hx =>
    ⟨isMinOn_iff.mp hmin x hx, isMaxOn_iff.mp hmax x hx⟩⟩

/--
If `u` has a maximum on `C`, then `u` is bounded above on `C`.
-/
theorem ValueUpperBoundedOn.of_isMaxOn
    {C : Set (Point n)} {u : Point n -> Real} {xmax : Point n}
    (hmax : IsMaxOn u C xmax) :
    ValueUpperBoundedOn C u :=
  ⟨u xmax, fun x hx => isMaxOn_iff.mp hmax x hx⟩

/--
If `u` has a minimum on `C`, then `u` is bounded below on `C`.
-/
theorem ValueLowerBoundedOn.of_isMinOn
    {C : Set (Point n)} {u : Point n -> Real} {xmin : Point n}
    (hmin : IsMinOn u C xmin) :
    ValueLowerBoundedOn C u :=
  ⟨u xmin, fun x hx => isMinOn_iff.mp hmin x hx⟩

/--
If `C` is nonempty and compact and `u` is upper semicontinuous on `C`, then
`u` is bounded above on `C`.
-/
theorem ValueUpperBoundedOn.of_upperSemicontinuousOn_isCompact
    {C : Set (Point n)} {u : Point n -> Real}
    (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (husc : UpperSemicontinuousOn u C) :
    ValueUpperBoundedOn C u := by
  rcases UpperSemicontinuousOn.exists_isMaxOn hCne hCcompact husc with
    ⟨xmax, _hxmax, hmax⟩
  exact ValueUpperBoundedOn.of_isMaxOn hmax

/--
If `C` is nonempty and compact and `u` is lower semicontinuous on `C`, then
`u` is bounded below on `C`.
-/
theorem ValueLowerBoundedOn.of_lowerSemicontinuousOn_isCompact
    {C : Set (Point n)} {u : Point n -> Real}
    (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn u C) :
    ValueLowerBoundedOn C u := by
  rcases LowerSemicontinuousOn.exists_isMinOn hCne hCcompact hlsc with
    ⟨xmin, _hxmin, hmin⟩
  exact ValueLowerBoundedOn.of_isMinOn hmin

/--
If `C` is nonempty and compact, `u` is lower semicontinuous on `C`, and
`u` is upper semicontinuous on `C`, then `u` is bounded above and below on
`C`.
-/
theorem ValueBoundedOn.of_lower_upperSemicontinuousOn_isCompact
    {C : Set (Point n)} {u : Point n -> Real}
    (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn u C) (husc : UpperSemicontinuousOn u C) :
    ValueBoundedOn C u := by
  rcases LowerSemicontinuousOn.exists_isMinOn hCne hCcompact hlsc with
    ⟨xmin, _hxmin, hmin⟩
  rcases UpperSemicontinuousOn.exists_isMaxOn hCne hCcompact husc with
    ⟨xmax, _hxmax, hmax⟩
  exact ValueBoundedOn.of_isMinOn_isMaxOn hmin hmax

/--
If `C` is nonempty and compact and `u` is continuous on `C`, then `u` is
bounded above and below on `C`.
-/
theorem ValueBoundedOn.of_continuousOn_isCompact
    {C : Set (Point n)} {u : Point n -> Real}
    (hCne : C.Nonempty) (hCcompact : IsCompact C) (hu : ContinuousOn u C) :
    ValueBoundedOn C u :=
  ValueBoundedOn.of_lower_upperSemicontinuousOn_isCompact hCne hCcompact
    hu.lowerSemicontinuousOn hu.upperSemicontinuousOn

/--
Boundary comparison on a set `C`: for every `x` in the topological frontier of
`C`, `u x ≤ v x`.
-/
def BoundaryComparisonOn (C : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ frontier C -> u x <= v x

/--
If `u ≤ v` on `frontier C` and `δ > 0`, then `u - δ < v` on `frontier C`.

In quantified mathematical form, for every `x ∈ frontier C`,
`u x - δ < v x`.
-/
theorem BoundaryComparisonOn.sub_const_lt_on_frontier
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ) :
    ∀ x : Point n, x ∈ frontier C -> u x - δ < v x := by
  intro x hx
  have huv : u x <= v x := hboundary x hx
  linarith

/--
If `x ∈ closure C` and `x ∉ frontier C`, then `x ∈ interior C`.
-/
theorem mem_interior_of_mem_closure_of_not_mem_frontier
    {C : Set (Point n)} {x : Point n}
    (hxclosure : x ∈ closure C) (hxfrontier : x ∉ frontier C) :
    x ∈ interior C := by
  have hx : x ∈ closure C \ frontier C := ⟨hxclosure, hxfrontier⟩
  simpa [closure_sdiff_frontier] using hx

/--
If `x ∈ closure C` and `x ∉ frontier C`, then `x ∈ C`.
-/
theorem mem_of_mem_closure_of_not_mem_frontier
    {C : Set (Point n)} {x : Point n}
    (hxclosure : x ∈ closure C) (hxfrontier : x ∉ frontier C) :
    x ∈ C :=
  interior_subset (mem_interior_of_mem_closure_of_not_mem_frontier hxclosure hxfrontier)

/--
Assume `u ≤ v` on `frontier C` and `δ > 0`. If `x ∈ closure C` and
`v x < u x - δ`, then `x ∈ C`.
-/
theorem BoundaryComparisonOn.mem_of_mem_closure_of_shifted_gap
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real} {x : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hxclosure : x ∈ closure C) (hgap : v x < u x - δ) :
    x ∈ C := by
  refine mem_of_mem_closure_of_not_mem_frontier hxclosure ?_
  intro hxfrontier
  have hlt : u x - δ < v x :=
    hboundary.sub_const_lt_on_frontier hδ x hxfrontier
  linarith

/--
If `x0 ∈ interior C` and `x i -> x0`, then `x i ∈ C` for all `i` in a set
belonging to the filter.
-/
theorem eventually_mem_of_tendsto_of_mem_interior
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {x : ι -> Point n} {x0 : Point n}
    (hx0 : x0 ∈ interior C) (hx : Tendsto x l (nhds x0)) :
    ∀ᶠ i in l, x i ∈ C := by
  have hC : C ∈ nhds x0 :=
    mem_nhds_iff.mpr ⟨interior C, interior_subset, isOpen_interior, hx0⟩
  exact hx hC

/--
If `x0 ∈ interior C`, `x i -> x0`, and `y i -> x0`, then
`x i ∈ C` and `y i ∈ C` for all `i` in a set belonging to the filter.
-/
theorem eventually_pair_mem_of_tendsto_of_mem_interior
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {x y : ι -> Point n} {x0 : Point n}
    (hx0 : x0 ∈ interior C) (hx : Tendsto x l (nhds x0))
    (hy : Tendsto y l (nhds x0)) :
    ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C := by
  filter_upwards [eventually_mem_of_tendsto_of_mem_interior hx0 hx,
    eventually_mem_of_tendsto_of_mem_interior hx0 hy] with i hxi hyi
  exact ⟨hxi, hyi⟩

/--
Assume `u ≤ v` on `frontier C` and `δ > 0`. If `x0 ∈ closure C`,
`v x0 < u x0 - δ`, `x i -> x0`, and `y i -> x0`, then
`x i ∈ C` and `y i ∈ C` for all `i` in a set belonging to the filter.
-/
theorem BoundaryComparisonOn.eventually_pair_mem_of_tendsto_of_shifted_gap
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {u v : Point n -> Real} {δ : Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hx : Tendsto x l (nhds x0)) (hy : Tendsto y l (nhds x0)) :
    ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C := by
  have hx0interior : x0 ∈ interior C := by
    by_contra hx0not
    have hx0frontier : x0 ∈ frontier C := by
      rw [← closure_sdiff_interior]
      exact ⟨hx0closure, hx0not⟩
    have hlt : u x0 - δ < v x0 :=
      hboundary.sub_const_lt_on_frontier hδ x0 hx0frontier
    linarith
  exact eventually_pair_mem_of_tendsto_of_mem_interior hx0interior hx hy

/--
Compact-closure condition on a set `C`: the closure of `C` is compact.
-/
def CompactClosure (C : Set (Point n)) : Prop :=
  IsCompact (closure C)

theorem CompactClosure.isCompact_closure {C : Set (Point n)}
    (hC : CompactClosure C) :
    IsCompact (closure C) :=
  hC

/--
The boundary, scalar-range, and compactness assumptions used by the first
boundary-value comparison target.
-/
def BoundaryComparisonHypothesesOn
    (C : Set (Point n)) (R : Set Real) (u v : Point n -> Real) : Prop :=
  BoundaryComparisonOn C u v ∧ ScalarRangeOn C R u ∧ CompactClosure C

/--
The doubled-variable localization hypothesis in the filter form used by the
standard comparison proof.

Let `ι` be an index type with a filter `l`, and let `α i`, `x i`, and `y i`
be data depending on `i`. This predicate says: if there exists `z ∈ C` such
that `v z < u z`, then the following two statements hold.

First, for all `i` in a set belonging to the filter `l`,
`α i > 0`, `x i ∈ C`, `y i ∈ C`, `u (x i) ∈ R`, `v (y i) ≤ u (x i)`, and
`(x i, y i)` maximizes
`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
on `C × C`.

Second, the real numbers

`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`

converge to `0` through positive values along `l`.
-/
def StrictDoubledVariableLocalizationAlongOn
    {ι : Type*} (C : Set (Point n)) (R : Set Real) (u v : Point n -> Real)
    (l : Filter ι) (α : ι -> Real) (x y : ι -> Point n) : Prop :=
  (∃ z : Point n, z ∈ C ∧ v z < u z) ->
    (∀ᶠ i in l,
      0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧ u (x i) ∈ R ∧ v (y i) <= u (x i) ∧
        IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
          (C ×ˢ C) (x i, y i)) ∧
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖)
      l (nhdsWithin 0 (Set.Ioi 0))

/--
For functions `α : ι -> R` and `x y : ι -> R^n` and a filter `l` on `ι`, this
predicate is the conjunction of the following three statements:

* `α i * ‖x i - y i‖ ^ 2` tends to `0` along `l`;
* `‖x i - y i‖` tends to `0` along `l`;
* `{i | x i ≠ y i}` belongs to `l`.

Together with `0 < α i` for all `i` in a set belonging to `l`, these
statements imply that
`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖` tends to `0` through positive values
along `l`.
-/
def DoubledVariableScaleEstimatesAlong
    {ι : Type*} (l : Filter ι) (α : ι -> Real) (x y : ι -> Point n) : Prop :=
  Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) ∧
    Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) ∧
      ∀ᶠ i in l, x i ≠ y i

/--
Let `α i` be real numbers indexed by a filter `l`. If `α i -> +∞` along `l`,
then `{i | 0 < α i}` belongs to `l`.
-/
theorem eventually_pos_of_tendsto_atTop
    {ι : Type*} {l : Filter ι} {α : ι -> Real}
    (hα : Tendsto α l atTop) :
    ∀ᶠ i in l, 0 < α i := by
  have hset : {a : Real | 0 < a} ∈ (atTop : Filter Real) := by
    rw [Filter.mem_atTop_sets]
    exact ⟨1, by intro b hb; exact lt_of_lt_of_le zero_lt_one hb⟩
  exact hα hset

/--
Let `α i` be real numbers indexed by a filter `l`. If `α i -> +∞` along `l`,
then `{i | 1 ≤ α i}` belongs to `l`.
-/
theorem eventually_one_le_of_tendsto_atTop
    {ι : Type*} {l : Filter ι} {α : ι -> Real}
    (hα : Tendsto α l atTop) :
    ∀ᶠ i in l, 1 <= α i := by
  have hset : {a : Real | 1 <= a} ∈ (atTop : Filter Real) := by
    rw [Filter.mem_atTop_sets]
    exact ⟨1, by intro b hb; exact hb⟩
  exact hα hset

theorem ScalarRangeOn.mono_spatial_set
    {C D : Set (Point n)} {R : Set Real} {u : Point n -> Real}
    (hu : ScalarRangeOn D R u) (hCD : C ⊆ D) :
    ScalarRangeOn C R u :=
  fun x hx => hu x (hCD hx)

theorem ScalarRangeOn.mono_scalar_set
    {C : Set (Point n)} {R S : Set Real} {u : Point n -> Real}
    (hu : ScalarRangeOn C R u) (hRS : R ⊆ S) :
    ScalarRangeOn C S u :=
  fun x hx => hRS (hu x hx)

/--
For every function `u`, the scalar range condition holds with scalar set
`Set.univ`.

In quantified mathematical form, for every `x ∈ C`, `u x ∈ Set.univ`.
-/
theorem ScalarRangeOn.univ
    (C : Set (Point n)) (u : Point n -> Real) :
    ScalarRangeOn C Set.univ u :=
  fun x _hx => Set.mem_univ (u x)

/--
The set of all real numbers is closed under subtracting nonnegative constants.
-/
theorem ClosedUnderSubNonneg.univ :
    ClosedUnderSubNonneg (Set.univ : Set Real) :=
  fun r _hr δ _hδ => Set.mem_univ (r - δ)

/--
An upper closed ray is closed under subtracting nonnegative constants.

In quantified mathematical form, if `r ≤ a` and `0 ≤ δ`, then `r - δ ≤ a`.
-/
theorem ClosedUnderSubNonneg.Iic (a : Real) :
    ClosedUnderSubNonneg (Set.Iic a) := by
  intro r hr δ hδ
  have hrle : r <= a := by simpa using hr
  have hle : r - δ <= a := by linarith
  simpa using hle

/--
An upper open ray is closed under subtracting nonnegative constants.

In quantified mathematical form, if `r < a` and `0 ≤ δ`, then `r - δ < a`.
-/
theorem ClosedUnderSubNonneg.Iio (a : Real) :
    ClosedUnderSubNonneg (Set.Iio a) := by
  intro r hr δ hδ
  have hrlt : r < a := by simpa using hr
  have hlt : r - δ < a := by linarith
  simpa using hlt

/--
If the scalar set is closed under subtracting nonnegative constants, then
subtracting a nonnegative constant preserves scalar range.

In quantified mathematical form, if `u x ∈ R` for every `x ∈ C`, if
`0 ≤ δ`, and if `r ∈ R` implies `r - δ ∈ R`, then `u x - δ ∈ R` for every
`x ∈ C`.
-/
theorem ScalarRangeOn.sub_const_of_closedUnderSubNonneg
    {C : Set (Point n)} {R : Set Real} {u : Point n -> Real} {δ : Real}
    (hu : ScalarRangeOn C R u) (hR : ClosedUnderSubNonneg R) (hδ : 0 <= δ) :
    ScalarRangeOn C R (fun x => u x - δ) :=
  fun x hx => hR (u x) (hu x hx) δ hδ

theorem ValueBoundedOn.mono_spatial_set
    {C D : Set (Point n)} {u : Point n -> Real}
    (hu : ValueBoundedOn D u) (hCD : C ⊆ D) :
    ValueBoundedOn C u := by
  rcases hu with ⟨m, M, hbound⟩
  exact ⟨m, M, fun x hx => hbound x (hCD hx)⟩

theorem BoundaryComparisonHypothesesOn.boundary
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    (h : BoundaryComparisonHypothesesOn C R u v) :
    BoundaryComparisonOn C u v :=
  h.1

theorem BoundaryComparisonHypothesesOn.scalarRange
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    (h : BoundaryComparisonHypothesesOn C R u v) :
    ScalarRangeOn C R u :=
  h.2.1

theorem BoundaryComparisonHypothesesOn.compactClosure
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    (h : BoundaryComparisonHypothesesOn C R u v) :
    CompactClosure C :=
  h.2.2

end ViscositySolns
