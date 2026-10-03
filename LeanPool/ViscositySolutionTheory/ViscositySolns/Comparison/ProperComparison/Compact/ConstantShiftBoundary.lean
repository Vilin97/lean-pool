/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Algebra

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact and subsequence comparison bridges. (ConstantShiftBoundary)

Part of the compact and subsequence comparison bridge development.
Split from `Compact.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Assume `ε > 0`, `u` is a strict subsolution with margin `ε`, `v` is a
supersolution, `F` is proper and continuous, `F` satisfies the Ishii
structural condition, and `QuadraticPenaltyIshiiLemmaOn C C u v` holds.

Let `l` be a filter on `ι` with `NeBot l`. Suppose there are functions
`α : ι -> R` and `x y : ι -> R^n` such that, for all `i` in a set belonging to
`l`, one has `0 < α i`, `x i ∈ C`, `y i ∈ C`, and `(x i, y i)` maximizes
`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
on `C × C`.
Suppose also that `DoubledVariableScaleEstimatesAlong l α x y` holds and that
`u x ∈ R` for every `x ∈ C`. Then `u ≤ v` on `C`.
-/
theorem strictComparison_of_eventually_maximizers_of_scaleEstimates
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hscale : DoubledVariableScaleEstimatesAlong l α x y) :
    ComparisonConclusionOn C u v := by
  refine strictComparison_of_doubledVariableLocalizationAlong
    (l := l) (α := α) (x := x) (y := y)
    hu hv hFcont hproper hcomp hIshii hε ?_
  intro hfail
  exact strictDoubledVariableLocalizationAlongOn_of_scaleEstimates
    hfail huR hmax hscale hfail

/--
Assume `ε > 0`, `u` is a strict subsolution with margin `ε`, `v` is a
supersolution, `F` is proper and continuous, `F` satisfies the Ishii
structural condition, and `QuadraticPenaltyIshiiLemmaOn C C u v` holds.

Let `l` be a filter on `ι` with `NeBot l`. Suppose there are functions
`α : ι -> R` and `x y : ι -> R^n` such that, for all `i` in a set belonging to
`l`, one has `0 < α i`, `x i ∈ C`, `y i ∈ C`, and `(x i, y i)` maximizes
`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
on `C × C`.
Suppose also that `u x ∈ R` for every `x ∈ C`, that
`α i * ‖x i - y i‖ ^ 2 -> 0` along `l`, and that
`‖x i - y i‖ -> 0` along `l`. Then `u ≤ v` on `C`.

The theorem does not assume separately that `{i | x i ≠ y i}` belongs to
`l`. If comparison failed, the strict subsolution inequality and Ishii's lemma
would imply that
`0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖` for all `i` in a set belonging to
`l`.
-/
theorem strictComparison_of_eventually_maximizers_of_scales
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0)) :
    ComparisonConclusionOn C u v := by
  refine strictComparison_of_doubledVariableLocalizationAlong
    (l := l) (α := α) (x := x) (y := y)
    hu hv hFcont hproper hcomp hIshii hε ?_
  intro hfail
  have hvyux :
      ∀ᶠ i in l, v (y i) <= u (x i) :=
    eventually_value_right_le_left_of_eventually_isMaxOn_doubledObjective hfail hmax
  have hscale_pos :
      ∀ᶠ i in l, 0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ := by
    have hdata :
        ∀ᶠ i in l,
          0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧ v (y i) <= u (x i) ∧
            IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
              (C ×ˢ C) (x i, y i) := by
      filter_upwards [hmax, hvyux] with i hi hvyi
      exact ⟨hi.1, hi.2.1, hi.2.2.1, hvyi, hi.2.2.2⟩
    exact eventually_comparisonScale_pos_of_strict_eventually_isMaxOn
      hu hv hFcont hproper hIshii hε hdata
  exact strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange_of_scales
    hfail huR hmax hquad hdist hscale_pos hfail

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_scaleEstimates`. Instead of
assuming `DoubledVariableScaleEstimatesAlong l α x y` directly, assume:

* `α i * ‖x i - y i‖ ^ 2 -> 0` along `l`;
* `{i | 1 ≤ α i}` belongs to `l`.

Then `u ≤ v` on `C`.
-/
theorem strictComparison_of_eventually_maximizers_of_weightedDistanceSq
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_scales
    hu hv hFcont hproper hcomp hIshii hε huR hmax
    hquad
    (tendsto_distance_zero_of_tendsto_weightedDistanceSq_of_eventually_one_le
      hquad hαone)

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_weightedDistanceSq`, with the
condition `{i | 1 ≤ α i} ∈ l` replaced by `α i -> +∞` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_weightedDistanceSq_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_weightedDistanceSq
    hu hv hFcont hproper hcomp hIshii hε huR hmax hquad
    (eventually_one_le_of_tendsto_atTop hα)

/--
Strict comparison from shifted doubled-variable maximizers selected on
`closure C × closure C`.

In quantified mathematical form, assume `u ≤ v` on `frontier C`, `δ > 0`,
`x0 ∈ closure C`, and `v x0 < u x0 - δ`. Suppose selected points
`x i`, `y i` converge to `x0` within `closure C`, and for all `i` in a set
belonging to `l`, `(x i, y i)` maximizes

`(x', y') ↦ u x' - δ - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `closure C × closure C`. If `α i -> +∞`, `x ↦ u x - δ` is a strict
subsolution on `C`, `v` is a supersolution on `C`, the shifted function has
values in `R` on `C`, and the operator hypotheses and Ishii lemma hold on
`C`, then `u x - δ ≤ v x` for every `x ∈ C`.
-/
theorem strictComparison_of_shifted_closure_maximizers_of_tendsto_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    {u v : Point n -> Real} {δ ε : Real}
    {α : ι -> Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hu : StrictViscositySubsolution C F ε (fun z : Point n => u z - δ))
    (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C (fun z : Point n => u z - δ) v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R (fun z : Point n => u z - δ))
    (husc : UpperSemicontinuousOn (fun z : Point n => u z - δ) (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hx : Tendsto x l (nhdsWithin x0 (closure C)))
    (hy : Tendsto y l (nhdsWithin x0 (closure C)))
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C (fun z : Point n => u z - δ) v := by
  have hx_ambient : Tendsto x l (nhds x0) :=
    tendsto_nhds_of_tendsto_nhdsWithin hx
  have hy_ambient : Tendsto y l (nhds x0) :=
    tendsto_nhds_of_tendsto_nhdsWithin hy
  have hmaxC :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (C ×ˢ C) (x i, y i) :=
    eventually_isMaxOn_shifted_doubledObjective_restrict_closure_of_tendsto
      hboundary hδ hx0closure hgap hx_ambient hy_ambient hmax
  have hquad :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) :=
    tendsto_weightedDistanceSq_zero_of_shifted_closure_maximizers_of_tendsto
      hboundary hδ hx0closure hgap husc hvlsc hx hy hmax
  have hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) :=
    tendsto_distance_zero_of_tendsto_weightedDistanceSq_of_eventually_one_le
      hquad (eventually_one_le_of_tendsto_atTop hα)
  exact strictComparison_of_eventually_maximizers_of_scales
    hu hv hFcont hproper hcomp hIshii hε huR hmaxC hquad hdist

/--
Strict boundary comparison for a fixed positive constant shift.

In quantified mathematical form, assume:

* `u ≤ v` on `frontier C`;
* `δ > 0`;
* `x ↦ u x - δ` is a strict subsolution on `C`;
* `v` is a supersolution on `C`;
* `x ↦ u x - δ` is upper semicontinuous on `closure C`;
* `v` is lower semicontinuous on `closure C`;
* `closure C` is compact;
* the operator hypotheses and the quadratic-penalty Ishii lemma hold on `C`.

Then `u x - δ ≤ v x` for every `x ∈ C`.

The proof follows the comparison argument in CIL: if the conclusion failed,
choose maximum points of the shifted doubled-variable functional on
`closure C × closure C` for parameters tending to infinity. Compactness gives
a convergent subsequence of the first coordinates, the doubled-variable
estimate forces the second coordinates to have the same limit, boundary
strictness places the limit in `C`, and the already-proved strict comparison
contradiction applies.
-/
theorem strictComparison_of_constantShift_boundary
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    {u v : Point n -> Real} {δ ε : Real}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hu : StrictViscositySubsolution C F ε (fun z : Point n => u z - δ))
    (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C (fun z : Point n => u z - δ) v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R (fun z : Point n => u z - δ))
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (husc : UpperSemicontinuousOn (fun z : Point n => u z - δ) (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C)) :
    ComparisonConclusionOn C (fun z : Point n => u z - δ) v := by
  classical
  by_contra hnot
  have hfail : ∃ z : Point n, z ∈ C ∧ v z < u z - δ := by
    by_contra hno
    apply hnot
    intro z hz
    exact not_lt.mp fun hlt => hno ⟨z, hz, hlt⟩
  let α : ℕ -> Real := fun i => (i : Real) + 1
  have hα : Tendsto α atTop atTop := by
    rw [tendsto_atTop']
    intro s hs
    rcases Filter.mem_atTop_sets.mp hs with ⟨a, ha⟩
    have haSet : {b : Real | a <= b} ∈ (atTop : Filter Real) := by
      rw [Filter.mem_atTop_sets]
      exact ⟨a, fun b hb => hb⟩
    have hnat := (tendsto_natCast_atTop_atTop (R := Real)) haSet
    rcases Filter.mem_atTop_sets.mp hnat with ⟨N, hN⟩
    refine ⟨N, fun i hi => ha ((i : Real) + 1) ?_⟩
    have hai : a <= (i : Real) := hN i hi
    linarith
  have hclosureNonempty : (closure C).Nonempty := by
    rcases hCne with ⟨z, hz⟩
    exact ⟨z, subset_closure hz⟩
  rcases exists_eventually_isMaxOn_doubledObjective_along_of_isCompact
      (l := atTop) (C := closure C)
      (u := fun z : Point n => u z - δ) (v := v) (α := α)
      (eventually_pos_of_tendsto_atTop hα)
      hclosureNonempty hCcompact.isCompact_closure husc hvlsc with
    ⟨x, y, hmax⟩
  have hx_eventual : ∀ᶠ i in atTop, x i ∈ closure C := by
    filter_upwards [hmax] with i hi
    exact hi.2.1
  rcases hCcompact.isCompact_closure.tendsto_subseq' hx_eventual.frequently with
    ⟨x0, hx0closure, φ, hφ_mono, hxφ_tendsto⟩
  let α' : ℕ -> Real := fun k => α (φ k)
  let x' : ℕ -> Point n := fun k => x (φ k)
  let y' : ℕ -> Point n := fun k => y (φ k)
  have hmax' :
      ∀ᶠ k in atTop,
        0 < α' k ∧ x' k ∈ closure C ∧ y' k ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α' k) q)
            (closure C ×ˢ closure C) (x' k, y' k) := by
    simpa [α', x', y'] using hφ_mono.tendsto_atTop hmax
  have hα' : Tendsto α' atTop atTop := by
    exact hα.comp hφ_mono.tendsto_atTop
  have hx' : Tendsto x' atTop (nhdsWithin x0 (closure C)) := by
    have hx_ambient : Tendsto x' atTop (nhds x0) := by
      simpa [x', Function.comp_def] using hxφ_tendsto
    have hx_mem : ∀ᶠ k in atTop, x' k ∈ closure C := by
      filter_upwards [hmax'] with k hk
      exact hk.2.1
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x' hx_ambient hx_mem
  have hbounds :
      ∃ m M : Real, ∀ᶠ k in atTop, m <= v (y' k) ∧
        (fun z : Point n => u z - δ) (x' k) <= M :=
    eventually_uv_bounds_of_upper_lowerBoundedOn_of_eventually_isMaxOn
      (C := closure C) (u := fun z : Point n => u z - δ) (v := v)
      (α := α') (x := x') (y := y')
      (ValueUpperBoundedOn.of_upperSemicontinuousOn_isCompact
        hclosureNonempty hCcompact.isCompact_closure husc)
      (ValueLowerBoundedOn.of_lowerSemicontinuousOn_isCompact
        hclosureNonempty hCcompact.isCompact_closure hvlsc)
      hmax'
  rcases hbounds with ⟨m, M, hbounds⟩
  have hdist : Tendsto (fun k : ℕ => ‖x' k - y' k‖) atTop (nhds 0) :=
    tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_uv_bounds
      (C := closure C) (u := fun z : Point n => u z - δ) (v := v)
      (α := α') (x := x') (y := y') (z := x0) (m := m) (M := M)
      hx0closure hmax' hα' hbounds
  have hy' : Tendsto y' atTop (nhdsWithin x0 (closure C)) := by
    have hy_mem : ∀ᶠ k in atTop, y' k ∈ closure C := by
      filter_upwards [hmax'] with k hk
      exact hk.2.2.1
    exact tendsto_right_nhdsWithin_of_tendsto_left_nhdsWithin_of_tendsto_distance_zero
      hx' hy_mem hdist
  rcases hfail with ⟨z, hz, hgapz⟩
  have hgapx0 : v x0 < u x0 - δ :=
    shifted_gap_at_limit_of_closure_maximizers
      (C := C) (u := u) (v := v) (δ := δ) (α := α') (x := x') (y := y')
      hz hgapz hx0closure husc hvlsc hx' hy' hmax'
  have hcomparison :
      ComparisonConclusionOn C (fun z : Point n => u z - δ) v :=
    strictComparison_of_shifted_closure_maximizers_of_tendsto_atTop
      (C := C) (R := R) (F := F) (u := u) (v := v) (δ := δ) (ε := ε)
      (α := α') (x := x') (y := y') (x0 := x0)
      hboundary hδ hx0closure hgapx0 hu hv hFcont hproper hcomp hIshii hε
      huR husc hvlsc hx' hy' hmax' hα'
  exact hnot hcomparison

/--
Proper comparison from constant shifts, following the paper's strictification
argument.

In quantified mathematical form, assume:

* `u ≤ v` on `frontier C`;
* `u` is a viscosity subsolution and `v` is a viscosity supersolution on `C`;
* `u` is upper semicontinuous and `v` is lower semicontinuous on `closure C`;
* `closure C` is compact;
* the operator hypotheses and the quadratic-penalty Ishii lemma constructor
  hold on `C`;
* the scalar set is closed under subtracting nonnegative constants;
* for every `η > 0`, there are `δ` and `ε` such that
  `0 < δ`, `δ ≤ η`, `0 < ε`, and
  `F x (r - δ) p X ≤ F x r p X - ε` for every
  `x ∈ C`, `r`, `p`, and `X`.

Then `u x ≤ v x` for every `x ∈ C`.
-/
theorem comparison_of_constantShift_boundary
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v := by
  intro z hz
  refine le_of_forall_pos_le_add fun η hη => ?_
  rcases hdecrease η hη with ⟨δ, ε, hδpos, hδη, hε, hdec⟩
  have hshift : ComparisonConclusionOn C (fun z : Point n => u z - δ) v :=
    strictComparison_of_constantShift_boundary
      (C := C) (R := R) (F := F) (u := u) (v := v) (δ := δ) (ε := ε)
      hboundary hδpos
      (hu.strict_sub_const_of_uniformScalarDecrease hdec)
      hv hFcont hproper hcomp
      (hIshii (fun z : Point n => u z - δ) v
        (hu.1.add upperSemicontinuousOn_const) hv.1)
      hε
      (huR.sub_const_of_closedUnderSubNonneg hR hδpos.le)
      hCne hCcompact
      (husc.add upperSemicontinuousOn_const)
      hvlsc
  have hzshift : u z - δ <= v z := hshift z hz
  linarith

/--
Non-strict boundary comparison from the constant-shift argument, with the
quadratic-penalty Ishii lemma constructor supplied by the localized Jensen
and Aleksandrov analytic inputs.

In quantified mathematical form, assume the localized Jensen contact-set
theorem and the localized Aleksandrov second-differentiability theorem in
dimension `n + n`, and assume the relative topology on `C` is locally
compact. If `F` is proper and continuous, `F` satisfies the Ishii operator
comparison condition on `C` and `R`, `u ≤ v` on `frontier C`, `u x ∈ R` for
every `x ∈ C`, `R` is closed under subtracting nonnegative constants, `C` is
nonempty, `closure C` is compact, `u` is a viscosity subsolution, `v` is a
viscosity supersolution, `u` is upper semicontinuous on `closure C`, `v` is
lower semicontinuous on `closure C`, and every positive `η` has a positive
constant shift which makes the subsolution inequality strict, then `u x ≤ v x`
for every `x ∈ C`.
-/
theorem comparison_of_constantShift_boundary_of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v := by
  exact comparison_of_constantShift_boundary hproper hFcont hcomp hboundary
    huR hR
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_localized_jensen_aleksandrov
      (n := n) hJensen hAleksandrov)
    hCne hCcompact hu hv husc hvlsc hdecrease

/--
Non-strict boundary comparison from the constant-shift argument follows from
the localized Aleksandrov second-differentiability theorem in dimension
`n + n`, because the localized Jensen contact-set theorem has already been
proved.
-/
theorem comparison_of_constantShift_boundary_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v :=
  comparison_of_constantShift_boundary_of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov hproper hFcont hcomp hboundary huR hR hCne hCcompact
    hu hv husc hvlsc hdecrease

/-- Compact-domain comparison with the analytic Jensen and Aleksandrov inputs discharged. -/
theorem comparison_of_constantShift_boundary_proof
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v :=
  comparison_of_constantShift_boundary_of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hproper hFcont hcomp hboundary huR hR hCne hCcompact hu hv husc hvlsc hdecrease

/--
Constant-shift data stated using maximizers on `closure C × closure C` imply
comparison for a fixed pair of functions.

In quantified mathematical form, assume:

* `F` is proper and continuous;
* `F` satisfies `IshiiOperatorComparisonConditionOn C R F`;
* `u` is a viscosity subsolution of `F = 0` on `C`;
* `v` is a viscosity supersolution of `F = 0` on `C`;
* `u ≤ v` on `frontier C`;
* for every `η > 0`, there are `δ`, `ε`, `α`, `x`, `y`, and `x0` satisfying
  the conditions in `ConstantShiftClosureMaximizerDataOn C R F u v`.

Then `u z ≤ v z` for every `z ∈ C`.
-/
theorem comparison_of_constantShiftClosureMaximizerData
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (hdata : ConstantShiftClosureMaximizerDataOn C R F u v) :
    ComparisonConclusionOn C u v := by
  intro z hz
  refine le_of_forall_pos_le_add fun η hη => ?_
  rcases hdata η hη with
    ⟨δ, ε, α, x, y, x0, hδpos, hδη, hε, hdec, hIshii, huR, hx0closure,
      hgap, husc, hvlsc, hx, hy, hmax, hα⟩
  have hstrict : StrictViscositySubsolution C F ε (fun z : Point n => u z - δ) :=
    hu.strict_sub_const_of_uniformScalarDecrease hdec
  have hshift :
      ComparisonConclusionOn C (fun z : Point n => u z - δ) v :=
    strictComparison_of_shifted_closure_maximizers_of_tendsto_atTop
      hboundary hδpos hx0closure hgap hstrict hv hFcont hproper hcomp hIshii hε
      huR husc hvlsc hx hy hmax hα
  have hzshift : u z - δ <= v z := hshift z hz
  linarith

/--
If the ordinary boundary-value hypotheses construct constant-shift data stated
using maximizers on `closure C × closure C`, then the ordinary boundary
comparison statement on `C` follows.
-/
theorem properBoundaryComparisonStatementOn_of_constantShiftClosureMaximizerDataConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hconstruct : ConstantShiftBoundaryClosureMaximizerDataConstructorOn C R F) :
    ProperBoundaryComparisonStatementOn C R F := by
  intro hproper hFcont hcomp u v hextra hu hv _huR
  rcases hextra with ⟨hboundary, huR, hCcompact⟩
  by_cases hCne : C.Nonempty
  · exact comparison_of_constantShiftClosureMaximizerData
      hproper hFcont hcomp hboundary hu hv
      (hconstruct u v hCne hboundary huR hCcompact hu hv)
  · intro x hx
    exact (hCne ⟨x, hx⟩).elim

end ViscositySolns
