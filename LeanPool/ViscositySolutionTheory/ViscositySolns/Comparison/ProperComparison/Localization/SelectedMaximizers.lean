/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Doubled-variable localization estimates for proper comparison. (SelectedMaximizers)

Part of the doubled-variable localization estimates for proper comparison.
Split from `Localization.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Let `α i`, `x i`, and `y i` be selected doubled-variable data along a filter
`l`. Suppose there exists `z ∈ C` such that `v z < u z`. If, for all `i` in
a set belonging to `l`, `α i > 0`, `x i ∈ C`, `y i ∈ C`, and `(x i, y i)`
maximizes the doubled-variable objective on `C × C`, then for all `i` in a
set belonging to `l`, `v (y i) ≤ u (x i)`.
-/
theorem eventually_value_right_le_left_of_eventually_isMaxOn_doubledObjective
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hfail : ∃ z : Point n, z ∈ C ∧ v z < u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ∀ᶠ i in l, v (y i) <= u (x i) := by
  rcases hfail with ⟨z, hz, hgap⟩
  filter_upwards [hmax] with i hi
  rcases hi with ⟨hαi, _hxi, _hyi, hmaxi⟩
  exact value_right_le_left_of_pos_gap_of_isMaxOn_doubledObjective
    hαi.le hz hgap hmaxi

/--
Let `α i`, `x i`, and `y i` be selected doubled-variable data along a filter
`l`. If, for all `i` in a set belonging to `l`, `x i ∈ C`, and if
`u x ∈ R` for every `x ∈ C`, then for all `i` in a set belonging to `l`,
`u (x i) ∈ R`.
-/
theorem eventually_scalarRange_of_eventually_isMaxOn_doubledObjective
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ∀ᶠ i in l, u (x i) ∈ R := by
  filter_upwards [hmax] with i hi
  exact huR (x i) hi.2.1

/--
Suppose `(x i, y i)` maximizes the doubled-variable objective on
`closure C × closure C` for all `i` in a set belonging to `l`. If
`x i ∈ C` and `y i ∈ C` for all `i` in a set belonging to `l`, then
`(x i, y i)` maximizes the same objective on `C × C` for all `i` in a set
belonging to `l`.
-/
theorem eventually_isMaxOn_doubledObjective_restrict_closure
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (closure C ×ˢ closure C) (x i, y i))
    (hmem : ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C) :
    ∀ᶠ i in l,
      0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
        IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
          (C ×ˢ C) (x i, y i) := by
  filter_upwards [hmax, hmem] with i hi hmemi
  rcases hi with ⟨hαi, _hxiclosure, _hyiclosure, hmaxi⟩
  refine ⟨hαi, hmemi.1, hmemi.2, ?_⟩
  intro q hq
  exact hmaxi ⟨subset_closure hq.1, subset_closure hq.2⟩

/--
Assume `u ≤ v` on `frontier C` and `δ > 0`. Suppose `x0 ∈ closure C`,
`v x0 < u x0 - δ`, `x i -> x0`, and `y i -> x0`. If `(x i, y i)`
maximizes

`(x', y') ↦ u x' - δ - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `closure C × closure C` for all `i` in a set belonging to `l`, then
`(x i, y i)` maximizes the same function on `C × C` for all `i` in a set
belonging to `l`.
-/
theorem eventually_isMaxOn_shifted_doubledObjective_restrict_closure_of_tendsto
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hx : Tendsto x l (nhds x0)) (hy : Tendsto y l (nhds x0))
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i)) :
    ∀ᶠ i in l,
      0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
        IsMaxOn
          (fun q : DoubledPoint n =>
            doubledObjective (fun z : Point n => u z - δ) v (α i) q)
          (C ×ˢ C) (x i, y i) :=
  eventually_isMaxOn_doubledObjective_restrict_closure hmax
    (hboundary.eventually_pair_mem_of_tendsto_of_shifted_gap
      hδ hx0closure hgap hx hy)

/--
Suppose `(x i, y i)` maximizes the shifted doubled-variable objective on
`closure C × closure C` for all `i` in a set belonging to `l`. If
`z ∈ closure C`, then, for all `i` in a set belonging to `l`,

`u z - δ - v z ≤ u (x i) - δ - v (y i)`.
-/
theorem eventually_shifted_value_sub_ge_of_closure_maximizers
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hz : z ∈ closure C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i)) :
    ∀ᶠ i in l, u z - δ - v z <= u (x i) - δ - v (y i) := by
  filter_upwards [hmax] with i hi
  rcases hi with ⟨hαi, _hxiclosure, _hyiclosure, hmaxi⟩
  have hdiag : (z, z) ∈ closure C ×ˢ closure C := ⟨hz, hz⟩
  have hcompare := hmaxi hdiag
  have hpen_nonneg :
      0 <= quadraticPenalty (α i) (x i) (y i) :=
    quadraticPenalty_nonneg hαi.le (x i) (y i)
  have hcompare' :
      u z - δ - v z <=
        u (x i) - δ - v (y i) - quadraticPenalty (α i) (x i) (y i) := by
    simpa [doubledObjective, quadraticPenalty_self] using hcompare
  linarith

/--
Assume `u ≤ v` on `frontier C` and `δ > 0`. Suppose `x0 ∈ closure C`,
`v x0 < u x0 - δ`, `x i -> x0`, and `y i -> x0`. Suppose also that, for
all `i` in a set belonging to `l`, `(x i, y i)` maximizes

`(x', y') ↦ u x' - δ - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `closure C × closure C`. If the shifted function `x ↦ u x - δ` has
values in `R` on `C`, and if

`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`

tends to `0` through positive values along `l`, then the selected data
satisfy
`StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v l α x y`.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_shifted_closure_maximizers_of_tendsto
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hx : Tendsto x l (nhds x0)) (hy : Tendsto y l (nhds x0))
    (huR : ScalarRangeOn C R (fun z : Point n => u z - δ))
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i))
    (hscale :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖)
        l (nhdsWithin 0 (Set.Ioi 0))) :
    StrictDoubledVariableLocalizationAlongOn C R (fun z : Point n => u z - δ)
      v l α x y := by
  have hx0C : x0 ∈ C :=
    hboundary.mem_of_mem_closure_of_shifted_gap hδ hx0closure hgap
  have hfail : ∃ z : Point n, z ∈ C ∧ v z < u z - δ :=
    ⟨x0, hx0C, hgap⟩
  have hmaxC :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (C ×ˢ C) (x i, y i) :=
    eventually_isMaxOn_shifted_doubledObjective_restrict_closure_of_tendsto
      hboundary hδ hx0closure hgap hx hy hmax
  have hrange :
      ∀ᶠ i in l, (fun z : Point n => u z - δ) (x i) ∈ R :=
    eventually_scalarRange_of_eventually_isMaxOn_doubledObjective huR hmaxC
  have hvyux :
      ∀ᶠ i in l, v (y i) <= (fun z : Point n => u z - δ) (x i) :=
    eventually_value_right_le_left_of_eventually_isMaxOn_doubledObjective hfail hmaxC
  intro _hfail
  refine ⟨?_, hscale⟩
  filter_upwards [hmaxC, hrange, hvyux] with i hmaxi hri hvyi
  rcases hmaxi with ⟨hαi, hxi, hyi, hmaxi⟩
  exact ⟨hαi, hxi, hyi, hri, hvyi, hmaxi⟩

/--
Let `u` be bounded on `C`, and let `x i` and `y i` belong to `C` for all
`i` in a set belonging to `l`. Then there exist real numbers `m` and `M`
such that, for all `i` in a set belonging to `l`,
`m ≤ u (y i)` and `u (x i) ≤ M`.
-/
theorem ValueBoundedOn.eventually_selected_bounds_of_eventually_mem
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u : Point n -> Real} {x y : ι -> Point n}
    (hu : ValueBoundedOn C u)
    (hmem : ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C) :
    ∃ m M : Real, ∀ᶠ i in l, m <= u (y i) ∧ u (x i) <= M := by
  rcases hu with ⟨m, M, hbound⟩
  refine ⟨m, M, ?_⟩
  filter_upwards [hmem] with i hi
  exact ⟨(hbound (y i) hi.2).1, (hbound (x i) hi.1).2⟩

/--
Let `u` be bounded on `C`. If, for all `i` in a set belonging to `l`, `x i`
and `y i` belong to `C` and `(x i, y i)` maximizes the doubled-variable
objective on `C × C`, then there exist real numbers `m` and `M` such that,
for all `i` in a set belonging to `l`,
`m ≤ u (y i)` and `u (x i) ≤ M`.
-/
theorem ValueBoundedOn.eventually_selected_bounds_of_eventually_isMaxOn
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hu : ValueBoundedOn C u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ∃ m M : Real, ∀ᶠ i in l, m <= u (y i) ∧ u (x i) <= M :=
  hu.eventually_selected_bounds_of_eventually_mem <| by
    filter_upwards [hmax] with i hi
    exact ⟨hi.2.1, hi.2.2.1⟩

/--
Let `s i` be real numbers. If `s i -> 0` along `l` and `0 < s i` for all
`i` in a set belonging to `l`, then `s i -> 0` through positive values along
`l`.
-/
theorem tendsto_nhdsWithin_Ioi_of_tendsto_nhds_of_eventually_pos
    {ι : Type*} {l : Filter ι} {s : ι -> Real}
    (hzero : Tendsto s l (nhds 0)) (hpos : ∀ᶠ i in l, 0 < s i) :
    Tendsto s l (nhdsWithin 0 (Set.Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hzero hpos

/--
Let `α i`, `x i`, and `y i` be selected doubled-variable data along a filter
`l`. If, for all `i` in a set belonging to `l`, `α i > 0`, and if
`x i ≠ y i` for all `i` in a set belonging to `l`, then for all `i` in a set
belonging to `l`,

`0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`.
-/
theorem eventually_comparisonScale_pos_of_eventually_isMaxOn_of_eventually_ne
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hne : ∀ᶠ i in l, x i ≠ y i) :
    ∀ᶠ i in l, 0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ := by
  filter_upwards [hmax, hne] with i hmaxi hnei
  exact comparisonScale_pos_of_ne hmaxi.1 hnei

/--
Suppose `α i`, `x i`, and `y i` are selected doubled-variable data along a
filter `l`. If, for all `i` in a set belonging to `l`, `α i > 0`,
`x i ∈ C`, `y i ∈ C`, and `(x i, y i)` maximizes the doubled-variable
objective on `C × C`; if `u (x i) ∈ R` and `v (y i) ≤ u (x i)` also hold for
all `i` in a set belonging to `l`; and if

`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`

tends to `0` through positive values along `l`; then
`StrictDoubledVariableLocalizationAlongOn C R u v l α x y` holds.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hrange : ∀ᶠ i in l, u (x i) ∈ R)
    (hvyux : ∀ᶠ i in l, v (y i) <= u (x i))
    (hscale :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖)
        l (nhdsWithin 0 (Set.Ioi 0))) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y := by
  intro _hfail
  refine ⟨?_, hscale⟩
  filter_upwards [hmax, hrange, hvyux] with i hmaxi hri hvyi
  rcases hmaxi with ⟨hαi, hxi, hyi, hmaxi⟩
  exact ⟨hαi, hxi, hyi, hri, hvyi, hmaxi⟩

/--
Suppose selected doubled-variable maximizers are available along a filter
`l`, and suppose the associated scales tend to `0` through positive values
along `l`. If there exists `z ∈ C` such that `v z < u z`, and if
`u x ∈ R` for every `x ∈ C`, then these selected data satisfy
`StrictDoubledVariableLocalizationAlongOn C R u v l α x y`.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hfail : ∃ z : Point n, z ∈ C ∧ v z < u z)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hscale :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖)
        l (nhdsWithin 0 (Set.Ioi 0))) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y :=
  strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers
    hmax
    (eventually_scalarRange_of_eventually_isMaxOn_doubledObjective huR hmax)
    (eventually_value_right_le_left_of_eventually_isMaxOn_doubledObjective hfail hmax)
    hscale

/--
Suppose selected doubled-variable maximizers are available along a filter
`l`. If there exists `z ∈ C` such that `v z < u z`, if
`ScalarRangeOn C R u` holds, if the selected scales tend to `0` along `l`,
and if the selected scales are positive for all `i` in a set belonging to
`l`, then these data satisfy
`StrictDoubledVariableLocalizationAlongOn C R u v l α x y`.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange_of_scale
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {R : Set Real} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hfail : ∃ z : Point n, z ∈ C ∧ v z < u z)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hscale_zero :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) l (nhds 0))
    (hscale_pos :
      ∀ᶠ i in l, 0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y :=
  strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange
    hfail huR hmax
    (tendsto_nhdsWithin_Ioi_of_tendsto_nhds_of_eventually_pos hscale_zero hscale_pos)

/--
If

`α i * ‖x i - y i‖ ^ 2 -> 0`

and

`‖x i - y i‖ -> 0`

along `l`, then the comparison scale

`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`

tends to `0` along `l`.
-/
theorem tendsto_comparisonScale_zero_of_tendsto_quadratic_and_distance
    {ι : Type*} {l : Filter ι} {α : ι -> Real} {x y : ι -> Point n}
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0)) :
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) l (nhds 0) := by
  simpa using hquad.add hdist

/--
Let `s i` and `e i` be real-valued functions on an index type with filter
`l`. If `s i ≥ 0` for all `i` in a set belonging to `l`, if
`s i ≤ 2 * e i` for all `i` in a set belonging to `l`, and if `e i -> 0`
along `l`, then `s i -> 0` along `l`.
-/
theorem tendsto_zero_of_eventually_nonneg_of_eventually_le_two_mul_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {s e : ι -> Real}
    (hs_nonneg : ∀ᶠ i in l, 0 <= s i)
    (hs_le : ∀ᶠ i in l, s i <= 2 * e i)
    (he : Tendsto e l (nhds 0)) :
    Tendsto s l (nhds 0) := by
  refine squeeze_zero' hs_nonneg hs_le ?_
  simpa using (tendsto_const_nhds.mul he : Tendsto (fun i : ι => 2 * e i) l (nhds (2 * 0)))

/--
Assume `(x i, y i)` maximizes the doubled-variable objective on `C × C` for
all `i` in a set belonging to `l`, and assume
`u (x i) - u (y i) -> 0` along `l`. Then
`α i * ‖x i - y i‖ ^ 2 -> 0` along `l`.
-/
theorem tendsto_weightedDistanceSq_zero_of_eventually_isMaxOn_of_tendsto_valueGap
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hgap : Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0)) :
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) := by
  refine tendsto_zero_of_eventually_nonneg_of_eventually_le_two_mul_of_tendsto_zero ?_ ?_ hgap
  · filter_upwards [hmax] with i hi
    exact mul_nonneg hi.1.le (sq_nonneg ‖x i - y i‖)
  · filter_upwards [hmax] with i hi
    rcases hi with ⟨hαi, _hxi, hyi, hmaxi⟩
    have hpen := quadraticPenalty_le_value_sub_value_of_isMaxOn_doubledObjective
      (C := C) (u := u) (v := v) (α := α i) (x := x i) (y := y i) hyi hmaxi
    have hnorm :=
      norm_weightedDistanceSq_le_quadraticPenalty_mul_two hαi.le (x i) (y i)
    nlinarith

/--
Let `α i`, `x i`, and `y i` be indexed by a filter `l`. If `α i -> +∞`
along `l` and, for all `i` in a set belonging to `l`,

`α i * ‖x i - y i‖ ^ 2 ≤ B`,

where `B` is a fixed real number, then `‖x i - y i‖ -> 0` along `l`.
-/
theorem tendsto_distance_zero_of_eventually_weightedDistanceSq_le_const_of_tendsto_atTop
    {ι : Type*} {l : Filter ι} {α : ι -> Real} {x y : ι -> Point n}
    {B : Real}
    (hα : Tendsto α l atTop)
    (hle : ∀ᶠ i in l, α i * ‖x i - y i‖ ^ 2 <= B) :
    Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) := by
  have hsquare :
      Tendsto (fun i : ι => ‖x i - y i‖ ^ 2) l (nhds 0) := by
    refine squeeze_zero'
      (f := fun i : ι => ‖x i - y i‖ ^ 2)
      (g := fun i : ι => B * (α i)⁻¹) ?_ ?_ ?_
    · exact Eventually.of_forall fun i => sq_nonneg ‖x i - y i‖
    · filter_upwards [eventually_pos_of_tendsto_atTop hα, hle] with i hαi hlei
      have hsq : 0 <= ‖x i - y i‖ ^ 2 := sq_nonneg ‖x i - y i‖
      have hinv_nonneg : 0 <= (α i)⁻¹ := inv_nonneg.mpr hαi.le
      calc
        ‖x i - y i‖ ^ 2 =
            (α i * ‖x i - y i‖ ^ 2) * (α i)⁻¹ := by
              field_simp [ne_of_gt hαi]
        _ <= B * (α i)⁻¹ := mul_le_mul_of_nonneg_right hlei hinv_nonneg
    · simpa using
        (tendsto_const_nhds.mul hα.inv_tendsto_atTop :
          Tendsto (fun i : ι => B * (α i)⁻¹) l (nhds (B * 0)))
  have hsqrt :
      Tendsto (fun i : ι => √(‖x i - y i‖ ^ 2)) l (nhds 0) := by
    simpa using hsquare.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt

/--
Assume `(x i, y i)` maximizes the doubled-variable objective on `C × C` for
all `i` in a set belonging to `l`. Assume also that, for all `i` in a set
belonging to `l`, `m ≤ u (y i)` and `u (x i) ≤ M`. Then, for all `i` in a set
belonging to `l`,

`α i * ‖x i - y i‖ ^ 2 ≤ 2 * (M - m)`.
-/
theorem eventually_weightedDistanceSq_le_two_value_range_of_eventually_isMaxOn
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n} {m M : Real}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hbounds : ∀ᶠ i in l, m <= u (y i) ∧ u (x i) <= M) :
    ∀ᶠ i in l, α i * ‖x i - y i‖ ^ 2 <= 2 * (M - m) := by
  filter_upwards [hmax, hbounds] with i hmaxi hboundsi
  rcases hmaxi with ⟨hαi, _hxi, hyi, hmaxi⟩
  exact weightedDistanceSq_le_two_value_range_of_isMaxOn_doubledObjective
    (C := C) (u := u) (v := v) (α := α i) (m := m) (M := M)
    (x := x i) (y := y i) hαi.le hyi hboundsi.1 hboundsi.2 hmaxi

/--
Assume `(x i, y i)` maximizes the doubled-variable objective on `C × C` for
all `i` in a set belonging to `l`. If `α i -> +∞` along `l` and, for all
`i` in a set belonging to `l`, `m ≤ u (y i)` and `u (x i) ≤ M`, then
`‖x i - y i‖ -> 0` along `l`.
-/
theorem tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_value_bounds
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n} {m M : Real}
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hα : Tendsto α l atTop)
    (hbounds : ∀ᶠ i in l, m <= u (y i) ∧ u (x i) <= M) :
    Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) :=
  tendsto_distance_zero_of_eventually_weightedDistanceSq_le_const_of_tendsto_atTop
    hα
    (eventually_weightedDistanceSq_le_two_value_range_of_eventually_isMaxOn
      hmax hbounds)

/--
Assume `(x i, y i)` maximizes the doubled-variable objective on `C × C` for
all `i` in a set belonging to `l`. Suppose `z ∈ C`, and suppose there are
real numbers `m` and `M` such that, for all `i` in a set belonging to `l`,
`m ≤ v (y i)` and `u (x i) ≤ M`. Then, for all `i` in a set belonging to
`l`,

`α i * ‖x i - y i‖ ^ 2 ≤ 2 * (M - m - (u z - v z))`.
-/
theorem eventually_weightedDistanceSq_le_two_value_sub_value_at_diagonal_range_of_eventually_isMaxOn
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n} {z : Point n} {m M : Real}
    (hz : z ∈ C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hbounds : ∀ᶠ i in l, m <= v (y i) ∧ u (x i) <= M) :
    ∀ᶠ i in l,
      α i * ‖x i - y i‖ ^ 2 <= 2 * (M - m - (u z - v z)) := by
  filter_upwards [hmax, hbounds] with i hmaxi hboundsi
  rcases hmaxi with ⟨hαi, _hxi, _hyi, hmaxi⟩
  exact weightedDistanceSq_le_two_value_sub_value_at_diagonal_range_of_isMaxOn
    (C := C) (u := u) (v := v) (α := α i) (m := m) (M := M)
    (x := x i) (y := y i) (z := z) hαi.le hz hboundsi.1 hboundsi.2 hmaxi

/--
Assume `(x i, y i)` maximizes the doubled-variable objective on `C × C` for
all `i` in a set belonging to `l`. If `α i -> +∞` along `l`, `z ∈ C`, and
there are real numbers `m` and `M` such that, for all `i` in a set belonging
to `l`, `m ≤ v (y i)` and `u (x i) ≤ M`, then
`‖x i - y i‖ -> 0` along `l`.
-/
theorem tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_uv_bounds
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n} {z : Point n} {m M : Real}
    (hz : z ∈ C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hα : Tendsto α l atTop)
    (hbounds : ∀ᶠ i in l, m <= v (y i) ∧ u (x i) <= M) :
    Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) :=
  tendsto_distance_zero_of_eventually_weightedDistanceSq_le_const_of_tendsto_atTop
    hα
    (eventually_weightedDistanceSq_le_two_value_sub_value_at_diagonal_range_of_eventually_isMaxOn
      hz hmax hbounds)

end ViscositySolns
