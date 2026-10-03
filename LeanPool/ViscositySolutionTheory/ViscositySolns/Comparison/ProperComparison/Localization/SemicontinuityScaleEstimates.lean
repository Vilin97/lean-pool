/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Localization.SelectedMaximizers

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Doubled-variable localization estimates for proper comparison. (SemicontinuityScaleEstimates)

Part of the doubled-variable localization estimates for proper comparison.
Split from `Localization.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Let `u` be bounded above on `C`, and let `v` be bounded below on `C`. If, for
all `i` in a set belonging to `l`, `x i ∈ C` and `y i ∈ C`, then there exist
real numbers `m` and `M` such that, for all `i` in a set belonging to `l`,
`m ≤ v (y i)` and `u (x i) ≤ M`.
-/
theorem eventually_uv_bounds_of_upper_lowerBoundedOn_of_eventually_mem
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real} {x y : ι -> Point n}
    (hu : ValueUpperBoundedOn C u) (hv : ValueLowerBoundedOn C v)
    (hmem : ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C) :
    ∃ m M : Real, ∀ᶠ i in l, m <= v (y i) ∧ u (x i) <= M := by
  rcases hu with ⟨M, hM⟩
  rcases hv with ⟨m, hm⟩
  exact ⟨m, M, by
    filter_upwards [hmem] with i hi
    exact ⟨hm (y i) hi.2, hM (x i) hi.1⟩⟩

/--
Let `u` be bounded above on `C`, and let `v` be bounded below on `C`. If
`(x i, y i)` maximizes the doubled-variable objective on `C × C` for all
`i` in a set belonging to `l`, then there exist real numbers `m` and `M`
such that, for all `i` in a set belonging to `l`, `m ≤ v (y i)` and
`u (x i) ≤ M`.
-/
theorem eventually_uv_bounds_of_upper_lowerBoundedOn_of_eventually_isMaxOn
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n}
    (hu : ValueUpperBoundedOn C u) (hv : ValueLowerBoundedOn C v)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ∃ m M : Real, ∀ᶠ i in l, m <= v (y i) ∧ u (x i) <= M :=
  eventually_uv_bounds_of_upper_lowerBoundedOn_of_eventually_mem hu hv <| by
    filter_upwards [hmax] with i hi
    exact ⟨hi.2.1, hi.2.2.1⟩

/--
Let `u : R^n -> R` be continuous at `z`. If `x i -> z` and `y i -> z` along
`l`, then `u (x i) - u (y i) -> 0` along `l`.
-/
theorem tendsto_valueGap_zero_of_continuousAt_of_tendsto_same
    {ι : Type*} {l : Filter ι} {u : Point n -> Real} {x y : ι -> Point n}
    {z : Point n}
    (hu : ContinuousAt u z)
    (hx : Tendsto x l (nhds z)) (hy : Tendsto y l (nhds z)) :
    Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0) := by
  have hxv : Tendsto (fun i : ι => u (x i)) l (nhds (u z)) := hu.tendsto.comp hx
  have hyv : Tendsto (fun i : ι => u (y i)) l (nhds (u z)) := hu.tendsto.comp hy
  simpa using hxv.sub hyv

/--
Let `u : R^n -> R` be continuous at `z`. If `(x i, y i) -> (z, z)` along
`l`, then `u (x i) - u (y i) -> 0` along `l`.
-/
theorem tendsto_valueGap_zero_of_continuousAt_of_tendsto_pair_diagonal
    {ι : Type*} {l : Filter ι} {u : Point n -> Real} {x y : ι -> Point n}
    {z : Point n}
    (hu : ContinuousAt u z)
    (hxy : Tendsto (fun i : ι => (x i, y i)) l (nhds (z, z))) :
    Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0) := by
  have hx : Tendsto x l (nhds z) := by
    exact (continuous_fst.tendsto (z, z)).comp hxy
  have hy : Tendsto y l (nhds z) := by
    exact (continuous_snd.tendsto (z, z)).comp hxy
  exact tendsto_valueGap_zero_of_continuousAt_of_tendsto_same hu hx hy

/--
If `x i -> z` and `‖x i - y i‖ -> 0` along `l`, then `y i -> z` along `l`.
-/
theorem tendsto_right_of_tendsto_left_of_tendsto_distance_zero
    {ι : Type*} {l : Filter ι} {x y : ι -> Point n} {z : Point n}
    (hx : Tendsto x l (nhds z))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0)) :
    Tendsto y l (nhds z) := by
  have hdiff : Tendsto (fun i : ι => x i - y i) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hdist
  have hy' : Tendsto (fun i : ι => x i - (x i - y i)) l (nhds (z - 0)) :=
    hx.sub hdiff
  have hy_eq : (fun i : ι => x i - (x i - y i)) = y := by
    funext i
    abel
  simpa [hy_eq]
    using hy'

/--
If `x i -> z` and `‖x i - y i‖ -> 0` along `l`, then
`(x i, y i) -> (z, z)` along `l`.
-/
theorem tendsto_pair_diagonal_of_tendsto_left_of_tendsto_distance_zero
    {ι : Type*} {l : Filter ι} {x y : ι -> Point n} {z : Point n}
    (hx : Tendsto x l (nhds z))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0)) :
    Tendsto (fun i : ι => (x i, y i)) l (nhds (z, z)) := by
  exact hx.prodMk_nhds
    (tendsto_right_of_tendsto_left_of_tendsto_distance_zero hx hdist)

/--
If `x i -> z` within `C`, if `y i ∈ C` for all `i` in a set belonging to
`l`, and if `‖x i - y i‖ -> 0` along `l`, then `y i -> z` within `C` along
`l`.
-/
theorem tendsto_right_nhdsWithin_of_tendsto_left_nhdsWithin_of_tendsto_distance_zero
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {x y : ι -> Point n} {z : Point n}
    (hx : Tendsto x l (nhdsWithin z C))
    (hyC : ∀ᶠ i in l, y i ∈ C)
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0)) :
    Tendsto y l (nhdsWithin z C) := by
  have hx_ambient : Tendsto x l (nhds z) :=
    tendsto_nhds_of_tendsto_nhdsWithin hx
  have hy_ambient : Tendsto y l (nhds z) :=
    tendsto_right_of_tendsto_left_of_tendsto_distance_zero hx_ambient hdist
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within y hy_ambient hyC

/--
If `‖x i - z‖ -> 0` along `l` and `x i ∈ C` for all `i` in a set belonging
to `l`, then `x i -> z` within `C` along `l`.
-/
theorem tendsto_nhdsWithin_of_tendsto_norm_sub_zero_of_eventually_mem
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {x : ι -> Point n} {z : Point n}
    (hxz : Tendsto (fun i : ι => ‖x i - z‖) l (nhds 0))
    (hxC : ∀ᶠ i in l, x i ∈ C) :
    Tendsto x l (nhdsWithin z C) := by
  have hx : Tendsto x l (nhds z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hxz
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x hx hxC

/--
Let `u : R^n -> R` be continuous at `z` relative to `C`. If
`x i -> z` within `C` and `y i -> z` within `C` along `l`, then
`u (x i) - u (y i) -> 0` along `l`.
-/
theorem tendsto_valueGap_zero_of_continuousWithinAt_of_tendsto_same
    {ι : Type*} {l : Filter ι} {C : Set (Point n)} {u : Point n -> Real}
    {x y : ι -> Point n} {z : Point n}
    (hu : ContinuousWithinAt u C z)
    (hx : Tendsto x l (nhdsWithin z C)) (hy : Tendsto y l (nhdsWithin z C)) :
    Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0) := by
  have hxv : Tendsto (fun i : ι => u (x i)) l (nhds (u z)) := hu.tendsto.comp hx
  have hyv : Tendsto (fun i : ι => u (y i)) l (nhds (u z)) := hu.tendsto.comp hy
  simpa using hxv.sub hyv

/--
Let `u` be upper semicontinuous at `z` relative to `C`, and let `v` be lower
semicontinuous at `z` relative to `C`. If `x i -> z` within `C` and
`y i -> z` within `C` along `l`, then for every real number `ε > 0`,

`u (x i) - v (y i) < u z - v z + ε`

for all `i` in a set belonging to `l`.
-/
theorem eventually_value_sub_lt_of_upper_lowerSemicontinuousWithinAt_of_tendsto_same
    {ι : Type*} {l : Filter ι} {C : Set (Point n)} {u v : Point n -> Real}
    {x y : ι -> Point n} {z : Point n} {ε : Real}
    (hu : UpperSemicontinuousWithinAt u C z)
    (hv : LowerSemicontinuousWithinAt v C z)
    (hx : Tendsto x l (nhdsWithin z C)) (hy : Tendsto y l (nhdsWithin z C))
    (hε : 0 < ε) :
    ∀ᶠ i in l, u (x i) - v (y i) < u z - v z + ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hux :
      ∀ᶠ p in nhdsWithin z C, u p < u z + ε / 2 :=
    hu (u z + ε / 2) (by linarith)
  have hvy :
      ∀ᶠ p in nhdsWithin z C, v z - ε / 2 < v p :=
    hv (v z - ε / 2) (by linarith)
  filter_upwards [hx hux, hy hvy] with i hxi hyi
  change u (x i) < u z + ε / 2 at hxi
  change v z - ε / 2 < v (y i) at hyi
  linarith

/--
Let `(x i, y i)` maximize the shifted doubled-variable objective on
`closure C × closure C` for all `i` in a set belonging to `l`. Suppose
`z ∈ C`, `v z < u z - δ`, and `x0 ∈ closure C`. If `x i -> x0` and
`y i -> x0` within `closure C`, and if `x ↦ u x - δ` is upper
semicontinuous on `closure C` while `v` is lower semicontinuous on
`closure C`, then
`v x0 < u x0 - δ`.
-/
theorem shifted_gap_at_limit_of_closure_maximizers
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {z x0 : Point n}
    (hz : z ∈ C) (hgap : v z < u z - δ) (hx0closure : x0 ∈ closure C)
    (hu : UpperSemicontinuousOn (fun z : Point n => u z - δ) (closure C))
    (hv : LowerSemicontinuousOn v (closure C))
    (hx : Tendsto x l (nhdsWithin x0 (closure C)))
    (hy : Tendsto y l (nhdsWithin x0 (closure C)))
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i)) :
    v x0 < u x0 - δ := by
  have hzclosure : z ∈ closure C := subset_closure hz
  have hgap_pos : 0 < u z - δ - v z := by
    linarith
  have hε : 0 < (u z - δ - v z) / 2 := by
    linarith
  have hlower :
      ∀ᶠ i in l, u z - δ - v z <= u (x i) - δ - v (y i) :=
    eventually_shifted_value_sub_ge_of_closure_maximizers hzclosure hmax
  have hupper :
    ∀ᶠ i in l,
        (fun z : Point n => u z - δ) (x i) - v (y i) <
          (fun z : Point n => u z - δ) x0 - v x0 +
            (u z - δ - v z) / 2 :=
    eventually_value_sub_lt_of_upper_lowerSemicontinuousWithinAt_of_tendsto_same
      (hu x0 hx0closure) (hv x0 hx0closure) hx hy hε
  rcases (hlower.and hupper).exists with ⟨i, hlower_i, hupper_i⟩
  change u (x i) - δ - v (y i) <
      u x0 - δ - v x0 + (u z - δ - v z) / 2 at hupper_i
  have hpositive : 0 < u x0 - δ - v x0 := by
    linarith
  linarith

/--
Let `(x i, y i)` maximize the doubled-variable objective on `C × C` for all
`i` in a set belonging to `l`. Suppose `z ∈ C`, `u` is upper semicontinuous
on `C`, `v` is lower semicontinuous on `C`, `x i -> z` within `C`, and
`y i -> z` within `C`, all along `l`. Then

`α i * ‖x i - y i‖ ^ 2 -> 0`

along `l`.
-/
theorem tendsto_weightedDistanceSq_zero_of_eventually_isMaxOn_of_semicontinuousOn_of_tendsto_same
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real}
    {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v C)
    (hz : z ∈ C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhdsWithin z C)) (hy : Tendsto y l (nhdsWithin z C)) :
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [hmax] with i hi
    exact lt_of_lt_of_le hb (mul_nonneg hi.1.le (sq_nonneg ‖x i - y i‖))
  · intro b hb
    have hb2 : 0 < b / 2 := by linarith
    have hvalue :
        ∀ᶠ i in l, u (x i) - v (y i) < u z - v z + b / 2 :=
      eventually_value_sub_lt_of_upper_lowerSemicontinuousWithinAt_of_tendsto_same
        (hu z hz) (hv z hz) hx hy hb2
    filter_upwards [hmax, hvalue] with i hi hvalue_i
    rcases hi with ⟨hαi, _hxi, _hyi, hmaxi⟩
    have hpenalty :=
      quadraticPenalty_le_value_sub_value_at_diagonal_of_isMaxOn_doubledObjective
        (C := C) (u := u) (v := v) (α := α i)
        (x := x i) (y := y i) (z := z) hz hmaxi
    have hpenalty' :
        (α i / 2) * ‖x i - y i‖ ^ 2 <=
          u (x i) - v (y i) - (u z - v z) := by
      have hnorm :=
        norm_weightedDistanceSq_le_quadraticPenalty_mul_two hαi.le (x i) (y i)
      nlinarith
    have hright : u (x i) - v (y i) - (u z - v z) < b / 2 := by
      linarith
    have hhalf : (α i / 2) * ‖x i - y i‖ ^ 2 < b / 2 :=
      lt_of_le_of_lt hpenalty' hright
    nlinarith

/--
Assume `u ≤ v` on `frontier C` and `δ > 0`. Suppose `x0 ∈ closure C`,
`v x0 < u x0 - δ`, `x i -> x0` and `y i -> x0` within `closure C`, and
`(x i, y i)` maximizes the shifted doubled-variable objective on
`closure C × closure C` for all `i` in a set belonging to `l`. If
`x ↦ u x - δ` is upper semicontinuous on `closure C` and `v` is lower
semicontinuous on `closure C`, then

`α i * ‖x i - y i‖ ^ 2 -> 0`

along `l`.
-/
theorem tendsto_weightedDistanceSq_zero_of_shifted_closure_maximizers_of_tendsto
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hu : UpperSemicontinuousOn (fun z : Point n => u z - δ) (closure C))
    (hv : LowerSemicontinuousOn v (closure C))
    (hx : Tendsto x l (nhdsWithin x0 (closure C)))
    (hy : Tendsto y l (nhdsWithin x0 (closure C)))
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i)) :
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) := by
  let w : Point n -> Real := fun z => u z - δ
  have hx0C : x0 ∈ C :=
    hboundary.mem_of_mem_closure_of_shifted_gap hδ hx0closure hgap
  have hx_ambient : Tendsto x l (nhds x0) :=
    tendsto_nhds_of_tendsto_nhdsWithin hx
  have hy_ambient : Tendsto y l (nhds x0) :=
    tendsto_nhds_of_tendsto_nhdsWithin hy
  have hmem :
      ∀ᶠ i in l, x i ∈ C ∧ y i ∈ C :=
    hboundary.eventually_pair_mem_of_tendsto_of_shifted_gap
      hδ hx0closure hgap hx_ambient hy_ambient
  have hmaxC :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective w v (α i) q)
            (C ×ˢ C) (x i, y i) := by
    simpa [w] using
      eventually_isMaxOn_doubledObjective_restrict_closure
        (C := C) (u := w) (v := v) hmax hmem
  have hxC : Tendsto x l (nhdsWithin x0 C) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x hx_ambient
      (hmem.mono fun _ hi => hi.1)
  have hyC : Tendsto y l (nhdsWithin x0 C) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within y hy_ambient
      (hmem.mono fun _ hi => hi.2)
  have huC : UpperSemicontinuousOn w C :=
    hu.mono subset_closure
  have hvC : LowerSemicontinuousOn v C :=
    hv.mono subset_closure
  exact tendsto_weightedDistanceSq_zero_of_eventually_isMaxOn_of_semicontinuousOn_of_tendsto_same
    huC hvC hx0C hmaxC hxC hyC

/--
Assume `α i * ‖x i - y i‖ ^ 2 -> 0` along `l`, and assume that
`1 ≤ α i` for all `i` in a set belonging to `l`. Then
`‖x i - y i‖ -> 0` along `l`.
-/
theorem tendsto_distance_zero_of_tendsto_weightedDistanceSq_of_eventually_one_le
    {ι : Type*} {l : Filter ι} {α : ι -> Real} {x y : ι -> Point n}
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) := by
  have hsquare :
      Tendsto (fun i : ι => ‖x i - y i‖ ^ 2) l (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hquad
    · exact Eventually.of_forall fun i => sq_nonneg ‖x i - y i‖
    · filter_upwards [hαone] with i hαi
      have hsq : 0 <= ‖x i - y i‖ ^ 2 := sq_nonneg ‖x i - y i‖
      calc
        ‖x i - y i‖ ^ 2 = 1 * ‖x i - y i‖ ^ 2 := by ring
        _ <= α i * ‖x i - y i‖ ^ 2 := mul_le_mul_of_nonneg_right hαi hsq
  have hsqrt :
      Tendsto (fun i : ι => √(‖x i - y i‖ ^ 2)) l (nhds 0) := by
    simpa using hsquare.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt

/--
Under the hypotheses of
`tendsto_weightedDistanceSq_zero_of_shifted_closure_maximizers_of_tendsto`,
if additionally `α i -> +∞`, then

`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ -> 0`

along `l`.
-/
theorem tendsto_comparisonScale_zero_of_shifted_closure_maximizers_of_tendsto_atTop
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    {α : ι -> Real} {x y : ι -> Point n} {x0 : Point n}
    (hboundary : BoundaryComparisonOn C u v) (hδ : 0 < δ)
    (hx0closure : x0 ∈ closure C) (hgap : v x0 < u x0 - δ)
    (hu : UpperSemicontinuousOn (fun z : Point n => u z - δ) (closure C))
    (hv : LowerSemicontinuousOn v (closure C))
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
    Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) l (nhds 0) := by
  have hquad :
      Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) :=
    tendsto_weightedDistanceSq_zero_of_shifted_closure_maximizers_of_tendsto
      hboundary hδ hx0closure hgap hu hv hx hy hmax
  have hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) :=
    tendsto_distance_zero_of_tendsto_weightedDistanceSq_of_eventually_one_le
      hquad (eventually_one_le_of_tendsto_atTop hα)
  exact tendsto_comparisonScale_zero_of_tendsto_quadratic_and_distance hquad hdist

/--
Assume `α i * ‖x i - y i‖ ^ 2 -> 0` along `l`, assume that
`1 ≤ α i` for all `i` in a set belonging to `l`, and assume that
`x i ≠ y i` for all `i` in a set belonging to `l`. Then
`DoubledVariableScaleEstimatesAlong l α x y` holds.
-/
theorem doubledVariableScaleEstimatesAlong_of_quadratic_of_eventually_one_le_of_ne
    {ι : Type*} {l : Filter ι} {α : ι -> Real} {x y : ι -> Point n}
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hαone : ∀ᶠ i in l, 1 <= α i)
    (hne : ∀ᶠ i in l, x i ≠ y i) :
    DoubledVariableScaleEstimatesAlong l α x y :=
  ⟨hquad,
    tendsto_distance_zero_of_tendsto_weightedDistanceSq_of_eventually_one_le
      hquad hαone,
    hne⟩

/--
Assume `α i * ‖x i - y i‖ ^ 2 -> 0` along `l`, assume `α i -> +∞` along
`l`, and assume `{i | x i ≠ y i}` belongs to `l`. Then
`DoubledVariableScaleEstimatesAlong l α x y` holds.
-/
theorem doubledVariableScaleEstimatesAlong_of_quadratic_of_tendsto_atTop_of_ne
    {ι : Type*} {l : Filter ι} {α : ι -> Real} {x y : ι -> Point n}
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hα : Tendsto α l atTop)
    (hne : ∀ᶠ i in l, x i ≠ y i) :
    DoubledVariableScaleEstimatesAlong l α x y :=
  doubledVariableScaleEstimatesAlong_of_quadratic_of_eventually_one_le_of_ne
    hquad (eventually_one_le_of_tendsto_atTop hα) hne

/--
Suppose selected doubled-variable maximizers are available along a filter
`l`. If there exists `z ∈ C` such that `v z < u z`, if
`ScalarRangeOn C R u` holds, if
`α i * ‖x i - y i‖ ^ 2 -> 0`, if `‖x i - y i‖ -> 0`, and if the selected
scale is positive for all `i` in a set belonging to `l`, then these data
satisfy `StrictDoubledVariableLocalizationAlongOn C R u v l α x y`.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange_of_scales
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
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0))
    (hscale_pos :
      ∀ᶠ i in l, 0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y :=
  strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange_of_scale
    hfail huR hmax
    (tendsto_comparisonScale_zero_of_tendsto_quadratic_and_distance hquad hdist)
    hscale_pos

/--
Suppose selected doubled-variable maximizers are available along a filter
`l`. If there exists `z ∈ C` such that `v z < u z`, if
`ScalarRangeOn C R u` holds, if
`α i * ‖x i - y i‖ ^ 2 -> 0`, if `‖x i - y i‖ -> 0`, and if `x i ≠ y i`
for all `i` in a set belonging to `l`, then these data satisfy
`StrictDoubledVariableLocalizationAlongOn C R u v l α x y`.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_scales_of_ne
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
    (hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0))
    (hne : ∀ᶠ i in l, x i ≠ y i) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y :=
  strictDoubledVariableLocalizationAlongOn_of_eventually_maximizers_of_scalarRange_of_scales
    hfail huR hmax hquad hdist
    (eventually_comparisonScale_pos_of_eventually_isMaxOn_of_eventually_ne hmax hne)

/--
Assume there are functions `α : ι -> R` and `x y : ι -> R^n` such that, for
all `i` in a set belonging to `l`, one has `0 < α i`, `x i ∈ C`, `y i ∈ C`,
and `(x i, y i)` maximizes
`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
on `C × C`.

If there exists `z ∈ C` such that `v z < u z`, if `ScalarRangeOn C R u`
holds, and if `DoubledVariableScaleEstimatesAlong l α x y` holds, then
`StrictDoubledVariableLocalizationAlongOn C R u v l α x y` holds.
-/
theorem strictDoubledVariableLocalizationAlongOn_of_scaleEstimates
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
    (hscale : DoubledVariableScaleEstimatesAlong l α x y) :
    StrictDoubledVariableLocalizationAlongOn C R u v l α x y :=
  strictDoubledVariableLocalizationAlongOn_of_scales_of_ne
    hfail huR hmax hscale.1 hscale.2.1 hscale.2.2

end ViscositySolns
