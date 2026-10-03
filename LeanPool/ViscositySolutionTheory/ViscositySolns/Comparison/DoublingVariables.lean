/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Doubling variables

This file contains the basic functions used in the doubling-of-variables
argument for comparison theorems.

For functions `u v : R^n -> R` and a parameter `α`, the central expression is

`u x - v y - (α / 2) * ∑ i, (x i - y i)^2`.

The first-order components of the quadratic penalty are recorded explicitly as
`α • (x - y)` and `-α • (x - y)`.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/-- The product space used in the doubling-of-variables argument. -/
abbrev DoubledPoint (n : Nat) : Type :=
  Point n × Point n

/--
The coordinate quadratic penalty

`(α / 2) * ∑ i, (x i - y i)^2`.

This is the differentiable Euclidean quadratic form used in the matrix
inequalities. The ambient topology on `Point n` is still Lean's finite product
topology, and the finite-dimensional comparison lemmas in `Foundation.lean`
relate this quadratic form to the norm used in little-oh statements.
-/
def quadraticPenalty (α : Real) (x y : Point n) : Real :=
  (α / 2) * dotProduct (x - y) (x - y)

/--
The doubled-variable objective

`u x - v y - (α / 2) * ∑ i, (x i - y i)^2`.
-/
def doubledObjective (u v : Point n -> Real) (α : Real) (q : DoubledPoint n) :
    Real :=
  u q.1 - v q.2 - quadraticPenalty α q.1 q.2

/-- The derivative of the quadratic penalty with respect to the first variable. -/
def quadraticPenaltyGradientLeft (α : Real) (x y : Point n) : Point n :=
  α • (x - y)

/-- The derivative of the quadratic penalty with respect to the second variable. -/
def quadraticPenaltyGradientRight (α : Real) (x y : Point n) : Point n :=
  -α • (x - y)

/-- The Hessian block of the quadratic penalty in the first variable. -/
def quadraticPenaltyHessianLeftLeft (α : Real) : Hessian n :=
  α • (1 : Hessian n)

/-- The mixed Hessian block of the quadratic penalty. -/
def quadraticPenaltyHessianLeftRight (α : Real) : Hessian n :=
  -α • (1 : Hessian n)

/-- The Hessian block of the quadratic penalty in the second variable. -/
def quadraticPenaltyHessianRightRight (α : Real) : Hessian n :=
  α • (1 : Hessian n)

@[simp]
theorem quadraticPenalty_apply (α : Real) (x y : Point n) :
    quadraticPenalty α x y = (α / 2) * dotProduct (x - y) (x - y) :=
  rfl

@[simp]
theorem doubledObjective_apply (u v : Point n -> Real) (α : Real) (x y : Point n) :
    doubledObjective u v α (x, y) = u x - v y - quadraticPenalty α x y :=
  rfl

theorem quadraticPenalty_self (α : Real) (x : Point n) :
    quadraticPenalty α x x = 0 := by
  simp [quadraticPenalty]

theorem quadraticPenalty_nonneg {α : Real} (hα : 0 <= α) (x y : Point n) :
    0 <= quadraticPenalty α x y := by
  dsimp [quadraticPenalty]
  have hdot : 0 <= dotProduct (x - y) (x - y) := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg ((x - y) i)
  exact mul_nonneg (by linarith) hdot

theorem norm_weightedDistanceSq_le_quadraticPenalty_mul_two
    {α : Real} (hα : 0 <= α) (x y : Point n) :
    α * ‖x - y‖ ^ 2 <= 2 * quadraticPenalty α x y := by
  have hnormdot : ‖x - y‖ ^ 2 <= dotProduct (x - y) (x - y) :=
    norm_sq_le_dotProduct_self (x - y)
  calc
    α * ‖x - y‖ ^ 2 <= α * dotProduct (x - y) (x - y) := by
      exact mul_le_mul_of_nonneg_left hnormdot hα
    _ = 2 * quadraticPenalty α x y := by
      simp [quadraticPenalty]
      ring

/--
If `α > 0`, then
`0 ≤ α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
theorem comparisonScale_nonneg {α : Real} (hα : 0 < α) (x y : Point n) :
    0 <= α * ‖x - y‖ ^ 2 + ‖x - y‖ := by
  have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
  have hprod : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
  exact add_nonneg hprod (norm_nonneg _)

/--
If `α > 0` and `x ≠ y`, then
`0 < α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
theorem comparisonScale_pos_of_ne {α : Real} (hα : 0 < α) {x y : Point n}
    (hxy : x ≠ y) :
    0 < α * ‖x - y‖ ^ 2 + ‖x - y‖ := by
  have hnorm : 0 < ‖x - y‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hxy
  have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
  have hprod : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
  exact add_pos_of_nonneg_of_pos hprod hnorm

@[simp]
theorem quadraticPenaltyGradientRight_eq_neg_left (α : Real) (x y : Point n) :
    quadraticPenaltyGradientRight α x y = -quadraticPenaltyGradientLeft α x y := by
  ext i
  simp [quadraticPenaltyGradientRight, quadraticPenaltyGradientLeft]

theorem neg_quadraticPenaltyGradientRight_eq_left (α : Real) (x y : Point n) :
    -quadraticPenaltyGradientRight α x y = quadraticPenaltyGradientLeft α x y := by
  rw [quadraticPenaltyGradientRight_eq_neg_left, neg_neg]

theorem continuous_quadraticPenalty (α : Real) :
    Continuous fun q : DoubledPoint n => quadraticPenalty α q.1 q.2 := by
  have hdiff : Continuous fun q : DoubledPoint n => q.1 - q.2 :=
    continuous_fst.sub continuous_snd
  change Continuous fun q : DoubledPoint n => (α / 2) * dotProduct (q.1 - q.2) (q.1 - q.2)
  exact continuous_const.mul (hdiff.dotProduct hdiff)

theorem continuous_doubledObjective {u v : Point n -> Real} {α : Real}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun q : DoubledPoint n => doubledObjective u v α q := by
  have huq : Continuous fun q : DoubledPoint n => u q.1 := hu.comp continuous_fst
  have hvq : Continuous fun q : DoubledPoint n => v q.2 := hv.comp continuous_snd
  exact (huq.sub hvq).sub (continuous_quadraticPenalty α)

/--
If `u` is upper semicontinuous on `K` and `v` is lower semicontinuous on `L`,
then the function
`(x, y) ↦ u x - v y - (α / 2) * ∑ i, (x i - y i)^2`
is upper semicontinuous on `K × L`.
-/
theorem upperSemicontinuousOn_doubledObjective
    {K L : Set (Point n)} {u v : Point n -> Real} {α : Real}
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L) :
    UpperSemicontinuousOn (fun q : DoubledPoint n => doubledObjective u v α q) (K ×ˢ L) := by
  have huq : UpperSemicontinuousOn (fun q : DoubledPoint n => u q.1) (K ×ˢ L) :=
    hu.comp continuous_fst.continuousOn (fun q hq => hq.1)
  have hvq : LowerSemicontinuousOn (fun q : DoubledPoint n => v q.2) (K ×ˢ L) :=
    hv.comp continuous_snd.continuousOn (fun q hq => hq.2)
  have hnegv : UpperSemicontinuousOn (fun q : DoubledPoint n => -v q.2) (K ×ˢ L) := by
    simpa [Function.comp_def] using
      (continuous_neg.comp_lowerSemicontinuousOn_antitone hvq
        (fun _ _ h => neg_le_neg h))
  have hpen : ContinuousOn
      (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2) (K ×ˢ L) :=
    (continuous_quadraticPenalty α).continuousOn
  have hnegpen : UpperSemicontinuousOn
      (fun q : DoubledPoint n => -quadraticPenalty α q.1 q.2) (K ×ˢ L) :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp hpen.neg).2
  simpa [doubledObjective, sub_eq_add_neg] using (huq.add hnegv).add hnegpen

/--
Let `K` and `L` be nonempty compact sets. If `u` is upper semicontinuous on
`K` and `v` is lower semicontinuous on `L`, then there exists
`(x, y) ∈ K × L` such that for every `(x', y') ∈ K × L`,

`u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2 ≤
 u x - v y - (α / 2) * ∑ i, (x i - y i)^2`.
-/
theorem exists_isMaxOn_doubledObjective_of_isCompact
    {K L : Set (Point n)} {u v : Point n -> Real} {α : Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L) :
    ∃ q ∈ K ×ˢ L, IsMaxOn (fun z : DoubledPoint n => doubledObjective u v α z) (K ×ˢ L) q := by
  have hprod_ne : (K ×ˢ L).Nonempty := by
    rcases hKne with ⟨x, hx⟩
    rcases hLne with ⟨y, hy⟩
    exact ⟨(x, y), hx, hy⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hprod_ne (hKcompact.prod hLcompact)
    (upperSemicontinuousOn_doubledObjective hu hv)

/--
Let `u z - v z` be positive at some `z ∈ C`. If `(x, y)` maximizes

`(x', y') ↦ u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`

on `C × C` and `α ≥ 0`, then `v y ≤ u x`.
-/
theorem value_right_le_left_of_pos_gap_of_isMaxOn_doubledObjective
    {C : Set (Point n)} {u v : Point n -> Real} {α : Real} {x y z : Point n}
    (hα : 0 <= α) (hz : z ∈ C) (hgap : v z < u z)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q)
      (C ×ˢ C) (x, y)) :
    v y <= u x := by
  have hzpair : (z, z) ∈ C ×ˢ C := ⟨hz, hz⟩
  have hcompare := hmax hzpair
  have hpen : 0 <= quadraticPenalty α x y := quadraticPenalty_nonneg hα x y
  have hgap_pos : 0 < u z - v z := sub_pos.mpr hgap
  have hcompare' : u z - v z <= u x - v y - quadraticPenalty α x y := by
    simpa [doubledObjective, quadraticPenalty_self] using hcompare
  linarith

/--
If `(x, y)` maximizes the doubled-variable objective on `C × C` and `y ∈ C`,
then comparison with the diagonal point `(y, y)` gives

`quadraticPenalty α x y ≤ u x - u y`.
-/
theorem quadraticPenalty_le_value_sub_value_of_isMaxOn_doubledObjective
    {C : Set (Point n)} {u v : Point n -> Real} {α : Real} {x y : Point n}
    (hy : y ∈ C)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q)
      (C ×ˢ C) (x, y)) :
    quadraticPenalty α x y <= u x - u y := by
  have hdiag : (y, y) ∈ C ×ˢ C := ⟨hy, hy⟩
  have hcompare := hmax hdiag
  have hcompare' : u y - v y <= u x - v y - quadraticPenalty α x y := by
    simpa [doubledObjective, quadraticPenalty_self] using hcompare
  nlinarith

/--
If `(x, y)` maximizes the doubled-variable objective on `C × C` and `z ∈ C`,
then comparison with the diagonal point `(z, z)` gives

`quadraticPenalty α x y ≤ u x - v y - (u z - v z)`.
-/
theorem quadraticPenalty_le_value_sub_value_at_diagonal_of_isMaxOn_doubledObjective
    {C : Set (Point n)} {u v : Point n -> Real} {α : Real} {x y z : Point n}
    (hz : z ∈ C)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q)
      (C ×ˢ C) (x, y)) :
    quadraticPenalty α x y <= u x - v y - (u z - v z) := by
  have hdiag : (z, z) ∈ C ×ˢ C := ⟨hz, hz⟩
  have hcompare := hmax hdiag
  have hcompare' : u z - v z <= u x - v y - quadraticPenalty α x y := by
    simpa [doubledObjective, quadraticPenalty_self] using hcompare
  nlinarith

/--
Assume `(x, y)` maximizes the doubled-variable objective on `C × C`, `y ∈ C`,
`m ≤ u y`, and `u x ≤ M`. Then

`α * ‖x - y‖ ^ 2 ≤ 2 * (M - m)`.
-/
theorem weightedDistanceSq_le_two_value_range_of_isMaxOn_doubledObjective
    {C : Set (Point n)} {u v : Point n -> Real} {α m M : Real} {x y : Point n}
    (hα : 0 <= α) (hy : y ∈ C) (hlo : m <= u y) (hhi : u x <= M)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q)
      (C ×ˢ C) (x, y)) :
    α * ‖x - y‖ ^ 2 <= 2 * (M - m) := by
  have hpen := quadraticPenalty_le_value_sub_value_of_isMaxOn_doubledObjective
    (C := C) (u := u) (v := v) (α := α) (x := x) (y := y) hy hmax
  have hnorm := norm_weightedDistanceSq_le_quadraticPenalty_mul_two hα x y
  nlinarith

/--
Assume `(x, y)` maximizes the doubled-variable objective on `C × C`, `z ∈ C`,
`m ≤ v y`, and `u x ≤ M`. Then

`α * ‖x - y‖ ^ 2 ≤ 2 * (M - m - (u z - v z))`.
-/
theorem weightedDistanceSq_le_two_value_sub_value_at_diagonal_range_of_isMaxOn
    {C : Set (Point n)} {u v : Point n -> Real} {α m M : Real} {x y z : Point n}
    (hα : 0 <= α) (hz : z ∈ C) (hlo : m <= v y) (hhi : u x <= M)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q)
      (C ×ˢ C) (x, y)) :
    α * ‖x - y‖ ^ 2 <= 2 * (M - m - (u z - v z)) := by
  have hpen := quadraticPenalty_le_value_sub_value_at_diagonal_of_isMaxOn_doubledObjective
    (C := C) (u := u) (v := v) (α := α) (x := x) (y := y) (z := z) hz hmax
  have hnorm := norm_weightedDistanceSq_le_quadraticPenalty_mul_two hα x y
  nlinarith

/--
Let `α i` be a family of positive parameters for all `i` in a set belonging
to a filter `l`. Let `C` be nonempty and compact. If `u` is upper
semicontinuous on `C` and `v` is lower semicontinuous on `C`, then one can
choose functions `x i` and `y i` such that, for all `i` in a set belonging to
`l`, `α i > 0`, `x i ∈ C`, `y i ∈ C`, and `(x i, y i)` maximizes

`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `C × C`.
-/
theorem exists_eventually_isMaxOn_doubledObjective_along_of_isCompact
    {ι : Type*} {l : Filter ι} {C : Set (Point n)}
    {u v : Point n -> Real} {α : ι -> Real}
    (hα : ∀ᶠ i in l, 0 < α i)
    (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v C) :
    ∃ x y : ι -> Point n,
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i) := by
  classical
  have hsel :
      ∀ i : ι,
        ∃ q ∈ C ×ˢ C,
          IsMaxOn (fun z : DoubledPoint n => doubledObjective u v (α i) z)
            (C ×ˢ C) q := fun i =>
    exists_isMaxOn_doubledObjective_of_isCompact hCne hCne hCcompact hCcompact hu hv
  choose q hq hmax using hsel
  refine ⟨fun i => (q i).1, fun i => (q i).2, ?_⟩
  filter_upwards [hα] with i hαi
  exact ⟨hαi, (hq i).1, (hq i).2, hmax i⟩

end ViscositySolns
