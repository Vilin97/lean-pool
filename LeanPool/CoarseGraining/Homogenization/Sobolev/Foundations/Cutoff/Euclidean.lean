/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.Euclidean
import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Real.Pointwise
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Euclidean -/

noncomputable section

open scoped BigOperators
open scoped Pointwise
open Set

namespace Homogenization

/-!
# Explicit Euclidean geometry on `Vec d`

The project uses `Vec d = Fin d → ℝ`, whose default metric is the product/sup
metric.  This file defines the Euclidean squared distance and Euclidean balls
explicitly on the same underlying type, so later cutoff statements can be about
round Euclidean balls without changing ambient type to `EuclideanSpace`.
-/

/-- Euclidean squared distance on `Vec d`, independent of the default `Vec d`
metric. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

/-- The legacy squared-distance expression is the square of the explicit
Euclidean distance. -/
theorem euclideanSqDist_eq_euclideanDist_sq {d : ℕ} (x y : Vec d) :
    euclideanSqDist x y = euclideanDist x y ^ 2 := by
  rw [euclideanSqDist, euclideanDist, euclideanNorm_sq]

/-- Explicit Euclidean open ball on `Vec d`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- Explicit Euclidean closed ball on `Vec d`. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

/-- Explicit Euclidean sphere on `Vec d`. -/
def euclideanSphere {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ = R ^ 2}

@[simp] theorem euclideanSqDist_self {d : ℕ} (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

@[simp] theorem euclideanSqDist_zero_zero {d : ℕ} :
    euclideanSqDist (0 : Vec d) 0 = 0 := by
  simp

theorem euclideanSqDist_add_right {d : ℕ} (x y z : Vec d) :
    euclideanSqDist (x + z) (y + z) = euclideanSqDist x y := by
  have hsub : (x + z) - (y + z) = x - y := by
    ext i
    simp
  simp [euclideanSqDist, hsub]

theorem euclideanSqDist_smul_smul {d : ℕ} (r : ℝ) (x y : Vec d) :
    euclideanSqDist (r • x) (r • y) = r ^ 2 * euclideanSqDist x y := by
  have hsub : r • x - r • y = r • (x - y) := by
    ext i
    simp [sub_eq_add_neg, mul_add]
  rw [euclideanSqDist, hsub, vecNormSq_smul]
  rfl

theorem euclideanSqDist_smul_zero {d : ℕ} (r : ℝ) (x : Vec d) :
    euclideanSqDist (r • x) 0 = r ^ 2 * euclideanSqDist x 0 := by
  simpa using euclideanSqDist_smul_smul (d := d) r x 0

theorem euclideanSqDist_affine_center {d : ℕ} (x₀ y : Vec d) (r : ℝ) :
    euclideanSqDist (r • y + x₀) x₀ = r ^ 2 * euclideanSqDist y 0 := by
  calc
    euclideanSqDist (r • y + x₀) x₀ =
        euclideanSqDist (r • y) 0 := by
          simpa using euclideanSqDist_add_right (r • y) 0 x₀
    _ = r ^ 2 * euclideanSqDist y 0 :=
        euclideanSqDist_smul_zero r y

/-- Translating a point by `-z` from the center has the same explicit
Euclidean squared distance as `z` from the origin. -/
theorem euclideanSqDist_sub_left_self {d : ℕ} (x z : Vec d) :
    euclideanSqDist (x - z) x = euclideanSqDist z (0 : Vec d) := by
  unfold euclideanSqDist vecNormSq vecDot
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp

/-- If `z` lies in the explicit Euclidean ball about the origin, then `x - z`
lies in the corresponding explicit Euclidean ball about `x`. -/
theorem sub_mem_euclideanBall_center_of_mem_zero
    {d : ℕ} {x z : Vec d} {R : ℝ}
    (hz : z ∈ euclideanBall (0 : Vec d) R) :
    x - z ∈ euclideanBall x R := by
  change euclideanSqDist (x - z) x < R ^ 2
  rw [euclideanSqDist_sub_left_self]
  simpa [euclideanBall] using hz

theorem affine_mem_euclideanBall_iff_of_pos {d : ℕ}
    (x₀ y : Vec d) {r : ℝ} (hr : 0 < r) :
    r • y + x₀ ∈ euclideanBall x₀ r ↔ y ∈ euclideanBall (0 : Vec d) 1 := by
  change euclideanSqDist (r • y + x₀) x₀ < r ^ 2 ↔ euclideanSqDist y 0 < 1 ^ 2
  rw [euclideanSqDist_affine_center]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  norm_num
  constructor <;> intro h <;> nlinarith

theorem affine_mem_euclideanClosedBall_iff_of_pos {d : ℕ}
    (x₀ y : Vec d) {r : ℝ} (hr : 0 < r) :
    r • y + x₀ ∈ euclideanClosedBall x₀ r ↔
      y ∈ euclideanClosedBall (0 : Vec d) 1 := by
  change euclideanSqDist (r • y + x₀) x₀ ≤ r ^ 2 ↔ euclideanSqDist y 0 ≤ 1 ^ 2
  rw [euclideanSqDist_affine_center]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  norm_num
  constructor <;> intro h <;> nlinarith

theorem euclideanBall_eq_translateSet_smul_unit_of_pos {d : ℕ}
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = translateSet x₀ (r • euclideanBall (0 : Vec d) 1) := by
  ext z
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hz
    refine Set.mem_smul_set.2 ⟨r⁻¹ • (z - x₀), ?_, ?_⟩
    · have hpoint : r • (r⁻¹ • (z - x₀)) + x₀ ∈ euclideanBall x₀ r := by
        have hpoint_eq : r • (r⁻¹ • (z - x₀)) + x₀ = z := by
          ext i
          simp [hr.ne', sub_eq_add_neg]
        simpa [hpoint_eq] using hz
      exact (affine_mem_euclideanBall_iff_of_pos x₀ (r⁻¹ • (z - x₀)) hr).1 hpoint
    · ext i
      simp [hr.ne']
  · intro hz
    rcases Set.mem_smul_set.1 hz with ⟨y, hy, hy_eq⟩
    have hpoint : r • y + x₀ ∈ euclideanBall x₀ r :=
      (affine_mem_euclideanBall_iff_of_pos x₀ y hr).2 hy
    have hpoint_eq : r • y + x₀ = z := by
      ext i
      simp [hy_eq, sub_eq_add_neg, add_assoc]
    simpa [hpoint_eq] using hpoint

theorem euclideanClosedBall_eq_translateSet_smul_unit_of_pos {d : ℕ}
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanClosedBall x₀ r =
      translateSet x₀ (r • euclideanClosedBall (0 : Vec d) 1) := by
  ext z
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hz
    refine Set.mem_smul_set.2 ⟨r⁻¹ • (z - x₀), ?_, ?_⟩
    · have hpoint : r • (r⁻¹ • (z - x₀)) + x₀ ∈ euclideanClosedBall x₀ r := by
        have hpoint_eq : r • (r⁻¹ • (z - x₀)) + x₀ = z := by
          ext i
          simp [hr.ne', sub_eq_add_neg]
        simpa [hpoint_eq] using hz
      exact (affine_mem_euclideanClosedBall_iff_of_pos x₀ (r⁻¹ • (z - x₀)) hr).1 hpoint
    · ext i
      simp [hr.ne']
  · intro hz
    rcases Set.mem_smul_set.1 hz with ⟨y, hy, hy_eq⟩
    have hpoint : r • y + x₀ ∈ euclideanClosedBall x₀ r :=
      (affine_mem_euclideanClosedBall_iff_of_pos x₀ y hr).2 hy
    have hpoint_eq : r • y + x₀ = z := by
      ext i
      simp [hy_eq, sub_eq_add_neg, add_assoc]
    simpa [hpoint_eq] using hpoint

theorem euclideanSqDist_nonneg {d : ℕ} (x y : Vec d) :
    0 ≤ euclideanSqDist x y := by
  unfold euclideanSqDist
  exact vecNormSq_nonneg _

/-- Convexity inequality for the coordinate Euclidean squared norm. -/
theorem vecNormSq_weighted_add_le {d : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (v w : Vec d) :
    vecNormSq (a • v + b • w) ≤ a * vecNormSq v + b * vecNormSq w := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, (a • v + b • w) i * (a • v + b • w) i
        ≤ ∑ i : Fin d, (a * (v i * v i) + b * (w i * w i)) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          have hnonneg :
              0 ≤ a * b * (v i - w i) ^ 2 :=
            mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith
    _ = a * (∑ i : Fin d, v i * v i) +
        b * (∑ i : Fin d, w i * w i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Convexity inequality for the coordinate Euclidean squared distance. -/
theorem euclideanSqDist_weighted_add_le {d : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y x₀ : Vec d) :
    euclideanSqDist (a • x + b • y) x₀ ≤
      a * euclideanSqDist x x₀ + b * euclideanSqDist y x₀ := by
  have hsub :
      (a • x + b • y) - x₀ = a • (x - x₀) + b • (y - x₀) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * x i + b * y i - x₀ i =
          a * x i + b * y i - (a + b) * x₀ i := by
            rw [hab]
            ring
      _ = a * (x i - x₀ i) + b * (y i - x₀ i) := by
            ring
  rw [euclideanSqDist, hsub, euclideanSqDist]
  exact vecNormSq_weighted_add_le ha hb hab (x - x₀) (y - x₀)

/-- Explicit Euclidean closed balls are convex subsets of the project carrier. -/
theorem convex_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    Convex ℝ (euclideanClosedBall x₀ R) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change euclideanSqDist (a • x + b • y) x₀ ≤ R ^ 2
  have hconv := euclideanSqDist_weighted_add_le ha hb hab x y x₀
  have hweighted :
      a * euclideanSqDist x x₀ + b * euclideanSqDist y x₀ ≤
        a * R ^ 2 + b * R ^ 2 := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
  have hright : a * R ^ 2 + b * R ^ 2 = R ^ 2 := by
    nlinarith
  exact hconv.trans (hweighted.trans_eq hright)

/-- Explicit Euclidean open balls are convex subsets of the project carrier. -/
theorem convex_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    Convex ℝ (euclideanBall x₀ R) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change euclideanSqDist (a • x + b • y) x₀ < R ^ 2
  have hconv := euclideanSqDist_weighted_add_le ha hb hab x y x₀
  by_cases ha_zero : a = 0
  · have hb_one : b = 1 := by nlinarith
    calc
      euclideanSqDist (a • x + b • y) x₀
          ≤ a * euclideanSqDist x x₀ + b * euclideanSqDist y x₀ := hconv
      _ = euclideanSqDist y x₀ := by rw [ha_zero, hb_one]; ring
      _ < R ^ 2 := hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    have hx_strict :
        a * euclideanSqDist x x₀ < a * R ^ 2 :=
      mul_lt_mul_of_pos_left hx ha_pos
    have hy_le :
        b * euclideanSqDist y x₀ ≤ b * R ^ 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have hweighted :
        a * euclideanSqDist x x₀ + b * euclideanSqDist y x₀ <
          a * R ^ 2 + b * R ^ 2 :=
      add_lt_add_of_lt_of_le hx_strict hy_le
    have hright : a * R ^ 2 + b * R ^ 2 = R ^ 2 := by
      nlinarith
    exact hconv.trans_lt (hweighted.trans_eq hright)

theorem sq_coord_sub_le_euclideanSqDist {d : ℕ} (x y : Vec d) (i : Fin d) :
    (x i - y i) ^ 2 ≤ euclideanSqDist x y := by
  unfold euclideanSqDist vecNormSq vecDot
  let f : Fin d → ℝ := fun j => (x - y) j * (x - y) j
  have hsingle :
      f i ≤ ∑ j, f j := by
    exact Finset.single_le_sum
      (fun j _ => by
        have hsq : 0 ≤ ((x - y) j) ^ 2 := sq_nonneg ((x - y) j)
        simpa [f, pow_two] using hsq)
      (Finset.mem_univ i)
  simpa [f, Pi.sub_apply, pow_two] using hsingle

theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) (fun i _hi =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i))

theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

theorem continuous_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    Continuous (fun x : Vec d => euclideanSqDist x x₀) :=
  (contDiff_euclideanSqDist_left x₀).continuous

theorem isOpen_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsOpen (euclideanBall x₀ R) := by
  change IsOpen ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact isOpen_Iio.preimage (continuous_euclideanSqDist_left x₀)

theorem isClosed_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanClosedBall x₀ R) := by
  change IsClosed ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iic (R ^ 2))
  exact isClosed_Iic.preimage (continuous_euclideanSqDist_left x₀)

/-- Explicit Euclidean spheres are closed in the default product topology. -/
theorem isClosed_euclideanSphere {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanSphere x₀ R) := by
  change IsClosed ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' {R ^ 2})
  exact isClosed_singleton.preimage (continuous_euclideanSqDist_left x₀)

/-- The explicit sphere is contained in the corresponding explicit closed ball. -/
theorem euclideanSphere_subset_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    euclideanSphere x₀ R ⊆ euclideanClosedBall x₀ R := by
  intro x hx
  exact le_of_eq hx

/--
The closed Euclidean ball is the disjoint union of its open ball and sphere,
stated as a set-difference identity.
-/
theorem euclideanClosedBall_diff_euclideanBall_eq_euclideanSphere
    {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    euclideanClosedBall x₀ R \ euclideanBall x₀ R = euclideanSphere x₀ R := by
  ext x
  constructor
  · rintro ⟨hx_closed, hx_not_open⟩
    exact le_antisymm hx_closed (le_of_not_gt hx_not_open)
  · intro hx
    refine ⟨le_of_eq hx, ?_⟩
    change ¬ euclideanSqDist x x₀ < R ^ 2
    rw [hx]
    exact not_lt_of_ge le_rfl

/-- The closed Euclidean ball is covered by its open ball and sphere. -/
theorem euclideanClosedBall_subset_euclideanBall_union_euclideanSphere
    {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    euclideanClosedBall x₀ R ⊆ euclideanBall x₀ R ∪ euclideanSphere x₀ R := by
  intro x hx
  by_cases hlt : euclideanSqDist x x₀ < R ^ 2
  · exact Or.inl hlt
  · exact Or.inr (le_antisymm hx (le_of_not_gt hlt))

/-- A positive-radius explicit Euclidean sphere lies in the frontier of the
corresponding explicit closed ball. -/
theorem euclideanSphere_subset_frontier_euclideanClosedBall_of_pos
    {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    euclideanSphere x₀ R ⊆ frontier (euclideanClosedBall x₀ R) := by
  intro y hy
  rw [(isClosed_euclideanClosedBall x₀ R).frontier_eq]
  refine ⟨le_of_eq hy, ?_⟩
  intro hy_int
  rcases Metric.isOpen_iff.1 isOpen_interior y hy_int with ⟨ε, hε, hε_sub⟩
  let δ : ℝ := ε / (4 * R)
  let z : Vec d := (1 + δ) • (y - x₀) + x₀
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hdiff_sq :
      euclideanSqDist (y - x₀) (0 : Vec d) = euclideanSqDist y x₀ := by
    have htranslate :=
      euclideanSqDist_add_right (d := d) (y - x₀) (0 : Vec d) x₀
    have hy_eq : (y - x₀) + x₀ = y := by
      ext i
      simp
    simpa [hy_eq] using htranslate.symm
  have hz_sq :
      euclideanSqDist z x₀ = (1 + δ) ^ 2 * R ^ 2 := by
    calc
      euclideanSqDist z x₀ =
          (1 + δ) ^ 2 * euclideanSqDist (y - x₀) (0 : Vec d) := by
            simpa [z] using
              euclideanSqDist_affine_center (d := d) x₀ (y - x₀) (1 + δ)
      _ = (1 + δ) ^ 2 * R ^ 2 := by
            rw [hdiff_sq, hy]
  have hz_not_closed : z ∉ euclideanClosedBall x₀ R := by
    change ¬ euclideanSqDist z x₀ ≤ R ^ 2
    rw [hz_sq]
    have hR_sq_pos : 0 < R ^ 2 := sq_pos_of_pos hR
    have hone_lt : 1 < (1 + δ) ^ 2 := by
      nlinarith [hδ_pos]
    nlinarith
  have hz_ball : z ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have hcoord_sq : (y i - x₀ i) ^ 2 ≤ R ^ 2 := by
      rw [← hy]
      exact sq_coord_sub_le_euclideanSqDist y x₀ i
    have hcoord_abs : |y i - x₀ i| ≤ R :=
      abs_le_of_sq_le_sq hcoord_sq hR.le
    have hδR_lt : δ * R < ε := by
      dsimp [δ]
      field_simp [hR.ne']
      nlinarith [hε]
    have hdist_bound : dist (z i) (y i) ≤ δ * R := by
      rw [Real.dist_eq]
      have hcoord :
          z i - y i = δ * (y i - x₀ i) := by
        change ((1 + δ) * (y i - x₀ i) + x₀ i) - y i =
          δ * (y i - x₀ i)
        ring
      rw [hcoord, abs_mul, abs_of_pos hδ_pos]
      exact mul_le_mul_of_nonneg_left hcoord_abs hδ_pos.le
    exact lt_of_le_of_lt hdist_bound hδR_lt
  exact hz_not_closed (interior_subset (hε_sub hz_ball))

theorem center_mem_euclideanBall {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    x₀ ∈ euclideanBall x₀ R := by
  have hsq : 0 < R ^ 2 := sq_pos_of_pos hR
  simpa [euclideanBall] using hsq

theorem euclideanBall_nonempty {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    (euclideanBall x₀ R).Nonempty :=
  ⟨x₀, center_mem_euclideanBall x₀ hR⟩

theorem euclideanBall_subset_euclideanClosedBall_abs {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    euclideanBall x₀ R ⊆ euclideanClosedBall x₀ |R| := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2 at hx
  change euclideanSqDist x x₀ ≤ |R| ^ 2
  rw [sq_abs]
  exact le_of_lt hx

theorem euclideanClosedBall_subset_metricClosedBall {d : ℕ} {x₀ : Vec d} {R : ℝ}
    (hR : 0 ≤ R) :
    euclideanClosedBall x₀ R ⊆ Metric.closedBall x₀ R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  unfold euclideanClosedBall at hx
  have hsqi : (x i - x₀ i) ^ 2 ≤ R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans hx
  have habs : |x i - x₀ i| ≤ R :=
    abs_le_of_sq_le_sq hsqi hR
  simpa [Real.dist_eq, abs_sub_comm] using habs

/-- An explicit coordinate-Euclidean open ball is contained in the default
product-metric open ball of the same radius. -/
theorem euclideanBall_subset_metricBall {d : ℕ} {x₀ : Vec d} {R : ℝ}
    (hR : 0 < R) :
    euclideanBall x₀ R ⊆ Metric.ball x₀ R := by
  intro x hx
  rw [Metric.mem_ball, dist_pi_lt_iff hR]
  intro i
  unfold euclideanBall at hx
  have hsqi : (x i - x₀ i) ^ 2 < R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans_lt hx
  have habs : |x i - x₀ i| < R :=
    abs_lt_of_sq_lt_sq hsqi hR.le
  simpa [Real.dist_eq, abs_sub_comm] using habs

/--
A positive explicit Euclidean ball contains a small default-metric closed ball
around its center.  The conservative radius avoids needing a sharp comparison
between the product metric and the coordinate Euclidean norm.
-/
theorem metricClosedBall_div_two_natCast_succ_subset_euclideanBall
    {d : ℕ} {x₀ : Vec d} {R : ℝ} (hR : 0 < R) :
    Metric.closedBall x₀ (R / (2 * ((d : ℝ) + 1))) ⊆ euclideanBall x₀ R := by
  intro x hx
  let ρ : ℝ := R / (2 * ((d : ℝ) + 1))
  have hden_pos : 0 < 2 * ((d : ℝ) + 1) := by positivity
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hcoord : ∀ i : Fin d, |x i - x₀ i| ≤ ρ := by
    have hx' : dist x x₀ ≤ ρ := by
      simpa [ρ, Metric.mem_closedBall] using hx
    rw [dist_pi_le_iff hρ_nonneg] at hx'
    intro i
    simpa [Real.dist_eq, abs_sub_comm] using hx' i
  change euclideanSqDist x x₀ < R ^ 2
  unfold euclideanSqDist vecNormSq vecDot
  have hsum_le :
      (∑ i : Fin d, (x - x₀) i * (x - x₀) i) ≤ ∑ _i : Fin d, ρ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hsq_abs : |x i - x₀ i| ^ 2 ≤ ρ ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    simpa [pow_two] using hsq_abs
  have hsum_const : (∑ _i : Fin d, ρ ^ 2) = (d : ℝ) * ρ ^ 2 := by
    simp
  have harith : (d : ℝ) * ρ ^ 2 < R ^ 2 := by
    have hR_sq_pos : 0 < R ^ 2 := sq_pos_of_pos hR
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hd1_pos : 0 < (d : ℝ) + 1 := by positivity
    dsimp [ρ]
    field_simp [hden_pos.ne']
    nlinarith [hR_sq_pos, hd_nonneg, sq_nonneg ((d : ℝ) + 1)]
  exact lt_of_le_of_lt (hsum_le.trans_eq hsum_const) harith

theorem isCompact_euclideanClosedBall {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (euclideanClosedBall x₀ R) :=
  (ProperSpace.isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_euclideanClosedBall x₀ R)
    (euclideanClosedBall_subset_metricClosedBall hR)

theorem euclideanClosedBall_subset_euclideanBall {d : ℕ} {x₀ : Vec d} {s R : ℝ}
    (hs : 0 ≤ s) (hsR : s < R) :
    euclideanClosedBall x₀ s ⊆ euclideanBall x₀ R := by
  intro x hx
  unfold euclideanClosedBall at hx
  unfold euclideanBall
  have hR : 0 < R := lt_of_le_of_lt hs hsR
  have hsq : s ^ 2 < R ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self hs hsR
  exact lt_of_le_of_lt hx hsq

theorem euclideanBall_subset_euclideanBall {d : ℕ} {x₀ : Vec d} {s R : ℝ}
    (hs : 0 ≤ s) (hsR : s < R) :
    euclideanBall x₀ s ⊆ euclideanBall x₀ R := by
  intro x hx
  have hx_closed : x ∈ euclideanClosedBall x₀ s := by
    simpa [abs_of_nonneg hs] using euclideanBall_subset_euclideanClosedBall_abs x₀ s hx
  exact euclideanClosedBall_subset_euclideanBall hs hsR hx_closed

end Homogenization
