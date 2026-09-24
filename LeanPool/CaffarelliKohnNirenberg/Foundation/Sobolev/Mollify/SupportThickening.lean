/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersSphere

/-!
# Support Thickening

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

open Set MeasureTheory
open scoped Pointwise Convolution Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


/-!
# Support, mollifier support, and thickening lemmas

These five results were previously private lemmas in
`CKN/Foundation/Euclidean/RieszSecondExterior.lean` (the `d = 3` versions)
and `CKN/Foundation/Sobolev/Mollify/LpApproximation.lean` (the general `d`
version of `mollifier_tsupp_eq_closedBall`).  They are collected here as public
theorems.
-/

/-- If a function `b` vanishes outside a set `A`, then its support is contained
in the closure of `A`. -/
theorem support_subset_closure_of_zero_outside {b : Vec3 → ℝ} {A : Set Vec3}
    (hbA : ∀ y ∉ A, b y = 0) : Function.support b ⊆ closure A := by
  intro y hy
  by_contra hya
  exact hy (hbA y (fun ha => hya (subset_closure ha)))

/-- The topological support of the normalized mollifier kernel of radius `ε > 0`
in any dimension `d` is exactly the closed ball of radius `ε` centred at `0`. -/
theorem mollifier_tsupp_eq_closedBall {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifier (d := d) ε hε) = Metric.closedBall 0 ε := by
  exact (standardMollifier (d := d) ε hε).tsupport_normed_eq

/-- The support of `mollify b ε hε` is contained in the Minkowski sum of the
closed ball of radius `δ` and the closure of `A`, provided `b` vanishes outside
`A` and `ε ≤ δ`. -/
theorem mollify_support_subset {b : Vec3 → ℝ} {A : Set Vec3} {δ ε : ℝ}
    (hε : 0 < ε)
    (hbA : ∀ y ∉ A, b y = 0) (hεA : ε ≤ δ) :
    Function.support (mollify b ε hε) ⊆
      Metric.closedBall (0 : Vec3) δ + closure A := by
  calc
    Function.support (mollify b ε hε) ⊆
        Function.support (mollifier (d := 3) ε hε) + Function.support b := by
      simpa [mollify] using
        (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
          (f := mollifier (d := 3) ε hε) (g := b))
    _ ⊆ Metric.closedBall (0 : Vec3) δ + closure A := by
      apply Set.add_subset_add
      · exact (subset_tsupport _).trans (by
          rw [mollifier_tsupp_eq_closedBall hε]
          exact Metric.closedBall_subset_closedBall hεA)
      · exact support_subset_closure_of_zero_outside hbA

/-- The Minkowski sum of a closed ball of radius `δ/12` and the closure of a
bounded set `A` is compact. -/
theorem thickening_compact {A : Set Vec3} (hAb : Bornology.IsBounded A)
    {δ : ℝ} :
    IsCompact (Metric.closedBall (0 : Vec3) (δ / 12) + closure A) := by
  exact (isCompact_closedBall (0 : Vec3) (δ / 12)).add hAb.isCompact_closure

/-- If points in `U` are at Euclidean distance at least `δ` from `A`, then every
point of the thickening `closed ball (δ/12) + closure A` is at distance at least
`δ/2` from every point of `U`. -/
theorem thickening_separated {A U : Set Vec3} {δ : ℝ}
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    ∀ x ∈ U, ∀ y ∈ Metric.closedBall (0 : Vec3) (δ / 12) + closure A,
      δ / 2 ≤ vec3EuclideanNorm (x - y) := by
  intro x hx y hy
  rcases Set.mem_add.mp hy with ⟨z, hz, a, ha, rfl⟩
  have hcl : ∀ a ∈ closure A, δ ≤ vec3EuclideanNorm (x - a) := by
    intro a ha
    apply closure_minimal (hsep x hx)
    on_goal 1 =>
      have hcont : Continuous (fun a : Vec3 => vec3EuclideanNorm (x - a)) := by
        unfold vec3EuclideanNorm
        fun_prop
    on_goal 1 => exact isClosed_le continuous_const hcont
    exact ha
  have hz' : ‖z‖ ≤ δ / 12 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hδ0 : 0 ≤ δ := by
    have := norm_nonneg z
    linarith only [this, hz']
  have hza : vec3EuclideanNorm z ≤ δ / 4 := by
    calc
      vec3EuclideanNorm z ≤ 3 * ‖z‖ := euclideanNorm_le_three_mul_space_norm z
      _ ≤ 3 * (δ / 12) := by gcongr
      _ = δ / 4 := by ring
  have htri : vec3EuclideanNorm (x - a) ≤
      vec3EuclideanNorm (x - (z + a)) + vec3EuclideanNorm z := by
    have hdecomp : x - a = (x - (z + a)) + z := by abel
    rw [hdecomp]
    exact vec3EuclideanNorm_triangle _ _
  have hz0 : 0 ≤ vec3EuclideanNorm z := vec3EuclideanNorm_nonneg z
  have hmain : δ ≤ vec3EuclideanNorm (x - (z + a)) + δ / 4 :=
    (hcl a ha).trans (htri.trans (add_le_add_right hza _))
  linarith only [hz0, hza, hmain]

end CKN
