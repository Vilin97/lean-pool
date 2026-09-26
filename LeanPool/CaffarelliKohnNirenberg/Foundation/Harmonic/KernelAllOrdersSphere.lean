/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean

/-!
# Kernel All Orders Sphere

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators Topology
open CKN.Foundation.Parabolic


/-!
# Euclidean geometry of space and sup bounds on the unit sphere

The Euclidean length on `Vec3` obeys the triangle inequality and is positive off
the origin, and the Euclidean unit sphere is compact, so a function continuous
away from the origin is bounded on it.  These are the scaling inputs for the
all-order kernel estimates of `cor:CZ-harmonic`.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- The triangle inequality for the Euclidean length on space. -/
theorem vec3EuclideanNorm_triangle (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    WithLp.toLp_add]
  exact norm_add_le _ _

/-- The Euclidean length is positive away from the origin. -/
theorem vec3EuclideanNorm_pos_of_ne_zero {x : Vec3} (hx : x ≠ 0) :
    0 < vec3EuclideanNorm x := by
  rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
  intro hzero
  exact hx ((WithLp.toLp_eq_zero 2).mp hzero)

/-- A point of positive Euclidean length is nonzero. -/
theorem ne_zero_of_vec3EuclideanNorm_pos {x : Vec3} (hx : 0 < vec3EuclideanNorm x) :
    x ≠ 0 := by
  intro hx0
  rw [hx0, vec3EuclideanNorm_zero] at hx
  exact lt_irrefl 0 hx

/-- A function continuous away from the origin is bounded on the Euclidean unit sphere. -/
theorem exists_bound_on_vec3Sphere {F : Type*} [NormedAddCommGroup F]
    {f : Vec3 → F} (hf : ContinuousOn f {z : Vec3 | z ≠ 0}) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z : Vec3, vec3EuclideanNorm z = 1 → ‖f z‖ ≤ c := by
  let S : Set Vec3 := {z : Vec3 | vec3EuclideanNorm z = 1}
  have hcont : Continuous vec3EuclideanNorm := by
    unfold vec3EuclideanNorm
    fun_prop
  have hclosed : IsClosed S := by
    have hS : S = vec3EuclideanNorm ⁻¹' {1} := by
      ext z
      simp [S]
    rw [hS]
    exact isClosed_singleton.preimage hcont
  have hbounded : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := 1)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ CKN.spaceEuclideanNorm z := CKN.space_norm_le_euclideanNorm z
      _ = vec3EuclideanNorm z := rfl
      _ = 1 := hz
  have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hsub : S ⊆ {z : Vec3 | z ≠ 0} := by
    intro z hz hz0
    have hz1 : vec3EuclideanNorm z = 1 := hz
    rw [hz0, vec3EuclideanNorm_zero] at hz1
    exact one_ne_zero hz1.symm
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z hz
  exact (hC z hz).trans (le_max_left C 0)

end CKN.Foundation.Heat
