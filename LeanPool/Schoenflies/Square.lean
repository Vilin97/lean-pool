/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Plane

/-!
# The sup metric and axis-parallel squares

The blueprint takes the Euclidean norm as primary and uses the sup norm for the
axis-parallel objects the polygonal work is built on: grids of small squares, the vertex
squares of the redrawing argument, and the large square a bounded set is caught inside.
Appendix C item 1 asks for the comparison `‖x‖∞ ≤ ‖x‖ ≤ √2 ‖x‖∞`, which is `supNorm_le_norm`
and `norm_le_sqrt_two_mul_supNorm` here.

The one theorem of substance is `isConnected_beyondSquare`: the plane outside a closed
square is connected. It is a *square* and not a disk on purpose — the outside of a square is
exactly a union of four half-planes, each convex, with consecutive ones sharing a point,
whereas the outside of a disk would need the polar decomposition this development withholds.

## Blueprint

* `supNorm`, `supDist` — Appendix C, item 1 (the sup metric).
* `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` — the comparison, used without comment.
* `closedSquare`, `openSquare` — the axis-parallel square about a point.
* `isConnected_beyondSquare` — the outside of a square is connected; what makes exactly one
  face of a plane graph unbounded.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### Coordinates -/

theorem sub_apply (x y : Plane) (i : Fin 2) : (x - y) i = x i - y i := rfl

theorem smul_add_apply (a b : ℝ) (x y : Plane) (i : Fin 2) :
    (a • x + b • y) i = a * x i + b * y i := by simp

theorem continuous_coord (i : Fin 2) : Continuous fun x : Plane => x i :=
  PiLp.continuous_apply _ _ i

/-! ### The sup norm -/

/-- The sup norm `‖x‖∞ = max |x₁| |x₂|`. -/
noncomputable def supNorm (x : Plane) : ℝ := max |x 0| |x 1|

/-- The sup distance. -/
noncomputable def supDist (x y : Plane) : ℝ := supNorm (x - y)

theorem supNorm_nonneg (x : Plane) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem supDist_nonneg (x y : Plane) : 0 ≤ supDist x y := supNorm_nonneg _

@[simp] theorem supDist_self (x : Plane) : supDist x x = 0 := by
  simp [supDist, supNorm]

theorem supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  simp only [supDist, supNorm, sub_apply]
  rw [abs_sub_comm (x 0) (y 0), abs_sub_comm (x 1) (y 1)]

theorem abs_sub_zero_le_supDist (x y : Plane) : |x 0 - y 0| ≤ supDist x y :=
  le_max_left _ _

theorem abs_sub_one_le_supDist (x y : Plane) : |x 1 - y 1| ≤ supDist x y :=
  le_max_right _ _

theorem abs_zero_le_supNorm (x : Plane) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : Plane) : |x 1| ≤ supNorm x := le_max_right _ _

/-- The sup distance satisfies the triangle inequality, one coordinate at a time. -/
theorem supDist_triangle (x y z : Plane) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_zero_le_supDist x y) (abs_sub_zero_le_supDist y z)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_one_le_supDist x y) (abs_sub_one_le_supDist y z)

theorem norm_sq_eq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- Half of Appendix C item 1's comparison: the sup norm is at most the Euclidean norm. -/
theorem supNorm_le_norm (x : Plane) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

/-- The other half: the Euclidean norm is at most `√2` times the sup norm. -/
theorem norm_le_sqrt_two_mul_supNorm (x : Plane) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

/-! ### Coordinate half-planes

One convexity proof per direction serves all four sides of a square, and the outside of a
square is four of them. -/

theorem convex_coord_le (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_ge (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r ≤ x i} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_lt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i < r} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem convex_coord_gt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r < x i} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem isOpen_coord_lt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | x i < r} :=
  isOpen_lt (continuous_coord i) continuous_const

theorem isOpen_coord_gt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | r < x i} :=
  isOpen_lt continuous_const (continuous_coord i)

/-! ### Axis-parallel squares -/

/-- The closed axis-parallel square of radius `r` about `c`. -/
def closedSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c ≤ r}

/-- The open axis-parallel square of radius `r` about `c`. -/
def openSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c < r}

theorem closedSquare_eq_inter (c : Plane) (r : ℝ) :
    closedSquare c r =
      ({x : Plane | c 0 - r ≤ x 0} ∩ {x : Plane | x 0 ≤ c 0 + r}) ∩
      ({x : Plane | c 1 - r ≤ x 1} ∩ {x : Plane | x 1 ≤ c 1 + r}) := by
  ext x
  simp only [closedSquare, supDist, supNorm, sub_apply, Set.mem_ofPred_eq, mem_inter_iff,
    max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem openSquare_eq_inter (c : Plane) (r : ℝ) :
    openSquare c r =
      ({x : Plane | c 0 - r < x 0} ∩ {x : Plane | x 0 < c 0 + r}) ∩
      ({x : Plane | c 1 - r < x 1} ∩ {x : Plane | x 1 < c 1 + r}) := by
  ext x
  simp only [openSquare, supDist, supNorm, sub_apply, Set.mem_ofPred_eq, mem_inter_iff,
    max_lt_iff, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem convex_closedSquare (c : Plane) (r : ℝ) : Convex ℝ (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((convex_coord_ge 0 _).inter (convex_coord_le 0 _)).inter
    ((convex_coord_ge 1 _).inter (convex_coord_le 1 _))

theorem convex_openSquare (c : Plane) (r : ℝ) : Convex ℝ (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter
    ((convex_coord_gt 1 _).inter (convex_coord_lt 1 _))

theorem isOpen_openSquare (c : Plane) (r : ℝ) : IsOpen (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter
    ((isOpen_coord_gt 1 _).inter (isOpen_coord_lt 1 _))

theorem isClosed_closedSquare (c : Plane) (r : ℝ) : IsClosed (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((isClosed_le continuous_const (continuous_coord 0)).inter
      (isClosed_le (continuous_coord 0) continuous_const)).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

/-! ### The outside of a square -/

/-- The plane outside the closed square of radius `r` about the origin. -/
def beyondSquare (r : ℝ) : Set Plane := {x | r < |x 0| ∨ r < |x 1|}

/-- The outside of a square is connected.

Four half-planes, each convex and hence connected, with consecutive ones sharing a corner.
No polar decomposition, and no arbitrary union of connected sets. The radius needs no sign
condition: for `r < 0` the four half-planes already cover the plane. -/
theorem isConnected_beyondSquare (r : ℝ) : IsConnected (beyondSquare r) := by
  set R : Set Plane := {x : Plane | r < x 0} with hR
  set L : Set Plane := {x : Plane | x 0 < -r} with hL
  set T : Set Plane := {x : Plane | r < x 1} with hT
  set B : Set Plane := {x : Plane | x 1 < -r} with hB
  have hcover : beyondSquare r = R ∪ T ∪ L ∪ B := by
    ext x
    simp only [beyondSquare, hR, hL, hT, hB, Set.mem_ofPred_eq, mem_union, lt_abs]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (by linarith)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  -- Consecutive sides share a corner. Membership unfolds definitionally, so `show` states
  -- the inequality the corner satisfies and `linarith` closes it.
  have hRT : mk (r + 1) (r + 1) ∈ R ∩ T :=
    ⟨show r < r + 1 by linarith, show r < r + 1 by linarith⟩
  have hTL : mk (-r - 1) (r + 1) ∈ T ∩ L :=
    ⟨show r < r + 1 by linarith, show -r - 1 < -r by linarith⟩
  have hLB : mk (-r - 1) (-r - 1) ∈ L ∩ B :=
    ⟨show -r - 1 < -r by linarith, show -r - 1 < -r by linarith⟩
  have cR : IsConnected R :=
    (convex_coord_gt 0 r).isConnected ⟨mk (r + 1) 0, show r < r + 1 by linarith⟩
  have cL : IsConnected L :=
    (convex_coord_lt 0 (-r)).isConnected ⟨mk (-r - 1) 0, show -r - 1 < -r by linarith⟩
  have cT : IsConnected T :=
    (convex_coord_gt 1 r).isConnected ⟨mk 0 (r + 1), show r < r + 1 by linarith⟩
  have cB : IsConnected B :=
    (convex_coord_lt 1 (-r)).isConnected ⟨mk 0 (-r - 1), show -r - 1 < -r by linarith⟩
  have c1 : IsConnected (R ∪ T) := cR.union ⟨mk (r + 1) (r + 1), hRT.1, hRT.2⟩ cT
  have c2 : IsConnected (R ∪ T ∪ L) :=
    c1.union ⟨mk (-r - 1) (r + 1), Or.inr hTL.1, hTL.2⟩ cL
  have c3 : IsConnected (R ∪ T ∪ L ∪ B) :=
    c2.union ⟨mk (-r - 1) (-r - 1), Or.inr hLB.1, hLB.2⟩ cB
  rw [hcover]
  exact c3

end Plane

end Schoenflies
