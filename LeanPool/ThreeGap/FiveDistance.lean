/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.EuclideanAngle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# The sharp Euclidean five-distance theorem `g₂ ≤ 5` — Haynes–Marklof Theorem 8 core

Grind toward the sharp bound `g₂ ≤ 5` (Haynes–Marklof, *IMRN* 2022, arXiv:2009.08444), the
**elementary, dynamics-free** route. This file builds the combinatorial core (their Theorem 8): the
`5`-vectors-on-a-circle argument. Geometric heart here: the 2D **signed area** (`det2`) and the
characterisation of the open positive cone `{s•x + t•z : s,t > 0}` by sign conditions on `det2`.

This composes with the already-proven `EuclideanAngle.norm_sub_lt_max_of_angle_lt` (their Prop 2)
and
`EuclideanAngle.angle_ge_pi_div_three_of_norm_sub_gt` (the record-angle bound).
-/

namespace ThreeGap.FiveDistance

open scoped Real EuclideanSpace

/-- The 2D signed area (cross product) of `x, y ∈ ℝ²`. -/
def det2 (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0

theorem det2_skew (x y : EuclideanSpace ℝ (Fin 2)) : det2 x y = - det2 y x := by
  simp only [det2]; ring

open RealInnerProductSpace in
/-- The real inner product on `EuclideanSpace ℝ (Fin 2)` in coordinates. -/
theorem inner_eq_coord (x y : EuclideanSpace ℝ (Fin 2)) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply]; simp [Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

open RealInnerProductSpace in
/-- **The 2D Lagrange identity:** `(det2 x y)² + ⟪x,y⟫² = ‖x‖²‖y‖²`. Converts angle conditions
(inner product) into orientation conditions (signed area `det2`). -/
theorem det2_sq_add_inner_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    (det2 x y) ^ 2 + (⟪x, y⟫) ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_coord]; ring
  have hy : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_coord]; ring
  rw [det2, inner_eq_coord, hx, hy]; ring

/-- **Cramer reconstruction in the plane.** If `x, z` are independent (`det2 x z ≠ 0`), every `y` is
`s•x + t•z` with `s = det2 y z / det2 x z`, `t = det2 x y / det2 x z`. -/
theorem cramer (x y z : EuclideanSpace ℝ (Fin 2)) (hxz : det2 x z ≠ 0) :
    y = (det2 y z / det2 x z) • x + (det2 x y / det2 x z) • z := by
  have hkey : ∀ i : Fin 2, det2 x z * y i = det2 y z * x i + det2 x y * z i := by
    intro i; fin_cases i <;> (simp only [det2, Fin.mk_zero, Fin.mk_one, Fin.isValue]; ring)
  ext i
  have hcoord : ((det2 y z / det2 x z) • x + (det2 x y / det2 x z) • z) i
      = (det2 y z / det2 x z) * x i + (det2 x y / det2 x z) * z i := rfl
  rw [hcoord]; field_simp; linarith [hkey i]

/-- **Cone membership from signed-area signs.** If `x, z` are independent and `det2 x y`, `det2 y z`
have the **same sign** as `det2 x z`, then `y` lies in the open positive cone of `x, z`:
`y = s•x + t•z` with `s, t > 0`. -/
theorem mem_openCone_of_det_signs (x y z : EuclideanSpace ℝ (Fin 2)) (hxz : det2 x z ≠ 0)
    (hs : 0 < det2 y z / det2 x z) (ht : 0 < det2 x y / det2 x z) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ y = s • x + t • z :=
  ⟨det2 y z / det2 x z, det2 x y / det2 x z, hs, ht, cramer x y z hxz⟩

open RealInnerProductSpace in
/-- **The cosine-difference law from signed areas.** `⟪v₀,vᵢ⟫⟪v₀,vⱼ⟫ + det2 v₀ vᵢ · det2 v₀ vⱼ =
‖v₀‖²·⟪vᵢ,vⱼ⟫`. Writing `(aᵢ,dᵢ) = (⟪v₀,vᵢ⟫, det2 v₀ vᵢ)/(‖v₀‖‖vᵢ‖)` as the cosine/sine of the
signed
angle of `vᵢ` from `v₀`, this says `cos∠(vᵢ,vⱼ) = aᵢaⱼ + dᵢdⱼ` — the full planar trigonometry,
derived
from `det2` + inner alone (no `oangle`/`kahler`). -/
theorem inner_mul_add_det2_mul (v0 vi vj : EuclideanSpace ℝ (Fin 2)) :
    ⟪v0, vi⟫ * ⟪v0, vj⟫ + det2 v0 vi * det2 v0 vj = ‖v0‖ ^ 2 * ⟪vi, vj⟫ := by
  have h0 : ‖v0‖ ^ 2 = v0 0 ^ 2 + v0 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_coord]; ring
  rw [inner_eq_coord, inner_eq_coord, inner_eq_coord, det2, det2, h0]; ring

open RealInnerProductSpace in
/-- **The sine-difference law from signed areas.** `‖v₀‖²·det2 vᵢ vⱼ = det2 v₀ vⱼ · ⟪v₀,vᵢ⟫ −
⟪v₀,vⱼ⟫ · det2 v₀ vᵢ`. In the `(aᵢ,dᵢ) = (cos,sin)` reading, `sin∠(vᵢ→vⱼ) = dⱼaᵢ − aⱼdᵢ` — so the
sign
of `det2 vᵢ vⱼ` (which orientation `vⱼ` is from `vᵢ`) is read off the `v₀`-relative coordinates. -/
theorem det2_mul_eq (v0 vi vj : EuclideanSpace ℝ (Fin 2)) :
    ‖v0‖ ^ 2 * det2 vi vj = det2 v0 vj * ⟪v0, vi⟫ - ⟪v0, vj⟫ * det2 v0 vi := by
  have h0 : ‖v0‖ ^ 2 = v0 0 ^ 2 + v0 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_coord]; ring
  rw [det2, det2, det2, inner_eq_coord, inner_eq_coord, h0]; ring

open RealInnerProductSpace in
/-- **The signed area is `‖x‖‖y‖·sin∠`.** `|det2 x y| = ‖x‖ ‖y‖ · sin∠(x,y)`. With the cosine law
`⟪x,y⟫ = ‖x‖‖y‖cos∠` and Lagrange `det2² = ‖x‖²‖y‖² − ⟪x,y⟫²`, this gives `det2² = ‖x‖²‖y‖²sin²∠`.
So `dᵢ := det2(v₀,vᵢ)` has magnitude `‖v₀‖‖vᵢ‖·sin βᵢ` (`βᵢ = ∠(v₀,vᵢ)`) — the "sine" coordinate. -/
theorem abs_det2_eq (x y : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) (hy : y ≠ 0) :
    |det2 x y| = ‖x‖ * ‖y‖ * Real.sin (InnerProductGeometry.angle x y) := by
  have hcos : ⟪x, y⟫ = ‖x‖ * ‖y‖ * Real.cos (InnerProductGeometry.angle x y) := by
    rw [InnerProductGeometry.cos_angle]
    field_simp [norm_ne_zero_iff.mpr hx, norm_ne_zero_iff.mpr hy]
  have hsin0 : 0 ≤ Real.sin (InnerProductGeometry.angle x y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _)
  have hpyth := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle x y)
  have hsq : (det2 x y) ^ 2 = (‖x‖ * ‖y‖ * Real.sin (InnerProductGeometry.angle x y)) ^ 2 := by
    have h := det2_sq_add_inner_sq x y
    rw [hcos] at h; nlinarith [h, hpyth]
  have hb : (0:ℝ) ≤ ‖x‖ * ‖y‖ * Real.sin (InnerProductGeometry.angle x y) :=
    mul_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y)) hsin0
  rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq hb]

open RealInnerProductSpace in
/-- **Angle composition (same side).** If `vᵢ, vⱼ` are on the same side of `v₀` (`det2 v₀ vᵢ`,
`det2 v₀ vⱼ` same sign), then `∠(vᵢ,vⱼ)` has cosine `cos(βᵢ − βⱼ)` (`βₖ = ∠(v₀,vₖ)`). -/
theorem cos_angle_same_side (v0 vi vj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0) (hi : vi ≠ 0)
    (hj : vj ≠ 0) (hsame : 0 < det2 v0 vi * det2 v0 vj) :
    Real.cos (InnerProductGeometry.angle vi vj)
      = Real.cos (InnerProductGeometry.angle v0 vi - InnerProductGeometry.angle v0 vj) := by
  have hv0 : (0:ℝ) < ‖v0‖ := norm_pos_iff.mpr h0
  have hvi : (0:ℝ) < ‖vi‖ := norm_pos_iff.mpr hi
  have hvj : (0:ℝ) < ‖vj‖ := norm_pos_iff.mpr hj
  have hci : ⟪v0, vi⟫ = ‖v0‖ * ‖vi‖ * Real.cos (InnerProductGeometry.angle v0 vi) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hcj : ⟪v0, vj⟫ = ‖v0‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle v0 vj) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hcij : ⟪vi, vj⟫ = ‖vi‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle vi vj) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have habs : det2 v0 vi * det2 v0 vj = |det2 v0 vi| * |det2 v0 vj| := by
    rw [← abs_mul, abs_of_pos hsame]
  have key := inner_mul_add_det2_mul v0 vi vj
  rw [hci, hcj, hcij, habs, abs_det2_eq v0 vi h0 hi, abs_det2_eq v0 vj h0 hj] at key
  rw [Real.cos_sub]
  have hA : (0:ℝ) < ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ := by positivity
  have heq : ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle vi vj)
      = ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ * (Real.cos (InnerProductGeometry.angle v0 vi)
          * Real.cos (InnerProductGeometry.angle v0 vj)
        + Real.sin (InnerProductGeometry.angle v0 vi)
          * Real.sin (InnerProductGeometry.angle v0 vj)) := by nlinarith [key]
  exact mul_left_cancel₀ (ne_of_gt hA) heq

open RealInnerProductSpace in
/-- **Angle composition (opposite sides).** If `vᵢ, vⱼ` are on opposite sides of `v₀`
(`det2 v₀ vᵢ`, `det2 v₀ vⱼ` of opposite sign), then `∠(vᵢ,vⱼ)` has cosine `cos(βᵢ + βⱼ)`. -/
theorem cos_angle_opp_side (v0 vi vj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0) (hi : vi ≠ 0)
    (hj : vj ≠ 0) (hopp : det2 v0 vi * det2 v0 vj < 0) :
    Real.cos (InnerProductGeometry.angle vi vj)
      = Real.cos (InnerProductGeometry.angle v0 vi + InnerProductGeometry.angle v0 vj) := by
  have hv0 : (0:ℝ) < ‖v0‖ := norm_pos_iff.mpr h0
  have hvi : (0:ℝ) < ‖vi‖ := norm_pos_iff.mpr hi
  have hvj : (0:ℝ) < ‖vj‖ := norm_pos_iff.mpr hj
  have hci : ⟪v0, vi⟫ = ‖v0‖ * ‖vi‖ * Real.cos (InnerProductGeometry.angle v0 vi) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hcj : ⟪v0, vj⟫ = ‖v0‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle v0 vj) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hcij : ⟪vi, vj⟫ = ‖vi‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle vi vj) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have habs : det2 v0 vi * det2 v0 vj = -(|det2 v0 vi| * |det2 v0 vj|) := by
    rw [← abs_mul, abs_of_neg hopp]; ring
  have key := inner_mul_add_det2_mul v0 vi vj
  rw [hci, hcj, hcij, habs, abs_det2_eq v0 vi h0 hi, abs_det2_eq v0 vj h0 hj] at key
  rw [Real.cos_add]
  have hA : (0:ℝ) < ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ := by positivity
  have heq : ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle vi vj)
      = ‖v0‖ ^ 2 * ‖vi‖ * ‖vj‖ * (Real.cos (InnerProductGeometry.angle v0 vi)
          * Real.cos (InnerProductGeometry.angle v0 vj)
        - Real.sin (InnerProductGeometry.angle v0 vi)
          * Real.sin (InnerProductGeometry.angle v0 vj)) := by nlinarith [key]
  exact mul_left_cancel₀ (ne_of_gt hA) heq

open RealInnerProductSpace in
/-- **Same-side angle is the angle difference.** When `vᵢ, vⱼ` lie on the same side of `v₀`,
`∠(vᵢ,vⱼ) = |βᵢ − βⱼ|` exactly (both lie in `[0,π]`, and cosine is injective there). This is the
fact Step A feeds to `not_four_in_interval`: same-side record vectors pairwise `> π/3` apart give
their `βᵢ` pairwise `> π/3` apart in the length-`π` interval `[0,π]`. -/
theorem angle_eq_abs_sub_of_same_side (v0 vi vj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0)
    (hi : vi ≠ 0) (hj : vj ≠ 0) (hsame : 0 < det2 v0 vi * det2 v0 vj) :
    InnerProductGeometry.angle vi vj
      = |InnerProductGeometry.angle v0 vi - InnerProductGeometry.angle v0 vj| := by
  have hcos := cos_angle_same_side v0 vi vj h0 hi hj hsame
  rw [← Real.cos_abs (InnerProductGeometry.angle v0 vi - InnerProductGeometry.angle v0 vj)] at hcos
  refine Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _,
    InnerProductGeometry.angle_le_pi _ _⟩ ⟨abs_nonneg _, ?_⟩ hcos
  have hi1 := InnerProductGeometry.angle_le_pi v0 vi
  have hj1 := InnerProductGeometry.angle_nonneg v0 vj
  have hi0 := InnerProductGeometry.angle_nonneg v0 vi
  have hj0' := InnerProductGeometry.angle_le_pi v0 vj
  rw [abs_le]; constructor <;> linarith

open RealInnerProductSpace in
/-- **Opposite-side angle is the reduced angle sum.** When `vᵢ, vⱼ` lie on opposite sides of `v₀`,
`∠(vᵢ,vⱼ) = π − |π − (βᵢ + βⱼ)|` — i.e. `βᵢ + βⱼ` if that is `≤ π`, else `2π − (βᵢ + βⱼ)` (the
reflection of the angle sum back into `[0,π]`). The flanking-wedge step uses the second branch: a
large angle sum forces a *small* cross-side angle. -/
theorem angle_eq_of_opp_side (v0 vi vj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0) (hi : vi ≠ 0)
    (hj : vj ≠ 0) (hopp : det2 v0 vi * det2 v0 vj < 0) :
    InnerProductGeometry.angle vi vj
      = π - |π - (InnerProductGeometry.angle v0 vi + InnerProductGeometry.angle v0 vj)| := by
  set x := InnerProductGeometry.angle v0 vi + InnerProductGeometry.angle v0 vj with hx
  have hcos : Real.cos (InnerProductGeometry.angle vi vj) = Real.cos (π - |π - x|) := by
    rw [cos_angle_opp_side v0 vi vj h0 hi hj hopp, Real.cos_pi_sub, Real.cos_abs, Real.cos_pi_sub]
    ring
  have hxle : x ≤ 2 * π := by
    have := InnerProductGeometry.angle_le_pi v0 vi
    have := InnerProductGeometry.angle_le_pi v0 vj
    rw [hx]; linarith
  have hx0 : 0 ≤ x := by
    have := InnerProductGeometry.angle_nonneg v0 vi
    have := InnerProductGeometry.angle_nonneg v0 vj
    rw [hx]; linarith
  have hpi := Real.pi_pos
  refine Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _,
    InnerProductGeometry.angle_le_pi _ _⟩ ⟨?_, ?_⟩ hcos
  · rw [sub_nonneg, abs_le]; constructor <;> linarith
  · have : 0 ≤ |π - x| := abs_nonneg _
    linarith

open RealInnerProductSpace in
/-- **Step B (flanking wedge).** If `vᵢ, vⱼ` are on opposite sides of `v₀` with angle sum
`βᵢ + βⱼ > 5π/3`, then the cross-side angle `∠(vᵢ,vⱼ) < π/3`. (The two vectors flank `v₀` so widely
that, wrapping past `π`, they come back within `π/3` of each other.) Contrapositive: a cross-side
pair that is `≥ π/3` apart has `βᵢ + βⱼ ≤ 5π/3`. -/
theorem angle_lt_of_opp_side_of_sum_gt (v0 vi vj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0)
    (hi : vi ≠ 0) (hj : vj ≠ 0) (hopp : det2 v0 vi * det2 v0 vj < 0)
    (hsum : 5 * π / 3 < InnerProductGeometry.angle v0 vi + InnerProductGeometry.angle v0 vj) :
    InnerProductGeometry.angle vi vj < π / 3 := by
  rw [angle_eq_of_opp_side v0 vi vj h0 hi hj hopp]
  have hpi := Real.pi_pos
  have hnp : π - (InnerProductGeometry.angle v0 vi + InnerProductGeometry.angle v0 vj) ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnp]
  linarith

/-! ## The packing core (real-number form) -/

/-- **At most 3 reals in an interval of length `π` can be pairwise more than `π/3` apart.** Four are
impossible: sorting, the three consecutive gaps each exceed `π/3` so sum to `> π`, but the span is
`≤ π`. This is the real-number heart of "4 vectors in a half-plane can't be pairwise `> π/3`" (the
arc
has length `≤ π`). -/
theorem not_four_in_interval (θ : Fin 4 → ℝ) (a : ℝ) (hmem : ∀ i, θ i ∈ Set.Icc a (a + π))
    (hsep : ∀ i j, i ≠ j → π / 3 < |θ i - θ j|) : False := by
  set σ := Tuple.sort θ with hσ
  have hmono : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  have hinj : Function.Injective σ := σ.injective
  have gap : ∀ i : Fin 4, ∀ j : Fin 4, i ≤ j → i ≠ j → π / 3 < θ (σ j) - θ (σ i) := by
    intro i j hle hne
    have hmle : θ (σ i) ≤ θ (σ j) := hmono hle
    have := hsep (σ i) (σ j) (hinj.ne hne)
    rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hmle)] at this
  have g0 := gap 0 1 (by decide) (by decide)
  have g1 := gap 1 2 (by decide) (by decide)
  have g2 := gap 2 3 (by decide) (by decide)
  have hb0 := (Set.mem_Icc.mp (hmem (σ 0))).1
  have hb3 := (Set.mem_Icc.mp (hmem (σ 3))).2
  have hpi := Real.pi_pos
  linarith

/-- **At most 2 reals in an interval of length `2π/3` can be pairwise more than `π/3` apart.** Three
are impossible: sorting, the two consecutive gaps each exceed `π/3` so sum to `> 2π/3`, but the span
is `≤ 2π/3`. The `2π/3`-length analogue of `not_four_in_interval` — it bounds the number of vectors
on
one *strict side* of `v₀` (where reference angles live in `(π/3, π]`, of length `< 2π/3`). -/
theorem not_three_in_interval (θ : Fin 3 → ℝ) (a : ℝ)
    (hmem : ∀ i, θ i ∈ Set.Icc a (a + 2 * π / 3))
    (hsep : ∀ i j, i ≠ j → π / 3 < |θ i - θ j|) : False := by
  set σ := Tuple.sort θ with hσ
  have hmono : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  have hinj : Function.Injective σ := σ.injective
  have gap : ∀ i j : Fin 3, i ≤ j → i ≠ j → π / 3 < θ (σ j) - θ (σ i) := by
    intro i j hle hne
    have hmle : θ (σ i) ≤ θ (σ j) := hmono hle
    have := hsep (σ i) (σ j) (hinj.ne hne)
    rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hmle)] at this
  have g0 := gap 0 1 (by decide) (by decide)
  have g1 := gap 1 2 (by decide) (by decide)
  have hb0 := (Set.mem_Icc.mp (hmem (σ 0))).1
  have hb2 := (Set.mem_Icc.mp (hmem (σ 2))).2
  have hpi := Real.pi_pos
  linarith

/-- The reduced angle `|(↑Δ).toReal|` never exceeds `|Δ|`: reducing modulo `2π` into `(-π,π]` can
only shrink the magnitude (or keep it, when `|Δ| ≤ π`). -/
theorem abs_toReal_coe_le_abs (Δ : ℝ) : |((Δ : Real.Angle)).toReal| ≤ |Δ| := by
  rcases lt_or_ge |Δ| π with h | h
  · rw [abs_lt] at h
    rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr ⟨h.1, h.2.le⟩]
  · exact le_trans (Real.Angle.abs_toReal_le_pi _) h

/-- The reduced angle `|(↑Δ).toReal|` also bounded by the *complementary* arc `2π − |Δ|` (for
`|Δ| ≤ 2π`): together with `abs_toReal_coe_le_abs`, the reduced angle is `≤ min(|Δ|, 2π−|Δ|)`,
the cyclic distance. -/
theorem abs_toReal_coe_le_two_pi_sub (Δ : ℝ) (h : |Δ| ≤ 2 * π) :
    |((Δ : Real.Angle)).toReal| ≤ 2 * π - |Δ| := by
  have hpi := Real.pi_pos
  rcases le_or_gt |Δ| π with h1 | h1
  · have := Real.Angle.abs_toReal_le_pi (Δ : Real.Angle); linarith
  · rcases abs_cases Δ with ⟨hΔ, _⟩ | ⟨hΔ, hΔneg⟩
    · rw [hΔ] at h1 h ⊢
      rw [Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr ⟨h1, by linarith⟩]
      rw [abs_of_nonpos (by linarith)]; linarith
    · rw [hΔ] at h1 h ⊢
      rw [Real.Angle.toReal_coe_eq_self_add_two_pi_iff.mpr ⟨by linarith, by linarith⟩]
      rw [abs_of_nonneg (by linarith)]; linarith

/-- **At most 5 points on a circle can be pairwise more than `π/3` apart (real-number core).**
Six reals with pairwise cyclic distance `min(|θᵢ−θⱼ|, 2π−|θᵢ−θⱼ|) > π/3` are impossible: sorting,
the five consecutive gaps telescope to `θ₅−θ₀ > 5π/3`, while the wrap-around gap `2π−(θ₅−θ₀) > π/3`
forces `θ₅−θ₀ < 5π/3`. (The six cyclic gaps each exceed `π/3` so sum to `> 2π`, but the circle has
circumference `2π`.) This is the circular analogue of `not_four_in_interval`. -/
theorem not_six_circular (θ : Fin 6 → ℝ)
    (hsep : ∀ i j, i ≠ j → π / 3 < min |θ i - θ j| (2 * π - |θ i - θ j|)) : False := by
  set σ := Tuple.sort θ with hσ
  have hmono : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  have hinj : Function.Injective σ := σ.injective
  have gap : ∀ i j : Fin 6, i ≤ j → i ≠ j → π / 3 < θ (σ j) - θ (σ i) := by
    intro i j hle hne
    have hm : θ (σ i) ≤ θ (σ j) := hmono hle
    have hs := hsep (σ i) (σ j) (hinj.ne hne)
    have heq : |θ (σ i) - θ (σ j)| = θ (σ j) - θ (σ i) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have := (lt_min_iff.mp hs).1
    rwa [heq] at this
  have g01 := gap 0 1 (by decide) (by decide)
  have g12 := gap 1 2 (by decide) (by decide)
  have g23 := gap 2 3 (by decide) (by decide)
  have g34 := gap 3 4 (by decide) (by decide)
  have g45 := gap 4 5 (by decide) (by decide)
  have hw := hsep (σ 5) (σ 0) (hinj.ne (by decide))
  have hmono50 : θ (σ 0) ≤ θ (σ 5) := hmono (by decide)
  have heqw : |θ (σ 5) - θ (σ 0)| = θ (σ 5) - θ (σ 0) := abs_of_nonneg (by linarith)
  have hwrap := (lt_min_iff.mp hw).2
  rw [heqw] at hwrap
  linarith

/-- **At most 5 vectors in the plane can be pairwise more than `π/3` apart.** Six nonzero vectors
of `ℝ²` cannot be pairwise `> π/3` apart: assigning each a circular coordinate
`θᵢ = (oangle(w₀, wᵢ)).toReal` and using `∠(wᵢ,wⱼ) = |oangle(wᵢ,wⱼ).toReal|` with oriented-angle
additivity, the pairwise condition becomes pairwise cyclic distance `> π/3` among six circle points
— impossible by `not_six_circular`. This is the kissing-type packing bound behind the sharp
Euclidean five-distance theorem (`g₂ ≤ 5`). -/
theorem not_six_vectors_pairwise
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    (w : Fin 6 → EuclideanSpace ℝ (Fin 2)) (hw : ∀ i, w i ≠ 0)
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j)) : False := by
  apply not_six_circular (fun i => (o.oangle (w 0) (w i)).toReal)
  intro i j hij
  set a := o.oangle (w 0) (w i) with ha
  set b := o.oangle (w 0) (w j) with hb
  -- oriented angle ∠(wᵢ,wⱼ) = b − a, so its toReal is the reduced (b.toReal − a.toReal)
  have hadd : o.oangle (w i) (w j) = b - a := by
    have h1 := o.oangle_add (hw i) (hw 0) (hw j)
    rw [o.oangle_rev (w 0) (w i)] at h1
    rw [← h1, ha, hb]; abel
  have hcoe : o.oangle (w i) (w j) = ((b.toReal - a.toReal : ℝ) : Real.Angle) := by
    rw [hadd, Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  have hang : InnerProductGeometry.angle (w i) (w j)
      = |(((b.toReal - a.toReal : ℝ) : Real.Angle)).toReal| := by
    rw [o.angle_eq_abs_oangle_toReal (hw i) (hw j), hcoe]
  -- the difference of two `toReal`s lies in `(-2π, 2π)`
  have hbnd : |b.toReal - a.toReal| ≤ 2 * π := by
    have ha1 := Real.Angle.neg_pi_lt_toReal a
    have ha2 := Real.Angle.toReal_le_pi a
    have hb1 := Real.Angle.neg_pi_lt_toReal b
    have hb2 := Real.Angle.toReal_le_pi b
    rw [abs_le]; constructor <;> linarith
  have h1 := abs_toReal_coe_le_abs (b.toReal - a.toReal)
  have h2 := abs_toReal_coe_le_two_pi_sub (b.toReal - a.toReal) hbnd
  have hpos := hsep i j hij
  rw [hang] at hpos
  have habseq : |a.toReal - b.toReal| = |b.toReal - a.toReal| := abs_sub_comm _ _
  rw [habseq, lt_min_iff]
  exact ⟨lt_of_lt_of_le hpos h1, lt_of_lt_of_le hpos h2⟩

/-- **At most 5 vectors pairwise `> π/3` (finite-set form).** A finset of nonzero plane vectors that
are pairwise more than `π/3` apart has at most `5` elements — the form the record list consumes (the
`K` distinct nearest-neighbour distances give `K` pairwise-`> π/3` vectors, so `K ≤ 5`). -/
theorem card_le_five_of_pairwise
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    (s : Finset (EuclideanSpace ℝ (Fin 2))) (h0 : ∀ v ∈ s, v ≠ 0)
    (hsep : ∀ v ∈ s, ∀ u ∈ s, v ≠ u → π / 3 < InnerProductGeometry.angle v u) :
    s.card ≤ 5 := by
  by_contra h
  push Not at h
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 6 ≤ s.card by omega)
  let e := (Finset.equivFinOfCardEq htc).symm
  set w : Fin 6 → EuclideanSpace ℝ (Fin 2) := fun i => (e i : EuclideanSpace ℝ (Fin 2)) with hwdef
  have hmem : ∀ i, w i ∈ s := fun i => hts (e i).2
  have hinj : Function.Injective w := fun i j hij => e.injective (Subtype.ext hij)
  refine not_six_vectors_pairwise o w (fun i => h0 _ (hmem i)) ?_
  intro i j hij
  exact hsep _ (hmem i) _ (hmem j) (fun he => hij (hinj he))

/-- **Distinct-value count `≤ 5` from a separated record assignment (HM direct-route interface).**
If each value `val i` (`i ∈ s`) is assigned a *record vector* `rec (val i)` that is nonzero, and
records of distinct values are pairwise more than `π/3` apart, then there are at most `5` distinct
values. This is the exact interface for the sharp Euclidean `g₂ ≤ 5`: the `K` distinct
nearest-neighbour gaps at a fixed `N`, assigned their realizing orbit-difference vectors (records),
are pairwise `> π/3` by the minimality crux (`EuclideanAngle.angle_gt_pi_div_three`), so `K ≤ 5`.
The remaining work is supplying the assignment `rec` and its two hypotheses — the gaps↔records
correspondence — *not* the geometry, which `card_le_five_of_pairwise` now discharges. -/
theorem card_image_le_five_of_record_assignment {ι : Type*} (s : Finset ι) (val : ι → ℝ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    (rec : ℝ → EuclideanSpace ℝ (Fin 2)) (hne : ∀ i ∈ s, rec (val i) ≠ 0)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, val i ≠ val j →
      π / 3 < InnerProductGeometry.angle (rec (val i)) (rec (val j))) :
    (s.image val).card ≤ 5 := by
  set T := s.image val with hT
  have hrec_inj : Set.InjOn rec T := by
    intro a ha b hb hab
    by_contra hne'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hangpos := hsep i hi j hj (fun h => hne' h)
    rw [hab, InnerProductGeometry.angle_self (hne j hj)] at hangpos
    have := Real.pi_pos
    linarith
  have hcard_eq : (T.image rec).card = T.card := Finset.card_image_of_injOn hrec_inj
  have hle : (T.image rec).card ≤ 5 := by
    refine card_le_five_of_pairwise o _ ?_ ?_
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact hne i hi
    · intro v hv u hu hvu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      refine hsep i hi j hj (fun h => hvu ?_)
      rw [h]
  rw [hcard_eq] at hle
  exact hle

open RealInnerProductSpace in
/-- **Step A: at most 3 vectors can be on one side of `v₀` and pairwise `> π/3`.** Four nonzero
vectors all on the same side of `v₀` (all `det2 v₀ (w i)` of one sign) and pairwise more than `π/3`
apart are impossible: their reference angles `βᵢ = ∠(v₀, w i)` lie in the length-`π` interval
`[0,π]`
and (same side) are pairwise `> π/3` apart, contradicting `not_four_in_interval`. -/
theorem not_four_same_side (v0 : EuclideanSpace ℝ (Fin 2)) (w : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (h0 : v0 ≠ 0) (hw : ∀ i, w i ≠ 0) (hside : ∀ i j, 0 < det2 v0 (w i) * det2 v0 (w j))
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j)) : False := by
  apply not_four_in_interval (fun i => InnerProductGeometry.angle v0 (w i)) 0
  · intro i
    exact ⟨InnerProductGeometry.angle_nonneg _ _, by
      simpa using InnerProductGeometry.angle_le_pi v0 (w i)⟩
  · intro i j hij
    rw [← angle_eq_abs_sub_of_same_side v0 (w i) (w j) h0 (hw i) (hw j) (hside i j)]
    exact hsep i j hij

open RealInnerProductSpace in
/-- **At most 2 vectors strictly on one side of `v₀` and `> π/3` from `v₀`, pairwise `> π/3`.**
Three
nonzero vectors all on the same strict side of `v₀` (`det2 v₀ (w i)` of one sign), each more than
`π/3` from `v₀`, and pairwise more than `π/3` apart are impossible: their reference angles
`βᵢ = ∠(v₀, w i)` lie in the length-`2π/3` interval `(π/3, π]` and are pairwise `> π/3` apart,
contradicting `not_three_in_interval`. This is the per-side ceiling the Theorem-8 cyclic argument
uses
(so the four non-shortest vectors split with `≥ 1` strictly on each side of the shortest). -/
theorem not_three_same_side (v0 : EuclideanSpace ℝ (Fin 2)) (w : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (h0 : v0 ≠ 0) (hw : ∀ i, w i ≠ 0) (hside : ∀ i j, 0 < det2 v0 (w i) * det2 v0 (w j))
    (hbeta : ∀ i, π / 3 < InnerProductGeometry.angle v0 (w i))
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j)) : False := by
  apply not_three_in_interval (fun i => InnerProductGeometry.angle v0 (w i)) (π / 3)
  · intro i
    refine ⟨(hbeta i).le, ?_⟩
    have := InnerProductGeometry.angle_le_pi v0 (w i)
    linarith
  · intro i j hij
    rw [← angle_eq_abs_sub_of_same_side v0 (w i) (w j) h0 (hw i) (hw j) (hside i j)]
    exact hsep i j hij

open RealInnerProductSpace in
/-- **At most one vector can be antiparallel to `v₀`.** If `det2 v₀ wᵢ = 0` and `det2 v₀ wⱼ = 0`
with
both `> π/3` from `v₀`, then `∠(wᵢ,wⱼ) ≤ π/3` — impossible under pairwise `> π/3`. (Zero signed area
+
`v₀ ≠ 0` ⟹ parallel to `v₀`; `> π/3` from `v₀` forces `∠(v₀,·)=π` (antiparallel); two antiparallel
vectors point the same way, so `∠(wᵢ,wⱼ)=0`.) -/
theorem antiparallel_unique (v0 wi wj : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0) (hwi : wi ≠ 0)
    (hwj : wj ≠ 0) (hi0 : det2 v0 wi = 0) (hj0 : det2 v0 wj = 0)
    (hbi : π / 3 < InnerProductGeometry.angle v0 wi)
    (hbj : π / 3 < InnerProductGeometry.angle v0 wj)
    (hsep : π / 3 < InnerProductGeometry.angle wi wj) : False := by
  have hang : ∀ w : EuclideanSpace ℝ (Fin 2), w ≠ 0 → det2 v0 w = 0 →
      π / 3 < InnerProductGeometry.angle v0 w → InnerProductGeometry.angle v0 w = π := by
    intro w hw hdet hb
    have hs := abs_det2_eq v0 w h0 hw
    rw [hdet, abs_zero] at hs
    have hsin : Real.sin (InnerProductGeometry.angle v0 w) = 0 := by
      have hpos : (0 : ℝ) < ‖v0‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr hw)
      have he : ‖v0‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle v0 w) = 0 := hs.symm
      rcases mul_eq_zero.mp he with h | h
      · exact absurd h hpos.ne'
      · exact h
    rcases InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mp hsin with h | h
    · linarith [Real.pi_pos]
    · exact h
  obtain ⟨_, ri, hri, hwi_eq⟩ := InnerProductGeometry.angle_eq_pi_iff.mp (hang wi hwi hi0 hbi)
  obtain ⟨_, rj, hrj, hwj_eq⟩ := InnerProductGeometry.angle_eq_pi_iff.mp (hang wj hwj hj0 hbj)
  have h0' : InnerProductGeometry.angle wi wj = 0 := by
    rw [hwi_eq, hwj_eq, InnerProductGeometry.angle_smul_left_of_neg _ _ hri,
      InnerProductGeometry.angle_smul_right_of_neg _ _ hrj,
      InnerProductGeometry.angle_self (neg_ne_zero.mpr h0)]
  linarith [Real.pi_pos]

open RealInnerProductSpace in
/-- **At least one vector strictly on the positive side of `v₀`.** Among 4 nonzero vectors each `>
π/3`
from `v₀` and pairwise `> π/3`, some has `det2 v₀ (w i) > 0`. Otherwise all have `det2 ≤ 0`; at most
one is antiparallel (`det2 = 0`, by `antiparallel_unique`), so `≥ 3` are strictly negative — but
`not_three_same_side` forbids `3` on one strict side. -/
theorem exists_pos_det2 (v0 : EuclideanSpace ℝ (Fin 2)) (w : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (h0 : v0 ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hbeta : ∀ i, π / 3 < InnerProductGeometry.angle v0 (w i))
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j)) :
    ∃ i, 0 < det2 v0 (w i) := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : (Finset.univ.filter (fun i => det2 v0 (w i) = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact antiparallel_unique v0 (w a) (w b) h0 (hw a) (hw b) ha hb (hbeta a) (hbeta b)
      (hsep a b hab)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4))) (fun i => det2 v0 (w i) < 0)
  have hcongr : (Finset.univ.filter (fun i => ¬ det2 v0 (w i) < 0))
      = Finset.univ.filter (fun i => det2 v0 (w i) = 0) :=
    Finset.filter_congr (fun i _ => by
      have := hcon i; rw [not_lt]; exact ⟨fun h => le_antisymm this h, fun h => h.ge⟩)
  rw [hcongr, Finset.card_univ, Fintype.card_fin] at hpart
  have hneg : 3 ≤ (Finset.univ.filter (fun i => det2 v0 (w i) < 0)).card := by omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hneg
  set e := (t.equivFinOfCardEq htc).symm with he
  have hnegi : ∀ i : Fin 3, det2 v0 (w (e i : Fin 4)) < 0 := by
    intro i
    have := hts (e i).2
    simp only [Finset.mem_filter] at this; exact this.2
  exact not_three_same_side v0 (fun i => w (e i : Fin 4)) h0 (fun i => hw _)
    (fun i j => mul_pos_of_neg_of_neg (hnegi i) (hnegi j)) (fun i => hbeta _)
    (fun i j hij => hsep _ _ (fun heq => hij (e.injective (Subtype.ext heq))))

open RealInnerProductSpace in
/-- **At least one vector strictly on the negative side of `v₀`** (mirror of `exists_pos_det2`). -/
theorem exists_neg_det2 (v0 : EuclideanSpace ℝ (Fin 2)) (w : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (h0 : v0 ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hbeta : ∀ i, π / 3 < InnerProductGeometry.angle v0 (w i))
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (w i) (w j)) :
    ∃ i, det2 v0 (w i) < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : (Finset.univ.filter (fun i => det2 v0 (w i) = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact antiparallel_unique v0 (w a) (w b) h0 (hw a) (hw b) ha hb (hbeta a) (hbeta b)
      (hsep a b hab)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4))) (fun i => 0 < det2 v0 (w i))
  have hcongr : (Finset.univ.filter (fun i => ¬ 0 < det2 v0 (w i)))
      = Finset.univ.filter (fun i => det2 v0 (w i) = 0) :=
    Finset.filter_congr (fun i _ => by
      rw [not_lt]; exact ⟨fun h => le_antisymm h (hcon i), fun h => h.le⟩)
  rw [hcongr, Finset.card_univ, Fintype.card_fin] at hpart
  have hpos3 : 3 ≤ (Finset.univ.filter (fun i => 0 < det2 v0 (w i))).card := by omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hpos3
  set e := (t.equivFinOfCardEq htc).symm with he
  have hposi : ∀ i : Fin 3, 0 < det2 v0 (w (e i : Fin 4)) := by
    intro i
    have := hts (e i).2
    simp only [Finset.mem_filter] at this; exact this.2
  exact not_three_same_side v0 (fun i => w (e i : Fin 4)) h0 (fun i => hw _)
    (fun i j => mul_pos (hposi i) (hposi j)) (fun i => hbeta _)
    (fun i j hij => hsep _ _ (fun heq => hij (e.injective (Subtype.ext heq))))

/-- **`v₁` lies in the open cone of a flanking pair.** If `vⱼ` is strictly on the positive side of
`v₁` (`det2 v₁ vⱼ > 0`), `vₖ` strictly on the negative side (`det2 v₁ vₖ < 0`), and the through-`v₁`
arc is less than `π` (`det2 vⱼ vₖ < 0`, the orientation that makes `vⱼ, v₁, vₖ` a positively-spanned
triple), then `v₁ = s·vⱼ + t·vₖ` with `s, t > 0`. From `mem_openCone_of_det_signs`. -/
theorem v1_mem_openCone_of_flanking {v1 vj vk : EuclideanSpace ℝ (Fin 2)} (hpos : 0 < det2 v1 vj)
    (hneg : det2 v1 vk < 0) (harc : det2 vj vk < 0) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ v1 = s • vj + t • vk := by
  refine mem_openCone_of_det_signs vj v1 vk (ne_of_lt harc) ?_ ?_
  · exact div_pos_iff.mpr (Or.inr ⟨hneg, harc⟩)
  · refine div_pos_iff.mpr (Or.inr ⟨?_, harc⟩)
    rw [det2_skew]; linarith

open RealInnerProductSpace in
/-- **Flanking sign from the angle sum.** For `vⱼ` strictly on the positive side of `v₀`
(`det2 v₀ vⱼ > 0`) and `vₖ` strictly on the negative side (`det2 v₀ vₖ < 0`), the signed area
`det2 vⱼ vₖ = −‖vⱼ‖‖vₖ‖·sin(βⱼ+βₖ)` (`βₘ = ∠(v₀,vₘ)`), via the sine-difference law and `sin_add`. In
particular `βⱼ+βₖ < π ⟹ det2 vⱼ vₖ < 0` — the through-`v₀` arc is `< π`, the orientation
`v1_mem_openCone_of_flanking` needs. -/
theorem det2_neg_of_opp_side_of_sum_lt_pi (v0 vj vk : EuclideanSpace ℝ (Fin 2)) (h0 : v0 ≠ 0)
    (hj : vj ≠ 0) (hk : vk ≠ 0) (hjpos : 0 < det2 v0 vj) (hkneg : det2 v0 vk < 0)
    (hsum : InnerProductGeometry.angle v0 vj + InnerProductGeometry.angle v0 vk < π) :
    det2 vj vk < 0 := by
  set bj := InnerProductGeometry.angle v0 vj with hbj
  set bk := InnerProductGeometry.angle v0 vk with hbk
  have hvj : (0 : ℝ) < ‖vj‖ := norm_pos_iff.mpr hj
  have hvk : (0 : ℝ) < ‖vk‖ := norm_pos_iff.mpr hk
  have hcj : ⟪v0, vj⟫ = ‖v0‖ * ‖vj‖ * Real.cos bj := by
    rw [hbj, InnerProductGeometry.cos_angle]; field_simp
  have hck : ⟪v0, vk⟫ = ‖v0‖ * ‖vk‖ * Real.cos bk := by
    rw [hbk, InnerProductGeometry.cos_angle]; field_simp
  have hdj : det2 v0 vj = ‖v0‖ * ‖vj‖ * Real.sin bj := by
    rw [hbj]; have h := abs_det2_eq v0 vj h0 hj; rw [abs_of_pos hjpos] at h; exact h
  have hdk : det2 v0 vk = -(‖v0‖ * ‖vk‖ * Real.sin bk) := by
    rw [hbk]; have h := abs_det2_eq v0 vk h0 hk; rw [abs_of_neg hkneg] at h; linarith
  have hbjpos : 0 < bj := by
    by_contra hc
    push Not at hc
    have hge : 0 ≤ bj := by rw [hbj]; exact InnerProductGeometry.angle_nonneg v0 vj
    have hbj0 : bj = 0 := le_antisymm hc hge
    rw [hbj0, Real.sin_zero, mul_zero] at hdj; linarith
  have hbknn : 0 ≤ bk := by rw [hbk]; exact InnerProductGeometry.angle_nonneg v0 vk
  have hmain := det2_mul_eq v0 vj vk
  rw [hcj, hck, hdj, hdk] at hmain
  have hsinpos : 0 < Real.sin (bj + bk) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) hsum
  have hv0sq : (0 : ℝ) < ‖v0‖ ^ 2 := by positivity
  have hkey : ‖v0‖ ^ 2 * det2 vj vk = -(‖v0‖ ^ 2 * ‖vj‖ * ‖vk‖ * Real.sin (bj + bk)) := by
    rw [Real.sin_add]; linear_combination hmain
  have hprod : 0 < ‖v0‖ ^ 2 * ‖vj‖ * ‖vk‖ * Real.sin (bj + bk) :=
    mul_pos (mul_pos (mul_pos hv0sq hvj) hvk) hsinpos
  nlinarith [hkey, hprod, hv0sq]

/-- A 2D vector with zero signed area against a nonzero `v₀` is a scalar multiple of it
(`det2 v₀ w = 0 ⟹ w ∈ ℝ·v₀`). -/
theorem parallel_of_det2_zero {v0 w : EuclideanSpace ℝ (Fin 2)} (h0 : v0 ≠ 0)
    (hdet : det2 v0 w = 0) : ∃ c : ℝ, w = c • v0 := by
  have hor : v0 0 ≠ 0 ∨ v0 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (PiLp.ext fun i => by fin_cases i <;> simp [hc.1, hc.2])
  have hdet' : v0 0 * w 1 = v0 1 * w 0 := by
    have : v0 0 * w 1 - v0 1 * w 0 = 0 := hdet
    linarith
  rcases hor with h00 | h01
  · refine ⟨w 0 / v0 0, PiLp.ext fun i => ?_⟩
    fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one]
    · field_simp
    · field_simp; linear_combination hdet'
  · refine ⟨w 1 / v0 1, PiLp.ext fun i => ?_⟩
    fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one]
    · field_simp; linear_combination -hdet'
    · field_simp

open RealInnerProductSpace in
/-- **Antiparallel angle.** If `w` is a negative multiple of `v₀` (forced when `det2 v₀ w = 0` and
`∠(v₀,w) > π/3`, since then `w` is parallel but not codirectional), then for any `u`,
`∠(w,u) = π − ∠(v₀,u)`. The reflected reference vector flips the angle through `π`. -/
theorem angle_antiparallel {v0 w : EuclideanSpace ℝ (Fin 2)} (u : EuclideanSpace ℝ (Fin 2))
    (h0 : v0 ≠ 0) (hw : w ≠ 0) (hdet : det2 v0 w = 0)
    (hbeta : π / 3 < InnerProductGeometry.angle v0 w) :
    InnerProductGeometry.angle w u = π - InnerProductGeometry.angle v0 u := by
  obtain ⟨c, hc⟩ := parallel_of_det2_zero h0 hdet
  have hcneg : c < 0 := by
    rcases lt_trichotomy c 0 with h | h | h
    · exact h
    · exact absurd (hc.trans (by rw [h, zero_smul])) hw
    · exfalso
      have hz : InnerProductGeometry.angle v0 w = 0 := by
        rw [hc, InnerProductGeometry.angle_smul_right_of_pos _ _ h,
          InnerProductGeometry.angle_self h0]
      rw [hz] at hbeta; linarith [Real.pi_pos]
  rw [hc, InnerProductGeometry.angle_smul_left_of_neg _ _ hcneg,
    InnerProductGeometry.angle_neg_left]

/-- **Haynes–Marklof Theorem 8 — final contradiction step.** With the cone property (the shortest
vector `v 0` is in no open cone `openCone(v j, v k)` for higher indices `0 < j, k`, `j ≠ k`), a
*flanking pair* — `v j` strictly positive of `v 0`, `v k` strictly negative, through-`v 0` arc `< π`
(`det2 (v j) (v k) < 0`) — is contradictory, since it puts `v 0 ∈ openCone(v j, v k)`. The arc-`< π`
fact (from `det2_neg_of_opp_side_of_sum_lt_pi` once the gap argument gives `βⱼ+βₖ < π`) is the
single
remaining geometric input for `g₂ ≤ 5` along this route. -/
theorem hm_theorem8_final {v : Fin 5 → EuclideanSpace ℝ (Fin 2)}
    (hcone : ∀ j k : Fin 5, 0 < j → 0 < k → j ≠ k →
      ¬ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ v 0 = s • v j + t • v k)
    {j k : Fin 5} (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k)
    (hpos : 0 < det2 (v 0) (v j)) (hneg : det2 (v 0) (v k) < 0) (harc : det2 (v j) (v k) < 0) :
    False :=
  hcone j k hj hk hjk (v1_mem_openCone_of_flanking hpos hneg harc)

open RealInnerProductSpace in
/-- **Antiparallel reference angle is `π`.** If `det2 v₀ w = 0` (so `w` is parallel to `v₀`) and
`∠(v₀,w) > π/3` (ruling out codirectional), then `∠(v₀,w) = π`. Extracted from
`antiparallel_unique`'s
inner argument; the signed-angle gap argument needs it to pin antiparallel records to `ψ = π`. -/
theorem angle_eq_pi_of_det2_zero {v0 w : EuclideanSpace ℝ (Fin 2)} (h0 : v0 ≠ 0) (hw : w ≠ 0)
    (hdet : det2 v0 w = 0) (hb : π / 3 < InnerProductGeometry.angle v0 w) :
    InnerProductGeometry.angle v0 w = π := by
  have hs := abs_det2_eq v0 w h0 hw
  rw [hdet, abs_zero] at hs
  have hsin : Real.sin (InnerProductGeometry.angle v0 w) = 0 := by
    have hpos : (0 : ℝ) < ‖v0‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr hw)
    rcases mul_eq_zero.mp hs.symm with h | h
    · exact absurd h hpos.ne'
    · exact h
  rcases InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mp hsin with h | h
  · linarith [Real.pi_pos]
  · exact h

open RealInnerProductSpace in
/-- **Haynes–Marklof gap-existence (the flanking pair).** Among 5 nonzero vectors pairwise more than
`π/3` apart, there is a *flanking pair* for `v 0`: indices `j, k ≠ 0` with `v j` strictly on the
positive side (`det2 (v 0) (v j) > 0`), `v k` strictly on the negative side (`det2 (v 0) (v k) <
0`),
and reference-angle sum `βⱼ + βₖ < π`. **Proof.** Pick the minimal-`β` vector on each side; if their
sum is `< π` we are done. Otherwise, place all 4 non-`v 0` vectors at signed angles `ψ` (positive
side
`ψ = β`, negative/antiparallel side `ψ = 2π − β`); the assumed sum `≥ π` compresses them into an
interval of length `π`, where they are still pairwise `> π/3` (same-side: `|βᵢ−βⱼ|`; cross-side:
`2π−(βᵢ+βⱼ)`; antiparallel: `π−β`) — impossible by `not_four_in_interval`. -/
theorem exists_flanking_pair {v : Fin 5 → EuclideanSpace ℝ (Fin 2)} (hne : ∀ i, v i ≠ 0)
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (v i) (v j)) :
    ∃ j k : Fin 5, j ≠ 0 ∧ k ≠ 0 ∧ 0 < det2 (v 0) (v j) ∧ det2 (v 0) (v k) < 0 ∧
      InnerProductGeometry.angle (v 0) (v j) + InnerProductGeometry.angle (v 0) (v k) < π := by
  classical
  have hpi := Real.pi_pos
  set w : Fin 4 → EuclideanSpace ℝ (Fin 2) := fun t => v t.succ with hwdef
  have hw0 : ∀ t, w t ≠ 0 := fun t => hne t.succ
  have hsuccne : ∀ t : Fin 4, (t.succ : Fin 5) ≠ 0 := fun t => Fin.succ_ne_zero t
  have hbpos : ∀ t : Fin 4, π / 3 < InnerProductGeometry.angle (v 0) (w t) := fun t =>
    hsep 0 t.succ (fun h => hsuccne t h.symm)
  have hble : ∀ t : Fin 4, InnerProductGeometry.angle (v 0) (w t) ≤ π := fun t =>
    InnerProductGeometry.angle_le_pi _ _
  have hbnn : ∀ t : Fin 4, 0 ≤ InnerProductGeometry.angle (v 0) (w t) := fun t =>
    InnerProductGeometry.angle_nonneg _ _
  have hwsep : ∀ s t : Fin 4, s ≠ t → π / 3 < InnerProductGeometry.angle (w s) (w t) :=
    fun s t hst => hsep s.succ t.succ (fun h => hst (Fin.succ_injective _ h))
  obtain ⟨ip, hip⟩ := exists_pos_det2 (v 0) w (hne 0) hw0 hbpos hwsep
  obtain ⟨im, him⟩ := exists_neg_det2 (v 0) w (hne 0) hw0 hbpos hwsep
  obtain ⟨js, hjs_mem, hjs_min⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun t => 0 < det2 (v 0) (w t)))
    (fun t => InnerProductGeometry.angle (v 0) (w t))
    ⟨ip, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hip⟩⟩
  obtain ⟨ks, hks_mem, hks_min⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun t => det2 (v 0) (w t) < 0))
    (fun t => InnerProductGeometry.angle (v 0) (w t))
    ⟨im, Finset.mem_filter.mpr ⟨Finset.mem_univ _, him⟩⟩
  have hjs_pos : 0 < det2 (v 0) (w js) := (Finset.mem_filter.mp hjs_mem).2
  have hks_neg : det2 (v 0) (w ks) < 0 := (Finset.mem_filter.mp hks_mem).2
  rcases lt_or_ge (InnerProductGeometry.angle (v 0) (w js)
      + InnerProductGeometry.angle (v 0) (w ks)) π with hlt | hge
  · exact ⟨js.succ, ks.succ, hsuccne js, hsuccne ks, hjs_pos, hks_neg, hlt⟩
  · exfalso
    set θ : Fin 4 → ℝ :=
      fun t => if 0 < det2 (v 0) (w t) then InnerProductGeometry.angle (v 0) (w t)
        else 2 * π - InnerProductGeometry.angle (v 0) (w t) with hθ
    have θpos : ∀ t, 0 < det2 (v 0) (w t) → θ t = InnerProductGeometry.angle (v 0) (w t) := by
      intro t h; rw [hθ]; exact if_pos h
    have θneg : ∀ t, det2 (v 0) (w t) < 0 →
        θ t = 2 * π - InnerProductGeometry.angle (v 0) (w t) := by
      intro t h; rw [hθ]; exact if_neg (not_lt.mpr h.le)
    have θzero : ∀ t, det2 (v 0) (w t) = 0 →
        θ t = 2 * π - InnerProductGeometry.angle (v 0) (w t) := by
      intro t h; rw [hθ]; exact if_neg (by rw [h]; exact lt_irrefl 0)
    refine not_four_in_interval θ (InnerProductGeometry.angle (v 0) (w js)) ?_ ?_
    · -- membership in the length-π interval
      intro t
      rw [Set.mem_Icc]
      rcases lt_trichotomy (det2 (v 0) (w t)) 0 with htn | htz | htp
      · rw [θneg t htn]
        refine ⟨?_, ?_⟩
        · have := hble t; have := hble js; linarith
        · have hmin := hks_min t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htn⟩); linarith
      · rw [θzero t htz]
        have hbt : InnerProductGeometry.angle (v 0) (w t) = π :=
          angle_eq_pi_of_det2_zero (hne 0) (hw0 t) htz (hbpos t)
        refine ⟨?_, ?_⟩
        · rw [hbt]; have := hble js; linarith
        · rw [hbt]; have := hbnn js; linarith
      · rw [θpos t htp]
        refine ⟨hjs_min t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htp⟩), ?_⟩
        have := hble t; have := hbnn js; linarith
    · -- pairwise > π/3
      intro s t hst
      have hwst : π / 3 < InnerProductGeometry.angle (w s) (w t) := hwsep s t hst
      rcases lt_trichotomy (det2 (v 0) (w s)) 0 with hsn | hsz | hsp <;>
        rcases lt_trichotomy (det2 (v 0) (w t)) 0 with htn | htz | htp
      · -- (−,−)
        rw [θneg s hsn, θneg t htn]
        have hsame := angle_eq_abs_sub_of_same_side (v 0) (w s) (w t) (hne 0) (hw0 s) (hw0 t)
          (mul_pos_of_neg_of_neg hsn htn)
        have he : (2 * π - InnerProductGeometry.angle (v 0) (w s))
            - (2 * π - InnerProductGeometry.angle (v 0) (w t))
            = InnerProductGeometry.angle (v 0) (w t) - InnerProductGeometry.angle (v 0) (w s) := by
          ring
        rw [he, abs_sub_comm, ← hsame]; exact hwst
      · -- (−, anti)
        rw [θneg s hsn, θzero t htz]
        have hbt : InnerProductGeometry.angle (v 0) (w t) = π :=
          angle_eq_pi_of_det2_zero (hne 0) (hw0 t) htz (hbpos t)
        have hanti : InnerProductGeometry.angle (w s) (w t)
            = π - InnerProductGeometry.angle (v 0) (w s) := by
          rw [InnerProductGeometry.angle_comm (w s) (w t)]
          exact angle_antiparallel (w s) (hne 0) (hw0 t) htz (hbpos t)
        rw [hbt]
        have he : (2 * π - InnerProductGeometry.angle (v 0) (w s)) - (2 * π - π)
            = π - InnerProductGeometry.angle (v 0) (w s) := by ring
        rw [he, abs_of_nonneg (by have := hble s; linarith)]
        rw [hanti] at hwst; linarith
      · -- (−, +)
        rw [θneg s hsn, θpos t htp]
        have hopp := angle_eq_of_opp_side (v 0) (w s) (w t) (hne 0) (hw0 s) (hw0 t)
          (mul_neg_of_neg_of_pos hsn htp)
        rw [hopp] at hwst
        have hk : |π - (InnerProductGeometry.angle (v 0) (w s)
            + InnerProductGeometry.angle (v 0) (w t))| < 2 * π / 3 := by linarith
        rw [abs_lt] at hk
        have he : (2 * π - InnerProductGeometry.angle (v 0) (w s))
            - InnerProductGeometry.angle (v 0) (w t)
            = 2 * π - (InnerProductGeometry.angle (v 0) (w s)
              + InnerProductGeometry.angle (v 0) (w t)) := by ring
        rw [he, abs_of_nonneg (by have := hble s; have := hble t; linarith)]
        linarith [hk.1]
      · -- (anti, −)
        rw [θzero s hsz, θneg t htn]
        have hbs : InnerProductGeometry.angle (v 0) (w s) = π :=
          angle_eq_pi_of_det2_zero (hne 0) (hw0 s) hsz (hbpos s)
        have hanti : InnerProductGeometry.angle (w s) (w t)
            = π - InnerProductGeometry.angle (v 0) (w t) :=
          angle_antiparallel (w t) (hne 0) (hw0 s) hsz (hbpos s)
        rw [hbs]
        have he : (2 * π - π) - (2 * π - InnerProductGeometry.angle (v 0) (w t))
            = InnerProductGeometry.angle (v 0) (w t) - π := by ring
        rw [he, abs_sub_comm, abs_of_nonneg (by have := hble t; linarith)]
        rw [hanti] at hwst; linarith
      · -- (anti, anti) — impossible
        exact (antiparallel_unique (v 0) (w s) (w t) (hne 0) (hw0 s) (hw0 t) hsz htz
          (hbpos s) (hbpos t) hwst).elim
      · -- (anti, +)
        rw [θzero s hsz, θpos t htp]
        have hbs : InnerProductGeometry.angle (v 0) (w s) = π :=
          angle_eq_pi_of_det2_zero (hne 0) (hw0 s) hsz (hbpos s)
        have hanti : InnerProductGeometry.angle (w s) (w t)
            = π - InnerProductGeometry.angle (v 0) (w t) :=
          angle_antiparallel (w t) (hne 0) (hw0 s) hsz (hbpos s)
        rw [hbs]
        have he : (2 * π - π) - InnerProductGeometry.angle (v 0) (w t)
            = π - InnerProductGeometry.angle (v 0) (w t) := by ring
        rw [he, abs_of_nonneg (by have := hble t; linarith)]
        rw [hanti] at hwst; linarith
      · -- (+, −)
        rw [θpos s hsp, θneg t htn]
        have hopp := angle_eq_of_opp_side (v 0) (w s) (w t) (hne 0) (hw0 s) (hw0 t)
          (mul_neg_of_pos_of_neg hsp htn)
        rw [hopp] at hwst
        have hk : |π - (InnerProductGeometry.angle (v 0) (w s)
            + InnerProductGeometry.angle (v 0) (w t))| < 2 * π / 3 := by linarith
        rw [abs_lt] at hk
        have he : InnerProductGeometry.angle (v 0) (w s)
            - (2 * π - InnerProductGeometry.angle (v 0) (w t))
            = (InnerProductGeometry.angle (v 0) (w s)
              + InnerProductGeometry.angle (v 0) (w t)) - 2 * π := by ring
        rw [he, abs_sub_comm, abs_of_nonneg (by have := hble s; have := hble t; linarith)]
        linarith [hk.1]
      · -- (+, anti)
        rw [θpos s hsp, θzero t htz]
        have hbt : InnerProductGeometry.angle (v 0) (w t) = π :=
          angle_eq_pi_of_det2_zero (hne 0) (hw0 t) htz (hbpos t)
        have hanti : InnerProductGeometry.angle (w s) (w t)
            = π - InnerProductGeometry.angle (v 0) (w s) := by
          rw [InnerProductGeometry.angle_comm (w s) (w t)]
          exact angle_antiparallel (w s) (hne 0) (hw0 t) htz (hbpos t)
        rw [hbt]
        have he : InnerProductGeometry.angle (v 0) (w s) - (2 * π - π)
            = InnerProductGeometry.angle (v 0) (w s) - π := by ring
        rw [he, abs_sub_comm, abs_of_nonneg (by have := hble s; linarith)]
        rw [hanti] at hwst; linarith
      · -- (+, +)
        rw [θpos s hsp, θpos t htp]
        have hsame := angle_eq_abs_sub_of_same_side (v 0) (w s) (w t) (hne 0) (hw0 s) (hw0 t)
          (mul_pos hsp htp)
        rw [← hsame]; exact hwst

open RealInnerProductSpace in
/-- **Haynes–Marklof Theorem 8.** Five nonzero vectors pairwise more than `π/3` apart cannot satisfy
the cone property for `v 0` (the shortest vector lies in no open cone of two higher-indexed
vectors).
Combines the flanking pair (`exists_flanking_pair`), the arc-sign bridge
(`det2_neg_of_opp_side_of_sum_lt_pi`), and the cone contradiction (`hm_theorem8_final`). This is the
geometric heart of the sharp Euclidean five-distance theorem `g₂ ≤ 5`. -/
theorem hm_theorem8 {v : Fin 5 → EuclideanSpace ℝ (Fin 2)} (hne : ∀ i, v i ≠ 0)
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (v i) (v j))
    (hcone : ∀ j k : Fin 5, 0 < j → 0 < k → j ≠ k →
      ¬ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ v 0 = s • v j + t • v k) : False := by
  obtain ⟨j, k, hj0, hk0, hjpos, hkneg, hsum⟩ := exists_flanking_pair hne hsep
  have harc : det2 (v j) (v k) < 0 :=
    det2_neg_of_opp_side_of_sum_lt_pi (v 0) (v j) (v k) (hne 0) (hne j) (hne k) hjpos hkneg hsum
  exact hm_theorem8_final hcone (Fin.pos_of_ne_zero hj0) (Fin.pos_of_ne_zero hk0)
    (fun h => by rw [h] at hjpos; exact absurd hkneg (by linarith)) hjpos hkneg harc

end ThreeGap.FiveDistance
