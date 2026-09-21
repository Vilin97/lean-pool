/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Convex.Segment
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Hull
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.TubeDomain.Basic

/-!
# Parabolic analytic discs in tubes and the hull of two segments

For a vertex `p` and two points `t₁, t₂` of the real base, the triangle with these vertices is
parametrized by `p + u • v₁ + v • v₂` with `|u| ≤ v ≤ 1`, where `v₁ = (t₁ - t₂)/2` and `v₂ = (t₁
+ t₂)/2 - p`. The parabolic analytic disc `ζ ↦ p + ζ • v₁ + (c ζ² + 1 - c) • v₂`, restricted to
the planar region where its real part lies in the triangle, has boundary over the two sides `[p,
t₁]` and `[p, t₂]`. By the planar maximum principle, every point of the disc lies in the
holomorphic hull of the boundary, relative to any tube whose base contains the triangle. As `c`
varies, the discs cover all points of the triangle with `|u| < v < 1`. No coordinate
normalization is needed, and the two points may be linearly dependent.

References: [Korevaar–Wiegerinck][KorevaarWiegerinck2017], Exercise 6.28;
[Hörmander][Hormander1973] §2.5, Lemma 2.5.11.

## Main definitions

* `triDir₁`: The half-difference direction of a triangle with vertex `p` and points `t₁, t₂`.
* `triDir₂`: The half-sum direction of a triangle with vertex `p` and points `t₁, t₂`.
* `triPt`: The point of the triangle with parameters `u, v`.
* `tri`: The triangle with vertex `p` and points `t₁, t₂`, scaled by `b` toward `p`.
* `parabolaHeight`: The real-quadratic function defining the parabolic disc region.
* `parabolaRegion`: The planar region over which the parabolic disc lies inside the triangle.
* `parabolaDisc`: The parabolic analytic disc with parameter `c`, translated by the imaginary vector
  `η`.

## Main results

* `convex_tri`: Scaled triangles are convex.
* `segment_subset_tri`: The segment between `t₁` and `t₂` lies in the triangle of scale one.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace SeveralComplexVariables.BochnerTube

variable {ι : Type*}

section Triangle

/-- The half-difference direction of a triangle with vertex `p` and points `t₁, t₂`. -/
@[expose] def triDir₁ (_p t₁ t₂ : ι → ℝ) : ι → ℝ := (1 / 2 : ℝ) • (t₁ - t₂)

/-- The half-sum direction of a triangle with vertex `p` and points `t₁, t₂`. -/
@[expose] def triDir₂ (p t₁ t₂ : ι → ℝ) : ι → ℝ := (1 / 2 : ℝ) • (t₁ + t₂) - p

/-- The point of the triangle with parameters `u, v`. -/
@[expose] def triPt (p t₁ t₂ : ι → ℝ) (u v : ℝ) : ι → ℝ :=
  p + u • triDir₁ p t₁ t₂ + v • triDir₂ p t₁ t₂

/-- The triangle with vertex `p` and points `t₁, t₂`, scaled by `b` toward `p`. -/
@[expose] def tri (p t₁ t₂ : ι → ℝ) (b : ℝ) : Set (ι → ℝ) :=
  {x | ∃ u v : ℝ, |u| ≤ v ∧ v ≤ b ∧ x = triPt p t₁ t₂ u v}

variable (p t₁ t₂ : ι → ℝ)

/-- The triangle point as a combination of the vertex and the two points. -/
theorem triPt_eq (u v : ℝ) :
    triPt p t₁ t₂ u v = p + ((v + u) / 2) • (t₁ - p) + ((v - u) / 2) • (t₂ - p) := by
  unfold triPt triDir₁ triDir₂
  module

/-- The parameters `(0, 0)` give the vertex. -/
@[simp] theorem triPt_zero : triPt p t₁ t₂ 0 0 = p := by simp [triPt]

/-- The parameters `(1, 1)` give the first point. -/
theorem triPt_one_one : triPt p t₁ t₂ 1 1 = t₁ := by rw [triPt_eq]; module

/-- The parameters `(-1, 1)` give the second point. -/
theorem triPt_neg_one_one : triPt p t₁ t₂ (-1) 1 = t₂ := by rw [triPt_eq]; module

/-- Points with `|u| = v` lie on the two sides through the vertex. -/
theorem triPt_mem_union_segment {u v : ℝ} (huv : |u| = v) (hv1 : v ≤ 1) :
    triPt p t₁ t₂ u v ∈ segment ℝ p t₁ ∪ segment ℝ p t₂ := by
  have hv0 : 0 ≤ v := huv ▸ abs_nonneg u
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu] at huv
    subst huv
    left
    rw [segment_eq_image']
    refine ⟨u, ⟨hu, hv1⟩, ?_⟩
    rw [triPt_eq]
    simp only
    module
  · rw [abs_of_neg hu] at huv
    subst huv
    right
    rw [segment_eq_image']
    refine ⟨-u, ⟨by linarith, hv1⟩, ?_⟩
    rw [triPt_eq]
    simp only
    module

/-- The segment between `t₁` and `t₂` lies in the triangle of scale one. -/
theorem segment_subset_tri : segment ℝ t₁ t₂ ⊆ tri p t₁ t₂ 1 := by
  intro x hx
  rw [segment_eq_image'] at hx
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
  refine ⟨1 - 2 * θ, 1, ?_, le_rfl, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [triPt_eq]
    simp only
    module

/-- Scaled triangles increase with the scale. -/
theorem tri_mono {b b' : ℝ} (h : b ≤ b') : tri p t₁ t₂ b ⊆ tri p t₁ t₂ b' := by
  rintro x ⟨u, v, huv, hv, rfl⟩
  exact ⟨u, v, huv, hv.trans h, rfl⟩

/-- The vertex lies in every scaled triangle of nonnegative scale. -/
theorem mem_tri_self {b : ℝ} (hb : 0 ≤ b) : p ∈ tri p t₁ t₂ b :=
  ⟨0, 0, by simp, hb, by simp⟩

/-- The triangle of scale zero is the vertex. -/
theorem tri_zero : tri p t₁ t₂ 0 = {p} := by
  ext x
  constructor
  · rintro ⟨u, v, huv, hv, rfl⟩
    have hv0 : v = 0 := le_antisymm hv ((abs_nonneg u).trans huv)
    have hu0 : u = 0 := abs_eq_zero.mp (le_antisymm (hv0 ▸ huv) (abs_nonneg u))
    simp [hu0, hv0]
  · rintro rfl
    exact mem_tri_self _ _ _ le_rfl

/-- Scaled triangles are convex. -/
theorem convex_tri (b : ℝ) : Convex ℝ (tri p t₁ t₂ b) := by
  rintro x ⟨u, v, huv, hv, rfl⟩ y ⟨u', v', huv', hv', rfl⟩ a a' ha ha' haa
  refine ⟨a * u + a' * u', a * v + a' * v', ?_, ?_, ?_⟩
  · calc |a * u + a' * u'| ≤ |a * u| + |a' * u'| := abs_add_le _ _
      _ = a * |u| + a' * |u'| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg ha']
      _ ≤ a * v + a' * v' := by gcongr
  · calc a * v + a' * v' ≤ a * b + a' * b :=
          add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hv' ha')
      _ = b := by rw [← add_mul, haa, one_mul]
  · simp only [triPt]
    linear_combination (norm := module) haa • p

/-- Scaling the two points toward the vertex scales the first direction. -/
theorem triDir₁_scale (b : ℝ) :
    triDir₁ p (p + b • (t₁ - p)) (p + b • (t₂ - p)) = b • triDir₁ p t₁ t₂ := by
  unfold triDir₁; module

/-- Scaling the two points toward the vertex scales the second direction. -/
theorem triDir₂_scale (b : ℝ) :
    triDir₂ p (p + b • (t₁ - p)) (p + b • (t₂ - p)) = b • triDir₂ p t₁ t₂ := by
  unfold triDir₂; module

/-- Points of a scaled triangle in terms of the original parametrization. -/
theorem triPt_scale {a : ℝ} (ha : a ≠ 0) (u v : ℝ) :
    triPt p (p + a • (t₁ - p)) (p + a • (t₂ - p)) (u / a) (v / a) = triPt p t₁ t₂ u v := by
  simp only [triPt, triDir₁_scale, triDir₂_scale, smul_smul, div_mul_cancel₀ _ ha]

/-- Scaling the two points toward the vertex scales the triangle. -/
theorem tri_scale {b : ℝ} (hb : 0 < b) :
    tri p t₁ t₂ b = tri p (p + b • (t₁ - p)) (p + b • (t₂ - p)) 1 := by
  have hd₁ := triDir₁_scale p t₁ t₂ b
  have hd₂ := triDir₂_scale p t₁ t₂ b
  ext x
  constructor
  · rintro ⟨u, v, huv, hv, rfl⟩
    refine ⟨u / b, v / b, ?_, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hb]; exact div_le_div_of_nonneg_right huv hb.le
    · exact (div_le_one hb).mpr hv
    · simp only [triPt, hd₁, hd₂, smul_smul, div_mul_cancel₀ _ hb.ne']
  · rintro ⟨u, v, huv, hv, rfl⟩
    refine ⟨b * u, b * v, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left huv hb.le
    · calc b * v ≤ b * 1 := mul_le_mul_of_nonneg_left hv hb.le
        _ = b := mul_one b
    · simp only [triPt, hd₁, hd₂, smul_smul, mul_comm b]

/-- For `0 ≤ b ≤ 1`, the segment from `p` toward `t` scaled by `b` lies on the original segment. -/
theorem segment_scaled_subset {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (t : ι → ℝ) :
    segment ℝ p (p + b • (t - p)) ⊆ segment ℝ p t := by
  intro x hx
  rw [segment_eq_image'] at hx ⊢
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
  refine ⟨θ * b, ⟨by positivity, ?_⟩, ?_⟩
  · calc θ * b ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · simp only [add_sub_cancel_left, smul_smul]

end Triangle

section Disc

variable (p t₁ t₂ : ι → ℝ)

/-- The real-quadratic function defining the parabolic disc region. -/
def parabolaHeight (c : ℝ) (ζ : ℂ) : ℝ := c * (ζ.re ^ 2 - ζ.im ^ 2) + (1 - c)

/-- The planar region over which the parabolic disc lies inside the triangle. -/
@[expose] def parabolaRegion (c : ℝ) : Set ℂ :=
  {ζ | |ζ.re| < parabolaHeight c ζ ∧ parabolaHeight c ζ < 1}

/-- The parabolic analytic disc with parameter `c`, translated by the imaginary vector `η`. -/
@[expose] def parabolaDisc (c : ℝ) (η : ι → ℝ) (ζ : ℂ) : ι → ℂ :=
  ofRealPi p + ζ • ofRealPi (triDir₁ p t₁ t₂) +
    (c * ζ ^ 2 + (1 - c)) • ofRealPi (triDir₂ p t₁ t₂) + I • ofRealPi η

/-- The height function of the parabolic region is continuous. -/
theorem continuous_parabolaHeight (c : ℝ) : Continuous (parabolaHeight c) := by
  unfold parabolaHeight; fun_prop

/-- The real part of a complex multiple of a real vector. -/
theorem rePi_smul_ofRealPi (ζ : ℂ) (v : ι → ℝ) : rePi (ζ • ofRealPi v) = ζ.re • v := by
  funext i
  simp [rePi, ofRealPi, Complex.mul_re]

/-- The imaginary part of a complex multiple of a real vector. -/
theorem imPi_smul_ofRealPi (ζ : ℂ) (v : ι → ℝ) : imPi (ζ • ofRealPi v) = ζ.im • v := by
  funext i
  simp [imPi, ofRealPi, Complex.mul_im]

/-- The real part of the parabolic coefficient is the height function. -/
theorem re_parabolaCoeff (c : ℝ) (ζ : ℂ) : (c * ζ ^ 2 + (1 - c) : ℂ).re = parabolaHeight c ζ := by
  simp [parabolaHeight, sq, Complex.mul_re]

/-- The real part of a disc point is the triangle point with parameters given by the real part of
`ζ` and the height. -/
theorem rePi_parabolaDisc (c : ℝ) (η : ι → ℝ) (ζ : ℂ) :
    rePi (parabolaDisc p t₁ t₂ c η ζ) = triPt p t₁ t₂ ζ.re (parabolaHeight c ζ) := by
  unfold parabolaDisc triPt
  rw [rePi_add, rePi_add, rePi_add, rePi_ofRealPi, rePi_smul_ofRealPi, rePi_smul_ofRealPi,
    rePi_I_smul_ofRealPi, re_parabolaCoeff, add_zero]

/-- The imaginary part of a disc point expands in the triangle directions, shifted by `η`. -/
theorem imPi_parabolaDisc (c : ℝ) (η : ι → ℝ) (ζ : ℂ) :
    imPi (parabolaDisc p t₁ t₂ c η ζ) =
      ζ.im • triDir₁ p t₁ t₂ + (c * ζ ^ 2 + (1 - c) : ℂ).im • triDir₂ p t₁ t₂ + η := by
  unfold parabolaDisc
  funext i
  simp [imPi, ofRealPi, Complex.mul_im]

/-- The disc map is continuous. -/
theorem continuous_parabolaDisc (c : ℝ) (η : ι → ℝ) : Continuous (parabolaDisc p t₁ t₂ c η) := by
  unfold parabolaDisc; fun_prop

/-- The disc map is entire. -/
theorem differentiable_parabolaDisc (c : ℝ) (η : ι → ℝ) :
    Differentiable ℂ (parabolaDisc p t₁ t₂ c η) := by
  rw [differentiable_pi]
  intro i
  simp only [parabolaDisc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofRealPi]
  fun_prop

/-- The parabolic region is open. -/
theorem isOpen_parabolaRegion (c : ℝ) : IsOpen (parabolaRegion c) :=
  (isOpen_lt (by fun_prop) (continuous_parabolaHeight c)).inter
    (isOpen_lt (continuous_parabolaHeight c) continuous_const)

/-- The closure of the parabolic region is contained in the corresponding closed sublevel set. -/
theorem closure_parabolaRegion_subset (c : ℝ) :
    closure (parabolaRegion c) ⊆ {ζ | |ζ.re| ≤ parabolaHeight c ζ ∧ parabolaHeight c ζ ≤ 1} :=
  closure_minimal (fun ζ hζ => ⟨hζ.1.le, hζ.2.le⟩)
    ((isClosed_le (by fun_prop) (continuous_parabolaHeight c)).inter
      (isClosed_le (continuous_parabolaHeight c) continuous_const))

/-- If the height equals one and `|Re ζ| ≤ 1`, then `|Re ζ| = 1`. -/
theorem abs_re_eq_one_of_parabolaHeight_eq_one {c : ℝ} (hc : 0 < c) {ζ : ℂ}
    (hre : |ζ.re| ≤ 1) (h : parabolaHeight c ζ = 1) : |ζ.re| = 1 := by
  unfold parabolaHeight at h
  have h1 : ζ.re ^ 2 - ζ.im ^ 2 = 1 := by
    have : c * (ζ.re ^ 2 - ζ.im ^ 2) = c := by linarith
    exact mul_left_cancel₀ hc.ne' (this.trans (mul_one c).symm)
  have h2 : 1 ≤ ζ.re ^ 2 := by nlinarith [sq_nonneg ζ.im]
  have h3 : 1 ≤ |ζ.re| := by
    rw [← sq_le_sq₀ zero_le_one (abs_nonneg _), one_pow, sq_abs]
    exact h2
  exact le_antisymm hre h3

/-- Frontier points of the region have `|Re ζ| = parabolaHeight c ζ ≤ 1`. -/
theorem frontier_parabolaRegion_subset {c : ℝ} (hc : 0 < c) :
    frontier (parabolaRegion c) ⊆ {ζ | |ζ.re| = parabolaHeight c ζ ∧ parabolaHeight c ζ ≤ 1} := by
  intro ζ hζ
  have hcl := closure_parabolaRegion_subset c hζ.1
  have hnot : ζ ∉ parabolaRegion c := fun h => hζ.2 (by rwa [(isOpen_parabolaRegion c).interior_eq])
  refine ⟨?_, hcl.2⟩
  rcases hcl.1.lt_or_eq with hlt | heq
  · exfalso
    apply hnot
    refine ⟨hlt, ?_⟩
    rcases hcl.2.lt_or_eq with hlt2 | heq2
    · exact hlt2
    · exfalso
      have := abs_re_eq_one_of_parabolaHeight_eq_one hc (hcl.1.trans hcl.2) heq2
      linarith
  · exact heq

/-- The region is bounded. -/
theorem isBounded_parabolaRegion {c : ℝ} (hc : 0 < c) :
    Bornology.IsBounded (parabolaRegion c) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 + 1 / c, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := hζ
  have hre : |ζ.re| ≤ 1 := h1.le.trans h2.le
  have hre2 : ζ.re ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) hre
  have him : c * ζ.im ^ 2 ≤ 1 := by
    unfold parabolaHeight at h1
    nlinarith [abs_nonneg ζ.re]
  have him2 : ζ.im ^ 2 ≤ 1 / c := by
    rw [le_div_iff₀ hc]; linarith
  have him3 : |ζ.im| ≤ 1 + 1 / c := by
    have : |ζ.im| ≤ ζ.im ^ 2 + 1 := by
      rcases le_or_gt |ζ.im| 1 with h | h
      · linarith [sq_nonneg ζ.im]
      · have : |ζ.im| ≤ |ζ.im| ^ 2 := by nlinarith [abs_nonneg ζ.im]
        rw [sq_abs] at this
        linarith
    linarith
  rw [mem_closedBall, dist_zero_right]
  calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
    _ ≤ 1 + (1 + 1 / c) := add_le_add hre him3
    _ = 2 + 1 / c := by ring

/-- The image of the frontier of the region under the disc map is compact. -/
theorem isCompact_image_frontier_parabolaRegion {c : ℝ} (hc : 0 < c) (η : ι → ℝ) :
    IsCompact (parabolaDisc p t₁ t₂ c η '' frontier (parabolaRegion c)) :=
  (((isBounded_parabolaRegion hc).isCompact_closure).of_isClosed_subset isClosed_frontier
    frontier_subset_closure).image (continuous_parabolaDisc p t₁ t₂ c η)

/-- The disc over the closed region lies in the tube over the triangle. -/
theorem parabolaDisc_mem_tubeDomain_tri (c : ℝ) (η : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ closure (parabolaRegion c)) :
    parabolaDisc p t₁ t₂ c η ζ ∈ tubeDomain (tri p t₁ t₂ 1) := by
  have h := closure_parabolaRegion_subset c hζ
  rw [mem_tubeDomain, rePi_parabolaDisc]
  exact ⟨ζ.re, parabolaHeight c ζ, h.1, h.2, rfl⟩

/-- The disc boundary lies in the tube over the two sides through the vertex. -/
theorem parabolaDisc_frontier_subset {c : ℝ} (hc : 0 < c) (η : ι → ℝ) :
    parabolaDisc p t₁ t₂ c η '' frontier (parabolaRegion c) ⊆
      tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
  rintro _ ⟨ζ, hζ, rfl⟩
  have h := frontier_parabolaRegion_subset hc hζ
  rw [mem_tubeDomain, rePi_parabolaDisc]
  exact triPt_mem_union_segment p t₁ t₂ h.1 h.2

/-- **Disc points lie in the hull of the disc boundary.** For any open base containing the
triangle, every point of the parabolic disc over the closed region lies in the holomorphic hull,
relative to the tube, of the image of the frontier of the region. -/
theorem parabolaDisc_mem_holomorphicHull [Fintype ι] {A : Set (ι → ℝ)}
    (hT : tri p t₁ t₂ 1 ⊆ A) {c : ℝ} (hc : 0 < c) (η : ι → ℝ) {ζ₀ : ℂ}
    (hζ₀ : ζ₀ ∈ closure (parabolaRegion c)) :
    parabolaDisc p t₁ t₂ c η ζ₀ ∈
      holomorphicHull (tubeDomain A) (parabolaDisc p t₁ t₂ c η '' frontier (parabolaRegion c)) := by
  refine ⟨tubeDomain_mono hT (parabolaDisc_mem_tubeDomain_tri p t₁ t₂ c η hζ₀), ?_⟩
  intro g hg M hM
  have hmaps : MapsTo (parabolaDisc p t₁ t₂ c η) (closure (parabolaRegion c)) (tubeDomain A) :=
    fun ζ hζ => tubeDomain_mono hT (parabolaDisc_mem_tubeDomain_tri p t₁ t₂ c η hζ)
  have hd : DiffContOnCl ℂ (g ∘ parabolaDisc p t₁ t₂ c η) (parabolaRegion c) := by
    apply DifferentiableOn.diffContOnCl
    exact hg.differentiableOn.comp (differentiable_parabolaDisc p t₁ t₂ c η).differentiableOn hmaps
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_parabolaRegion hc) hd
    (fun ζ hζ => hM _ (mem_image_of_mem _ hζ)) hζ₀

/-- Every point of the triangle with `|u| < v < 1` lies on a parabolic disc. -/
theorem exists_parabolaDisc_of_lt {u v : ℝ} (huv : |u| < v) (hv1 : v < 1) (η : ι → ℝ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (u : ℂ) ∈ parabolaRegion c ∧
      parabolaDisc p t₁ t₂ c η u = ofRealPi (triPt p t₁ t₂ u v) + I • ofRealPi η := by
  have hu1 : |u| < 1 := huv.trans hv1
  have hu2 : u ^ 2 < 1 := by
    rw [← sq_abs]
    exact pow_lt_one₀ (abs_nonneg _) hu1 two_ne_zero
  have hu2v : u ^ 2 < v := by
    calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
      _ ≤ |u| := by nlinarith [abs_nonneg u]
      _ < v := huv
  set c : ℝ := (1 - v) / (1 - u ^ 2) with hc
  have hden : 0 < 1 - u ^ 2 := by linarith
  have hc0 : 0 < c := div_pos (by linarith) hden
  have hc1 : c < 1 := by rw [hc, div_lt_one hden]; linarith
  have hheight : parabolaHeight c u = v := by
    unfold parabolaHeight
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [hc]
    field_simp
    ring
  refine ⟨c, hc0, hc1, ⟨?_, ?_⟩, ?_⟩
  · rw [hheight]; simpa using huv
  · rw [hheight]; exact hv1
  · have him : (c * (u : ℂ) ^ 2 + (1 - c) : ℂ).im = 0 := by simp [sq, Complex.mul_im]
    have := ofRealPi_rePi_add_I_smul_ofRealPi_imPi (parabolaDisc p t₁ t₂ c η u)
    rw [rePi_parabolaDisc, hheight, imPi_parabolaDisc, him] at this
    rw [← this]
    simp

end Disc

end SeveralComplexVariables.BochnerTube

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
