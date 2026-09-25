/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.CyclicPolygon

/-!
# Polygonal approximation from inside

For a planar convex body `K` with the origin in its interior and any `r > 1`, a sufficiently
fine *uniform* angle system produces an inscribed polygon `P` with

```
r⁻¹ • K ⊆ P ⊆ K.
```

The construction uses the uniform angles `θ j = j * (2π / M)`, so the cyclic order of the
vertices is immediate.  The inclusion `r⁻¹ • K ⊆ P` follows from two elementary facts:

* `r⁻¹ • K` is at distance at least `(1 - r⁻¹) * ρ` from the complement of `K`, where
  `ball 0 ρ ⊆ K`;
* a ray hitting a chord whose endpoints have radius at least `L` meets it at radius at least
  `L * cos (δ / 2)`, where `δ` is the angle subtended by the chord.
-/

@[expose] public section

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

/-- The uniform angle system with `M` directions. -/
def uniformAngles (M : ℕ) (hM : 5 ≤ M) : AngleSystem where
  m := M
  θ := fun j => (j : ℝ) * (2 * Real.pi / M)
  strictMono := by
    have hMpos : (0 : ℝ) < M := by
      have : (0 : ℕ) < M := by omega
      exact_mod_cast this
    intro j k hjk
    have : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
    have hpos : 0 < 2 * Real.pi / M := by positivity
    exact mul_lt_mul_of_pos_right this hpos
  period := by
    have hMpos : (0 : ℝ) < M := by
      have : (0 : ℕ) < M := by omega
      exact_mod_cast this
    intro j
    push_cast
    field_simp
  gap_lt := by
    have hMpos : (0 : ℝ) < M := by
      have : (0 : ℕ) < M := by omega
      exact_mod_cast this
    have hM5 : (5 : ℝ) ≤ M := by exact_mod_cast hM
    intro j
    have hpi := Real.pi_pos
    push_cast
    rw [show ((j : ℝ) + 1) * (2 * Real.pi / M) - (j : ℝ) * (2 * Real.pi / M)
        = 2 * Real.pi / M by ring]
    rw [div_lt_iff₀ hMpos]
    nlinarith

@[simp] theorem uniformAngles_m (M : ℕ) (hM : 5 ≤ M) : (uniformAngles M hM).m = M := rfl

@[simp] theorem uniformAngles_θ (M : ℕ) (hM : 5 ≤ M) (j : ℤ) :
    (uniformAngles M hM).θ j = (j : ℝ) * (2 * Real.pi / M) := rfl

/-- **Chord estimate.** A point of the plane whose direction lies in the angular sector
`[α, γ]` and whose norm is at most `L * cos ((γ - α)/2)` lies in the triangle spanned by the
origin and two points of radius at least `L` in the directions `α` and `γ`. -/
theorem mem_convexHull_triangle_of_norm_le {α γ t : ℝ} (hαt : α ≤ t) (htγ : t ≤ γ)
    (hlt : γ - α < Real.pi) {a b L s : ℝ} (hL : 0 < L) (ha : L ≤ a) (hb : L ≤ b)
    (hs : 0 ≤ s) (hsle : s ≤ L * Real.cos ((γ - α) / 2)) :
    s • circleVec t ∈ convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2) := by
  have hapos : 0 < a := lt_of_lt_of_le hL ha
  have hbpos : 0 < b := lt_of_lt_of_le hL hb
  have hmem0 : (0 : Point2) ∈ convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2) :=
    subset_convexHull _ _ (by simp)
  have hmemX : a • circleVec α
      ∈ convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2) :=
    subset_convexHull _ _ (by simp)
  have hmemY : b • circleVec γ
      ∈ convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2) :=
    subset_convexHull _ _ (by simp)
  have hconv := convex_convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2)
  rcases eq_or_lt_of_le (le_trans hαt htγ) with heq | hαγ
  · -- degenerate sector
    have ht : t = α := le_antisymm (by rw [heq]; exact htγ) hαt
    have hsL : s ≤ L := by
      have : (γ - α) / 2 = 0 := by rw [← heq]; ring
      rw [this, Real.cos_zero, mul_one] at hsle
      exact hsle
    have hsa : s / a ≤ 1 := by
      rw [div_le_one hapos]
      linarith
    have hpt : s • circleVec t = (s / a) • (a • circleVec α) + (1 - s / a) • (0 : Point2) := by
      rw [ht, smul_zero, add_zero, smul_smul, div_mul_cancel₀ _ hapos.ne']
    rw [hpt]
    exact hconv hmemX hmem0 (by positivity) (by linarith) (by ring)
  · -- nondegenerate sector
    have hδ : 0 < γ - α := by linarith
    have hsγα : 0 < Real.sin (γ - α) := Real.sin_pos_of_pos_of_lt_pi hδ hlt
    have hcos : 0 < Real.cos ((γ - α) / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> [linarith [Real.pi_pos]; linarith]
    set c1 : ℝ := s * Real.sin (γ - t) / (a * Real.sin (γ - α)) with hc1
    set c2 : ℝ := s * Real.sin (t - α) / (b * Real.sin (γ - α)) with hc2
    have hs1 : 0 ≤ Real.sin (γ - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hs2 : 0 ≤ Real.sin (t - α) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hc1nn : 0 ≤ c1 := by rw [hc1]; positivity
    have hc2nn : 0 ≤ c2 := by rw [hc2]; positivity
    -- the coefficients sum to at most one
    have hsum : c1 + c2 ≤ 1 := by
      have hsin_sum : Real.sin (γ - t) + Real.sin (t - α)
          = 2 * Real.sin ((γ - α) / 2) * Real.cos ((γ + α - 2 * t) / 2) := by
        rw [Real.sin_add_sin]
        congr 2 <;> ring_nf
      have hsin_gap : Real.sin (γ - α) = 2 * Real.sin ((γ - α) / 2) * Real.cos ((γ - α) / 2) := by
        rw [show γ - α = 2 * ((γ - α) / 2) by ring, Real.sin_two_mul]
        ring_nf
      have hhalfpos : 0 < Real.sin ((γ - α) / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hcosle : Real.cos ((γ + α - 2 * t) / 2) ≤ 1 := Real.cos_le_one _
      have hbound : c1 + c2 ≤ s * (Real.sin (γ - t) + Real.sin (t - α)) / (L * Real.sin (γ - α))
        := by
        rw [hc1, hc2]
        have e1 : s * Real.sin (γ - t) / (a * Real.sin (γ - α))
            ≤ s * Real.sin (γ - t) / (L * Real.sin (γ - α)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right ha hsγα.le
        have e2 : s * Real.sin (t - α) / (b * Real.sin (γ - α))
            ≤ s * Real.sin (t - α) / (L * Real.sin (γ - α)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hb hsγα.le
        have : s * (Real.sin (γ - t) + Real.sin (t - α)) / (L * Real.sin (γ - α))
            = s * Real.sin (γ - t) / (L * Real.sin (γ - α))
              + s * Real.sin (t - α) / (L * Real.sin (γ - α)) := by
          field_simp
        rw [this]
        linarith
      have hnum : s * (Real.sin (γ - t) + Real.sin (t - α))
          ≤ s * (2 * Real.sin ((γ - α) / 2)) := by
        rw [hsin_sum]
        have h1 : 2 * Real.sin ((γ - α) / 2) * Real.cos ((γ + α - 2 * t) / 2)
            ≤ 2 * Real.sin ((γ - α) / 2) := by
          nlinarith [hhalfpos, hcosle]
        exact mul_le_mul_of_nonneg_left h1 hs
      have hfinal : s * (2 * Real.sin ((γ - α) / 2)) / (L * Real.sin (γ - α)) ≤ 1 := by
        rw [hsin_gap, div_le_one (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hsle
          (by positivity : (0:ℝ) ≤ 2 * Real.sin ((γ - α) / 2))]
      have hstep : s * (Real.sin (γ - t) + Real.sin (t - α)) / (L * Real.sin (γ - α))
          ≤ s * (2 * Real.sin ((γ - α) / 2)) / (L * Real.sin (γ - α)) := by
        apply div_le_div_of_nonneg_right hnum (by positivity) |>.trans_eq rfl
      linarith
    -- the point is the corresponding combination
    have hpt : s • circleVec t = c1 • (a • circleVec α) + c2 • (b • circleVec γ) := by
      rw [smul_smul, smul_smul]
      have e1 : c1 * a = s * Real.sin (γ - t) / Real.sin (γ - α) := by
        rw [hc1]; field_simp
      have e2 : c2 * b = s * Real.sin (t - α) / Real.sin (γ - α) := by
        rw [hc2]; field_simp
      rw [e1, e2]
      have hcone := circleVec_cone_identity α t γ
      have : (s / Real.sin (γ - α)) • (Real.sin (γ - t) • circleVec α
          + Real.sin (t - α) • circleVec γ)
          = (s / Real.sin (γ - α)) • (Real.sin (γ - α) • circleVec t) := by
        rw [hcone]
      rw [smul_add, smul_smul, smul_smul, smul_smul] at this
      rw [show s * Real.sin (γ - t) / Real.sin (γ - α)
          = s / Real.sin (γ - α) * Real.sin (γ - t) by ring,
        show s * Real.sin (t - α) / Real.sin (γ - α)
          = s / Real.sin (γ - α) * Real.sin (t - α) by ring]
      rw [this, div_mul_cancel₀ _ hsγα.ne']
    rw [hpt]
    have hgen : ∀ (c d : ℝ) (X Y : Point2), 0 < c + d →
        (c + d) • ((c / (c + d)) • X + (d / (c + d)) • Y) + (1 - (c + d)) • (0 : Point2)
          = c • X + d • Y := by
      intro c d X Y h
      rw [smul_zero, add_zero, smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne']
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ c1 + c2) with hzero | hpos
    · have hc10 : c1 = 0 := by linarith
      have hc20 : c2 = 0 := by linarith
      rw [hc10, hc20, zero_smul, zero_smul, add_zero]
      exact hmem0
    · have hZ : (c1 / (c1 + c2)) • (a • circleVec α) + (c2 / (c1 + c2)) • (b • circleVec γ)
          ∈ convexHull ℝ ({0, a • circleVec α, b • circleVec γ} : Set Point2) := by
        refine hconv hmemX hmemY (by positivity) (by positivity) ?_
        field_simp
      have hcomb := hconv hZ hmem0 hpos.le (by linarith)
        (by ring : (c1 + c2) + (1 - (c1 + c2)) = 1)
      rw [hgen c1 c2 (a • circleVec α) (b • circleVec γ) hpos] at hcomb
      exact hcomb

/-- Inner and outer radii of a convex body with the origin in its interior. -/
theorem exists_inner_outer_radius (K : Body) (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ Metric.ball (0 : Point2) ρ ⊆ (K : Set Point2) ∧
      (K : Set Point2) ⊆ Metric.closedBall (0 : Point2) R := by
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  obtain ⟨R0, hR0⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point2)
  refine ⟨ρ0, max R0 1, hρ0, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun x hx => interior_subset (hball hx), fun x hx => ?_⟩
  exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR0 hx)

/-- A shrunken copy of `K` stays inside `K` together with a uniform ball. -/
theorem add_ball_subset_of_smul {K : Body} {ρ : ℝ}
    (hball : Metric.ball (0 : Point2) ρ ⊆ (K : Set Point2))
    {r : ℝ} (hr : 1 < r) {x : Point2} (hx : x ∈ r⁻¹ • (K : Set Point2))
    {y : Point2} (hy : ‖y - x‖ < (1 - r⁻¹) * ρ) : y ∈ (K : Set Point2) := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrinv0 : (0 : ℝ) < r⁻¹ := by positivity
  have hrinv1 : r⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right; exact hr
  set c : ℝ := 1 - r⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set w : Point2 := c⁻¹ • (y - r⁻¹ • z) with hw
  have hwball : w ∈ Metric.ball (0 : Point2) ρ := by
    rw [Metric.mem_ball, dist_zero_right, hw, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ c⁻¹)]
    rw [inv_mul_eq_div, div_lt_iff₀ hcpos]
    calc ‖y - r⁻¹ • z‖ < c * ρ := hy
      _ = ρ * c := by ring
  have hyeq : y = r⁻¹ • z + c • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
    abel
  rw [hyeq]
  exact K.convex hz (hball hwball) hrinv0.le hcpos.le (by rw [hc]; ring)

/-- **Inscribed polygonal approximation.** -/
theorem exists_polygon_sandwich (K : Body) (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {r : ℝ} (hr : 1 < r) :
    ∃ A : AngleSystem, r⁻¹ • (K : Set Point2) ⊆ polySet K A := by
  have hpi := Real.pi_pos
  obtain ⟨ρ, R, hρ, hR, hball, hbdd⟩ := exists_inner_outer_radius K h0
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrinv0 : (0 : ℝ) < r⁻¹ := by positivity
  have hrinv1 : r⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact hr
  set η : ℝ := (1 - r⁻¹) * ρ with hη
  have h1r : 0 < 1 - r⁻¹ := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  set c0 : ℝ := R / (R + η / 2) with hc0
  have hc0lt : c0 < 1 := by
    rw [hc0, div_lt_one (by linarith)]
    linarith
  set δ0 : ℝ := Real.sqrt (2 * (1 - c0)) with hδ0
  have hδ0pos : 0 < δ0 := Real.sqrt_pos.2 (by linarith)
  have hδ0cos : ∀ y : ℝ, |y| < δ0 → c0 < Real.cos y := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [Real.cos_zero]; linarith
    · have hsq : y ^ 2 < 2 * (1 - c0) := by
        have h1 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        have h2 : |y| ^ 2 < δ0 ^ 2 := by
          nlinarith [abs_nonneg y]
        rw [h1]
        calc |y| ^ 2 < δ0 ^ 2 := h2
          _ = 2 * (1 - c0) := Real.sq_sqrt (by linarith)
      have := Real.one_sub_sq_div_two_lt_cos hy0
      linarith
  -- choose the number of directions
  set ε0 : ℝ := min (η / (2 * R)) δ0 with hε0
  have hε0pos : 0 < ε0 := lt_min (by positivity) hδ0pos
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.pi / ε0)
  set M : ℕ := max 5 n with hM
  have hM5 : 5 ≤ M := le_max_left _ _
  have hMn : (n : ℝ) ≤ M := by exact_mod_cast le_max_right 5 n
  have hMpos : (0 : ℝ) < M := by
    have : (0 : ℕ) < M := by omega
    exact_mod_cast this
  have hδsmall : 2 * Real.pi / M < ε0 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε0pos] at hn
    nlinarith
  refine ⟨uniformAngles M hM5, ?_⟩
  set A := uniformAngles M hM5 with hA
  have hgapval : ∀ j : ℤ, A.θ (j + 1) - A.θ j = 2 * Real.pi / M := by
    intro j
    simp only [hA, uniformAngles]
    push_cast
    ring
  intro x hx
  rcases eq_or_ne x 0 with rfl | hxne
  · exact zero_mem_polySet
  have hxR : ‖x‖ ≤ R := by
    obtain ⟨z, hz, rfl⟩ := hx
    have hzR : ‖z‖ ≤ R := by
      have := hbdd hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrinv0.le]
    nlinarith [norm_nonneg z]
  obtain ⟨t, -, hxt⟩ := exists_angle x 0
  obtain ⟨j, hj1, hj2⟩ := A.exists_index t
  -- both neighbouring rays reach beyond `‖x‖ + η/2`
  have hkey : ∀ i : ℤ, |A.θ i - t| ≤ 2 * Real.pi / M → ‖x‖ + η / 2 ≤ rad K (A.θ i) := by
    intro i hi
    have hmem : (‖x‖ + η / 2) • circleVec (A.θ i) ∈ (K : Set Point2) := by
      refine add_ball_subset_of_smul hball hr hx ?_
      have hsplit : (‖x‖ + η / 2) • circleVec (A.θ i) - x
          = (η / 2) • circleVec (A.θ i) + ‖x‖ • (circleVec (A.θ i) - circleVec t) := by
        nth_rewrite 2 [hxt]
        module
      rw [hsplit]
      have hb1 : ‖(η / 2) • circleVec (A.θ i)‖ = η / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ η / 2),
          norm_circleVec, mul_one]
      have hb2 : ‖‖x‖ • (circleVec (A.θ i) - circleVec t)‖ ≤ R * (2 * Real.pi / M) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
        have h1 : ‖circleVec (A.θ i) - circleVec t‖ ≤ 2 * Real.pi / M :=
          le_trans (norm_circleVec_sub_le _ _) hi
        have h2 : (0:ℝ) ≤ 2 * Real.pi / M := by positivity
        nlinarith [norm_nonneg x]
      have hsmall : R * (2 * Real.pi / M) < η / 2 := by
        have hle : 2 * Real.pi / M < η / (2 * R) := lt_of_lt_of_le hδsmall (min_le_left _ _)
        rw [lt_div_iff₀ (by positivity)] at hle
        nlinarith
      calc ‖(η / 2) • circleVec (A.θ i) + ‖x‖ • (circleVec (A.θ i) - circleVec t)‖
          ≤ ‖(η / 2) • circleVec (A.θ i)‖ + ‖‖x‖ • (circleVec (A.θ i) - circleVec t)‖ :=
            norm_add_le _ _
        _ ≤ η / 2 + R * (2 * Real.pi / M) := by rw [hb1]; linarith
        _ < η := by rw [hη] at hηpos ⊢; linarith
    exact le_rad (by positivity) hmem
  have hgap := hgapval j
  have ha := hkey j (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hb := hkey (j + 1) (by rw [abs_of_nonneg (by linarith)]; linarith)
  -- the sector estimate
  have hLpos : 0 < ‖x‖ + η / 2 := by positivity
  have hcos : c0 < Real.cos ((A.θ (j + 1) - A.θ j) / 2) := by
    apply hδ0cos
    rw [hgap, abs_of_nonneg (by positivity)]
    have : 2 * Real.pi / M < δ0 := lt_of_lt_of_le hδsmall (min_le_right _ _)
    linarith
  have hratio : ‖x‖ / (‖x‖ + η / 2) ≤ c0 := by
    rw [hc0, div_le_div_iff₀ hLpos (by linarith)]
    nlinarith [norm_nonneg x]
  have hsle : ‖x‖ ≤ (‖x‖ + η / 2) * Real.cos ((A.θ (j + 1) - A.θ j) / 2) := by
    have h1 : ‖x‖ / (‖x‖ + η / 2) < Real.cos ((A.θ (j + 1) - A.θ j) / 2) := by
      linarith
    rw [div_lt_iff₀ hLpos] at h1
    linarith
  have hmem := mem_convexHull_triangle_of_norm_le (α := A.θ j) (γ := A.θ (j + 1)) (t := t)
    hj1 hj2.le (by linarith [A.gap_lt j]) hLpos ha hb (norm_nonneg x) hsle
  rw [← hxt] at hmem
  refine convexHull_min ?_ convex_polySet hmem
  rintro y (rfl | rfl | rfl)
  · exact zero_mem_polySet
  · exact vtx_mem_polySet j
  · exact vtx_mem_polySet (j + 1)

end HumanVerification.CauchyCrofton
