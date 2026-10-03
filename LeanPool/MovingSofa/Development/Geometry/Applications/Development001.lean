/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development006

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development007

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development005





public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development004

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001




/-!
# Moving sofa: related mathematical developments

* `Area.Applications.Development001`.
* `Area.Applications.Development002`.
* `Area.Applications.Development003`.
* `Cap.Applications.Development001`.
* `Gerver.Applications.Development001`.
* `Gerver.Applications.Development002`.
* `Polygon.Applications.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Middle`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-! # The middle part of the niche

`capMiddle_area_lower_bound` bounds the area of the part of a special cap's niche outside both
distinguished tail half-planes from below by the three signed areas of the middle fan: the two
wedge triangles and the inner-corner arc.

The geometry is that of the paper's proof.  Writing `φ` for the right distinguished angle,
`l = π/2 - φ` for the left one and `k = tan φ`, the two distinguished tail support lines are
`X = w - k y` and `X = z + k y`, where `w` and `z` are the horizontal coordinates of the two fan
points `W` and `Z`; the inner corner runs from the first line to the second through the open cone
between them, with strictly decreasing horizontal coordinate.  Adding a base line `y = -h` strictly
below the arc turns the arc together with the two side segments into a strictly monotone
three-piece roof over that base line, and the region under the roof exceeds the base trapezoid by
the asserted three signed areas.  Every point of the open region above the trapezoid lies in the
niche, because the roof point vertically above it exhibits a time whose open inward quadrant
contains it.
-/

public section

noncomputable section

namespace MovingSofa

/-- The middle area bound obtained from cap area, endpoint segments and the corner-path
integral. -/
@[expose]
def upperBoundMiddle (K : SpecialCapSpace) : ℝ :=
  ClassicalResults.area (K.val.val : Set Point) +
    segmentArea (distinguishedCapSides K.val).2.fanPoint
      (distinguishedCapSides K.val).2.corner -
    curveAreaFunctional (capMiddleBV K) +
    segmentArea (distinguishedCapSides K.val).1.corner
      (distinguishedCapSides K.val).1.fanPoint

/-! ### Arithmetic of a side segment of the middle cone

The two side segments of the four-piece loop run along the two tail support lines, so their
displacements `(Δ₀, Δ₁)` satisfy `Δ₀ cos = Δ₁ sin` for the relevant frame angle.  The two lemmas
below are the resulting sign computations for a point `δ` below such a segment. -/

/-- On a segment parallel to the frame tangent, the frame's normal coordinate of a point below the
segment is the vertical drop only. -/
private theorem segment_cross_eq {cs sn Δ0 Δ1 u δ : ℝ} (hΔ : Δ0 * cs = Δ1 * sn) :
    u * Δ0 * cs + (-(u * Δ1) - δ) * sn = -(δ * sn) := by linear_combination u * hΔ

/-- On a segment parallel to the frame tangent, the frame's tangent coordinate of a point below the
segment is negative. -/
private theorem segment_normal_neg {cs sn Δ0 Δ1 u δ : ℝ} (hcs : 0 < cs)
    (hpy : sn ^ 2 + cs ^ 2 = 1) (hΔ : Δ0 * cs = Δ1 * sn) (hΔ1 : 0 < Δ1)
    (hu0 : 0 ≤ u) (hδ : 0 < δ) :
    -(u * Δ0) * sn + (-(u * Δ1) - δ) * cs < 0 := by
  have key : (-(u * Δ0) * sn + (-(u * Δ1) - δ) * cs) * cs = -(u * Δ1) - δ * cs ^ 2 := by
    linear_combination (-(u * sn)) * hΔ + (-(u * Δ1)) * hpy
  have hneg : (-(u * Δ0) * sn + (-(u * Δ1) - δ) * cs) * cs < 0 * cs := by
    rw [key, zero_mul]
    have h1 : 0 ≤ u * Δ1 := mul_nonneg hu0 hΔ1.le
    have h2 : 0 < δ * cs ^ 2 := mul_pos hδ (pow_pos hcs 2)
    linarith
  exact lt_of_mul_lt_mul_right hneg hcs.le

/-! ### The cone between the two distinguished tail support lines -/

/-- Both distinguished fan points lie on the horizontal axis, at the horizontal intercepts of the
two distinguished tail support lines. -/
private theorem distinguishedCapSides_fanPoint_coordinates (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).1.fanPoint 0 =
        (supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 ∧
      (distinguishedCapSides K.val).1.fanPoint 1 = 0 ∧
      (distinguishedCapSides K.val).2.fanPoint 0 =
        -((supportValue (K.val.val : Set Point)
              ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1) ∧
      (distinguishedCapSides K.val).2.fanPoint 1 = 0 := by
  obtain ⟨-, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hsinl : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  obtain ⟨hW0, hW1⟩ := wedgeEndpoints_fst_coords K.val paperGerverConstants.2.1
  obtain ⟨hZ0, hZ1⟩ := wedgeEndpoints_snd_coords K.val paperGerverConstants.2.2
  rw [hsinl] at hZ0
  rw [distinguishedCapSides_fst_fanPoint, distinguishedCapSides_snd_fanPoint]
  exact ⟨hW0, hW1, hZ0, hZ1⟩

/-- The left fan point lies strictly to the left of the right one: otherwise the right fan point
would lie in the cap and in both tail half-planes, which the separation lemma forbids. -/
private theorem distinguishedCapSides_fanPoint_fst_lt (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).2.fanPoint 0 < (distinguishedCapSides K.val).1.fanPoint 0 := by
  obtain ⟨hrIoo, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨hW0, hW1, hZ0, -⟩ := distinguishedCapSides_fanPoint_coordinates K
  have hcosr : 0 < Real.cos paperGerverConstants.2.1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinl : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  have hcosladd : Real.cos (paperGerverConstants.2.2 + Real.pi / 2) =
      -Real.cos paperGerverConstants.2.1 := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsr1 : supportValue (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle) - 1 =
      (distinguishedCapSides K.val).1.fanPoint 0 * Real.cos paperGerverConstants.2.1 := by
    rw [hW0]
    field_simp
  have hsl1 : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -((distinguishedCapSides K.val).2.fanPoint 0 * Real.cos paperGerverConstants.2.1) := by
    rw [hZ0]
    field_simp
  by_contra hcon
  rw [not_lt] at hcon
  have hmul := mul_le_mul_of_nonneg_right hcon hcosr.le
  have h1 : (distinguishedCapSides K.val).1.fanPoint ∈
      (distinguishedCapSides K.val).1.upperHalfPlane := by
    change _ ≤ inner ℝ _ (normalVector (paperGerverConstants.2.1 : Real.Angle))
    rw [inner_normalVector_real, hW1, hsr1]
    simp
  have h2 : (distinguishedCapSides K.val).1.fanPoint ∈
      (distinguishedCapSides K.val).2.upperHalfPlane := by
    change _ ≤ inner ℝ _
      (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle))
    rw [inner_normalVector_real, hW1, hcosladd, hsl1]
    linarith only [hmul]
  exact Set.eq_empty_iff_forall_notMem.mp (cap_and_niche_tail_separation K).1 _
    ⟨⟨(specialCap_wedgeEndpoints_in_bottomEdge K).1.1.1, h1⟩, h2⟩

/-- The inner corner traverses the closed cone between the two distinguished tail support lines
`X = w - k y` and `X = z + k y` on the middle interval, with its two endpoints on the two lines.
Here `k = tan φ` is encoded by `hk`, and `w`, `z` by the two intercept equations. -/
private theorem capInnerCorner_mem_cone (K : SpecialCapSpace) {k w z : ℝ}
    (hk : k * Real.cos paperGerverConstants.2.1 = Real.sin paperGerverConstants.2.1)
    (hw : supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1 =
      w * Real.cos paperGerverConstants.2.1)
    (hz : supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(z * Real.cos paperGerverConstants.2.1)) :
    capInnerCorner K.val paperGerverConstants.2.1 0 +
        k * capInnerCorner K.val paperGerverConstants.2.1 1 = w ∧
      capInnerCorner K.val paperGerverConstants.2.2 0 -
        k * capInnerCorner K.val paperGerverConstants.2.2 1 = z ∧
      (∀ t ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        capInnerCorner K.val t 0 + k * capInnerCorner K.val t 1 ≤ w) ∧
      (∀ t ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        z ≤ capInnerCorner K.val t 0 - k * capInnerCorner K.val t 1) := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinl : Real.sin l = Real.cos r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.sin_pi_div_two_sub]
  have hcosl : Real.cos l = Real.sin r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.cos_pi_div_two_sub]
  have hcosladd : Real.cos (l + Real.pi / 2) = -Real.cos r := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsinladd : Real.sin (l + Real.pi / 2) = Real.sin r := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcosl]
    ring
  -- the right endpoint is on the right line, the left endpoint on the left line
  have hXR : xc r 0 + k * xc r 1 = w := by
    have h := inner_capInnerCorner_normalVector K.val r
    rw [inner_normalVector_real, hw] at h
    refine mul_right_cancel₀ (ne_of_gt hcosr) ?_
    linear_combination h + xc r 1 * hk
  have hXL : xc l 0 - k * xc l 1 = z := by
    have h := inner_capInnerCorner_tangentVector K.val l
    rw [inner_tangentVector_real, hsinl, hcosl, hz] at h
    refine mul_right_cancel₀ (ne_of_gt hcosr) ?_
    linear_combination -h - xc l 1 * hk
  -- strictly inside the cone away from the two endpoints, by the monotonicity intervals
  obtain ⟨hmonoR, hmonoL, -, -⟩ := cap_tail_monotonicity_intervals K
  have hnotR : ∀ t ∈ Set.Ioc r (Real.pi / 2), xc t 0 + k * xc t 1 < w := by
    intro t ht
    have h : ¬ (supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 ≤
        inner ℝ (xc t) (normalVector (r : Real.Angle))) :=
      fun hc ↦ (hmonoR t ht).1 hc
    rw [not_le, inner_normalVector_real, hw] at h
    refine lt_of_mul_lt_mul_right ?_ hcosr.le
    have he : (xc t 0 + k * xc t 1) * Real.cos r =
        xc t 0 * Real.cos r + xc t 1 * Real.sin r := by
      linear_combination xc t 1 * hk
    rw [he]
    exact h
  have hnotL : ∀ t ∈ Set.Ico (0 : ℝ) l, z < xc t 0 - k * xc t 1 := by
    intro t ht
    have h : ¬ (supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ (xc t) (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle))) :=
      fun hc ↦ (hmonoL t ht).1 hc
    rw [not_le, inner_normalVector_real, hcosladd, hsinladd, hz] at h
    refine lt_of_mul_lt_mul_right ?_ hcosr.le
    have he2 : (xc t 0 - k * xc t 1) * Real.cos r =
        xc t 0 * Real.cos r - xc t 1 * Real.sin r := by
      linear_combination -(xc t 1) * hk
    rw [he2]
    linarith only [h]
  refine ⟨hXR, hXL, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · rcases eq_or_lt_of_le ht.1 with heq | hlt
    · rw [← heq, hXR]
    · exact (hnotR t ⟨hlt, le_trans ht.2 hlIoo.2.le⟩).le
  · rcases eq_or_lt_of_le ht.2 with heq | hlt
    · rw [heq, hXL]
    · exact (hnotL t ⟨le_trans hrIoo.1.le ht.1, hlt⟩).le

/-- A horizontal line strictly below the inner corner on a compact subinterval of `[0, π/2]`. -/
private theorem exists_lt_capInnerCorner_snd (K : SpecialCapSpace) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    ∃ h : ℝ, 0 < h ∧ ∀ t ∈ Set.Icc a b, -h < capInnerCorner K.val t 1 := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hcont : ContinuousOn (fun t ↦ capInnerCorner K.val t 1) (Set.Icc a b) :=
    (PiLp.continuous_apply 2 _ 1).comp_continuousOn (K.property.1.2.1.continuousOn.mono hsub)
  obtain ⟨t0, -, hmin⟩ := isCompact_Icc.exists_isMinOn (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty)
    hcont
  refine ⟨|capInnerCorner K.val t0 1| + 1, by positivity, fun t ht ↦ ?_⟩
  have hle : capInnerCorner K.val t0 1 ≤ capInnerCorner K.val t 1 := hmin ht
  linarith only [hle, neg_abs_le (capInnerCorner K.val t0 1)]

/-- The area of the trapezoid cut from the strip `-h ≤ y ≤ 0` by two lines of opposite slope
meeting the horizontal axis at `z` and `w`. -/
private theorem volume_slantedTrapezoid {z w k h : ℝ} (hk : 0 ≤ k) (hzw : z ≤ w) (hh : 0 ≤ h) :
    MeasureTheory.volume {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} =
      ENNReal.ofReal (h * (w - z) + k * h ^ 2) := by
  have hkh : 0 ≤ k * h := mul_nonneg hk hh
  rw [show {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} =
      {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧
        p 0 ∈ Set.Icc (z + k * p 1) (w + -k * p 1)} from by
      refine Set.ext fun p ↦ ?_
      simp only [Set.mem_ofPred_eq, show w + -k * p 1 = w - k * p 1 from by ring],
    EuclideanSpace.volume_horizontalTrapezoid_band (by linarith) (by linarith) (by linarith)]
  congr 1
  ring

/-! ### The niche contains the open region above the base trapezoid -/

/-- Every point strictly below the three-piece roof made of the inner-corner arc and the two side
segments, and outside the base trapezoid, lies in the niche outside both distinguished tail
half-planes.  The roof point vertically above such a point exhibits a time of the closed middle
interval whose open inward quadrant contains it, and the strict cone bounds plus the point's
positive height put it in the fan and outside the two half-planes. -/
private theorem region_under_roof_diff_subset (K : SpecialCapSpace) {k w z h : ℝ} (hk0 : 0 < k)
    (hk : k * Real.cos paperGerverConstants.2.1 = Real.sin paperGerverConstants.2.1)
    (hw : supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) - 1 =
      w * Real.cos paperGerverConstants.2.1)
    (hz : supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(z * Real.cos paperGerverConstants.2.1))
    (P Q : Point) (γ : ContinuousBVPaths 0 3) (hP1 : P 1 = -h) (hQ1 : Q 1 = -h)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 →
      γ.val s = P + (s : ℝ) • (capInnerCorner K.val paperGerverConstants.2.2 - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = capInnerCorner K.val (paperGerverConstants.2.2 +
        ((s : ℝ) - 1) * (paperGerverConstants.2.1 - paperGerverConstants.2.2)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) →
      γ.val s = capInnerCorner K.val paperGerverConstants.2.1 +
        ((s : ℝ) - 2) • (Q - capInnerCorner K.val paperGerverConstants.2.1))
    (hconeR : ∀ s : Set.Icc (0 : ℝ) 3, γ.val s 0 + k * γ.val s 1 ≤ w)
    (hconeL : ∀ s : Set.Icc (0 : ℝ) 3, z ≤ γ.val s 0 - k * γ.val s 1)
    (hPpar : (capInnerCorner K.val paperGerverConstants.2.2 0 - P 0) *
        Real.cos paperGerverConstants.2.1 =
      (capInnerCorner K.val paperGerverConstants.2.2 1 - P 1) *
        Real.sin paperGerverConstants.2.1)
    (hQpar : (Q 0 - capInnerCorner K.val paperGerverConstants.2.1 0) *
        Real.cos paperGerverConstants.2.1 =
      (capInnerCorner K.val paperGerverConstants.2.1 1 - Q 1) *
        Real.sin paperGerverConstants.2.1) :
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1} \
        {p : Point | p 1 ∈ Set.Icc (-h) 0 ∧ p 0 ∈ Set.Icc (z + k * p 1) (w - k * p 1)} ⊆
      (capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  have hrl : r < l := paperGerverConstants_snd_fst_lt_snd_snd
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinr : 0 < Real.sin r :=
    Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [Real.pi_pos, hrIoo.2])
  have hpy : Real.sin r ^ 2 + Real.cos r ^ 2 = 1 := Real.sin_sq_add_cos_sq r
  have hsinl : Real.sin l = Real.cos r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.sin_pi_div_two_sub]
  have hcosl : Real.cos l = Real.sin r := by
    rw [show l = Real.pi / 2 - r by linarith, Real.cos_pi_div_two_sub]
  have hcosladd : Real.cos (l + Real.pi / 2) = -Real.cos r := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hsinl]
    ring
  have hsinladd : Real.sin (l + Real.pi / 2) = Real.sin r := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, hcosl]
    ring
  have hcoord : ∀ (p q : Point) (c : ℝ) (i : Fin 2),
      (p + c • (q - p)) i = p i + c * (q i - p i) := fun _ _ _ _ ↦ by simp
  rintro p ⟨hpP, hpR⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := hpP
  obtain ⟨δ, hδ0, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧ p 1 = γ.val s 1 - δ :=
    ⟨γ.val s 1 - p 1, by linarith only [hs2], by ring⟩
  have hkp : k * p 1 < k * γ.val s 1 := mul_lt_mul_of_pos_left hs2 hk0
  -- the point is strictly inside the open cone
  have hstrictR : p 0 + k * p 1 < w := by
    have h := hconeR s
    rw [hs0]
    linarith only [h, hkp]
  have hstrictL : z < p 0 - k * p 1 := by
    have h := hconeL s
    rw [hs0]
    linarith only [h, hkp]
  -- being outside the trapezoid, its height is positive
  have hp1pos : 0 < p 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hpR ⟨⟨hs1.le, hcon⟩, ⟨by linarith only [hstrictL], by linarith only [hstrictR]⟩⟩
  have hnotHR : p ∉ (distinguishedCapSides K.val).1.upperHalfPlane := by
    intro hc
    replace hc : supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 ≤
      inner ℝ p (normalVector (r : Real.Angle)) := hc
    rw [inner_normalVector_real, hw] at hc
    have hm : (p 0 + k * p 1) * Real.cos r < w * Real.cos r :=
      mul_lt_mul_of_pos_right hstrictR hcosr
    have he : (p 0 + k * p 1) * Real.cos r = p 0 * Real.cos r + p 1 * Real.sin r := by
      linear_combination p 1 * hk
    rw [he] at hm
    linarith only [hc, hm]
  have hnotHL : p ∉ (distinguishedCapSides K.val).2.upperHalfPlane := by
    intro hc
    replace hc : supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle)) := hc
    rw [inner_normalVector_real, hcosladd, hsinladd, hz] at hc
    have hm : z * Real.cos r < (p 0 - k * p 1) * Real.cos r :=
      mul_lt_mul_of_pos_right hstrictL hcosr
    have he : (p 0 - k * p 1) * Real.cos r = p 0 * Real.cos r - p 1 * Real.sin r := by
      linear_combination -(p 1) * hk
    rw [he] at hm
    linarith only [hc, hm]
  have hfan : p ∈ capFan (Real.pi / 2) := by
    refine ⟨?_, ?_⟩ <;>
      · change (0 : ℝ) ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        rw [inner_normalVector_pi_div_two]
        exact hp1pos.le
  -- the roof point above `p` provides the time whose inward quadrant contains `p`
  have hquad : ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      p ∈ innerQuadrant (K.val.val : Set Point) t := by
    rcases le_or_gt (s : ℝ) 1 with hc | hc
    · -- the left side segment, with witness time `l`
      have hγs1 : γ.val s 1 = P 1 + (s : ℝ) * (xc l 1 - P 1) := by
        rw [hγ0 s hc, hcoord]
      have hΔ1 : 0 < xc l 1 - P 1 := by
        nlinarith only [hγs1, hs1, hs2, hP1, s.property.1]
      have hΔ : (xc l 0 - P 0) * Real.sin l = (xc l 1 - P 1) * Real.cos l := by
        rw [hsinl, hcosl]
        exact hPpar
      have e0 : p 0 - xc l 0 = -((1 - (s : ℝ)) * (xc l 0 - P 0)) := by
        rw [hs0, hγ0 s hc, hcoord]
        ring
      have e1 : p 1 - xc l 1 = -((1 - (s : ℝ)) * (xc l 1 - P 1)) - δ := by
        rw [hδeq, hγ0 s hc, hcoord]
        ring
      refine ⟨l, ⟨hlIoo.1, hlIoo.2⟩, mem_innerQuadrant_of_frame_coordinates_neg K.val l p ?_ ?_⟩
      · rw [e0, e1]
        have hnn := segment_normal_neg (cs := Real.sin l) (sn := Real.cos l)
          (u := 1 - (s : ℝ)) (δ := δ) (by rw [hsinl]; exact hcosr)
          (by rw [hsinl, hcosl]; linarith only [hpy]) hΔ hΔ1 (by linarith only [hc]) hδ0
        linarith only [hnn]
      · rw [e0, e1]
        have hcr := segment_cross_eq (cs := Real.sin l) (sn := Real.cos l)
          (u := 1 - (s : ℝ)) (δ := δ) hΔ
        have hps : 0 < δ * Real.cos l := by
          rw [hcosl]
          exact mul_pos hδ0 hsinr
        linarith only [hcr, hps]
    · rcases le_or_gt (s : ℝ) 2 with hc2 | hc2
      · -- the middle arc, with witness time in `[r, l]`
        have htI := mem_Icc_roofArcTime hrl hc.le hc2
        set t : ℝ := l + ((s : ℝ) - 1) * (r - l) with htdef
        have hgs : γ.val s = xc t := hγ1 s hc.le hc2
        have e0 : p 0 - xc t 0 = 0 := by rw [hs0, hgs]; ring
        have e1 : p 1 - xc t 1 = -δ := by rw [hδeq, hgs]; ring
        have ht0 : 0 < t := lt_of_lt_of_le hrIoo.1 htI.1
        have htpi : t < Real.pi / 2 := lt_of_le_of_lt htI.2 hlIoo.2
        have hsint : 0 < Real.sin t :=
          Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith only [Real.pi_pos, htpi])
        have hcost : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, ht0], htpi⟩
        refine ⟨t, ⟨ht0, htpi⟩, mem_innerQuadrant_of_frame_coordinates_neg K.val t p ?_ ?_⟩
        · rw [e0, e1]
          have hps := mul_pos hδ0 hsint
          linarith only [hps]
        · rw [e0, e1]
          have hps := mul_pos hδ0 hcost
          linarith only [hps]
      · -- the right side segment, with witness time `r`
        have hγs1 : γ.val s 1 = xc r 1 + ((s : ℝ) - 2) * (Q 1 - xc r 1) := by
          rw [hγ2 s hc2.le, hcoord]
        have hΔ1 : 0 < xc r 1 - Q 1 := by
          nlinarith only [hγs1, hs1, hs2, hQ1, hc2, s.property.2]
        have e0 : p 0 - xc r 0 = ((s : ℝ) - 2) * (Q 0 - xc r 0) := by
          rw [hs0, hγ2 s hc2.le, hcoord]
          ring
        have e1 : p 1 - xc r 1 = -(((s : ℝ) - 2) * (xc r 1 - Q 1)) - δ := by
          rw [hδeq, hγ2 s hc2.le, hcoord]
          ring
        refine ⟨r, ⟨hrIoo.1, hrIoo.2⟩,
          mem_innerQuadrant_of_frame_coordinates_neg K.val r p ?_ ?_⟩
        · rw [e0, e1]
          have hcr := segment_cross_eq (cs := Real.cos r) (sn := Real.sin r)
            (u := (s : ℝ) - 2) (δ := δ) hQpar
          have hps := mul_pos hδ0 hsinr
          linarith only [hcr, hps]
        · rw [e0, e1]
          have hnn := segment_normal_neg (cs := Real.cos r) (sn := Real.sin r)
            (u := (s : ℝ) - 2) (δ := δ) hcosr hpy hQpar hΔ1 (by linarith only [hc2]) hδ0
          linarith only [hnn]
  obtain ⟨t, htmem, hq⟩ := hquad
  exact ⟨⟨⟨hfan, Set.mem_biUnion htmem hq⟩, hnotHR⟩, hnotHL⟩

/-! ### The lower estimate -/

theorem capMiddle_area_lower_bound (K : SpecialCapSpace) :
    segmentArea (distinguishedCapSides K.val).1.fanPoint
        (distinguishedCapSides K.val).1.corner +
      curveAreaFunctional (capMiddleBV K) +
      segmentArea (distinguishedCapSides K.val).2.corner
        (distinguishedCapSides K.val).2.fanPoint ≤
    ClassicalResults.area
      ((capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane) := by
  obtain ⟨hW0, hW1, hZ0, hZ1⟩ := distinguishedCapSides_fanPoint_coordinates K
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  set r : ℝ := paperGerverConstants.2.1 with hrdef
  set l : ℝ := paperGerverConstants.2.2 with hldef
  have hrl : r < l := paperGerverConstants_snd_fst_lt_snd_snd
  have hcosr : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrIoo.1], hrIoo.2⟩
  have hsinr : 0 < Real.sin r :=
    Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [Real.pi_pos, hrIoo.2])
  -- the cone's slope `k = tan φ` and the horizontal intercepts `w`, `z` of its two lines
  set kk : ℝ := Real.sin r / Real.cos r with hkkdef
  have hkk0 : 0 < kk := div_pos hsinr hcosr
  have hkcos : kk * Real.cos r = Real.sin r := by
    rw [hkkdef]
    field_simp
  set xc : ℝ → Point := capInnerCorner K.val with hxcdef
  set W : Point := (distinguishedCapSides K.val).1.fanPoint with hWdef
  set Z : Point := (distinguishedCapSides K.val).2.fanPoint with hZdef
  have hsr1 : supportValue (K.val.val : Set Point) (r : Real.Angle) - 1 = W 0 * Real.cos r := by
    rw [hW0, div_mul_cancel₀ _ (ne_of_gt hcosr)]
  have hsl1 : supportValue (K.val.val : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 =
      -(Z 0 * Real.cos r) := by
    rw [hZ0, neg_mul, div_mul_cancel₀ _ (ne_of_gt hcosr), neg_neg]
  have hzw : Z 0 < W 0 := distinguishedCapSides_fanPoint_fst_lt K
  -- the arc runs through the closed cone from one boundary line to the other
  obtain ⟨hXR, hXL, harcR, harcL⟩ := capInnerCorner_mem_cone K hkcos hsr1 hsl1
  -- a base line `y = -hgt` strictly below the arc, and the two base corners on it
  obtain ⟨hgt, hgt0, hgtlow⟩ := exists_lt_capInnerCorner_snd K hrl.le hrIoo.1.le hlIoo.2.le
  have hkh : (0 : ℝ) ≤ kk * hgt := mul_nonneg hkk0.le hgt0.le
  set Bp : Point := !₂[W 0 + kk * hgt, -hgt] with hBpdef
  set Dp : Point := !₂[Z 0 - kk * hgt, -hgt] with hDpdef
  have hBp0 : Bp 0 = W 0 + kk * hgt := rfl
  have hBp1 : Bp 1 = -hgt := rfl
  have hDp0 : Dp 0 = Z 0 - kk * hgt := rfl
  have hDp1 : Dp 1 = -hgt := rfl
  -- the three-piece roof `Dp → x(l) → arc → x(r) → Bp`
  obtain ⟨γ, hγ0, hγ1, hγ2, hγmono⟩ :=
    exists_strictMono_roof_of_strictAntiOn hrl (capMiddleBV K) xc Dp Bp (fun _ _ ↦ rfl)
      (strictAntiOn_capInnerCorner_fst K hrIoo.1.le hlIoo.2.le)
      (by
        rw [hDp0]
        have h : 0 < kk * (xc l 1 + hgt) :=
          mul_pos hkk0 (by linarith only [hgtlow l ⟨hrl.le, le_rfl⟩])
        linarith only [hXL, h])
      (by
        rw [hBp0]
        have h : 0 < kk * (xc r 1 + hgt) :=
          mul_pos hkk0 (by linarith only [hgtlow r ⟨le_rfl, hrl.le⟩])
        linarith only [hXR, h])
  -- the roof stays in the closed cone above the base line
  have hγconeR : ∀ s : Set.Icc (0 : ℝ) 3, γ.val s 0 + kk * γ.val s 1 ≤ W 0 := fun s ↦ by
    have h := le_of_threePieceRoof (α := 1) (β := kk) (cc := W 0) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp0, hDp1]; linarith only [hzw, hkh])
      (by rw [hBp0, hBp1]; linarith only []) (fun t ht ↦ by linarith only [harcR t ht]) s
    linarith only [h]
  have hγconeL : ∀ s : Set.Icc (0 : ℝ) 3, Z 0 ≤ γ.val s 0 - kk * γ.val s 1 := fun s ↦ by
    have h := le_of_threePieceRoof (α := -1) (β := kk) (cc := -Z 0) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp0, hDp1]; linarith only [])
      (by rw [hBp0, hBp1]; linarith only [hzw, hkh])
      (fun t ht ↦ by linarith only [harcL t ht]) s
    linarith only [h]
  have hγlow : ∀ s : Set.Icc (0 : ℝ) 3, -hgt ≤ γ.val s 1 := fun s ↦ by
    have h := le_of_threePieceRoof (α := 0) (β := -1) (cc := hgt) hrl xc Dp Bp γ hγ0 hγ1 hγ2
      (by rw [hDp1]; linarith only []) (by rw [hBp1]; linarith only [])
      (fun t ht ↦ by linarith only [hgtlow t ht]) s
    linarith only [h]
  -- the closed region under the roof and the base trapezoid
  set Pu : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -hgt ≤ p 1 ∧ p 1 ≤ γ.val s 1}
    with hPudef
  set Rg : Set Point :=
    {p : Point | p 1 ∈ Set.Icc (-hgt) 0 ∧ p 0 ∈ Set.Icc (Z 0 + kk * p 1) (W 0 - kk * p 1)}
    with hRgdef
  have hRgarea : MeasureTheory.volume Rg =
      ENNReal.ofReal (hgt * (W 0 - Z 0) + kk * hgt ^ 2) :=
    volume_slantedTrapezoid hkk0.le hzw.le hgt0.le
  have hRgreal : ClassicalResults.area Rg = hgt * (W 0 - Z 0) + kk * hgt ^ 2 := by
    rw [ClassicalResults.area, hRgarea, ENNReal.toReal_ofReal]
    positivity
  -- the four-piece signed area of the loop bounding the region
  have hPuarea : ClassicalResults.area Pu =
      segmentArea Bp (xc r) + curveAreaFunctional (capMiddleBV K) +
        segmentArea (xc l) Dp + segmentArea Dp Bp :=
    area_region_under_strictMono_roof hrl (capMiddleBV K) xc Dp Bp γ (fun _ _ ↦ rfl) hDp1 hBp1
      hγ0 hγ1 hγ2 hγmono hγlow
  -- the strict region above the trapezoid lies in the niche outside both half-planes
  have hincl := region_under_roof_diff_subset K hkk0 hkcos hsr1 hsl1 Dp Bp γ hDp1 hBp1
    hγ0 hγ1 hγ2 hγconeR hγconeL
    (by
      rw [hDp0, hDp1]
      linear_combination Real.cos r * hXL + (xc l 1 + hgt) * hkcos)
    (by
      rw [hBp0, hBp1]
      linear_combination (-Real.cos r) * hXR + (xc r 1 + hgt) * hkcos)
  -- comparing the three areas
  have hTgtfin : MeasureTheory.volume
      ((capNiche K.val \ (distinguishedCapSides K.val).1.upperHalfPlane) \
        (distinguishedCapSides K.val).2.upperHalfPlane) ≠ ⊤ :=
    ne_top_of_le_ne_top (niche_uniform_bounds.1 _ K.val).2.2.1.ne
      (MeasureTheory.measure_mono (Set.sdiff_subset.trans Set.sdiff_subset))
  have hbase : ∀ p : Point, (∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0) → p 1 = -hgt → p ∈ Rg := by
    rintro p ⟨s, hs0⟩ hp1
    have h1 : γ.val ⟨0, le_rfl, by norm_num⟩ 0 ≤ γ.val s 0 :=
      hγmono.monotone (show (⟨0, le_rfl, by norm_num⟩ : Set.Icc (0 : ℝ) 3) ≤ s from s.property.1)
    have h2 : γ.val s 0 ≤ γ.val ⟨3, by norm_num, le_rfl⟩ 0 :=
      hγmono.monotone (show s ≤ (⟨3, by norm_num, le_rfl⟩ : Set.Icc (0 : ℝ) 3) from s.property.2)
    rw [show γ.val ⟨0, le_rfl, by norm_num⟩ = Dp from by rw [hγ0 _ (by norm_num)]; simp] at h1
    rw [show γ.val ⟨3, by norm_num, le_rfl⟩ = Bp from by rw [hγ2 _ (by norm_num)]; norm_num] at h2
    rw [hDp0] at h1
    rw [hBp0] at h2
    refine ⟨⟨le_of_eq hp1.symm, by rw [hp1]; linarith only [hgt0]⟩, ?_⟩
    rw [hp1, hs0]
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hreal := area_region_under_roof_le γ hγmono Rg _
    (by rw [hRgarea]; exact ENNReal.ofReal_ne_top) hTgtfin hbase hincl
  -- the signed-area cancellation along the base line
  have harith : segmentArea W (xc r) + curveAreaFunctional (capMiddleBV K) +
      segmentArea (xc l) Z = ClassicalResults.area Pu - ClassicalResults.area Rg := by
    rw [hPuarea, hRgreal]
    simp only [segmentArea, planeCrossProduct, hBp0, hBp1, hDp0, hDp1, hW1, hZ1]
    linear_combination (-(hgt / 2)) * hXR + (hgt / 2) * hXL
  rw [show (distinguishedCapSides K.val).1.corner = xc r from rfl,
    show (distinguishedCapSides K.val).2.corner = xc l from rfl]
  linarith [harith, hreal]

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Properties`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Mamikon / Properties
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The tangential displacement from an exposed-edge endpoint to the path, extended by zero. -/
def mamikonOffset (K : ConvexBody Point) {a b : ℝ} (z : ContinuousBVPaths a b)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc a b then
    inner ℝ (z.val ⟨t, ht⟩ - (edgeVertices K (t : Real.Angle)).1)
      (tangentVector (t : Real.Angle))
  else 0

/-- Half the square integral of a bounded measurable family of integrands that is pointwise
convex-linear in its parameter is a quadratic and convex functional of that parameter. -/
theorem sqIntegral_quadratic_convex {α : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (c : unitInterval → α → α → α) (μ : Measure Ω) [IsFiniteMeasure μ] (g : α → Ω → ℝ)
    (hmeas : ∀ x, Measurable (g x)) (hbdd : ∀ x, ∃ C, ∀ ω, |g x ω| ≤ C)
    (hlin : ∀ (s : unitInterval) (x y : α) (ω : Ω),
      g (c s x y) ω = (1 - (s : ℝ)) * g x ω + (s : ℝ) * g y ω)
    (f : α → ℝ) (hf : ∀ x, f x = (∫ ω, g x ω ^ 2 ∂μ) / 2) :
    IsQuadraticFunctional c f ∧ IsConvexFunctional c f false := by
  have hint : ∀ x y, Integrable (fun ω ↦ g x ω * g y ω) μ := by
    intro x y
    obtain ⟨Cx, hCx⟩ := hbdd x
    obtain ⟨Cy, hCy⟩ := hbdd y
    refine Integrable.mono' (integrable_const (|Cx| * |Cy|))
      ((hmeas x).mul (hmeas y)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hCx ω).trans (le_abs_self _)) ((hCy ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  set B : α → α → ℝ := fun x y ↦ (∫ ω, g x ω * g y ω ∂μ) / 2
  have hBval : ∀ x y, B x y = (∫ ω, g x ω * g y ω ∂μ) / 2 := fun _ _ ↦ rfl
  have hBsymm : ∀ x y, B x y = B y x := fun x y ↦ by
    rw [hBval, hBval, integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)]
  have hBleft : ∀ (s : unitInterval) (x y z : α),
      B (c s x y) z = realCombination s (B x z) (B y z) := by
    intro s x y z
    rw [hBval, hBval, hBval, realCombination,
      integral_congr_ae (Filter.Eventually.of_forall fun ω ↦
        show g (c s x y) ω * g z ω =
            (1 - (s : ℝ)) * (g x ω * g z ω) + (s : ℝ) * (g y ω * g z ω) by
          rw [hlin]; ring),
      integral_add ((hint x z).const_mul _) ((hint y z).const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  have hB : IsConvexBilinear c c realCombination B := by
    refine ⟨fun x s y z ↦ ?_, fun z s x y ↦ hBleft s x y z⟩
    rw [hBsymm x (c s y z), hBleft s y z x, hBsymm y x, hBsymm z x]
  have hfB : ∀ x, f x = B x x := fun x ↦ by
    rw [hf x, hBval, integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ pow_two (g x ω))]
  refine ⟨⟨B, hB, hfB⟩, fun s x y ↦ ?_⟩
  change f (c s x y) ≤ realCombination s (f x) (f y)
  have hnn : 0 ≤ B x x - B x y - B y x + B y y := by
    have i1 : Integrable (fun ω ↦ g x ω * g x ω - g x ω * g y ω) μ := (hint x x).sub (hint x y)
    have i2 : Integrable (fun ω ↦ g x ω * g x ω - g x ω * g y ω - g y ω * g x ω) μ :=
      i1.sub (hint y x)
    have hsplit : (∫ ω, (g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω) ∂μ) =
        (∫ ω, g x ω * g x ω ∂μ) - (∫ ω, g x ω * g y ω ∂μ) - (∫ ω, g y ω * g x ω ∂μ) +
          ∫ ω, g y ω * g y ω ∂μ := by
      rw [integral_add i2 (hint y y), integral_sub i1 (hint y x),
        integral_sub (hint x x) (hint x y)]
    have hpos : 0 ≤ ∫ ω, (g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω) ∂μ :=
      integral_nonneg fun ω ↦ by
        change (0 : ℝ) ≤ g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω
        nlinarith [sq_nonneg (g x ω - g y ω)]
    rw [hsplit] at hpos
    rw [hBval, hBval, hBval, hBval]
    linarith
  have hexp : B (c s x y) (c s x y) = (1 - (s : ℝ)) ^ 2 * B x x +
      (s : ℝ) * (1 - (s : ℝ)) * (B x y + B y x) + (s : ℝ) ^ 2 * B y y := by
    rw [hBleft s x y (c s x y), realCombination, hB.1 x s x y, hB.1 y s x y, realCombination,
      realCombination]
    ring
  rw [hfB, hfB, hfB, realCombination, hexp]
  nlinarith [mul_nonneg (mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)) hnn]

/-- The Mamikon offset is convex-linear in the body along a convex-linear family of paths. -/
theorem mamikonOffset_convexBodyCombination (s : unitInterval) (K L : ConvexBody Point)
    {a b : ℝ} (zK zL : ContinuousBVPaths a b) (t : ℝ) :
    mamikonOffset (convexBodyCombination s K L) (bvPathCombination s zK zL) t =
      (1 - (s : ℝ)) * mamikonOffset K zK t + (s : ℝ) * mamikonOffset L zL t := by
  by_cases ht : t ∈ Set.Icc a b
  · have hz : (bvPathCombination s zK zL).val ⟨t, ht⟩ =
        (1 - (s : ℝ)) • zK.val ⟨t, ht⟩ + (s : ℝ) • zL.val ⟨t, ht⟩ := rfl
    have hv := ((convexBody_maps_linear s K L).2.1 (t : Real.Angle)).1
    simp only [mamikonOffset, dite_eq_left ht, hz, hv, inner_sub_left, inner_add_left,
      real_inner_smul_left]
    ring
  · simp only [mamikonOffset, dite_eq_right ht]
    ring

private theorem mamikon_frame_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (z : ContinuousBVPaths a b)
    (S : Set (Set.Icc a b)) (hSmeas : MeasurableSet S)
    (hSa : ∀ t ∈ S, a < (t : ℝ))
    (W Z U T D : Fin 2 → RightContinuousIntervalBV a b)
    (hW : ∀ i t, (W i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (hWm : ∀ i (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (W i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hU : ∀ i t, (U i).toFun t = normalVector ((t : ℝ) : Real.Angle) i)
    (hUd : ∀ i, HasIntervalStieltjesDensity (U i)
      (fun t ↦ tangentVector (t : Real.Angle) i))
    (hT : ∀ i t, (T i).toFun t = tangentVector ((t : ℝ) : Real.Angle) i)
    (hUc : ∀ i, Continuous (U i).toFun)
    (hDval : ∀ i t, (D i).toFun t =
      z.val t i - (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (A : RightContinuousIntervalBV a b)
    (hA : ∀ t, A.toFun t = ∑ i, (D i).toFun t * (T i).toFun t)
    (hAmeas : Measurable A.toFun)
    (hzt : ∀ t : Set.Icc a b, inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
      supportValue K ((t : ℝ) : Real.Angle))
    (CA : ℝ) (hCA : ∀ t, ‖A.toFun t‖ ≤ CA) (hCA0 : 0 ≤ CA)
    (hAUb : ∀ i t, ‖A.toFun t * (U i).toFun t‖ ≤ CA)
    (hperpframe : ∀ u : Real.Angle,
      normalVector u 0 * tangentVector u 0 + normalVector u 1 * tangentVector u 1 = 0) :
    intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
      intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S =
    -(∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ)) := by
  -- the integrated product rule against the rotating normal frame
  choose zu hzu hzum using fun i : Fin 2 ↦
    intervalStieltjes_product a b (Z i) (U i) (Or.inr (hUc i))
  choose wu hwu hwum using fun i : Fin 2 ↦
    intervalStieltjes_product a b (W i) (U i) (Or.inr (hUc i))
  obtain ⟨ZU, hZU, hZUm⟩ := intervalStieltjes_linear_combination a b (zu 0) (zu 1) 1 1
  obtain ⟨WU, hWU, hWUm⟩ := intervalStieltjes_linear_combination a b (wu 0) (wu 1) 1 1
  have hZUWU : ZU = WU := by
    refine RightContinuousIntervalBV.toFun_injective (funext fun t ↦ ?_)
    rw [hZU t, hWU t, hzu 0 t, hzu 1 t, hwu 0 t, hwu 1 t, hZ, hZ, hW, hW, hU, hU]
    have h1 := hzt t
    have h2 : inner ℝ (edgeVertices K ((t : ℝ) : Real.Angle)).1
        (normalVector ((t : ℝ) : Real.Angle)) = supportValue K ((t : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem K ((t : ℝ) : Real.Angle)).2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two] at h1 h2
    linear_combination h1 - h2
  have hAint : ∀ F : RightContinuousIntervalBV a b,
      (intervalStieltjesMeasure F).Integrable A.toFun := by
    intro F
    have _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
      BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
    exact A.boundedVariation.integrable
  have hsplitsum : ∀ F G H : RightContinuousIntervalBV a b,
      intervalStieltjesMeasure H =
          (1 : ℝ) • intervalStieltjesMeasure F + (1 : ℝ) • intervalStieltjesMeasure G →
      intervalStieltjesIntegral H A.toFun S =
        intervalStieltjesIntegral F A.toFun S + intervalStieltjesIntegral G A.toFun S := by
    intro F G H hH
    unfold intervalStieltjesIntegral
    rw [hH]
    simp only [one_smul]
    rw [VectorMeasure.restrict_add,
      VectorMeasure.integral_add_vectorMeasure (hAint F).integrableOn (hAint G).integrableOn]
  have hH2 : ∀ (i : Fin 2) (F P : RightContinuousIntervalBV a b),
      (∀ t, P.toFun t = F.toFun t * (U i).toFun t) →
      intervalStieltjesIntegral P A.toFun S =
        intervalStieltjesIntegral F (fun t ↦ A.toFun t * (U i).toFun t) S +
          intervalStieltjesIntegral (U i) (fun t ↦ A.toFun t * F.toFun t) S := fun i F P hP ↦
    intervalStieltjesIntegral_product_of_bounded hab.le F (U i) P (hUc i) hP A.toFun
      hAmeas CA hCA S hSmeas
  have hkey := hsplitsum (zu 0) (zu 1) ZU hZUm
  rw [hZUWU, hsplitsum (wu 0) (wu 1) WU hWUm, hH2 0 (Z 0) (zu 0) (hzu 0),
    hH2 1 (Z 1) (zu 1) (hzu 1), hH2 0 (W 0) (wu 0) (hwu 0), hH2 1 (W 1) (wu 1) (hwu 1)] at hkey
  -- the vertex measure pairs to zero against the rotating normal frame
  have hWzero : intervalStieltjesIntegral (W 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
      intervalStieltjesIntegral (W 1) (fun t ↦ A.toFun t * (U 1).toFun t) S = 0 := by
    have hdot := sum_intervalStieltjesIntegral_positiveVertex_dot K hab hturn W hWm
      (fun i t ↦ A.toFun t * (U i).toFun t) CA hCA0
      (fun i ↦ hAmeas.mul (U i).boundedVariation.measurable) hAUb (fun _ ↦ 0)
      (by
        intro t _
        rw [Fin.sum_univ_two]
        simp only [hU]
        linear_combination (A.toFun t) * hperpframe ((t : ℝ) : Real.Angle))
      S hSmeas hSa
    simpa [Fin.sum_univ_two] using hdot
  -- the Lebesgue density of the rotating frame
  have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := ⟨by
    rw [comap_subtype_coe_apply measurableSet_Icc]
    simp only [Set.image_univ, Subtype.range_val]
    exact measure_Icc_lt_top⟩
  let _ := hfinite
  have hdens : ∀ (i : Fin 2) (F : RightContinuousIntervalBV a b),
      intervalStieltjesIntegral (U i) (fun t ↦ A.toFun t * F.toFun t) S =
        ∫ t in S, A.toFun t * F.toFun t * tangentVector ((t : ℝ) : Real.Angle) i
          ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) := fun i F ↦
    intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (U i) (hUd i)
      (A.boundedVariation.bilinear_comp F.boundedVariation (ContinuousLinearMap.mul ℝ ℝ)) S hSmeas
  have hintd : ∀ (i : Fin 2) (F : RightContinuousIntervalBV a b),
      Integrable (fun t : Set.Icc a b ↦
        A.toFun t * F.toFun t * tangentVector ((t : ℝ) : Real.Angle) i)
        (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := by
    intro i F
    refine (A.boundedVariation.bilinear_comp F.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).integrable.mul_bdd (c := 1) ?_ ?_
    · have h : Continuous fun u : Real.Angle ↦ tangentVector u i := by
        fin_cases i
        · exact Real.Angle.continuous_sin.neg
        · exact Real.Angle.continuous_cos
      exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).aestronglyMeasurable
    · filter_upwards with t
      fin_cases i
      · simpa [tangentVector, frame] using Real.abs_sin_le_one (t : ℝ)
      · simpa [tangentVector, frame] using Real.abs_cos_le_one (t : ℝ)
  have haddZ : Integrable (fun t : Set.Icc a b ↦
      A.toFun t * (Z 0).toFun t * tangentVector ((t : ℝ) : Real.Angle) 0 +
        A.toFun t * (Z 1).toFun t * tangentVector ((t : ℝ) : Real.Angle) 1)
      (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := (hintd 0 (Z 0)).add (hintd 1 (Z 1))
  have haddW : Integrable (fun t : Set.Icc a b ↦
      A.toFun t * (W 0).toFun t * tangentVector ((t : ℝ) : Real.Angle) 0 +
        A.toFun t * (W 1).toFun t * tangentVector ((t : ℝ) : Real.Angle) 1)
      (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := (hintd 0 (W 0)).add (hintd 1 (W 1))
  have hsquare : (intervalStieltjesIntegral (U 0) (fun t ↦ A.toFun t * (Z 0).toFun t) S +
        intervalStieltjesIntegral (U 1) (fun t ↦ A.toFun t * (Z 1).toFun t) S) -
      (intervalStieltjesIntegral (U 0) (fun t ↦ A.toFun t * (W 0).toFun t) S +
        intervalStieltjesIntegral (U 1) (fun t ↦ A.toFun t * (W 1).toFun t) S) =
      ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) := by
    rw [hdens 0 (Z 0), hdens 1 (Z 1), hdens 0 (W 0), hdens 1 (W 1),
      ← integral_add (hintd 0 (Z 0)).integrableOn (hintd 1 (Z 1)).integrableOn,
      ← integral_add (hintd 0 (W 0)).integrableOn (hintd 1 (W 1)).integrableOn,
      ← integral_sub haddZ.integrableOn haddW.integrableOn]
    refine setIntegral_congr_fun hSmeas fun t _ ↦ ?_
    have h := hA t
    rw [Fin.sum_univ_two, hDval, hDval, hT, hT] at h
    simp only [hZ, hW]
    linear_combination (-A.toFun t) * h
  linarith [hkey, hWzero, hsquare]

private theorem mamikon_arc_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hba : b < a + Real.pi) (hturn : b ≤ a + 2 * Real.pi)
    (z : ContinuousBVPaths a b) (S : Set (Set.Icc a b))
    (hSmeas : MeasurableSet S) (hSa : ∀ t ∈ S, a < (t : ℝ))
    (W Z : Fin 2 → RightContinuousIntervalBV a b)
    (hWm : ∀ i (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (W i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hzt : ∀ t : Set.Icc a b, inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
      supportValue K ((t : ℝ) : Real.Angle))
    (himg : (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' S =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioo a b) :
    intervalStieltjesIntegral (W 1) (Z 0).toFun S -
      intervalStieltjesIntegral (W 0) (Z 1).toFun S = 2 * convexArcArea K a b := by
  obtain ⟨C0, hC0⟩ := (Z 0).exists_norm_bound hab.le
  obtain ⟨C1, hC1⟩ := (Z 1).exists_norm_bound hab.le
  have hCz0 : 0 ≤ max C0 C1 := le_trans (norm_nonneg _) ((hC0 ⟨a, le_rfl, hab.le⟩).trans
    (le_max_left _ _))
  have hdot := sum_intervalStieltjesIntegral_positiveVertex_dot K hab hturn W hWm
    ![fun t ↦ -(Z 1).toFun t, (Z 0).toFun] (max C0 C1) hCz0
    (by
      intro i
      fin_cases i
      · exact ((Z 1).boundedVariation.measurable).neg
      · exact (Z 0).boundedVariation.measurable)
    (by
      intro i t
      fin_cases i
      · simpa using (hC1 t).trans (le_max_right _ _)
      · simpa using (hC0 t).trans (le_max_left _ _))
    (fun u ↦ supportValue K u)
    (by
      intro t _
      have h := planeCrossProduct_tangentVector (z.val t) ((t : ℝ) : Real.Angle)
      rw [hzt t] at h
      simp only [planeCrossProduct] at h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hZ]
      linarith)
    S hSmeas hSa
  rw [Fin.sum_univ_two] at hdot
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hdot
  rw [show intervalStieltjesIntegral (W 0) (fun t ↦ -(Z 1).toFun t) S =
      -intervalStieltjesIntegral (W 0) (Z 1).toFun S from
    VectorMeasure.integral_fun_neg _ _ _] at hdot
  rw [himg] at hdot
  have harea := (convexArc_area a b hab hba).2.1 K
  rw [← hdot] at harea
  linarith

private theorem mamikon_endpoint_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (z : ContinuousBVPaths a b)
    (W Z : Fin 2 → RightContinuousIntervalBV a b)
    (hW : ∀ i t, (W i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hZc : ∀ i, Continuous (Z i).toFun) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
    let b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
    let S : Set (Set.Icc a b) := Set.Ioo a' b'
    (intervalStieltjesIntegral (W 1) (Z 0).toFun S +
           intervalStieltjesIntegral (Z 0) (W 1).toFun S) -
         (intervalStieltjesIntegral (W 0) (Z 1).toFun S +
           intervalStieltjesIntegral (Z 1) (W 0).toFun S) =
         2 * segmentArea (edgeVertices K ((a : ℝ) : Real.Angle)).1 (z.val a') +
           2 * segmentArea (z.val b') (edgeVertices K ((b : ℝ) : Real.Angle)).2 := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let S : Set (Set.Icc a b) := Set.Ioo a' b'
  have hS : S = Set.Ioo a' b' := rfl
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  -- the product-rule endpoint identity
  obtain ⟨p1, hp1, hp1m⟩ := intervalStieltjes_product a b (W 1) (Z 0) (Or.inr (hZc 0))
  obtain ⟨p0, hp0, hp0m⟩ := intervalStieltjes_product a b (W 0) (Z 1) (Or.inr (hZc 1))
  have hab' : a' < b' := hab
  have hIoo : ∀ P : RightContinuousIntervalBV a b,
      intervalStieltjesMeasure P S = Function.leftLim P.toFun b' - P.toFun a' := by
    intro P
    rw [hS, intervalStieltjesMeasure, P.boundedVariation.vectorMeasure_Ioo hab',
      (P.right_continuous a').rightLim_eq]
  have hleftLimP : ∀ (i j : Fin 2) (P : RightContinuousIntervalBV a b),
      (∀ t, P.toFun t = (W i).toFun t * (Z j).toFun t) →
      Function.leftLim P.toFun b' =
        (edgeVertices K ((b : ℝ) : Real.Angle)).2 i * z.val b' j := by
    intro i j P hP
    have hne : (nhdsWithin b' (Set.Iio b')).NeBot := nhdsLT_neBot_of_exists_lt ⟨a', hab'⟩
    let _ := hne
    refine tendsto_nhds_unique (P.boundedVariation.tendsto_leftLim b') ?_
    have h1 := (W i).boundedVariation.tendsto_leftLim b'
    rw [leftLim_positiveVertex_coordinate K W hW i b' hab] at h1
    have h2 : Filter.Tendsto (Z j).toFun (nhdsWithin b' (Set.Iio b')) (nhds ((Z j).toFun b')) :=
      (hZc j).continuousAt.continuousWithinAt
    rw [hZ j b'] at h2
    exact (h1.mul h2).congr fun t ↦ (hP t).symm
  have hEndpoint : (intervalStieltjesIntegral (W 1) (Z 0).toFun S +
        intervalStieltjesIntegral (Z 0) (W 1).toFun S) -
      (intervalStieltjesIntegral (W 0) (Z 1).toFun S +
        intervalStieltjesIntegral (Z 1) (W 0).toFun S) =
      2 * segmentArea (edgeVertices K ((a : ℝ) : Real.Angle)).1 (z.val a') +
        2 * segmentArea (z.val b') (edgeVertices K ((b : ℝ) : Real.Angle)).2 := by
    rw [← hp1m S hSmeas, ← hp0m S hSmeas, hIoo p1, hIoo p0,
      hleftLimP 1 0 p1 hp1, hleftLimP 0 1 p0 hp0, hp1 a', hp0 a', hW, hW, hZ, hZ]
    simp only [segmentArea, planeCrossProduct]
    ring
  exact hEndpoint

theorem mamikon_integral (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi) (z : ContinuousBVPaths a b)
    (hz : ∀ t : Set.Icc a b,
      z.val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1) :
    Measurable (mamikonOffset K z) ∧
    (∃ C : ℝ, ∀ t, |mamikonOffset K z t| ≤ C) ∧
    (∀ t : Set.Icc a b, z.val t = (edgeVertices K (t.val : Real.Angle)).1 +
      mamikonOffset K z t.val • tangentVector (t.val : Real.Angle)) ∧
    mamikonFunctional K a b hab hba z hz =
      (∫ t in Set.Icc a b, (mamikonOffset K z t) ^ 2) / 2 := by
  have hturn : b ≤ a + 2 * Real.pi := by linarith [Real.pi_pos]
  set a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩ with ha'
  set b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩ with hb'
  set S : Set (Set.Icc a b) := Set.Ioo a' b' with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  have hSa : ∀ t ∈ S, a < (t : ℝ) := fun t ht ↦ ht.1
  -- the frame data
  obtain ⟨W, hW, hWm⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  set Z : Fin 2 → RightContinuousIntervalBV a b := fun i ↦ continuousBVCoordinate z i with hZdef
  have hZ : ∀ i (t : Set.Icc a b), (Z i).toFun t = z.val t i := fun _ _ ↦ rfl
  have hZc : ∀ i, Continuous (Z i).toFun := fun i ↦
    (PiLp.continuous_apply 2 _ i).comp z.property.1
  choose U hU hUd using fun i : Fin 2 ↦ exists_normalVector_coordinate_intervalBV hab.le i
  choose T hT hTd using fun i : Fin 2 ↦ exists_tangentVector_coordinate_intervalBV hab.le i
  have hUc : ∀ i, Continuous (U i).toFun := by
    intro i
    have h : Continuous fun u : Real.Angle ↦ normalVector u i := by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin
    exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).congr
      fun t ↦ (hU i t).symm
  have hTc : ∀ i, Continuous (T i).toFun := by
    intro i
    have h : Continuous fun u : Real.Angle ↦ tangentVector u i := by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos
    exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).congr
      fun t ↦ (hT i t).symm
  choose D hD hDm using fun i : Fin 2 ↦
    intervalStieltjes_linear_combination a b (Z i) (W i) 1 (-1)
  have hDval : ∀ i (t : Set.Icc a b),
      (D i).toFun t = z.val t i - (edgeVertices K ((t : ℝ) : Real.Angle)).1 i := by
    intro i t
    rw [hD i t, hZ i t, hW i t]
    ring
  obtain ⟨A, hA, hAm⟩ := intervalStieltjes_inner_fin_two D T hTc
  have hAmeas : Measurable A.toFun := A.boundedVariation.measurable
  -- the offset is the tangent projection of the difference
  have hoffset : ∀ t : Set.Icc a b, mamikonOffset K z (t : ℝ) = A.toFun t := by
    intro t
    rw [hA t]
    simp only [mamikonOffset, dite_eq_left t.property, Subtype.coe_eta, hDval, hT,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, PiLp.sub_apply]
    ring
  have hoffsetval : ∀ t : Set.Icc a b, mamikonOffset K z (t : ℝ) =
      inner ℝ (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1)
        (tangentVector ((t : ℝ) : Real.Angle)) := fun t ↦ by
    simp only [mamikonOffset, dite_eq_left t.property, Subtype.coe_eta]
  have hzt : ∀ t : Set.Icc a b,
      inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
        supportValue K ((t : ℝ) : Real.Angle) := fun t ↦ hz t
  -- measurability and boundedness of the offset
  have hmeas : Measurable (mamikonOffset K z) := by
    refine measurable_of_restrict_of_restrict_compl (s := Set.Icc a b) measurableSet_Icc ?_ ?_
    · change Measurable fun t : Set.Icc a b ↦ mamikonOffset K z (t : ℝ)
      rw [funext hoffset]
      exact hAmeas
    · change Measurable fun t : ((Set.Icc a b)ᶜ : Set ℝ) ↦ mamikonOffset K z (t : ℝ)
      rw [show (fun t : ((Set.Icc a b)ᶜ : Set ℝ) ↦ mamikonOffset K z (t : ℝ)) = fun _ ↦ 0 from
        funext fun t ↦ dite_eq_right t.property]
      exact measurable_const
  obtain ⟨CA, hCA⟩ := A.exists_norm_bound hab.le
  have hbound : ∀ t : ℝ, |mamikonOffset K z t| ≤ max CA 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · have h := hCA ⟨t, ht⟩
      rw [Real.norm_eq_abs] at h
      rw [hoffset ⟨t, ht⟩]
      exact h.trans (le_max_left _ _)
    · simp only [mamikonOffset, dite_eq_right ht, abs_zero]
      exact le_max_right _ _
  have hrecon : ∀ t : Set.Icc a b, z.val t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 +
      mamikonOffset K z (t : ℝ) • tangentVector ((t : ℝ) : Real.Angle) := by
    intro t
    have hperp : inner ℝ (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1)
        (normalVector ((t : ℝ) : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzt t, (edgeVertices_fst_mem K ((t : ℝ) : Real.Angle)).2, sub_self]
    have hdec := inner_normalVector_smul_add_inner_tangentVector_smul
      (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1) ((t : ℝ) : Real.Angle)
    rw [hperp, zero_smul, zero_add] at hdec
    rw [hoffsetval t, hdec, add_sub_cancel]
  refine ⟨hmeas, ⟨max CA 0, hbound⟩, hrecon, ?_⟩
  have hCA0 : 0 ≤ CA := le_trans (norm_nonneg _) (hCA a')
  have himg : (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' S =
      (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ⟨ht.1, ht.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.le⟩, ⟨hs.1, hs.2⟩, rfl⟩
  have hUb : ∀ (i : Fin 2) (t : Set.Icc a b), ‖(U i).toFun t‖ ≤ 1 := by
    intro i t
    simp only [hU]
    fin_cases i
    · simpa [normalVector, frame] using Real.abs_cos_le_one (t : ℝ)
    · simpa [normalVector, frame] using Real.abs_sin_le_one (t : ℝ)
  have hAUb : ∀ (i : Fin 2) (t : Set.Icc a b), ‖A.toFun t * (U i).toFun t‖ ≤ CA := by
    intro i t
    rw [norm_mul]
    calc ‖A.toFun t‖ * ‖(U i).toFun t‖ ≤ CA * 1 :=
          mul_le_mul (hCA t) (hUb i t) (norm_nonneg _) hCA0
      _ = CA := mul_one CA
  have hperpframe : ∀ u : Real.Angle,
      normalVector u 0 * tangentVector u 0 + normalVector u 1 * tangentVector u 1 = 0 := by
    intro u
    simp only [normalVector, tangentVector, frame, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hTU0 : ∀ t : Set.Icc a b, (T 0).toFun t = -(U 1).toFun t := by
    intro t
    rw [hT, hU]
    simp [normalVector, tangentVector, frame]
  have hTU1 : ∀ t : Set.Icc a b, (T 1).toFun t = (U 0).toFun t := by
    intro t
    rw [hT, hU]
    simp [normalVector, tangentVector, frame]
  have hDA : ∀ (i : Fin 2) (t : Set.Icc a b), (D i).toFun t = A.toFun t * (T i).toFun t := by
    intro i t
    have h := congrArg (fun p : Point ↦ p i) (hrecon t)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    rw [hDval i t, hT i t, ← hoffset t]
    linarith [h]
  have hDU0 : ∀ t : Set.Icc a b,
      (Z 0).toFun t - (W 0).toFun t = -(A.toFun t * (U 1).toFun t) := by
    intro t
    have h := hDA 0 t
    rw [hD 0 t, hTU0 t] at h
    rw [show (Z 0).toFun t - (W 0).toFun t = 1 * (Z 0).toFun t + -1 * (W 0).toFun t by ring, h]
    ring
  have hDU1 : ∀ t : Set.Icc a b,
      (Z 1).toFun t - (W 1).toFun t = A.toFun t * (U 0).toFun t := by
    intro t
    have h := hDA 1 t
    rw [hD 1 t, hTU1 t] at h
    rw [show (Z 1).toFun t - (W 1).toFun t = 1 * (Z 1).toFun t + -1 * (W 1).toFun t by ring, h]
  -- integrability of interval-BV integrands
  have hFint : ∀ F G : RightContinuousIntervalBV a b,
      ((intervalStieltjesMeasure G).restrict S).Integrable F.toFun := by
    intro F G
    have _ : IsFiniteMeasure (intervalStieltjesMeasure G).variation :=
      BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure G.boundedVariation
    exact (show (intervalStieltjesMeasure G).Integrable F.toFun from
      F.boundedVariation.integrable).integrableOn
  have hsubint : ∀ F G H : RightContinuousIntervalBV a b,
      intervalStieltjesIntegral H (fun t ↦ F.toFun t - G.toFun t) S =
        intervalStieltjesIntegral H F.toFun S - intervalStieltjesIntegral H G.toFun S :=
    fun F G H ↦ VectorMeasure.integral_fun_sub (hFint F H) (hFint G H)
  -- the curve area functional over the open interval
  have hJ : 2 * curveAreaFunctional z =
      intervalStieltjesIntegral (Z 1) (Z 0).toFun S -
        intervalStieltjesIntegral (Z 0) (Z 1).toFun S := by
    rw [curveAreaFunctional,
      show (fun t : Set.Icc a b ↦ z.val t 0) = (Z 0).toFun from rfl,
      show (fun t : Set.Icc a b ↦ z.val t 1) = (Z 1).toFun from rfl,
      show continuousBVCoordinate z 1 = Z 1 from rfl,
      show continuousBVCoordinate z 0 = Z 0 from rfl,
      intervalStieltjesIntegral_univ_eq_Ioo_of_continuous hab.le (Z 1) (hZc 1) _ (hZc 0),
      intervalStieltjesIntegral_univ_eq_Ioo_of_continuous hab.le (Z 0) (hZc 0) _ (hZc 1)]
    rw [← hS]
    ring
  have hArc := mamikon_arc_identity K hab hba hturn z S hSmeas hSa W Z hWm hZ hzt himg
  have hEndpoint := mamikon_endpoint_identity K hab z W Z hW hZ hZc
  have hframe := mamikon_frame_identity K hab hturn z S hSmeas hSa W Z U T D
    hW hWm hZ hU hUd hT hUc hDval A hA hAmeas hzt CA hCA hCA0 hAUb hperpframe
  -- the offset difference of the two coordinate integrals
  have hGval : (intervalStieltjesIntegral (Z 1) (Z 0).toFun S -
        intervalStieltjesIntegral (Z 1) (W 0).toFun S) -
      (intervalStieltjesIntegral (Z 0) (Z 1).toFun S -
        intervalStieltjesIntegral (Z 0) (W 1).toFun S) =
      -(intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
        intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S) := by
    rw [← hsubint (Z 0) (W 0) (Z 1), ← hsubint (Z 1) (W 1) (Z 0),
      show intervalStieltjesIntegral (Z 1) (fun t ↦ (Z 0).toFun t - (W 0).toFun t) S =
        intervalStieltjesIntegral (Z 1) (fun t ↦ -(A.toFun t * (U 1).toFun t)) S from
      VectorMeasure.setIntegral_congr_fun fun t _ ↦ hDU0 t,
      show intervalStieltjesIntegral (Z 0) (fun t ↦ (Z 1).toFun t - (W 1).toFun t) S =
        intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S from
      VectorMeasure.setIntegral_congr_fun fun t _ ↦ hDU1 t,
      show intervalStieltjesIntegral (Z 1) (fun t ↦ -(A.toFun t * (U 1).toFun t)) S =
        -intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S from
      VectorMeasure.integral_fun_neg _ _ _]
    ring
  -- the open-interval subtype integral is the closed-interval Lebesgue integral
  have hLeb : ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) =
      ∫ t in Set.Icc a b, (mamikonOffset K z t) ^ 2 := by
    have hpre : {x : Set.Icc a b | (x : ℝ) ∈ Set.Ioo a b} = S := by
      ext t
      exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
    have hsubtype := integral_subtype_preimage (μ := volume) (s := Set.Icc a b)
      (t := Set.Ioo a b) measurableSet_Icc measurableSet_Ioo
      (fun s : ℝ ↦ (mamikonOffset K z s) ^ 2)
    rw [hpre, Measure.restrict_restrict_of_subset Set.Ioo_subset_Icc_self] at hsubtype
    rw [show ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) =
        ∫ t in S, (mamikonOffset K z (t : ℝ)) ^ 2
          ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) from
      setIntegral_congr_fun hSmeas fun t _ ↦ by rw [hoffset t], hsubtype]
    exact setIntegral_congr_set Ioo_ae_eq_Icc
  -- assemble
  unfold mamikonFunctional
  rw [← ha', ← hb']
  linarith [hJ, hArc, hEndpoint, hframe, hGval, hLeb]

theorem mamikon_quadratic_convex (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi)
    (F : ConvexBody Point → ContinuousBVPaths a b)
    (hF : ∀ K : ConvexBody Point, ∀ t : Set.Icc a b,
      (F K).val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1)
    (hlinear : IsConvexLinear convexBodyCombination bvPathCombination F) :
    IsQuadraticFunctional convexBodyCombination
        (fun K ↦ mamikonFunctional K a b hab hba (F K) (hF K)) ∧
      IsConvexFunctional convexBodyCombination
        (fun K ↦ mamikonFunctional K a b hab hba (F K) (hF K)) false := by
  have hdata := fun K : ConvexBody Point ↦ mamikon_integral K a b hab hba (F K) (hF K)
  refine sqIntegral_quadratic_convex convexBodyCombination (volume.restrict (Set.Icc a b))
    (fun K ↦ mamikonOffset K (F K)) (fun K ↦ (hdata K).1) (fun K ↦ (hdata K).2.1) ?_ _
    (fun K ↦ (hdata K).2.2.2)
  intro s K L t
  rw [show F (convexBodyCombination s K L) = bvPathCombination s (F K) (F L) from hlinear s K L]
  exact mamikonOffset_convexBodyCombination s K L (F K) (F L) t

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Tails`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Mamikon / Tails
-/

public section

noncomputable section

namespace MovingSofa

/-- The signed area between a convex boundary arc and its endpoint tangent segments. -/
@[expose]
def tangentMamikonValue (K : ConvexBody Point) (a b : ℝ) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1
      (supportingIntersection K (a : Real.Angle) (b : Real.Angle)) +
    segmentArea (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
      (edgeVertices K (b : Real.Angle)).2 - convexArcArea K a b

/-- The Mamikon value of the right tail on its Gerver angle interval. -/
@[expose]
def rightTailMamikon (B : ConvexBody Point) : ℝ :=
  tangentMamikonValue B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)

/-- The Mamikon value of the left tail on its Gerver angle interval. -/
@[expose]
def leftTailMamikon (D : ConvexBody Point) : ℝ :=
  tangentMamikonValue D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)

/-- Bundle the right and left tail Mamikon functionals. -/
def tailMamikonFunctionals : (ConvexBody Point → ℝ) × (ConvexBody Point → ℝ) :=
  (rightTailMamikon, leftTailMamikon)

/-- The support and endpoint identities of a cap-tail triple, in segment-area form. -/
theorem tailFanPoint_identities
    (K : RightAngleCapSpace) (B D : ConvexBody Point) {r l : ℝ}
    (hr : r ∈ Set.Ioo 0 (Real.pi / 2)) (hl : l ∈ Set.Ioo 0 (Real.pi / 2))
    (hB1 : supportValue (B : Set Point) ((Real.pi + r : ℝ) : Real.Angle) =
      1 - supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle))
    (hB2 : supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hD1 : supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hD2 : supportValue (D : Set Point) ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) =
      1 - supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle)) :
    supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) = (wedgeEndpoints K r).1 ∧
    supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) = (wedgeEndpoints K l).2 ∧
    segmentArea (wedgeEndpoints K r).1
        (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = 0 ∧
    segmentArea (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (wedgeEndpoints K l).2 = 0 ∧
    segmentArea (capInnerCorner K r) (wedgeEndpoints K r).1 -
        segmentArea (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
          (wedgeEndpoints K r).1 =
      segmentArea (capInnerCorner K r)
        (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1 ∧
    segmentArea (wedgeEndpoints K l).2 (capInnerCorner K l) -
        segmentArea (wedgeEndpoints K l).2
          (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2 =
      segmentArea (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
        (capInnerCorner K l) := by
  obtain ⟨hr0, hr2⟩ := hr
  obtain ⟨hl0, hl2⟩ := hl
  have hpi := Real.pi_pos
  have hcosr : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, hr2⟩
  have hsinl : 0 < Real.sin l := Real.sin_pos_of_pos_of_lt_pi hl0 (by linarith)
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  -- opposite normals
  have hnr : normalVector ((Real.pi + r : ℝ) : Real.Angle) =
      -normalVector ((r : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show Real.pi + r = r + Real.pi by ring), normalVector_add_pi]
  have hn32 : normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring), normalVector_add_pi]
  have hn32l : normalVector ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) =
      -normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show 3 * Real.pi / 2 + l = (Real.pi / 2 + l) + Real.pi by ring),
      normalVector_add_pi]
  have hnl : normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle) =
      tangentVector ((l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show Real.pi / 2 + l = l + Real.pi / 2 by ring),
      normalVector_add_pi_div_two_real]
  have hKl : supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) := by
    rw [hcast _ _ (show l + Real.pi / 2 = Real.pi / 2 + l by ring)]
  -- the two fan points
  have h1 : inner ℝ (wedgeEndpoints K r).1 (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    change inner ℝ (((supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1) /
      Real.cos r) • normalVector 0) _ = _
    rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
      zero_sub, Real.cos_neg]
    field_simp
  have h2 : inner ℝ (wedgeEndpoints K r).1
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    change inner ℝ (((supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1) /
      Real.cos r) • normalVector 0) _ = _
    rw [real_inner_smul_left, ← Real.Angle.coe_zero, inner_normalVector_normalVector,
      zero_sub, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  have h5 : inner ℝ (wedgeEndpoints K l).2
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    change inner ℝ (((supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (Real.pi / 2 - l)) • tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) _ = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real,
      Real.cos_pi_div_two_sub, hKl, show Real.pi / 2 + l - Real.pi / 2 = l by ring]
    field_simp
  have h6 : inner ℝ (wedgeEndpoints K l).2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    change inner ℝ (((supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (Real.pi / 2 - l)) • tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) _ = _
    rw [real_inner_smul_left, inner_tangentVector_normalVector_real, sub_self,
      Real.sin_zero, mul_zero]
  -- the two supporting intersections
  have hs1 : Real.sin (3 * Real.pi / 2 - (Real.pi + r)) ≠ 0 := by
    rw [show 3 * Real.pi / 2 - (Real.pi + r) = Real.pi / 2 - r by ring, Real.sin_pi_div_two_sub]
    exact ne_of_gt hcosr
  have hs2 : Real.sin (3 * Real.pi / 2 + l - 3 * Real.pi / 2) ≠ 0 := by
    rw [show 3 * Real.pi / 2 + l - 3 * Real.pi / 2 = l by ring]
    exact ne_of_gt hsinl
  have h3 : inner ℝ (supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)) (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    have h := supportingIntersection_inner_left B (Real.pi + r) (3 * Real.pi / 2)
    rw [hnr, inner_neg_right, hB1] at h
    linarith
  have h4 : inner ℝ (supportingIntersection B ((Real.pi + r : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h := supportingIntersection_inner_right B (Real.pi + r) (3 * Real.pi / 2) hs1
    rw [hn32, inner_neg_right, hB2] at h
    linarith
  have h7 : inner ℝ (supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 + l : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    have h := supportingIntersection_inner_right D (3 * Real.pi / 2)
      (3 * Real.pi / 2 + l) hs2
    rw [hn32l, inner_neg_right, hD2] at h
    linarith
  have h8 : inner ℝ (supportingIntersection D ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      ((3 * Real.pi / 2 + l : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h := supportingIntersection_inner_left D (3 * Real.pi / 2) (3 * Real.pi / 2 + l)
    rw [hn32, inner_neg_right, hD1] at h
    linarith
  -- the cap corners and the tail vertices
  have h9 : inner ℝ (capInnerCorner K r) (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := (inner_capInnerCorner K r).1
  have h13 : inner ℝ (capInnerCorner K l)
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    rw [hnl, (inner_capInnerCorner K l).2, hKl]
  have h10 : inner ℝ (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
      (normalVector ((r : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((r : ℝ) : Real.Angle) - 1 := by
    have h : inner ℝ (edgeVertices B ((Real.pi + r : ℝ) : Real.Angle)).1
        (normalVector ((Real.pi + r : ℝ) : Real.Angle)) =
        supportValue (B : Set Point) ((Real.pi + r : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem B ((Real.pi + r : ℝ) : Real.Angle)).2
    rw [hnr, inner_neg_right, hB1] at h
    linarith
  have h11 : inner ℝ (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h : inner ℝ (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
    rw [hn32, inner_neg_right, hB2] at h
    linarith
  have h12 : inner ℝ (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    have h : inner ℝ (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
    rw [hn32, inner_neg_right, hD1] at h
    linarith
  have h14 : inner ℝ (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
      (normalVector ((Real.pi / 2 + l : ℝ) : Real.Angle)) =
      supportValue (K.1 : Set Point) ((Real.pi / 2 + l : ℝ) : Real.Angle) - 1 := by
    have h : inner ℝ (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)) =
        supportValue (D : Set Point) ((3 * Real.pi / 2 + l : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2
    rw [hn32l, inner_neg_right, hD2] at h
    linarith
  refine ⟨?_, ?_, segmentArea_eq_zero_of_inner_normalVector_eq_zero h2 h11,
    segmentArea_eq_zero_of_inner_normalVector_eq_zero h12 h6,
    segmentArea_sub_segmentArea_of_inner_normalVector_eq h9 h10 h1, ?_⟩
  · refine eq_of_inner_normalVector_eq (s := r) (t := Real.pi / 2) ?_
      (h3.trans h1.symm) (h4.trans h2.symm)
    rw [show r - Real.pi / 2 = -(Real.pi / 2 - r) by ring, Real.sin_neg,
      Real.sin_pi_div_two_sub]
    exact neg_ne_zero.mpr (ne_of_gt hcosr)
  · refine eq_of_inner_normalVector_eq (s := Real.pi / 2 + l) (t := Real.pi / 2) ?_
      (h7.trans h5.symm) (h8.trans h6.symm)
    rw [show Real.pi / 2 + l - Real.pi / 2 = l by ring]
    exact ne_of_gt hsinl
  · have h := segmentArea_sub_segmentArea_of_inner_normalVector_eq h13 h14 h5
    linarith [segmentArea_swap (wedgeEndpoints K l).2 (capInnerCorner K l),
      segmentArea_swap (wedgeEndpoints K l).2
        (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2,
      segmentArea_swap (capInnerCorner K l)
        (edgeVertices D ((3 * Real.pi / 2 + l : ℝ) : Real.Angle)).2]

theorem upperBoundQ_decomposition (X : CapTailSpace) :
    upperBoundQ X = upperBoundMiddle X.cap - rightTailMamikon X.rightBody -
      leftTailMamikon X.leftBody := by
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have htop : supportValue (X.cap.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    X.cap.1.property.2.2.2.1
  have hB1 : supportValue (X.rightBody : Set Point)
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (X.cap.1.1 : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := X.right_eq paperGerverConstants.2.1 (by simp)
    linarith
  have hB2 : supportValue (X.rightBody : Set Point)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := X.right_eq (Real.pi / 2) (by simp)
    rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
    linarith
  have hD1 : supportValue (X.leftBody : Set Point)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := X.left_eq 0 (by simp)
    rw [hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring),
      hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring), htop] at h
    linarith
  have hD2 : supportValue (X.leftBody : Set Point)
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (X.cap.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    have h := X.left_eq paperGerverConstants.2.2 (by simp)
    linarith
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ :=
    tailFanPoint_identities X.cap.val X.rightBody X.leftBody hr hl hB1 hB2 hD1 hD2
  simp only [upperBoundQ, upperBoundMiddle, rightTailMamikon, leftTailMamikon,
    tangentMamikonValue, rightLeftTailArcs, distinguishedCapSides]
  rw [e1, e2]
  linarith

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Cap.PolylineBoundary`.
* `Cap.PolylineDefinition`.
* `Cap.Polyline`.
* `Cap.UpperBoundary.Polygon`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline Boundary
-/

public section

noncomputable section

namespace MovingSofa

/-- The slope and intercept of the inner B-wall line at angle `t`. -/
def capBAffine {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ × ℝ :=
  (-Real.cos t / Real.sin t,
    (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t)

/-- The slope and intercept of the inner D-wall line at angle `t`. -/
def capDAffine {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ × ℝ :=
  (Real.sin t / Real.cos t,
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.cos t)

/-- The slope and zero intercept of the slanted fan boundary. -/
def fanAffine (ω : ℝ) : ℝ × ℝ :=
  (-Real.cos ω / Real.sin ω, 0)

private def capAffinePieces {Θ : AngleSet} (K : PolygonCapSpace Θ) : Finset (ℝ × ℝ) :=
  {(0, 0), fanAffine Θ.angle} ∪
    Θ.directions.biUnion fun t ↦ {capBAffine K t, capDAffine K t}

/-- The lower boundary height of a polygon cap after removing its niche. -/
def capBoundaryHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) (x : ℝ) : ℝ :=
  max 0 (max (affineValue (fanAffine Θ.angle) x)
    (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x)))

private theorem continuous_capBoundaryHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    Continuous (capBoundaryHeight K) := by
  unfold capBoundaryHeight
  apply Continuous.max continuous_const
  apply Continuous.max (continuous_affineValue _)
  apply Continuous.finset_sup'_apply Θ.nonempty
  intro t ht
  exact (continuous_affineValue _).min (continuous_affineValue _)

private theorem capBoundaryHeight_eq_affineValue {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (x : ℝ) :
    ∃ c ∈ capAffinePieces K, capBoundaryHeight K x = affineValue c x := by
  obtain hzero | hrest := max_choice 0
    (max (affineValue (fanAffine Θ.angle) x)
      (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x)))
  · refine ⟨(0, 0), by simp [capAffinePieces], ?_⟩
    simpa [capBoundaryHeight, affineValue] using hzero
  · obtain hfan | hsup := max_choice (affineValue (fanAffine Θ.angle) x)
      (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) x) (affineValue (capDAffine K t) x))
    · refine ⟨fanAffine Θ.angle, by simp [capAffinePieces], ?_⟩
      rw [capBoundaryHeight, hrest, hfan]
    · obtain ⟨t, ht, htEq⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
        (fun t ↦ min (affineValue (capBAffine K t) x)
          (affineValue (capDAffine K t) x))
      obtain hB | hD := min_choice (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)
      · refine ⟨capBAffine K t, ?_, ?_⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
        · rw [capBoundaryHeight, hrest, hsup, htEq, hB]
      · refine ⟨capDAffine K t, ?_, ?_⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
        · rw [capBoundaryHeight, hrest, hsup, htEq, hD]

private theorem capAffinePieces_has_normal {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {c : ℝ × ℝ} (hc : c ∈ capAffinePieces K) :
    ∃ t ∈ angleDomain Θ, Real.cos t + c.1 * Real.sin t = 0 := by
  rw [capAffinePieces, Finset.mem_union] at hc
  rcases hc with hc | hc
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · refine ⟨Real.pi / 2, ?_, ?_⟩
      · simp [angleDomain]
      · simp
    · refine ⟨Θ.angle, ?_, ?_⟩
      · simp [angleDomain]
      · simp only [fanAffine]
        have hs : Real.sin Θ.angle ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).ne'
        field_simp
        ring
  · obtain ⟨t, ht, hc⟩ := Finset.mem_biUnion.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · refine ⟨t, by simp [angleDomain, ht], ?_⟩
      simp only [capBAffine]
      have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi
        (Θ.interior t ht).1
        ((Θ.interior t ht).2.trans_le Θ.angle_le |>.trans
          (by linarith [Real.pi_pos]))).ne'
      field_simp
      ring
    · refine ⟨t + Real.pi / 2, ?_, ?_⟩
      · simp [angleDomain, ht]
      · simp only [capDAffine, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
        have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, (Θ.interior t ht).1],
            (Θ.interior t ht).2.trans_le Θ.angle_le⟩).ne'
        field_simp
        ring

private theorem mem_innerQuadrant_iff_lt_min_affine {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) (p : Point) :
    p ∈ innerQuadrant K.val.val t ↔
      p 1 < min (affineValue (capBAffine K t) (p 0))
        (affineValue (capDAffine K t) (p 0)) := by
  have htt := Θ.interior t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htt.1
    ((htt.2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, htt.1], htt.2.trans_le Θ.angle_le⟩
  simp only [innerQuadrant, normalHalfPlane, Set.mem_inter_iff,
    Bool.false_eq_true, ite_false, ite_true]
  simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Set.mem_ofPred_eq, Real.cos_add,
    Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two, mul_one, zero_sub, Real.sin_add,
    zero_add, neg_mul, neg_add_lt_iff_lt_add, lt_min_iff]
  change
    (Real.cos t * p 0 + Real.sin t * p 1 <
        supportValue K.val.val (t : Real.Angle) - 1 ∧
      Real.cos t * p 1 < Real.sin t * p 0 +
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) ↔ _
  simp only [affineValue, capBAffine, capDAffine]
  have heqB : -Real.cos t / Real.sin t * p 0 +
      (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t =
      (supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * p 0) /
        Real.sin t := by
    field_simp
    ring
  have heqD : Real.sin t / Real.cos t * p 0 +
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos t =
      (Real.sin t * p 0 +
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) /
        Real.cos t := by
    field_simp
  rw [heqB, heqD]
  constructor
  · rintro ⟨hB, hD⟩
    constructor
    · apply (lt_div_iff₀ hs).2
      nlinarith
    · apply (lt_div_iff₀ hc).2
      nlinarith
  · rintro ⟨hB, hD⟩
    constructor
    · apply (lt_div_iff₀ hs).mp at hB
      nlinarith
    · apply (lt_div_iff₀ hc).mp at hD
      nlinarith

private theorem mem_capFan_iff_max_affine_le {Θ : AngleSet}
    (p : Point) :
    p ∈ capFan Θ.angle ↔
      max 0 (affineValue (fanAffine Θ.angle) (p 0)) ≤ p 1 := by
  have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  simp only [capFan, normalHalfPlane, ↓reduceIte, Bool.false_eq_true, normalVector, frame,
    Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul,
    zero_add, Set.mem_inter_iff, Set.mem_ofPred_eq, affineValue, fanAffine, add_zero,
    sup_le_iff]
  have heq : -Real.cos Θ.angle / Real.sin Θ.angle * p 0 =
      (-Real.cos Θ.angle * p 0) / Real.sin Θ.angle := by ring
  rw [heq]
  constructor
  · rintro ⟨hfan, hy⟩
    exact ⟨hy, (div_le_iff₀ hs).2 (by nlinarith)⟩
  · rintro ⟨hy, hfan⟩
    apply (div_le_iff₀ hs).mp at hfan
    exact ⟨by nlinarith, hy⟩

/-- The fan outside the polygon niche is the epigraph of its boundary height. -/
theorem capFan_sdiff_polygonNiche_eq_epigraph {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    capFan Θ.angle \ polygonNiche Θ K.val =
      {p | capBoundaryHeight K (p 0) ≤ p 1} := by
  ext p
  constructor
  · rintro ⟨hfan, hniche⟩
    have hnotUnion : p ∉ ⋃ t ∈ Θ.directions, innerQuadrant K.val.val t := by
      intro hp
      exact hniche ⟨hfan, hp⟩
    have hfan' := (mem_capFan_iff_max_affine_le (Θ := Θ) p).mp hfan
    change capBoundaryHeight K (p 0) ≤ p 1
    unfold capBoundaryHeight
    apply max_le
    · exact (le_max_left _ _).trans hfan'
    · apply max_le
      · exact (le_max_right _ _).trans hfan'
      · apply (Finset.sup'_le_iff Θ.nonempty _).2
        intro t ht
        apply le_of_not_gt
        intro hlt
        apply hnotUnion
        exact Set.mem_iUnion₂.mpr
          ⟨t, ht, (mem_innerQuadrant_iff_lt_min_affine K ht p).mpr hlt⟩
  · intro hp
    change capBoundaryHeight K (p 0) ≤ p 1 at hp
    unfold capBoundaryHeight at hp
    have hzero : 0 ≤ p 1 := by
      exact (le_max_left 0 _).trans hp
    have hfanLine : affineValue (fanAffine Θ.angle) (p 0) ≤ p 1 := by
      exact (le_max_left _ _).trans <|
        (le_max_right 0 _).trans hp
    have hsup : (Θ.directions.sup' Θ.nonempty fun t ↦
        min (affineValue (capBAffine K t) (p 0))
          (affineValue (capDAffine K t) (p 0))) ≤ p 1 := by
      exact (le_max_right _ _).trans <|
        (le_max_right 0 _).trans hp
    have hfan : p ∈ capFan Θ.angle :=
      (mem_capFan_iff_max_affine_le (Θ := Θ) p).mpr (max_le hzero hfanLine)
    refine ⟨hfan, ?_⟩
    rintro ⟨-, hunion⟩
    obtain ⟨t, ht, hquad⟩ := Set.mem_iUnion₂.mp hunion
    have hlt := (mem_innerQuadrant_iff_lt_min_affine K ht p).mp hquad
    have hle := ((Finset.sup'_le_iff Θ.nonempty _).1 hsup) t ht
    exact (not_lt_of_ge hle) hlt

/-- The cap outside its polygon niche is closed, with frontier the boundary graph. -/
theorem capFan_sdiff_polygonNiche_closed_frontier {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) ∧
    frontier (capFan Θ.angle \ polygonNiche Θ K.val) =
      Set.range (pointOnGraph (capBoundaryHeight K)) := by
  rw [capFan_sdiff_polygonNiche_eq_epigraph K]
  exact ⟨isClosed_verticalEpigraph (continuous_capBoundaryHeight K),
    frontier_verticalEpigraph (continuous_capBoundaryHeight K)⟩

/-- Every compact interval of the polygon-cap boundary graph is a finite polyline. -/
theorem exists_capBoundary_graphPolyline {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : ℝ} (hab : a < b) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph (capBoundaryHeight K) a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph (capBoundaryHeight K) b ∧
      p.carrier = pointOnGraph (capBoundaryHeight K) '' Set.Icc a b ∧
      (∀ i : Fin p.edges, ∃ t ∈ angleDomain Θ,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0) := by
  obtain ⟨p, hp, hp0, hp1, hpcarrier, hgraph, hpieces⟩ :=
    exists_graphPolyline_of_finite_affine_selector hab (capAffinePieces K)
      (continuous_capBoundaryHeight K).continuousOn
      (fun x _ ↦ capBoundaryHeight_eq_affineValue K x)
  refine ⟨p, hp, hp0, hp1, hpcarrier, ?_⟩
  intro i
  obtain ⟨c, hcL, hc⟩ := hpieces i
  obtain ⟨t, ht, horth⟩ := capAffinePieces_has_normal K hcL
  refine ⟨t, ht, ?_⟩
  have hab' : p.vertices i.castSucc 0 ≤ p.vertices i.succ 0 :=
    (p.increasing i.castSucc_lt_succ).le
  rw [hgraph i.succ, hgraph i.castSucc]
  change Set.EqOn (capBoundaryHeight K) (fun x ↦ c.1 * x + c.2)
    (Set.Icc (p.vertices i.castSucc 0) (p.vertices i.succ 0)) at hc
  exact inner_pointOnGraph_sub_normalVector_eq_zero
    (m := c.1) (c := c.2) (t := t)
    hc hab' horth

/-- The lower endpoint of the zero-angle cap face lies on the horizontal axis. -/
theorem capVertices_zero_snd_eq {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (capVertices K.val 0).1.2 =
      supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle) := by
  let A := supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle)
  have hAK : A ∈ (K.val.val : Set Point) :=
    supportValue_zero_smul_normalVector_mem K.val
  have hAedge : A ∈ exposedEdge K.val.val (0 : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle)
    dsimp [A]
    simp [normalVector, frame, PiLp.inner_apply]
  change (edgeVertices K.val.val (0 : Real.Angle)).2 = A
  apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hAedge
  intro q hq
  have hqFan := K.val.subset_capFan hq.1
  have hqy : 0 ≤ q 1 := by
    have h := hqFan.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at h
    simpa [normalVector, frame, PiLp.inner_apply] using h
  simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
    tangentVector, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_one, zero_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, one_mul, zero_add,
    ge_iff_le, A]
  exact hqy

/-- The terminal positive cap contact lies on the lower fan ray. -/
theorem capVertices_angle_fst_eq {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (capVertices K.val Θ.angle).2.1 =
      supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
        tangentVector (Θ.angle : Real.Angle) := by
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  let C := L • tangentVector (Θ.angle : Real.Angle)
  have hCK : C ∈ (K.val.val : Set Point) := by
    by_cases hω : Θ.angle = Real.pi / 2
    · have hmem := supportValue_pi_smul_normalVector_mem_of_eq K.val hω
      simpa [C, L, hω, tangentVector, normalVector, frame, PiLp.inner_apply] using hmem
    · exact supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K.val
        (Θ.angle_le.lt_of_ne hω)
  have hCedge : C ∈ exposedEdge K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C
      (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) = L
    rw [show ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
        (Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two, real_inner_smul_left,
      inner_tangentVector_self]
    ring
  change (edgeVertices K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1 = C
  apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hCedge
  intro q hq
  have hqFan := K.val.subset_capFan hq.1
  have hqu : 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) := hqFan.1
  rw [tangentVector_add_pi_div_two]
  simp only [inner_neg_right]
  have hCzero : inner ℝ C (normalVector (Θ.angle : Real.Angle)) = 0 := by
    dsimp [C]
    rw [real_inner_smul_left, real_inner_comm,
      inner_normalVector_tangentVector]
    simp
  rw [hCzero]
  simpa using neg_nonpos.mpr hqu

/-- The terminal cap contacts occur in strictly increasing horizontal order. -/
theorem polygonCap_left_x_lt_right_x {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    ((capVertices K.val Θ.angle).2.1) 0 < ((capVertices K.val 0).1.2) 0 := by
  let C := (capVertices K.val Θ.angle).2.1
  let A := (capVertices K.val 0).1.2
  have hq_le_A : ∀ q ∈ (K.val.val : Set Point), q 0 ≤ A 0 := by
    intro q hq
    have hq' := inner_le_supportValue K.val.val hq (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    calc
      q 0 = inner ℝ q (normalVector (0 : Real.Angle)) := by
        simp [normalVector, frame, PiLp.inner_apply]
      _ ≤ supportValue K.val.val (0 : Real.Angle) := hq'
      _ = inner ℝ A (normalVector (0 : Real.Angle)) := hA.symm
      _ = A 0 := by simp [normalVector, frame, PiLp.inner_apply]
  by_cases hω : Θ.angle = Real.pi / 2
  · have hC_le_q : ∀ q ∈ (K.val.val : Set Point), C 0 ≤ q 0 := by
      intro q hq
      have hq' := inner_le_supportValue K.val.val hq (Real.pi : Real.Angle)
      have hC := (edgeVertices_fst_mem K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).2
      change inner ℝ C
        (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) =
          supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) at hC
      have hang : ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
          (Real.pi : Real.Angle) := by
        congr 1
        rw [hω]
        ring
      rw [hang] at hC
      have hqcoord : -q 0 ≤ supportValue K.val.val (Real.pi : Real.Angle) := by
        simpa [normalVector, frame, PiLp.inner_apply] using hq'
      have hCcoord : -C 0 = supportValue K.val.val (Real.pi : Real.Angle) := by
        simpa [normalVector, frame, PiLp.inner_apply] using hC
      linarith
    by_contra hnot
    have hAC : A 0 = C 0 := by
      apply le_antisymm (le_of_not_gt hnot)
      exact hC_le_q A (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
    have hx : ∀ q ∈ (K.val.val : Set Point), q 0 = A 0 := by
      intro q hq
      exact le_antisymm (hq_le_A q hq) (hAC.trans_le (hC_le_q q hq))
    obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
      ((Real.pi / 2 : ℝ) : Real.Angle)
    obtain ⟨l, hlK, hl⟩ := exists_mem_inner_eq_supportValue K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have huy : u 1 = 1 := by
      rw [K.val.property.2.2.2.1] at hu
      simpa [normalVector, frame, PiLp.inner_apply] using hu
    have hly : l 1 = 0 := by
      rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hl
      linarith
    let m : Point := (2 : ℝ)⁻¹ • (u + l)
    let N : Set Real.Angle :=
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
    let U : Set Point := ⋂ t ∈ N,
      {p | inner ℝ p (normalVector t) < supportValue K.val.val t}
    have hdomain_finite : (angleDomain Θ).Finite := by
      unfold angleDomain
      exact (Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
          (Set.toFinite _)
    have hlower_finite : (capLowerNormals Θ.angle).Finite := by
      simp [capLowerNormals]
    have hNfinite : N.Finite := by
      dsimp [N]
      exact (hdomain_finite.image fun t : ℝ ↦ (t : Real.Angle)).union hlower_finite
    have hUopen : IsOpen U := by
      dsimp [U]
      apply hNfinite.isOpen_biInter
      intro t ht
      exact isOpen_lt (by fun_prop) continuous_const
    have hmU : m ∈ U := by
      dsimp [U]
      simp only [Set.mem_iInter]
      intro t htN
      rcases htN with ⟨r, hr, rfl⟩ | htLower
      · have hrI : r ∈ Set.Ioo 0 Real.pi := by
          rcases hr with (hr | ⟨s, hs, rfl⟩) | hr
          · exact ⟨(Θ.interior r hr).1,
              by linarith [(Θ.interior r hr).2, Θ.angle_le, Real.pi_pos]⟩
          · exact ⟨by linarith [(Θ.interior s hs).1, Real.pi_pos],
              by linarith [(Θ.interior s hs).2, hω, Real.pi_pos]⟩
          · rcases hr with rfl | hr
            · rw [hω]
              constructor <;> linarith [Real.pi_pos]
            · have hr : r = Real.pi / 2 := hr
              rw [hr]
              constructor <;> linarith [Real.pi_pos]
        have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hrI.1 hrI.2
        have htop : inner ℝ m (normalVector (r : Real.Angle)) <
            inner ℝ u (normalVector (r : Real.Angle)) := by
          have hux : u 0 = l 0 := (hx u huK).trans (hx l hlK).symm
          simp only [smul_add, normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
            PiLp.inner_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply,
            conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one, huy, mul_one, hly, mul_zero, add_zero,
            gt_iff_lt, m]
          rw [hux]
          norm_num
          nlinarith
        exact htop.trans_le (inner_le_supportValue K.val.val huK _)
      · simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at htLower
        rcases htLower with rfl | rfl
        · rw [K.val.property.2.2.2.2.1]
          norm_num [m, hω, normalVector, frame, PiLp.inner_apply, huy, hly]
        · rw [K.val.property.2.2.2.2.2.1]
          change inner ℝ m
            (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) < 0
          rw [inner_normalVector_three_pi_div_two]
          simp [m, huy, hly]
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hUopen) m hmU
    let q : Point := m + (ε / 2) • normalVector (0 : Real.Angle)
    have hqm : q ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [q, add_sub_cancel_left, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      have hn : ‖normalVector (0 : Real.Angle)‖ = 1 := by
        simpa only [Real.Angle.coe_zero] using norm_normalVector_real 0
      rw [hn, mul_one]
      linarith
    have hqU : q ∈ U := hball hqm
    have hqK : q ∈ (K.val.val : Set Point) := by
      rw [K.property.eq_iInter_supportValue]
      simp only [Set.mem_iInter]
      intro t ht
      have hqt := Set.mem_iInter.mp (Set.mem_iInter.mp hqU t) ht
      change inner ℝ q (normalVector t) < supportValue K.val.val t at hqt
      exact hqt.le
    have hq0 : q 0 = A 0 + ε / 2 := by
      simp [q, m, normalVector, frame, hx u huK, hx l hlK]
      ring
    have := hq_le_A q hqK
    rw [hq0] at this
    linarith
  · have hωlt : Θ.angle < Real.pi / 2 := Θ.angle_le.lt_of_ne hω
    rw [capVertices_zero_snd_eq K, capVertices_angle_fst_eq K]
    have hA0 : 0 < supportValue K.val.val (0 : Real.Angle) := by
      obtain ⟨p, hpK, hp⟩ := exists_mem_inner_eq_supportValue K.val.val
        (Θ.angle : Real.Angle)
      have hpy : p 1 ≤ 1 := by
        have hpy' := inner_le_supportValue K.val.val hpK
          ((Real.pi / 2 : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.1] at hpy'
        simpa [normalVector, frame, PiLp.inner_apply] using hpy'
      rw [K.val.property.2.2.1] at hp
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hωlt⟩
      have hsin_lt : Real.sin Θ.angle < 1 := by
        nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
      have hpx : 0 < p 0 := by
        simp [normalVector, frame, PiLp.inner_apply] at hp
        have hsin : 0 ≤ Real.sin Θ.angle :=
          (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
            (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
        have hmul := mul_le_mul_of_nonneg_left hpy hsin
        nlinarith
      exact hpx.trans_le (by
        have := inner_le_supportValue K.val.val hpK (0 : Real.Angle)
        simpa [normalVector, frame, PiLp.inner_apply] using this)
    have hL0 : 0 ≤ supportValue K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
      supportValue_nonneg_of_mem_capUpperAngles K.val hωlt
        (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
    have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
    have hprod : 0 ≤ supportValue K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) * Real.sin Θ.angle :=
      mul_nonneg hL0 hs.le
    have hprod' : 0 ≤ supportValue K.val.val
        ((Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) *
          Real.sin Θ.angle := by
      simpa only [Real.Angle.coe_add] using hprod
    simp [normalVector, tangentVector, frame]
    nlinarith

private theorem capBoundaryHeight_eq_zero_of_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {x : ℝ}
    (hx : ((capVertices K.val 0).1.2) 0 ≤ x) :
    capBoundaryHeight K x = 0 := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  have hsinω : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hAfan := K.val.subset_capFan (edgeVertices_snd_mem K.val.val
    (0 : Real.Angle)).1
  have hfanA : affineValue (fanAffine Θ.angle) (A 0) ≤ 0 := by
    change A = supportValue K.val.val (0 : Real.Angle) •
      normalVector (0 : Real.Angle) at hAeq
    change A ∈ capFan Θ.angle at hAfan
    have h := hAfan.1
    change 0 ≤ inner ℝ A (normalVector (Θ.angle : Real.Angle)) at h
    rw [hAeq] at h
    simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
      Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, PiLp.smul_apply,
      smul_eq_mul, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_zero, add_zero] at h
    have hAcoord : A 0 = supportValue K.val.val (0 : Real.Angle) := by
      rw [hAeq]
      simp [normalVector, frame]
    rw [hAcoord]
    simp only [affineValue, fanAffine, add_zero]
    have heq : -Real.cos Θ.angle / Real.sin Θ.angle *
        supportValue K.val.val (0 : Real.Angle) =
        (-Real.cos Θ.angle * supportValue K.val.val (0 : Real.Angle)) /
          Real.sin Θ.angle := by ring
    rw [heq]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [h]
    · exact hsinω.le
  have hfan : affineValue (fanAffine Θ.angle) x ≤ 0 := by
    simp only [affineValue, fanAffine, add_zero] at hfanA ⊢
    have hslope : -Real.cos Θ.angle / Real.sin Θ.angle ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcosω) hsinω.le
    exact (mul_le_mul_of_nonpos_left hx hslope).trans hfanA
  have hpieces : (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)) ≤ 0 := by
    apply (Finset.sup'_le_iff Θ.nonempty _).2
    intro t ht
    apply (min_le_left _ _).trans
    have htt := Θ.interior t ht
    have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htt.1
      ((htt.2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos]))
    have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
    have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
    have hgap : 0 < (wedgeGaps K.val t).1 :=
      hgapBounds.2.1.trans_le hgapBounds.1
    rw [wedgeGaps_fst_eq_supportValue] at hgap
    have hAcoord : A 0 = supportValue K.val.val (0 : Real.Angle) := by
      change A = supportValue K.val.val (0 : Real.Angle) •
        normalVector (0 : Real.Angle) at hAeq
      rw [hAeq]
      simp [normalVector, frame]
    have hnum : supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * x < 0 := by
      have hdiv := (sub_pos.mp hgap)
      have hmul := (div_lt_iff₀ hcost).mp hdiv
      rw [hAcoord] at hx
      nlinarith
    simp only [affineValue, capBAffine]
    have heq : -Real.cos t / Real.sin t * x +
        (supportValue K.val.val (t : Real.Angle) - 1) / Real.sin t =
        (supportValue K.val.val (t : Real.Angle) - 1 - Real.cos t * x) /
          Real.sin t := by
      field_simp
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum.le hsint.le
  unfold capBoundaryHeight
  rw [max_eq_left (max_le hfan hpieces)]

private theorem capBoundaryHeight_eq_fanAffine_of_left {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {x : ℝ}
    (hx : x ≤ ((capVertices K.val Θ.angle).2.1) 0) :
    capBoundaryHeight K x = affineValue (fanAffine Θ.angle) x := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hsinω : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hfan_nonneg : 0 ≤ affineValue (fanAffine Θ.angle) x := by
    by_cases hω : Θ.angle = Real.pi / 2
    · simp [affineValue, fanAffine, hω]
    · have hωlt : Θ.angle < Real.pi / 2 := Θ.angle_le.lt_of_ne hω
      have hL : 0 ≤ L := supportValue_nonneg_of_mem_capUpperAngles K.val hωlt
        (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
      have hCx : C 0 = -L * Real.sin Θ.angle := by
        change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
        rw [hCeq]
        simp [tangentVector, frame]
      have hx0 : x ≤ 0 := by
        rw [hCx] at hx
        nlinarith [mul_nonneg hL hsinω.le]
      simp only [affineValue, fanAffine, add_zero]
      exact mul_nonneg_of_nonpos_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcosω) hsinω.le) hx0
  have hpieces : (Θ.directions.sup' Θ.nonempty fun t ↦
      min (affineValue (capBAffine K t) x)
        (affineValue (capDAffine K t) x)) ≤
      affineValue (fanAffine Θ.angle) x := by
    apply (Finset.sup'_le_iff Θ.nonempty _).2
    intro t ht
    apply (min_le_right _ _).trans
    have htt := Θ.interior t ht
    have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
    have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
    have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
    have hgap : 0 < (wedgeGaps K.val t).2 :=
      hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
    rw [wedgeGaps_snd_eq_supportValue] at hgap
    have hCx : C 0 = -L * Real.sin Θ.angle := by
      change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
      rw [hCeq]
      simp [tangentVector, frame]
    have hsupport :
        supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 <
          L * Real.cos (Θ.angle - t) := by
      have hdiv := sub_pos.mp hgap
      exact (div_lt_iff₀ hcosδ).mp hdiv
    have hnum : Real.cos (Θ.angle - t) / Real.sin Θ.angle * x +
        supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 < 0 := by
      have hcoef : 0 < Real.cos (Θ.angle - t) / Real.sin Θ.angle :=
        div_pos hcosδ hsinω
      have hxC : x ≤ C 0 := by simpa [C] using hx
      have hx' : x ≤ -L * Real.sin Θ.angle := hCx ▸ hxC
      have hmul := mul_le_mul_of_nonneg_left hx' hcoef.le
      have hrhs : Real.cos (Θ.angle - t) / Real.sin Θ.angle *
          (-L * Real.sin Θ.angle) = -L * Real.cos (Θ.angle - t) := by
        field_simp [hsinω.ne']
      rw [hrhs] at hmul
      nlinarith
    have hdiff : affineValue (capDAffine K t) x -
        affineValue (fanAffine Θ.angle) x =
        (Real.cos (Θ.angle - t) / Real.sin Θ.angle * x +
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos t := by
      simp only [affineValue, capDAffine, fanAffine]
      rw [Real.cos_sub]
      field_simp [hcost.ne', hsinω.ne']
      ring
    rw [sub_eq_iff_eq_add] at hdiff
    rw [hdiff]
    have hdiv := div_nonpos_of_nonpos_of_nonneg hnum.le hcost.le
    linarith
  unfold capBoundaryHeight
  rw [max_eq_left hpieces, max_eq_right hfan_nonneg]

/-- The right cap contact lies on the boundary graph. -/
theorem pointOnGraph_capBoundaryHeight_rightEndpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    pointOnGraph (capBoundaryHeight K) (((capVertices K.val 0).1.2) 0) =
      (capVertices K.val 0).1.2 := by
  have hAeq := capVertices_zero_snd_eq K
  have hh := capBoundaryHeight_eq_zero_of_right K
    (x := ((capVertices K.val 0).1.2) 0) le_rfl
  ext i
  fin_cases i
  · rfl
  · change capBoundaryHeight K (((capVertices K.val 0).1.2) 0) =
      ((capVertices K.val 0).1.2) 1
    rw [hh, hAeq]
    simp [normalVector, frame]

/-- The left cap contact lies on the boundary graph. -/
theorem pointOnGraph_capBoundaryHeight_leftEndpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    pointOnGraph (capBoundaryHeight K) (((capVertices K.val Θ.angle).2.1) 0) =
      (capVertices K.val Θ.angle).2.1 := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hh := capBoundaryHeight_eq_fanAffine_of_left K
    (x := ((capVertices K.val Θ.angle).2.1) 0) le_rfl
  change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
  ext i
  fin_cases i
  · rfl
  · change capBoundaryHeight K (C 0) = C 1
    change capBoundaryHeight K (((capVertices K.val Θ.angle).2.1) 0) = C 1
    rw [hh]
    have hCxy : C 0 = -L * Real.sin Θ.angle ∧
        C 1 = L * Real.cos Θ.angle := by
      rw [hCeq]
      simp [tangentVector, frame]
    rw [hCxy.1, hCxy.2]
    simp [affineValue, fanAffine]
    field_simp [(Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).ne']

/-- The open ray to the right of a polygon-cap boundary is the right graph tail. -/
theorem capRightOpenRay_eq_graph_image {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    {q | ∃ s : ℝ, 0 < s ∧
      q = (capVertices K.val 0).1.2 + s • normalVector 0} =
      pointOnGraph (capBoundaryHeight K) ''
        Set.Ioi (((capVertices K.val 0).1.2) 0) := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  have hAy : A 1 = 0 := by
    change A = supportValue K.val.val (0 : Real.Angle) •
      normalVector (0 : Real.Angle) at hAeq
    rw [hAeq]
    simp [normalVector, frame]
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨A 0 + s, ?_, ?_⟩
    · change ((capVertices K.val 0).1.2) 0 < A 0 + s
      simpa [A] using (show A 0 < A 0 + s by linarith)
    · have hh := capBoundaryHeight_eq_zero_of_right K
        (x := A 0 + s) (by simpa [A] using (show A 0 ≤ A 0 + s by linarith))
      ext i
      fin_cases i <;> simp [pointOnGraph, hh, A, hAy, normalVector, frame]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - A 0, ?_, ?_⟩
    · exact sub_pos.mpr (by simpa [A] using hx)
    · have hh := capBoundaryHeight_eq_zero_of_right K
        (x := x) (by simpa [A] using hx.le)
      ext i
      fin_cases i <;> simp [pointOnGraph, hh, A, hAy, normalVector, frame]

/-- The open ray to the left of a polygon-cap boundary is the left graph tail. -/
theorem capLeftOpenRay_eq_graph_image {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    {q | ∃ s : ℝ, 0 < s ∧ q = (capVertices K.val Θ.angle).2.1 +
      s • tangentVector (Θ.angle : Real.Angle)} =
      pointOnGraph (capBoundaryHeight K) ''
        Set.Iio (((capVertices K.val Θ.angle).2.1) 0) := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
    (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))
  have hCxy : C 0 = -L * Real.sin Θ.angle ∧ C 1 = L * Real.cos Θ.angle := by
    change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
    rw [hCeq]
    simp [tangentVector, frame]
  ext q
  constructor
  · rintro ⟨s, hspos, rfl⟩
    let x := C 0 - s * Real.sin Θ.angle
    have hx : x < C 0 := by dsimp [x]; nlinarith
    refine ⟨x, by simpa [C] using hx, ?_⟩
    have hh := capBoundaryHeight_eq_fanAffine_of_left K
      (x := x) (by simpa [C] using hx.le)
    ext i
    fin_cases i
    · change x = C 0 + s * (-Real.sin Θ.angle)
      dsimp [x]
      ring
    · change capBoundaryHeight K x = C 1 + s * Real.cos Θ.angle
      rw [hh, hCxy.2]
      simp only [affineValue, fanAffine, add_zero]
      dsimp [x]
      rw [hCxy.1]
      field_simp [hs.ne']
      ring
  · rintro ⟨x, hx, rfl⟩
    let s := (C 0 - x) / Real.sin Θ.angle
    have hspos : 0 < s := div_pos (sub_pos.mpr (by simpa [C] using hx)) hs
    refine ⟨s, hspos, ?_⟩
    have hh := capBoundaryHeight_eq_fanAffine_of_left K
      (x := x) (by simpa [C] using hx.le)
    ext i
    fin_cases i
    · change x = C 0 + s * (-Real.sin Θ.angle)
      dsimp [s]
      field_simp [hs.ne']
      ring
    · change capBoundaryHeight K x = C 1 + s * Real.cos Θ.angle
      rw [hh, hCxy.2]
      simp only [affineValue, fanAffine, add_zero]
      dsimp [s]
      rw [hCxy.1]
      field_simp [hs.ne']
      ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline Definition
-/

public section

noncomputable section

namespace MovingSofa

/-- The open ray starting at `p` in direction `v`, excluding its initial point. -/
def openRay (p v : Point) : Set Point :=
  {q | ∃ s : ℝ, 0 < s ∧ q = p + s • v}

/-- The polyline and two disjoint endpoint rays describe the fan-minus-niche frontier. -/
def IsCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (p : XMonotonePolylineData) : Prop :=
  0 < p.edges ∧
  p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
  p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
  (∀ i : Fin p.edges, ∃ t : angleDomain Θ,
    inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0) ∧
  IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) ∧
  frontier (capFan Θ.angle \ polygonNiche Θ K.val) =
    openRay ((capVertices K.val Θ.angle).2.1) (tangentVector (Θ.angle : Real.Angle)) ∪
      p.carrier ∪ openRay ((capVertices K.val 0).1.2) (normalVector 0) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))) p.carrier ∧
  Disjoint p.carrier (openRay ((capVertices K.val 0).1.2) (normalVector 0)) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle)))
    (openRay ((capVertices K.val 0).1.2) (normalVector 0))

theorem polygonCap_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    ∃ p : XMonotonePolylineData, IsCapPolyline K p := by
  let C := (capVertices K.val Θ.angle).2.1
  let A := (capVertices K.val 0).1.2
  have hCA : C 0 < A 0 := polygonCap_left_x_lt_right_x K
  obtain ⟨p, hpedge, hpC, hpA, hcarrier, hedge⟩ :=
    exists_capBoundary_graphPolyline K hCA
  refine ⟨p, hpedge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpC]
    exact pointOnGraph_capBoundaryHeight_leftEndpoint K
  · rw [hpA]
    exact pointOnGraph_capBoundaryHeight_rightEndpoint K
  · intro i
    obtain ⟨t, ht, hi⟩ := hedge i
    exact ⟨⟨t, ht⟩, hi⟩
  · exact (capFan_sdiff_polygonNiche_closed_frontier K).1
  · rw [(capFan_sdiff_polygonNiche_closed_frontier K).2,
      show openRay ((capVertices K.val Θ.angle).2.1)
        (tangentVector (Θ.angle : Real.Angle)) = _ by
          simpa [openRay] using capLeftOpenRay_eq_graph_image K,
      show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
          simpa [openRay] using capRightOpenRay_eq_graph_image K, hcarrier]
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      rcases lt_or_ge x (C 0) with hx | hx
      · apply Or.inl
        apply Or.inl
        exact ⟨x, by simpa [C] using hx, rfl⟩
      · rcases le_or_gt x (A 0) with hxA | hxA
        · apply Or.inl
          apply Or.inr
          exact ⟨x, ⟨hx, hxA⟩, rfl⟩
        · apply Or.inr
          exact ⟨x, by simpa [A] using hxA, rfl⟩
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) <;>
        exact ⟨x, rfl⟩
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K, hcarrier]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    exact (not_lt_of_ge hy.1) hx'
  · rw [hcarrier, show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hy' : A 0 < x := by simpa [A] using hy
    exact (not_lt_of_ge hx.2) hy'
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K,
    show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    have hy' : A 0 < x := by simpa [A] using hy
    linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Polyline
-/

public section

noncomputable section

namespace MovingSofa

/-- A chosen monotone polyline describing the polygonal cap’s niche boundary. -/
def polygonCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ) : XMonotonePolylineData :=
  (polygonCap_polyline K).choose

/-- Sum the lengths of polyline edges perpendicular to a prescribed wall direction. -/
@[expose]
def polygonCapPolylineLength {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : ℝ := by
  classical
  let p := polygonCapPolyline K
  exact ∑ i : Fin p.edges,
    if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0 then
      dist (p.vertices i.castSucc) (p.vertices i.succ) else 0

/-- The cap’s surface measure at each wall direction equals the corresponding polyline length. -/
@[expose]
def IsBalancedPolygonCap {Θ : AngleSet} (K : PolygonCapSpace Θ) : Prop :=
  ∀ t : angleDomain Θ, surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} =
    ENNReal.ofReal (polygonCapPolylineLength K t)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Upper Boundary / Polygon
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory

private lemma PolygonCapSpace.eq_of_mem_of_fst_eq_of_fst_extremal {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 = b 0)
    (hext : (∀ q ∈ (K.val.val : Set Point), q 0 ≤ a 0) ∨
      (∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)) : a = b := by
  apply ConvexBody.eq_of_mem_of_fst_eq_of_fst_extremal K.val.val
    (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle)
    _ K.property _ ha hb hab hext
  · have hfinite : (angleDomain Θ).Finite := by
      unfold angleDomain
      exact (Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
          (Set.toFinite _)
    exact (hfinite.image _).union (by simp [capLowerNormals])
  · intro t ht
    rcases ht with ⟨r, hr, rfl⟩ | ht
    · exact (Real.sin_pos_of_pos_of_lt_pi
        (angleDomain_subset_Ioo Θ hr).1 (angleDomain_subset_Ioo Θ hr).2).ne'
    · simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · change Real.sin (Θ.angle + Real.pi) ≠ 0
        rw [Real.sin_add_pi]
        exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (by linarith [Θ.angle_le, Real.pi_pos])).ne'
      · change Real.sin (3 * Real.pi / 2) ≠ 0
        norm_num [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
          Real.sin_add]

private def upperSupportAffine (K : ConvexBody Point) (t : ℝ) : ℝ × ℝ :=
  (-Real.cos t / Real.sin t, supportValue K (t : Real.Angle) / Real.sin t)

private def upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) : ℝ :=
  D.inf' hne (fun t ↦ affineValue (upperSupportAffine K t) x)

private lemma continuous_upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) : Continuous (upperSupportHeight K D hne) := by
  apply Continuous.finset_inf'_apply hne
  intro t ht
  exact continuous_affineValue _

private lemma upperSupportHeight_eq_affineValue (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) :
    ∃ c ∈ D.image (upperSupportAffine K),
      upperSupportHeight K D hne x = affineValue c x := by
  obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_inf' hne
    (fun t ↦ affineValue (upperSupportAffine K t) x)
  exact ⟨upperSupportAffine K t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, heq⟩

private lemma inner_le_support_iff_snd_le_affine (K : ConvexBody Point)
    {t : ℝ} (ht : 0 < Real.sin t) (q : Point) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue K (t : Real.Angle) ↔
      q 1 ≤ affineValue (upperSupportAffine K t) (q 0) := by
  have hformula : affineValue (upperSupportAffine K t) (q 0) =
      (supportValue K (t : Real.Angle) - q 0 * Real.cos t) / Real.sin t := by
    simp only [affineValue, upperSupportAffine]
    ring
  rw [hformula, le_div_iff₀ ht]
  simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
    RCLike.inner_apply, conj_trivial, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor <;> intro h <;> nlinarith

private lemma snd_le_upperSupportHeight_iff (K : ConvexBody Point)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : ∀ t ∈ D, 0 < Real.sin t) (q : Point) :
    q 1 ≤ upperSupportHeight K D hne (q 0) ↔
      ∀ t ∈ D, inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue K (t : Real.Angle) := by
  rw [upperSupportHeight, Finset.le_inf'_iff]
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦
    (inner_le_support_iff_snd_le_affine K (hD t ht) q).symm

private lemma PolygonCapSpace.mem_iff_mem_capFan_and_support_le {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (p : Point) :
    p ∈ (K.val.val : Set Point) ↔ p ∈ capFan Θ.angle ∧
      ∀ t ∈ angleDomain Θ,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val.val (t : Real.Angle) := by
  constructor
  · intro hp
    exact ⟨K.val.subset_capFan hp, fun t _ ↦ inner_le_supportValue K.val.val hp _⟩
  · rintro ⟨hp, hupper⟩
    rw [K.property.eq_iInter_supportValue]
    simp only [Set.mem_iInter]
    intro a ha
    rcases ha with ⟨t, ht, rfl⟩ | ha
    · exact hupper t ht
    rcases ha with rfl | rfl
    · change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.1
    · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.2

private lemma mem_capFan_of_fst_eq_of_snd_le {ω : ℝ} (hω : 0 ≤ Real.sin ω)
    {p q : Point} (hp : p ∈ capFan ω) (hx : p 0 = q 0) (hy : p 1 ≤ q 1) :
    q ∈ capFan ω := by
  change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
  change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hp
  simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add] at hp ⊢
  rw [hx] at hp
  constructor
  · nlinarith [hp.1, mul_nonneg hω (sub_nonneg.mpr hy)]
  · exact hp.2.trans hy

private lemma pointOnGraph_upperSupportHeight_mem {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {x : ℝ}
    (hx : ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    pointOnGraph (upperSupportHeight K.val.val D hne) x ∈ (K.val.val : Set Point) := by
  obtain ⟨q, hq, hqx⟩ := hx
  have hqle : q 1 ≤ upperSupportHeight K.val.val D hne x := by
    rw [← hqx, snd_le_upperSupportHeight_iff K.val.val D hne hsin]
    exact fun t _ ↦ inner_le_supportValue K.val.val hq _
  apply (K.mem_iff_mem_capFan_and_support_le _).mpr
  constructor
  · apply mem_capFan_of_fst_eq_of_snd_le
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos]))) (K.val.subset_capFan hq)
    · exact hqx
    · exact hqle
  · intro t ht
    have htD : t ∈ D := by change t ∈ (D : Set ℝ); rwa [hD]
    apply (inner_le_support_iff_snd_le_affine K.val.val (hsin t htD) _).mpr
    change upperSupportHeight K.val.val D hne x ≤
      affineValue (upperSupportAffine K.val.val t) x
    exact Finset.inf'_le _ htD

private lemma exists_upperSupportHeight_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {a b : ℝ} (hab : a < b)
    (hfeasible : ∀ x ∈ Set.Icc a b, ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph (upperSupportHeight K.val.val D hne) a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph (upperSupportHeight K.val.val D hne) b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc a b ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  obtain ⟨p, hp, hpa, hpb, hcarrier, hvertices, hpieces⟩ :=
    exists_graphPolyline_of_finite_affine_selector hab (D.image (upperSupportAffine K.val.val))
      (continuous_upperSupportHeight K.val.val D hne).continuousOn
      (fun x _ ↦ upperSupportHeight_eq_affineValue K.val.val D hne x)
  refine ⟨p, hp, hpa, hpb, hcarrier, ?_, ?_⟩
  · rw [hcarrier]
    rintro q ⟨x, hx, rfl⟩
    exact pointOnGraph_upperSupportHeight_mem K D hne hD hsin (hfeasible x hx)
  · intro i
    obtain ⟨c, hc, heq⟩ := hpieces i
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨t, ht, ?_, ?_⟩
    · rw [hvertices i.succ, hvertices i.castSucc]
      apply inner_pointOnGraph_sub_normalVector_eq_zero heq
        (p.increasing i.castSucc_lt_succ).le
      dsimp [upperSupportAffine]
      field_simp [(hsin t ht).ne']
      ring
    · have hstart := heq ⟨le_rfl, (p.increasing i.castSucc_lt_succ).le⟩
      rw [hvertices i.castSucc]
      simp only [pointOnGraph, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      simp only [Real.Angle.cos_coe, Real.Angle.sin_coe]
      change Real.cos t * (p.vertices i.castSucc) 0 +
        Real.sin t * upperSupportHeight K.val.val D hne ((p.vertices i.castSucc) 0) = _
      rw [hstart]
      dsimp [upperSupportAffine, affineValue]
      field_simp [(hsin t ht).ne']
      ring

private lemma exists_upperSupportHeight_polyline_with_endpoints {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 < b 0)
    (hmin : ∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)
    (hmax : ∀ q ∈ (K.val.val : Set Point), q 0 ≤ b 0) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧ p.vertices 0 = a ∧
      p.vertices (Fin.last p.edges) = b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc (a 0) (b 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  have hsin : ∀ t ∈ D, 0 < Real.sin t := by
    intro t ht
    have ht' : t ∈ angleDomain Θ := hD ▸ ht
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ht').1
      (angleDomain_subset_Ioo Θ ht').2
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ :=
    exists_upperSupportHeight_polyline K D hne hD hsin hab
      (fun _ hx ↦ ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val ha hb hab hx)
  refine ⟨p, hp, ?_, ?_, hc, hK, hn⟩
  · rw [hpa]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨a, ha, rfl⟩) ha rfl
    exact Or.inr hmin
  · rw [hpb]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨b, hb, rfl⟩) hb rfl
    exact Or.inl hmax

/-- The terminal cap contacts bound every horizontal coordinate of a polygon cap. -/
lemma PolygonCapSpace.capVertices_fst_bounds {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {q : Point} (hq : q ∈ (K.val.val : Set Point)) :
    ((capVertices K.val Θ.angle).2.1) 0 ≤ q 0 ∧
      q 0 ≤ ((capVertices K.val 0).1.2) 0 := by
  constructor
  · rw [capVertices_angle_fst_eq]
    have hu := (K.val.subset_capFan hq).1
    have hv := inner_le_supportValue K.val.val hq
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    have hs : 0 ≤ Real.sin Θ.angle := (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])).le
    have hc : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hu
    simp [normalVector, tangentVector, frame, PiLp.inner_apply,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two] at hu hv ⊢
    nlinarith [congrArg (fun z : ℝ ↦ z * q 0) (Real.sin_sq_add_cos_sq Θ.angle),
      mul_nonneg hu hc, mul_le_mul_of_nonneg_right hv hs,
      sq_nonneg (Real.sin Θ.angle), sq_nonneg (Real.cos Θ.angle)]
  · have hq' := inner_le_supportValue K.val.val hq (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ ((capVertices K.val 0).1.2) (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    simp [normalVector, frame, PiLp.inner_apply] at hq' hA
    linarith

private lemma PolygonCapSpace.exists_upperBoundary_polyline {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧
      p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
      p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  apply exists_upperSupportHeight_polyline_with_endpoints K D hne hD
    (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
    (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
    (polygonCap_left_x_lt_right_x K)
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).1
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).2

private lemma PolygonCapSpace.exposedEdge_eq_upperSupportGraph_inter {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {t : ℝ} (ht : t ∈ D) :
    exposedEdge K.val.val (t : Real.Angle) =
      (pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0)) ∩
      {q | inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle)} := by
  have hsin : ∀ r ∈ D, 0 < Real.sin r := by
    intro r hr
    have hr' : r ∈ angleDomain Θ := hD ▸ hr
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ hr').1
      (angleDomain_subset_Ioo Θ hr').2
  ext q
  constructor
  · rintro ⟨hq, heq⟩
    refine ⟨⟨q 0, K.capVertices_fst_bounds hq, ?_⟩, heq⟩
    have hle : q 1 ≤ upperSupportHeight K.val.val D hne (q 0) :=
      (snd_le_upperSupportHeight_iff K.val.val D hne hsin q).mpr
        (fun r _ ↦ inner_le_supportValue K.val.val hq _)
    have hge := Finset.inf'_le (fun r ↦ affineValue (upperSupportAffine K.val.val r) (q 0)) ht
    have haff : affineValue (upperSupportAffine K.val.val t) (q 0) = q 1 := by
      change inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle) at heq
      simp [normalVector, frame, PiLp.inner_apply] at heq
      dsimp [affineValue, upperSupportAffine]
      field_simp [(hsin t ht).ne']
      nlinarith [heq]
    have hy : upperSupportHeight K.val.val D hne (q 0) = q 1 :=
      le_antisymm (haff ▸ hge) hle
    ext i
    fin_cases i
    · rfl
    · exact hy
  · rintro ⟨⟨x, hx, rfl⟩, heq⟩
    refine ⟨pointOnGraph_upperSupportHeight_mem K D hne hD hsin ?_, heq⟩
    exact ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val
      (edgeVertices_fst_mem K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
      (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
      (polygonCap_left_x_lt_right_x K) hx

/-- The sine-weighted exposed-face lengths equal the horizontal separation of cap contacts. -/
lemma PolygonCapSpace.sum_hausdorffMeasure_exposedEdge_mul_sin {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal *
      Real.sin t = ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ := K.exists_upperBoundary_polyline D hne hD
  have hangle : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi := by
    intro t ht
    exact angleDomain_subset_Ioo Θ (hD ▸ ht)
  have hface (t : ℝ) (ht : t ∈ D) :
      (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal =
        ∑ i : Fin p.edges,
          if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
            (normalVector (t : Real.Angle)) = 0 then
            dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
    rw [K.exposedEdge_eq_upperSupportGraph_inter D hne hD ht, ← hc]
    apply p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    intro i hi
    obtain ⟨r, hr, horth, hstart⟩ := hn i
    have hrt := eq_of_inner_sub_normalVector_eq_zero (hangle r hr) (hangle t ht)
      (p.increasing i.castSucc_lt_succ) horth hi
    subst r
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨c, hcoef, rfl⟩ := hq
    change inner ℝ (p.vertices i.castSucc + c •
      (p.vertices i.succ - p.vertices i.castSucc)) (normalVector (t : Real.Angle)) = _
    rw [inner_add_left, real_inner_smul_left, hi, mul_zero, add_zero, hstart]
  calc
    _ = ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hface t ht]
    _ = _ := by
      rw [p.sum_normal_lengths_mul_sin D hangle
        (fun i ↦ by obtain ⟨t, ht, ho, _⟩ := hn i; exact ⟨t, ht, ho⟩), hpa, hpb]

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.Area.Evaluator`.
* `Gerver.Area.CapFan`.
* `Gerver.Area.NicheCover`.
* `Gerver.Area`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Soundness of the contact evaluator

`GerverAreaCert.evalZ s z kind` evaluates one of the five phase formulas of Gerver's sofa,
and one of its four contact curves, on an interval of rotation angles.  This module proves
that it encloses the analytic value: `gerverBranch_eq` identifies the branch that the
piecewise vendor definitions `GerverSofa.Romik.path` and `GerverSofa.PartC.alphaBetaAt`
select, the five per-stage lemmas verify the phase formulas and the two velocity
coefficients against `GerverSofa.Romik.path1 … path5` and
`GerverSofa.Romik.alphaBeta1 … alphaBeta5`, and `evalZ_sound` assembles them through the
coordinate dictionary `fromPlane_paperGerverContacts`.  `contactZ_sound` and
`evalZ_interval_sound` specialise this to a grid angle and to a whole grid subinterval.
-/

/-! ### The contact evaluator -/

public section

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-- The five certified phase maps, selected by stage index. -/
def gerverBranchPath : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.path1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.path2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.path3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.path4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.path5 GerverSofa.PartB.params

/-- The five certified velocity-coefficient pairs, selected by stage index. -/
def gerverBranchAlphaBeta : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params

/-- On a grid angle of stage `s` both piecewise definitions select branch `s`. -/
theorem gerverBranch_eq (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {x : ℝ}
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x) :
    GerverSofa.Romik.path GerverSofa.PartB.params x = gerverBranchPath s x ∧
      GerverSofa.PartC.alphaBetaAt x = gerverBranchAlphaBeta s x := by
  have o12 : GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta := by
    have := gerverStageTime_lt_succ 1 (by norm_num)
    rwa [gerverStageTime_one, gerverStageTime_two] at this
  have o23 : GerverSofa.PartB.params.theta < GerverSofa.PartC.eta := by
    have := gerverStageTime_lt_succ 2 (by norm_num)
    rwa [gerverStageTime_two, gerverStageTime_three] at this
  have o34 : GerverSofa.PartC.eta < GerverSofa.PartC.tau := by
    have := gerverStageTime_lt_succ 3 (by norm_num)
    rwa [gerverStageTime_three, gerverStageTime_four] at this
  have hpath : GerverSofa.Romik.path GerverSofa.PartB.params x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.path1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.path2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.path3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.path4 GerverSofa.PartB.params x
      else GerverSofa.Romik.path5 GerverSofa.PartB.params x := rfl
  have hab : GerverSofa.PartC.alphaBetaAt x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params x
      else GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params x := rfl
  interval_cases s
  · rw [gerverStageTime_one] at hxhi
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_two] at hxhi
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := by
      have := hxlo (by norm_num)
      rw [gerverStageTime_one] at this
      exact not_le.mpr this
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_three] at hxhi
    have h2 : GerverSofa.PartB.params.theta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_two] at this
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_four] at hxhi
    have h3 : GerverSofa.PartC.eta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_three] at this
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
  · have h4 : GerverSofa.PartC.tau < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_four] at this
    have h3 : GerverSofa.PartC.eta < x := o34.trans h4
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl

/-- Transport an enclosure along an equality of the enclosed real number. -/
private theorem contains_of_eq_real {z : SI} {a b : ℝ} (hab : a = b) (h : SI.Contains z a) :
    SI.Contains z b := hab ▸ h

open SI in
/-- Stage-1 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage1_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 1 z 0).1 (gerverBranchPath 1 x).1 ∧
      SI.Contains (evalZ 1 z 0).2 (gerverBranchPath 1 x).2 ∧
      SI.Contains (evalZ 1 z 2).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 1 z 2).2
        ((gerverBranchPath 1 x).2 + (gerverBranchAlphaBeta 1 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).2
        ((gerverBranchPath 1 x).2 - (gerverBranchAlphaBeta 1 x).2 * Real.sin x) := by
  obtain ⟨hk11, hk12, -, -, -, -, -, -, -, -, ha1, ha2, -⟩ := contains_params
  have hf := contains_add (contains_add (contains_mul ha1 hcos) (contains_mul ha2 hsin))
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg ha2) hcos)
    (contains_mul ha1 hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hal := contains_add (contains_add (contains_mul (contains_imul (-2) ha1) hsin)
    (contains_mul (contains_imul 2 ha2) hcos)) (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 ha1) hcos)
    (contains_mul (contains_imul 2 ha2) hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk11
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk12
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path1,
      GerverSofa.Romik.alphaBeta1, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-2 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage2_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 2 z 0).1 (gerverBranchPath 2 x).1 ∧
      SI.Contains (evalZ 2 z 0).2 (gerverBranchPath 2 x).2 ∧
      SI.Contains (evalZ 2 z 2).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 2 z 2).2
        ((gerverBranchPath 2 x).2 + (gerverBranchAlphaBeta 2 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).2
        ((gerverBranchPath 2 x).2 - (gerverBranchAlphaBeta 2 x).2 * Real.sin x) := by
  obtain ⟨-, -, hk21, hk22, -, -, -, -, -, -, -, -, hb1, hb2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hb1 hz)) hb2
  have hg := contains_add (contains_add (contains_divn (b := 2) (by norm_num) hz)
    (contains_neg hb1)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_imul 2 hb1)) (contains_neg hz)
  have hbe := contains_add hf (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk21
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk22
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path2,
      GerverSofa.Romik.alphaBeta2, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-3 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage3_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 3 z 0).1 (gerverBranchPath 3 x).1 ∧
      SI.Contains (evalZ 3 z 0).2 (gerverBranchPath 3 x).2 ∧
      SI.Contains (evalZ 3 z 2).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 3 z 2).2
        ((gerverBranchPath 3 x).2 + (gerverBranchAlphaBeta 3 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).2
        ((gerverBranchPath 3 x).2 - (gerverBranchAlphaBeta 3 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, hk31, hk32, -, -, -, -, -, -, -, -, hc1, hc2, -⟩ := contains_params
  have hf := contains_sub hc1 hz
  have hg := contains_add hc2 hz
  have hal := contains_add (contains_ratI (a := -1) (b := 1) (by norm_num)) (contains_neg hg)
  have hbe := contains_add (contains_ratI (a := 1) (b := 1) (by norm_num)) hf
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk31
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk32
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
    simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path3,
      GerverSofa.Romik.alphaBeta3, GerverSofa.Romik.addK, GerverSofa.Romik.rot] <;>
    push_cast <;> ring

open SI in
/-- Stage-4 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage4_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 4 z 0).1 (gerverBranchPath 4 x).1 ∧
      SI.Contains (evalZ 4 z 0).2 (gerverBranchPath 4 x).2 ∧
      SI.Contains (evalZ 4 z 2).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 4 z 2).2
        ((gerverBranchPath 4 x).2 + (gerverBranchAlphaBeta 4 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).2
        ((gerverBranchPath 4 x).2 - (gerverBranchAlphaBeta 4 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, hk41, hk42, -, -, -, -, -, -, -, -, hd1, hd2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_neg (contains_divn (b := 2) (by norm_num) hz)) hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hd1 hz)) hd2
  have hal := contains_add (contains_neg hg) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_imul 2 hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))) (contains_neg hz)
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk41
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk42
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path4,
      GerverSofa.Romik.alphaBeta4, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-5 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage5_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 5 z 0).1 (gerverBranchPath 5 x).1 ∧
      SI.Contains (evalZ 5 z 0).2 (gerverBranchPath 5 x).2 ∧
      SI.Contains (evalZ 5 z 2).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 5 z 2).2
        ((gerverBranchPath 5 x).2 + (gerverBranchAlphaBeta 5 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).2
        ((gerverBranchPath 5 x).2 - (gerverBranchAlphaBeta 5 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, -, -, hk51, hk52, -, -, -, -, -, -, -, -, he1, he2, -⟩ :=
    contains_params
  have hf := contains_add (contains_add (contains_mul he1 hcos) (contains_mul he2 hsin))
    (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg he2) hcos)
    (contains_mul he1 hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_mul (contains_imul (-2) he1) hsin)) (contains_mul (contains_imul 2 he2) hcos)
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 he1) hcos)
    (contains_mul (contains_imul 2 he2) hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk51
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk52
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path5,
      GerverSofa.Romik.alphaBeta5, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

/-- Per-stage soundness of the phase-map evaluation, i.e. of the `kind = 0` output.
Pure interval arithmetic against `GerverSofa.Romik.path1 … path5`: five cases, each a chain
of `SI.contains_*` applications on top of `contains_params`, `hsin` and `hcos`. -/
theorem evalZ_zero_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 0).1 (gerverBranchPath s x).1 ∧
      SI.Contains (evalZ s z 0).2 (gerverBranchPath s x).2 := by
  interval_cases s
  · exact ⟨(evalZ_stage1_sound hsin hcos).1, (evalZ_stage1_sound hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage2_sound hz hsin hcos).1, (evalZ_stage2_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage3_sound hz hsin hcos).1, (evalZ_stage3_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage4_sound hz hsin hcos).1, (evalZ_stage4_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage5_sound hsin hcos).1, (evalZ_stage5_sound hsin hcos).2.1⟩

/-- Per-stage soundness of the `B` and `D` offsets, i.e. of the two velocity
coefficients `α` and `β` against `GerverSofa.Romik.alphaBeta1 … alphaBeta5`.  Note
`evalZ s z 1 = evalZ s z 2` shifted by `(cos x, sin x)` and
`evalZ s z 3 = evalZ s z 4` shifted by `(-sin x, cos x)`, so the remaining two kinds need no
separate stage analysis. -/
theorem evalZ_offset_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 2).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).1 * Real.sin x) ∧
      SI.Contains (evalZ s z 2).2
        ((gerverBranchPath s x).2 + (gerverBranchAlphaBeta s x).1 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).2 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).2
        ((gerverBranchPath s x).2 - (gerverBranchAlphaBeta s x).2 * Real.sin x) := by
  interval_cases s
  · exact (evalZ_stage1_sound hsin hcos).2.2
  · exact (evalZ_stage2_sound hz hsin hcos).2.2
  · exact (evalZ_stage3_sound hz hsin hcos).2.2
  · exact (evalZ_stage4_sound hz hsin hcos).2.2
  · exact (evalZ_stage5_sound hsin hcos).2.2

/-- Soundness of the executable phase/contact evaluator: on the branch that the
piecewise definitions select, the interval evaluation encloses both coordinates of the
selected curve.  Reduces to `gerverBranch_eq`, `evalZ_zero_sound`, `evalZ_offset_sound`,
`trigZ_sound` and the coordinate dictionary
`fromPlane_paperGerverContacts` (`GerverSofa.u t = (cos t, sin t)`,
`GerverSofa.v t = (-sin t, cos t)`). -/
theorem evalZ_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hx0 : 0 ≤ x) (hxT : x ≤ Real.pi / 2)
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x)
    (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (evalZ s z kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ s z kind).2 (gerverContactPoint kind x 1) := by
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_d2]
  obtain ⟨hsin, hcos⟩ := trigZ_sound hz hx0 hx2
  obtain ⟨hp, hab⟩ := gerverBranch_eq s hs1 hs5 hxhi hxlo
  obtain ⟨h0x, h0y⟩ := evalZ_zero_sound s hs1 hs5 hz hsin hcos
  obtain ⟨h2x, h2y, h4x, h4y⟩ := evalZ_offset_sound s hs1 hs5 hz hsin hcos
  have ht : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx0, hxT⟩
  -- The four contact curves in terms of the branch phase map and coefficients.
  set P : ℝ × ℝ := gerverBranchPath s x with hPdef
  set AB : ℝ × ℝ := gerverBranchAlphaBeta s x with hABdef
  have hpath1 : (GerverSofa.Romik.path GerverSofa.PartB.params x).1 = P.1 := by rw [hp]
  have hpath2 : (GerverSofa.Romik.path GerverSofa.PartB.params x).2 = P.2 := by rw [hp]
  have hal : (GerverSofa.PartC.alphaBetaAt x).1 = AB.1 := by rw [hab]
  have hbe : (GerverSofa.PartC.alphaBetaAt x).2 = AB.2 := by rw [hab]
  have hdA1 : gerverContactPoint 1 x 0 = P.1 - AB.1 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 1 x 0 = (GerverSofa.PartC.A x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 + (GerverSofa.u x).1 = _
    rw [hpath1, hal]
    change P.1 + AB.1 * (-Real.sin x) + Real.cos x = _
    ring
  have hdA2 : gerverContactPoint 1 x 1 = P.2 + AB.1 * Real.cos x + Real.sin x := by
    have h' : gerverContactPoint 1 x 1 = (GerverSofa.PartC.A x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 + (GerverSofa.u x).2 = _
    rw [hpath2, hal]
    change P.2 + AB.1 * Real.cos x + Real.sin x = _
    ring
  have hdB1 : gerverContactPoint 2 x 0 = P.1 - AB.1 * Real.sin x := by
    have h' : gerverContactPoint 2 x 0 = (GerverSofa.PartC.B x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 = _
    rw [hpath1, hal]
    change P.1 + AB.1 * (-Real.sin x) = _
    ring
  have hdB2 : gerverContactPoint 2 x 1 = P.2 + AB.1 * Real.cos x := by
    have h' : gerverContactPoint 2 x 1 = (GerverSofa.PartC.B x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 = _
    rw [hpath2, hal]
    rfl
  have hdC1 : gerverContactPoint 3 x 0 = P.1 - AB.2 * Real.cos x - Real.sin x := by
    have h' : gerverContactPoint 3 x 0 = (GerverSofa.PartC.C x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 + (GerverSofa.v x).1 = _
    rw [hpath1, hbe]
    change P.1 - AB.2 * Real.cos x + -Real.sin x = _
    ring
  have hdC2 : gerverContactPoint 3 x 1 = P.2 - AB.2 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 3 x 1 = (GerverSofa.PartC.C x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 + (GerverSofa.v x).2 = _
    rw [hpath2, hbe]
    rfl
  have hdD1 : gerverContactPoint 4 x 0 = P.1 - AB.2 * Real.cos x := by
    have h' : gerverContactPoint 4 x 0 = (GerverSofa.PartC.D x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 = _
    rw [hpath1, hbe]
    rfl
  have hdD2 : gerverContactPoint 4 x 1 = P.2 - AB.2 * Real.sin x := by
    have h' : gerverContactPoint 4 x 1 = (GerverSofa.PartC.D x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    change (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 = _
    rw [hpath2, hbe]
    rfl
  have hd01 : gerverContactPoint 0 x 0 = P.1 := hpath1
  have hd02 : gerverContactPoint 0 x 1 = P.2 := hpath2
  -- The `A` and `C` outputs are the `B` and `D` outputs shifted by the frame vectors.
  have eA1 : (evalZ s z 1).1 = SI.add (evalZ s z 2).1 (trigZ z).2 := rfl
  have eA2 : (evalZ s z 1).2 = SI.add (evalZ s z 2).2 (trigZ z).1 := rfl
  have eC1 : (evalZ s z 3).1 = SI.sub (evalZ s z 4).1 (trigZ z).1 := rfl
  have eC2 : (evalZ s z 3).2 = SI.add (evalZ s z 4).2 (trigZ z).2 := rfl
  interval_cases kind
  · exact ⟨hd01 ▸ h0x, hd02 ▸ h0y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdA1, eA1]
      exact SI.contains_add h2x hcos
    · rw [hdA2, eA2]
      exact SI.contains_add h2y hsin
  · exact ⟨hdB1 ▸ h2x, hdB2 ▸ h2y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdC1, eC1]
      exact SI.contains_sub h4x hsin
    · rw [hdC2, eC2]
      exact SI.contains_add h4y hcos
  · exact ⟨hdD1 ▸ h4x, hdD2 ▸ h4y⟩

/-- The left endpoint of the branch selected at the right end of a grid subinterval
does not exceed the left end of that subinterval. -/
theorem stageTime_pred_le_gerverGridTime (m : ℕ) (hm : m + 1 ≤ 5 * NN)
    (h2 : 2 ≤ stageOf (m + 1)) :
    gerverStageTime (stageOf (m + 1) - 1) ≤ gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ (m + 1) / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hk : (m + 1) / NN * NN = m + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have hstep : ((m + 1) / NN - 1) * NN = m + 1 - NN := by rw [Nat.sub_one_mul, hk]
    have hle : ((m + 1) / NN - 1) * NN ≤ m := by rw [hstep]; omega
    rw [max_eq_right (Nat.le_of_succ_le hd), ← gerverGridTime_mul_NN ((m + 1) / NN - 1)]
    exact gerverGridTime_le_of_le hle (by omega)
  · rw [Nat.add_sub_cancel]
    have hle1 : (m + 1) / NN * NN ≤ m + 1 := Nat.div_mul_le_self (m + 1) NN
    have hne : (m + 1) / NN * NN ≠ m + 1 := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have hle : (m + 1) / NN * NN ≤ m := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle1 hne)
    rw [← gerverGridTime_mul_NN ((m + 1) / NN)]
    exact gerverGridTime_le_of_le hle (by omega)

/-- The evaluator at a grid angle. -/
theorem contactZ_sound (m : ℕ) (hm : m ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (contactZ m kind).1 (gerverContactPoint kind (gerverGridTime m) 0) ∧
      SI.Contains (contactZ m kind).2 (gerverContactPoint kind (gerverGridTime m) 1) := by
  obtain ⟨h1, h5⟩ := stageOf_mem m hm
  obtain ⟨hg0, hgT⟩ := gerverGridTime_mem_Icc m hm
  exact evalZ_sound (stageOf m) h1 h5 (ttZ_sound m hm) hg0 hgT
    (gerverGridTime_le_stageTime m hm) (fun h ↦ stageTime_lt_gerverGridTime m hm h) kind hk

/-- The evaluator over a whole grid subinterval, on the branch selected at its right
endpoint (which is the branch of every angle in the half-open subinterval). -/
theorem evalZ_interval_sound (m : ℕ) (hm : m + 1 ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4)
    {x : ℝ} (hx : x ∈ Set.Ioc (gerverGridTime m) (gerverGridTime (m + 1))) :
    SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).2 (gerverContactPoint kind x 1) := by
  have hmm : m ≤ 5 * NN := by omega
  obtain ⟨hxl, hxr⟩ := hx
  obtain ⟨h1, h5⟩ := stageOf_mem (m + 1) hm
  obtain ⟨hg0, -⟩ := gerverGridTime_mem_Icc m hmm
  obtain ⟨-, hgT⟩ := gerverGridTime_mem_Icc (m + 1) hm
  have hM := SI.Mpos
  have hz : SI.Contains (⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ : SI) x := by
    obtain ⟨ha, -⟩ := ttZ_sound m hmm
    obtain ⟨-, hb⟩ := ttZ_sound (m + 1) hm
    exact ⟨ha.trans (mul_le_mul_of_nonneg_left hxl.le hM.le),
      (mul_le_mul_of_nonneg_left hxr hM.le).trans hb⟩
  refine evalZ_sound (stageOf (m + 1)) h1 h5 hz (hg0.trans hxl.le) (hxr.trans hgT)
    (hxr.trans (gerverGridTime_le_stageTime (m + 1) hm)) (fun h2 ↦ ?_) kind hk
  exact lt_of_le_of_lt (stageTime_pred_le_gerverGridTime m hm h2) hxl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The support-contact fan of the Gerver outer cap

The literal Gerver outer cap is a compact convex subset of the plane lying in the closed
quadrant above the fan anchor `L = C (π / 2)`, which sits on the wall.  The `640` listed
contacts `A (t)` and `C (t)` at the grid angles attain the cap support at the strictly
increasing normals `t` and `t + π / 2` of `[0, π)`, so `supportContact_fan_area` bounds the
cap area below by half the shoelace sum of the fan over the anchor.  The certificate
encloses that sum (`capDoubledZ_sound`), and its kernel-checked numeric conclusion
`GerverAreaCert.capOK_true` turns the enclosure into `28609 / 10000 ≤ |K₀|`.
-/

/-! ### Elementary geometry of the outer cap -/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-- The paper path starts at the origin. -/
theorem paperGerverPath_zero : paperGerverPath 0 = 0 := by
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  change GerverSofa.PartF.Coordinates.toPlane
    (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
  rw [hreg.2.1]
  ext i
  fin_cases i <;> rfl

/-- The outer cap written as an intersection of closed half-planes. -/
theorem gerverOuterCap_eq_iInter :
    gerverOuterCap =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ q (normalVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1} ∩
            {q : Point | inner ℝ q (tangentVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}) := by
  ext q
  simp only [gerverOuterCap, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter₂,
    inner_normalVector_pi_div_two]

/-- The outer cap is closed, being an intersection of closed half-spaces. -/
theorem isClosed_gerverOuterCap : IsClosed gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine IsClosed.inter (isClosed_le continuous_const
    (continuous_id.inner continuous_const)) ?_
  exact isClosed_biInter fun t _ ↦ IsClosed.inter
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)

/-- The outer cap is convex, being an intersection of half-spaces. -/
theorem convex_gerverOuterCap : Convex ℝ gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine Convex.inter (convex_halfSpace_ge (isLinearMap_inner_left _) 0) ?_
  exact convex_iInter₂ fun t _ ↦ Convex.inter
    (convex_halfSpace_le (isLinearMap_inner_left _) _)
    (convex_halfSpace_le (isLinearMap_inner_left _) _)

/-- The outer cap is contained in an explicit coordinate rectangle. -/
theorem gerverOuterCap_subset_box :
    gerverOuterCap ⊆ {p : Point |
      p 0 ∈ Set.Icc (-(inner ℝ (paperGerverPath (Real.pi / 2))
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1)) 1 ∧ p 1 ∈ Set.Icc 0 1} := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  intro q hq
  obtain ⟨hy, hcap⟩ := hq
  have h0 := hcap 0 ⟨le_rfl, hTpos.le⟩
  have hT := hcap (Real.pi / 2) ⟨hTpos.le, le_rfl⟩
  rw [paperGerverPath_zero, inner_normalVector_zero, inner_normalVector_zero,
    inner_tangentVector_zero, inner_tangentVector_zero] at h0
  refine ⟨⟨?_, ?_⟩, hy, ?_⟩
  · have h := hT.2
    rw [inner_tangentVector_pi_div_two] at h
    linarith
  · have h := h0.1
    simpa using h
  · have h := h0.2
    simpa using h

/-- The outer cap is compact: it is closed and contained in a coordinate rectangle. -/
theorem isCompact_gerverOuterCap : IsCompact gerverOuterCap := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_gerverOuterCap ?_
  set c : ℝ := -(inner ℝ (paperGerverPath (Real.pi / 2))
    (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1) with hc
  set K : ℝ := |c| + 1 with hK
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * K, fun q hq ↦ ?_⟩
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := gerverOuterCap_subset_box hq
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith [abs_nonneg c]
  have hsq : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, sq_abs]
  have hx : |q 0| ≤ K := by
    rw [abs_le]
    refine ⟨?_, by rw [hK]; linarith [abs_nonneg c]⟩
    have hcle : -|c| ≤ c := neg_abs_le c
    rw [hK]
    linarith [hx0]
  have hy : |q 1| ≤ K := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hx2 : q 0 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 0), abs_nonneg (q 0)]
  have hy2 : q 1 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 1), abs_nonneg (q 1)]
  nlinarith [norm_nonneg q, hsq, hx2, hy2, hK1]

/-- The outer cap is Borel measurable. -/
theorem measurableSet_gerverOuterCap : MeasurableSet gerverOuterCap :=
  isClosed_gerverOuterCap.measurableSet

/-- The outer cap has finite planar volume. -/
theorem volume_gerverOuterCap_lt_top : volume gerverOuterCap < ⊤ :=
  isCompact_gerverOuterCap.measure_lt_top

/-! ### The support-contact fan and the cap lower bound -/

/-- The fan anchor `L = C (π / 2)`. -/
def gerverFanAnchor : Point := paperGerverContacts (Real.pi / 2) 2

/-- The `i`-th listed support contact, `i < fanCount`. -/
def gerverFanPoint (i : ℕ) : Point :=
  gerverContactPoint (fanKind i) (gerverGridTime (fanIdx i))

/-- The support normal of the `i`-th listed contact. -/
def gerverFanNormal (i : ℕ) : ℝ :=
  if i ≤ 5 * NN then gerverGridTime i else gerverGridTime (i - 5 * NN) + Real.pi / 2

/-- The support value of the first outer contact in its own normal direction. -/
private theorem inner_paperGerverContacts_zero_normalVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := by
  change inner ℝ (paperGerverPath t +
    (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left,
    inner_tangentVector_normalVector_real, inner_normalVector_self]
  simp

/-- The support value of the third outer contact in the rotated normal direction. -/
private theorem inner_paperGerverContacts_two_tangentVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
  change inner ℝ (paperGerverPath t -
    (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self]
  ring

/-- `A t` attains the cap support at normal `t`. -/
theorem gerverOuterCap_support_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) := by
  rw [inner_paperGerverContacts_zero_normalVector]
  exact (hq.2 t ht).1

/-- `C t` attains the cap support at normal `t + π / 2`. -/
theorem gerverOuterCap_support_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 2) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  rw [normalVector_add_pi_div_two_real, inner_paperGerverContacts_two_tangentVector]
  exact (hq.2 t ht).2

/-- The anchor sits on the wall. -/
theorem gerverFanAnchor_snd : gerverFanAnchor 1 = 0 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  have h := congrArg Prod.snd (fromPlane_paperGerverContacts (Real.pi / 2) hT 2)
  have hC : (GerverSofa.PartC.C (Real.pi / 2)).2 = 0 :=
    GerverSofa.PartC.Stage2.C_T_snd_zero
  change (GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts (Real.pi / 2) 2)).2 = 0
  rw [h]
  simpa using hC

/-- The cap lies in the closed quadrant above the anchor. -/
theorem gerverOuterCap_quadrant {q : Point} (hq : q ∈ gerverOuterCap) :
    gerverFanAnchor 0 ≤ q 0 ∧ 0 ≤ q 1 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  refine ⟨?_, hq.1⟩
  have h := gerverOuterCap_support_C (Real.pi / 2) hT hq
  have hsplit : (Real.pi / 2 + Real.pi / 2 : ℝ) = 0 + Real.pi := by ring
  rw [hsplit, normalVector_add_pi, inner_neg_right, inner_neg_right,
    inner_normalVector_zero, inner_normalVector_zero] at h
  change gerverFanAnchor 0 ≤ q 0
  simp only [gerverFanAnchor]
  linarith

/-- The listed support normals are strictly increasing. -/
theorem gerverFanNormal_lt_succ (i : ℕ) (hi : i + 1 < fanCount) :
    gerverFanNormal i < gerverFanNormal (i + 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanNormal]
  split_ifs with h1 h2
  · exact gerverGridTime_lt_succ i (by omega)
  · have hi5 : i = 5 * NN := by omega
    subst hi5
    rw [Nat.add_sub_cancel_left, gerverGridTime_top]
    have h0 : gerverGridTime 0 < gerverGridTime 1 := gerverGridTime_lt_succ 0 (by omega)
    rw [gerverGridTime_zero] at h0
    linarith
  · omega
  · have hrw : i + 1 - 5 * NN = (i - 5 * NN) + 1 := by omega
    rw [hrw]
    have h := gerverGridTime_lt_succ (i - 5 * NN) (by omega)
    linarith

/-- The listed support normals lie in `[0, π)`. -/
theorem gerverFanNormal_mem_Ico (i : ℕ) (hi : i < fanCount) :
    0 ≤ gerverFanNormal i ∧ gerverFanNormal i < Real.pi := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  simp only [gerverFanNormal]
  split_ifs with h1
  · obtain ⟨hlo, hhi⟩ := gerverGridTime_mem_Icc i h1
    exact ⟨hlo, by linarith⟩
  · have hlt : i - 5 * NN < 5 * NN := by omega
    have hstrict := gerverGridTime_lt_of_lt hlt le_rfl
    rw [gerverGridTime_top] at hstrict
    obtain ⟨hlo, -⟩ := gerverGridTime_mem_Icc (i - 5 * NN) hlt.le
    exact ⟨by linarith, by linarith⟩

/-- The `kind = 1` slot of the contact dictionary is the first outer contact. -/
private theorem gerverContactPoint_one (x : ℝ) :
    gerverContactPoint 1 x = paperGerverContacts x 0 := rfl

/-- The `kind = 3` slot of the contact dictionary is the third outer contact. -/
private theorem gerverContactPoint_three (x : ℝ) :
    gerverContactPoint 3 x = paperGerverContacts x 2 := rfl

/-- Every listed contact lies in the cap. -/
theorem gerverFanPoint_mem (i : ℕ) (hi : i < fanCount) :
    gerverFanPoint i ∈ gerverOuterCap := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerver_outer_contact_A _ (gerverGridTime_mem_Icc i h1)
  · rw [gerverContactPoint_three]
    exact gerver_outer_contact_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega))

/-- Every listed contact attains the cap support at its listed normal. -/
theorem gerverFanPoint_support (i : ℕ) (hi : i < fanCount) {q : Point}
    (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (gerverFanNormal i : Real.Angle)) ≤
      inner ℝ (gerverFanPoint i) (normalVector (gerverFanNormal i : Real.Angle)) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, gerverFanNormal, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerverOuterCap_support_A _ (gerverGridTime_mem_Icc i h1) hq
  · rw [gerverContactPoint_three]
    exact gerverOuterCap_support_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega)) hq

/-- The certificate encloses both coordinates of every listed fan contact. -/
private theorem fanZ_sound (i : ℕ) (hi : i < fanCount) :
    SI.Contains (fanZ i).1 (gerverFanPoint i 0) ∧
      SI.Contains (fanZ i).2 (gerverFanPoint i 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hidx : fanIdx i ≤ 5 * NN := by
    simp only [fanIdx]
    split_ifs with h <;> omega
  have hkind : fanKind i ≤ 4 := by
    simp only [fanKind]
    split_ifs <;> norm_num
  exact contactZ_sound (fanIdx i) hidx (fanKind i) hkind

/-- The certificate encloses both coordinates of the fan anchor. -/
private theorem anchorZ_sound :
    SI.Contains anchorZ.1 (gerverFanAnchor 0) ∧ SI.Contains anchorZ.2 (gerverFanAnchor 1) := by
  have h := contactZ_sound (5 * NN) le_rfl 3 (by norm_num)
  rwa [gerverGridTime_top] at h

/-- The certificate encloses the fan shoelace sum. -/
theorem capDoubledZ_sound :
    SI.Contains capDoubledZ (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) := by
  have hNN : NN = 64 := rfl
  refine SI.contains_foldl_range (fanCount - 1) fun i hi => ?_
  simp only [fanCount] at hi
  obtain ⟨ha1, ha2⟩ := fanZ_sound i (by simp only [fanCount]; omega)
  obtain ⟨hb1, hb2⟩ := fanZ_sound (i + 1) (by simp only [fanCount]; omega)
  obtain ⟨hL1, hL2⟩ := anchorZ_sound
  have hcross : planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
      (gerverFanPoint (i + 1) - gerverFanAnchor) =
      (gerverFanPoint i 0 - gerverFanAnchor 0) *
          (gerverFanPoint (i + 1) 1 - gerverFanAnchor 1) -
        (gerverFanPoint i 1 - gerverFanAnchor 1) *
          (gerverFanPoint (i + 1) 0 - gerverFanAnchor 0) := by
    simp [planeCrossProduct]
  rw [hcross]
  exact SI.contains_sub
    (SI.contains_mul (SI.contains_sub ha1 hL1) (SI.contains_sub hb2 hL2))
    (SI.contains_mul (SI.contains_sub ha2 hL2) (SI.contains_sub hb1 hL1))

/-- The cap area lower bound. -/
theorem gerverOuterCap_area_certified_lower_bound :
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap := by
  have hNN : NN = 64 := rfl
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcount : fanCount = 640 := rfl
  -- The fan data on `Fin 640`.
  have hlt : ∀ i : Fin 640, (i : ℕ) < fanCount := fun i => by
    rw [hcount]; exact i.isLt
  have hmono : StrictMono fun i : Fin 640 => gerverFanNormal (i : ℕ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    simpa using gerverFanNormal_lt_succ (i : ℕ) (by rw [hcount]; omega)
  obtain ⟨-, hfan⟩ := supportContact_fan_area gerverOuterCap
    isCompact_gerverOuterCap convex_gerverOuterCap gerverFanAnchor
    (gerver_outer_contact_C (Real.pi / 2) ⟨hTpos.le, le_rfl⟩)
    gerverFanAnchor_snd (fun _ hq => gerverOuterCap_quadrant hq) 639
    (fun i : Fin 640 => gerverFanNormal (i : ℕ)) hmono
    (fun i => gerverFanNormal_mem_Ico (i : ℕ) (hlt i))
    (fun i : Fin 640 => gerverFanPoint (i : ℕ)) (fun i => gerverFanPoint_mem (i : ℕ) (hlt i))
    (fun i q hq => gerverFanPoint_support (i : ℕ) (hlt i) hq)
  -- Identify the `Fin`-indexed fan sum with the certificate's range sum.
  rw [show (∑ i : Fin 639, planeCrossProduct
        (gerverFanPoint (i.castSucc : Fin 640) - gerverFanAnchor)
        (gerverFanPoint (i.succ : Fin 640) - gerverFanAnchor)) =
      ∑ i ∈ Finset.range (fanCount - 1),
        planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
          (gerverFanPoint (i + 1) - gerverFanAnchor) by
    rw [hcount]
    exact Fin.sum_univ_eq_sum_range (fun i => planeCrossProduct
      (gerverFanPoint i - gerverFanAnchor) (gerverFanPoint (i + 1) - gerverFanAnchor)) 639] at hfan
  -- The kernel-checked numeric inequality.  The fan sum and the certificate endpoint are
  -- abstracted into local variables first, and the arithmetic tactics are used in their
  -- `only` form, so that no tactic ever tries to evaluate the 639-term fold.
  obtain ⟨S, hS⟩ : ∃ S : ℝ, (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) = S := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, capDoubledZ.lo = z := ⟨_, rfl⟩
  obtain ⟨hlo, -⟩ := capDoubledZ_sound
  rw [hS] at hfan
  rw [hS, hz] at hlo
  have hOK : 2 * 28609 * M ≤ 10000 * z := by
    have h := capOK_true
    unfold capOK at h
    rw [hz] at h
    exact of_decide_eq_true h
  have hOK' : (2 * 28609 * (M : ℝ)) ≤ 10000 * (z : ℝ) := by exact_mod_cast hOK
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hkey : 2 * 28609 ≤ 10000 * S := by nlinarith only [hlo, hOK', hM]
  refine le_trans ?_ hfan
  linarith only [hkey]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The rectangle cover of the literal Gerver niche

The literal niche is the union of the strict vertical fills under the three pieces of its
roof (`gerver_niche_vertical_fills`).  Each piece is traversed with monotone horizontal
coordinate, so subdividing the seven monotone roof stretches at the grid angles covers the
niche by `7 * NN` coordinate rectangles whose widths and heights the certificate encloses
(`gerverNicheRect_covers`).  The kernel-checked numeric conclusion
`GerverAreaCert.nicheOK_true` bounds the total rectangle area, hence `|N₀| ≤ 3301 / 5000`.
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-- The literal niche is Borel measurable: it is a closed half-plane intersected with a
countable union of open sets. -/
theorem measurableSet_gerverLiteralNiche : MeasurableSet gerverLiteralNiche := by
  have h : gerverLiteralNiche =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0} ∩
            {q : Point |
              inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}) := by
    ext q
    simp only [gerverLiteralNiche, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion₂,
      inner_normalVector_pi_div_two]
    tauto
  rw [h]
  refine MeasurableSet.inter
    ((isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet) ?_
  refine IsOpen.measurableSet (isOpen_biUnion fun t _ ↦ IsOpen.inter ?_ ?_)
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const

/-! ### The rectangle cover and the niche upper bound -/

/-- The covering rectangle of the `j`-th subinterval of roof piece `r`. -/
def gerverNicheRect (r j : ℕ) : Set Point :=
  {p : Point | p 0 ∈ Set.Icc (((rectLoZ r j : ℤ) : ℝ) / (M : ℝ))
      (((rectHiZ r j : ℤ) : ℝ) / (M : ℝ)) ∧
    p 1 ∈ Set.Icc 0 (((rectHZ r j : ℤ) : ℝ) / (M : ℝ))}

/-- A strict vertical fill splits along a subdivision of its parameter interval. -/
theorem strictVerticalFill_Icc_union {f : ℝ → Point} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    strictVerticalFill f (Set.Icc a c) =
      strictVerticalFill f (Set.Icc a b) ∪ strictVerticalFill f (Set.Icc b c) := by
  ext q
  simp only [strictVerticalFill, Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    rcases le_total t b with h | h
    · exact Or.inl ⟨t, ⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨t, ⟨h, h2⟩, h3⟩
  · rintro (⟨t, ⟨h1, h2⟩, h3⟩ | ⟨t, ⟨h1, h2⟩, h3⟩)
    · exact ⟨t, ⟨h1, h2.trans hbc⟩, h3⟩
    · exact ⟨t, ⟨hab.trans h1, h2⟩, h3⟩

/-- The strictly increasing chain of the six `ℕ`-indexed stage endpoints. -/
private theorem gerverStageTime_chain :
    gerverStageTime 0 = 0 ∧ gerverStageTime 0 < gerverStageTime 1 ∧
      gerverStageTime 1 < gerverStageTime 2 ∧ gerverStageTime 2 < gerverStageTime 3 ∧
      gerverStageTime 3 < gerverStageTime 4 ∧ gerverStageTime 4 < gerverStageTime 5 ∧
      gerverStageTime 5 = Real.pi / 2 :=
  ⟨gerverStageTime_zero, gerverStageTime_lt_succ 0 (by norm_num),
    gerverStageTime_lt_succ 1 (by norm_num), gerverStageTime_lt_succ 2 (by norm_num),
    gerverStageTime_lt_succ 3 (by norm_num), gerverStageTime_lt_succ 4 (by norm_num),
    gerverStageTime_five⟩

/-- `gerverRoofReverseTime` written in the `ℕ`-indexed stage endpoints. -/
private theorem gerverRoofReverseTime_eq_stageTime (s : ℝ) :
    gerverRoofReverseTime s = gerverStageTime 4 -
      (gerverStageTime 4 - gerverStageTime 1) / (gerverStageTime 3 - gerverStageTime 2) *
        (s - gerverStageTime 2) := rfl

/-- The first roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_D {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTime 2) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  gerverNicheRoof_of_le_two hs h

/-- The middle roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h2 : gerverStageTime 2 ≤ s) (h3 : s ≤ gerverStageTime 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) :=
  gerverNicheRoof_mid hs h2 h3

/-- The last roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_B {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h3 : gerverStageTime 3 ≤ s) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 :=
  gerverNicheRoof_of_ge_three hs h3

/-- Two roof arguments compare as their underlying reals. -/
private theorem gerverNicheRoof_fst_le_of_le {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (hab : a ≤ b) :
    gerverNicheRoof ⟨a, ha⟩ 0 ≤ gerverNicheRoof ⟨b, hb⟩ 0 :=
  gerver_niche_roof_strictMono.monotone (Subtype.mk_le_mk.mpr hab)

/-- The `D` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_three_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 3 0)
      (Set.Icc (gerverStageTime 0) (gerverStageTime 2)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_D hA ha.2, gerverNicheRoof_eq_D hB hb.2] at h

/-- The `B` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_one_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 1 0)
      (Set.Icc (gerverStageTime 3) (gerverStageTime 5)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_B hA ha.1, gerverNicheRoof_eq_B hB hb.1] at h

/-- The ambient path has antitone horizontal coordinate over the middle roof piece. -/
private theorem antitoneOn_paperGerverPath_fst :
    AntitoneOn (fun t ↦ paperGerverPath t 0)
      (Set.Icc (gerverStageTime 1) (gerverStageTime 4)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  have hne32 : gerverStageTime 3 - gerverStageTime 2 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hne41 : gerverStageTime 4 - gerverStageTime 1 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hc : 0 < (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) := div_pos (by linarith) (by linarith)
  have hcne : (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) ≠ 0 := ne_of_gt hc
  set c := (gerverStageTime 4 - gerverStageTime 1) /
    (gerverStageTime 3 - gerverStageTime 2) with hcdef
  -- The reverse-time map is inverted by `t ↦ e₂ + (e₄ - t) / c`.
  have hinv : ∀ t : ℝ, gerverRoofReverseTime (gerverStageTime 2 +
      (gerverStageTime 4 - t) / c) = t := by
    intro t
    rw [gerverRoofReverseTime_eq_stageTime, ← hcdef]
    field_simp
    ring
  have heq : (gerverStageTime 4 - gerverStageTime 1) / c =
      gerverStageTime 3 - gerverStageTime 2 := by
    rw [hcdef]
    field_simp
  have hmem : ∀ t : ℝ, gerverStageTime 1 ≤ t → t ≤ gerverStageTime 4 →
      gerverStageTime 2 ≤ gerverStageTime 2 + (gerverStageTime 4 - t) / c ∧
        gerverStageTime 2 + (gerverStageTime 4 - t) / c ≤ gerverStageTime 3 := by
    intro t ht1 ht4
    have hnn : 0 ≤ (gerverStageTime 4 - t) / c := div_nonneg (by linarith) hc.le
    have hstep : (gerverStageTime 4 - gerverStageTime 1) / c -
        (gerverStageTime 4 - t) / c = (t - gerverStageTime 1) / c := by
      field_simp
      ring
    have hnn2 : 0 ≤ (t - gerverStageTime 1) / c := div_nonneg (by linarith) hc.le
    exact ⟨by linarith, by linarith⟩
  intro a ha b hb hab
  obtain ⟨ha2, ha3⟩ := hmem a ha.1 ha.2
  obtain ⟨hb2, hb3⟩ := hmem b hb.1 hb.2
  have hAmem : gerverStageTime 2 + (gerverStageTime 4 - a) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hBmem : gerverStageTime 2 + (gerverStageTime 4 - b) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hba : gerverStageTime 2 + (gerverStageTime 4 - b) / c ≤
      gerverStageTime 2 + (gerverStageTime 4 - a) / c := by
    have hsub : (gerverStageTime 4 - a) / c - (gerverStageTime 4 - b) / c = (b - a) / c := by
      field_simp
      ring
    have hnn : 0 ≤ (b - a) / c := div_nonneg (by linarith) hc.le
    linarith
  have h := gerverNicheRoof_fst_le_of_le hBmem hAmem hba
  rwa [gerverNicheRoof_eq_path hBmem hb2 hb3, gerverNicheRoof_eq_path hAmem ha2 ha3,
    hinv a, hinv b] at h

/-- Each roof piece has monotone horizontal coordinate in the direction recorded by
`rowFwd`. -/
theorem gerverNicheRow_monotone (r : ℕ) (hr : r < 7) :
    (rowFwd r = true → MonotoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) ∧
      (rowFwd r = false → AntitoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) := by
  obtain ⟨-, c01, c12, c23, c34, c45, -⟩ := gerverStageTime_chain
  have sD0 : Set.Icc (gerverStageTime 0) (gerverStageTime 1) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc le_rfl c12.le
  have sD1 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc c01.le le_rfl
  have sP2 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc (c12.trans c23).le le_rfl
  have sP3 : Set.Icc (gerverStageTime 2) (gerverStageTime 3) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) := Set.Icc_subset_Icc c12.le c34.le
  have sP4 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc le_rfl (c23.trans c34).le
  have sB5 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc le_rfl c45.le
  have sB6 : Set.Icc (gerverStageTime 4) (gerverStageTime 5) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc c34.le le_rfl
  interval_cases r
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD0, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD1, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP2⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP3⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP4⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB5, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB6, fun h ↦ absurd h (by decide)⟩

/-- An integer lower bound at scale `M` read as a bound on the real quotient. -/
private theorem div_M_le_of_le {p : ℤ} {x : ℝ} (h : (p : ℝ) ≤ (M : ℝ) * x) :
    (p : ℝ) / (M : ℝ) ≤ x :=
  (div_le_iff₀ SI.Mpos).2 (by linarith)

/-- An integer upper bound at scale `M` read as a bound on the real quotient. -/
private theorem le_div_M_of_le {p : ℤ} {x : ℝ} (h : (M : ℝ) * x ≤ (p : ℝ)) :
    x ≤ (p : ℝ) / (M : ℝ) :=
  (le_div_iff₀ SI.Mpos).2 (by linarith)

/-- A strict vertical fill over an increasing subdivision of its parameter interval is the
union of the fills of the pieces.  Iterated form of `strictVerticalFill_Icc_union`. -/
private theorem strictVerticalFill_Icc_biUnion {f : ℝ → Point} (a : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → (∀ i j, i ≤ j → j ≤ n → a i ≤ a j) →
      strictVerticalFill f (Set.Icc (a 0) (a n)) =
        ⋃ i ∈ Finset.range n, strictVerticalFill f (Set.Icc (a i) (a (i + 1))) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
    intro _ ha
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [strictVerticalFill_Icc_union (ha 0 n (Nat.zero_le _) (by omega))
        (ha n (n + 1) (by omega) le_rfl),
        ih hpos fun i j hij hj => ha i j hij (by omega),
        Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]

/-- Each covering rectangle contains the strict vertical fill of its subinterval. -/
theorem gerverNicheRect_covers (r j : ℕ) (hr : r < 7) (hj : j < NN) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r j)) (gerverGridTime (rowBase r j + 1))) ⊆
      gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hM := SI.Mpos
  have hk : rowKind r ≤ 4 := by interval_cases r <;> decide
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have hj64 : j < 64 := by rwa [hNN] at hj
  have hm1 : rowBase r j + 1 ≤ 5 * NN := by simp only [rowBase, hNN]; omega
  have hm : rowBase r j ≤ 5 * NN := by omega
  have hlo : gerverStageTime (rowStage r - 1) ≤ gerverGridTime (rowBase r j) := by
    have h := gerverGridTime_le_of_le
      (show (rowStage r - 1) * NN ≤ rowBase r j by simp only [rowBase]; omega) hm
    rwa [gerverGridTime_mul_NN] at h
  have hhi : gerverGridTime (rowBase r j + 1) ≤ gerverStageTime (rowStage r) := by
    have h := gerverGridTime_le_of_le
      (show rowBase r j + 1 ≤ rowStage r * NN by simp only [rowBase, hNN]; omega)
      (Nat.mul_le_mul_right NN hS5)
    rwa [gerverGridTime_mul_NN] at h
  have hstep : gerverGridTime (rowBase r j) ≤ gerverGridTime (rowBase r j + 1) :=
    gerverGridTime_le_of_le (Nat.le_succ _) hm1
  have hmemL : gerverGridTime (rowBase r j) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo, hstep.trans hhi⟩
  have hmemR : gerverGridTime (rowBase r j + 1) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans hstep, hhi⟩
  obtain ⟨hmono, hanti⟩ := gerverNicheRow_monotone r hr
  rintro q ⟨t, ⟨htl, htr⟩, hq0, hq1a, hq1b⟩
  have hmemt : t ∈ Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans htl, htr.trans hhi⟩
  have hHmax : rectHZ r j = max
      (evalZ (stageOf (rowBase r j + 1))
        ⟨(ttZ (rowBase r j)).lo, (ttZ (rowBase r j + 1)).hi⟩ (rowKind r)).2.hi
      (contactZ (rowBase r j) (rowKind r)).2.hi := by
    simp only [rectHZ, SI.imax_eq_max]
  have hH : (M : ℝ) * gerverContactPoint (rowKind r) t 1 ≤ (rectHZ r j : ℝ) := by
    rcases eq_or_lt_of_le htl with heq | hlt
    · have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).2.2
      rw [← heq]
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_right _ _
    · have h := (evalZ_interval_sound (rowBase r j) hm1 (rowKind r) hk ⟨hlt, htr⟩).2.2
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_left _ _
  refine ⟨⟨?_, ?_⟩, hq1a, ?_⟩
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hmono hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hanti hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 :=
        hmono hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 :=
        hanti hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
  · have h2 : (M : ℝ) * q 1 ≤ (M : ℝ) * gerverContactPoint (rowKind r) t 1 :=
      mul_le_mul_of_nonneg_left hq1b.le hM.le
    exact le_div_M_of_le (h2.trans hH)

/-- The `NN` rectangles of a row cover the strict vertical fill of its whole stage. -/
private theorem strictVerticalFill_row_subset (r : ℕ) (hr : r < 7) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have ha0 : gerverGridTime (rowBase r 0) = gerverStageTime (rowStage r - 1) := by
    simpa [rowBase] using gerverGridTime_mul_NN (rowStage r - 1)
  have haN : gerverGridTime (rowBase r NN) = gerverStageTime (rowStage r) := by
    have hb : rowBase r NN = rowStage r * NN := by simp only [rowBase, hNN]; omega
    rw [hb, gerverGridTime_mul_NN]
  have hmono : ∀ i j, i ≤ j → j ≤ NN →
      gerverGridTime (rowBase r i) ≤ gerverGridTime (rowBase r j) := by
    intro i j hij hj
    refine gerverGridTime_le_of_le (by simp only [rowBase]; omega) ?_
    simp only [rowBase, hNN]; omega
  have hsplit : strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r 0)) (gerverGridTime (rowBase r NN))) =
      ⋃ i ∈ Finset.range NN, strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r i)) (gerverGridTime (rowBase r i + 1))) :=
    strictVerticalFill_Icc_biUnion (fun i => gerverGridTime (rowBase r i)) NN
      (by simp [hNN]) hmono
  rw [← ha0, ← haN, hsplit]
  refine Set.iUnion₂_subset fun i hi q hq => ?_
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨i, hi, gerverNicheRect_covers r i hr (Finset.mem_range.1 hi) hq⟩

/-- The `7 * NN` rectangles cover the literal niche. -/
theorem gerverLiteralNiche_subset_rects :
    gerverLiteralNiche ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have e0 : gerverStageTimes 0 = gerverStageTime 0 := rfl
  have e1 : gerverStageTimes 1 = gerverStageTime 1 := rfl
  have e2 : gerverStageTimes 2 = gerverStageTime 2 := rfl
  have e3 : gerverStageTimes 3 = gerverStageTime 3 := rfl
  have e4 : gerverStageTimes 4 = gerverStageTime 4 := rfl
  have e5 : gerverStageTimes 5 = gerverStageTime 5 := rfl
  have h01 : gerverStageTime 0 ≤ gerverStageTime 1 := (gerverStageTime_lt_succ 0 (by norm_num)).le
  have h12 : gerverStageTime 1 ≤ gerverStageTime 2 := (gerverStageTime_lt_succ 1 (by norm_num)).le
  have h23 : gerverStageTime 2 ≤ gerverStageTime 3 := (gerverStageTime_lt_succ 2 (by norm_num)).le
  have h34 : gerverStageTime 3 ≤ gerverStageTime 4 := (gerverStageTime_lt_succ 3 (by norm_num)).le
  have h45 : gerverStageTime 4 ≤ gerverStageTime 5 := (gerverStageTime_lt_succ 4 (by norm_num)).le
  have hrow : ∀ r, r < 7 → strictVerticalFill (gerverContactPoint (rowKind r))
      (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
    intro r hr q hq
    have h := strictVerticalFill_row_subset r hr hq
    simp only [Set.mem_iUnion, exists_prop] at h ⊢
    obtain ⟨j, hj, hjq⟩ := h
    exact ⟨r, Finset.mem_range.2 hr, j, hj, hjq⟩
  rw [gerver_niche_vertical_fills, e0, e1, e2, e3, e4, e5]
  refine Set.union_subset (Set.union_subset ?_ ?_) ?_
  · rw [strictVerticalFill_Icc_union h01 h12]
    exact Set.union_subset (hrow 0 (by norm_num)) (hrow 1 (by norm_num))
  · rw [strictVerticalFill_Icc_union h12 (h23.trans h34), strictVerticalFill_Icc_union h23 h34]
    exact Set.union_subset (hrow 4 (by norm_num))
      (Set.union_subset (hrow 3 (by norm_num)) (hrow 2 (by norm_num)))
  · rw [strictVerticalFill_Icc_union h34 h45]
    exact Set.union_subset (hrow 5 (by norm_num)) (hrow 6 (by norm_num))

/-- The planar volume of one covering rectangle. -/
theorem volume_gerverNicheRect (r j : ℕ) :
    volume (gerverNicheRect r j) =
      ENNReal.ofReal ((((rectHiZ r j - rectLoZ r j : ℤ)) : ℝ) / (M : ℝ)) *
        ENNReal.ofReal (((rectHZ r j : ℤ) : ℝ) / (M : ℝ)) := by
  rw [gerverNicheRect, EuclideanSpace.volume_setOf_apply_mem_Icc]
  congr 2
  · push_cast
    ring
  · ring

/-- The certificate bounds the total rectangle volume. -/
theorem gerverNicheRect_volume_sum_le :
    ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  have hM := SI.Mpos
  have hQ : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hM hM
  -- `unfold` rather than a type ascription: matching `nicheOK` against `decide _` by
  -- unification would force the elaborator to evaluate the whole certificate.
  have hcert : 5000 * nicheSumZ ≤ 3301 * M * M := by
    have h := nicheOK_true
    unfold nicheOK at h
    exact of_decide_eq_true h
  have harea : ∀ r j : ℕ,
      rectAreaZ r j = max 0 (rectHiZ r j - rectLoZ r j) * max 0 (rectHZ r j) := by
    intro r j
    simp only [rectAreaZ, SI.imax_eq_max]
  have hnn : ∀ r j : ℕ, (0 : ℝ) ≤ (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    intro r j
    refine div_nonneg ?_ hQ.le
    have : (0 : ℤ) ≤ rectAreaZ r j := by
      rw [harea]
      exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast this
  have hcell : ∀ r j : ℕ, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) := by
    intro r j
    have hA : ((rectHiZ r j - rectLoZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    have hB : ((rectHZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHZ r j)
    have hA0 : (0 : ℝ) ≤ ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      refine div_nonneg ?_ hM.le
      exact_mod_cast le_max_left (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    rw [volume_gerverNicheRect]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hB)) ?_
    rw [← ENNReal.ofReal_mul hA0]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [harea]
    push_cast
    field_simp
  have hns : nicheSumZ = ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, rectAreaZ r j := by
    rw [nicheSumZ, SI.foldl_range_int]
    exact Finset.sum_congr rfl fun r _ => by rw [rowSumZ, SI.foldl_range_int]
  have hsum : ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
      (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) =
        (nicheSumZ : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    rw [hns]
    push_cast
    simp only [← Finset.sum_div]
  calc ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j)
      ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => hcell r j
    _ = ∑ r ∈ Finset.range 7, ENNReal.ofReal
          (∑ j ∈ Finset.range NN, (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_congr rfl fun r _ =>
          (ENNReal.ofReal_sum_of_nonneg fun j _ => hnn r j).symm
    _ = ENNReal.ofReal (∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        (ENNReal.ofReal_sum_of_nonneg fun r _ => Finset.sum_nonneg fun j _ => hnn r j).symm
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsum, div_le_div_iff₀ hQ (by norm_num)]
        have hR : (5000 : ℝ) * (nicheSumZ : ℝ) ≤ 3301 * (M : ℝ) * (M : ℝ) := by
          exact_mod_cast hcert
        linarith

/-- The niche volume bound. -/
theorem gerver_niche_volume_le :
    volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  calc volume gerverLiteralNiche
      ≤ volume (⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_mono gerverLiteralNiche_subset_rects
    _ ≤ ∑ r ∈ Finset.range 7, volume (⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) :=
        Finset.sum_le_sum fun _ _ => measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := gerverNicheRect_volume_sum_le

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Rational area bounds for the canonical Gerver sofa

The canonical Gerver sofa is the paper's literal set (`gerver_canonical_paper_literal`), the
difference of the literal outer cap and the literal niche.  The cap and the niche are Borel
of finite area with `28609 / 10000 ≤ |K₀|` and `|N₀| ≤ 3301 / 5000`
(`gerver_geometric_area_bounds`), both numeric bounds coming from the kernel-checked
certificate `MovingSofa.Gerver.AreaCertificate` through the fan bound of
`MovingSofa.Gerver.Area.CapFan` and the rectangle cover of
`MovingSofa.Gerver.Area.NicheCover`.  Subadditivity of area then gives
`11 / 5 ≤ |G|` (`gerver_area_lower_bound`).
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory

theorem gerver_canonical_paper_literal :
    gerversSofa = paperGerverSofa ∧ paperGerverSofa = gerverLiteralSofa := by
  refine ⟨?_, paperGerverSofa_eq_literal⟩
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- Translate-then-rotate splits into rotation of the point plus rotation of the shift.
  have hrt : ∀ (α : Real.Angle) (v s : Point),
      rotateTranslate α v s = rotationMap α s + rotationMap α v := by
    intro α v s
    change (EuclideanGeometry.o.rotation α) (s + v) = _
    exact map_add _ _ _
  -- The canonical placements agree with the paper ones on `[0, π/2]`.
  have himg : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ S : Set Point,
      rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' S =
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' S := by
    intro t ht S
    apply Set.image_congr'
    intro s
    rw [hrt, canonical_path_rotation_eq_paper t ht]
  -- Membership in a rotated-translated coordinate region is read off in the moving frame.
  have himage : ∀ (P : ℝ → ℝ → Prop) (S : Set Point),
      (∀ s : Point, s ∈ S ↔ P (s 0) (s 1)) →
      ∀ (t : Real.Angle) (v z : Point),
        z ∈ (fun s ↦ rotationMap t s + v) '' S ↔
          P (inner ℝ (z - v) (normalVector t)) (inner ℝ (z - v) (tangentVector t)) := by
    intro P S hS t v z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h0 : inner ℝ (rotationMap t s + v - v) (normalVector t) = s 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t s + v - v) (tangentVector t) = s 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      rw [h0, h1]
      exact (hS s).1 hs
    · intro h
      obtain ⟨s, hs⟩ := (EuclideanGeometry.o.rotation t).surjective (z - v)
      have hsz : rotationMap t s = z - v := hs
      have h0 : s 0 = inner ℝ (z - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector s t, hsz]
      have h1 : s 1 = inner ℝ (z - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector s t, hsz]
      refine ⟨s, (hS s).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · change rotationMap t s + v = z
        rw [hsz]; abel
  have hhoriz : ∀ s : Point, s ∈ horizontalHallway ↔ s 0 ≤ 1 ∧ 0 ≤ s 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_horizontalHallway_coordinates,
      fun h => mem_horizontalHallway_of_coordinates s h.1 ⟨h.2.1, h.2.2⟩⟩
  have hvert : ∀ s : Point, s ∈ verticalHallway ↔ 0 ≤ s 0 ∧ s 0 ≤ 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_verticalHallway_coordinates,
      fun h => mem_verticalHallway_of_coordinates s ⟨h.1, h.2.1⟩ h.2.2⟩
  have hhall : ∀ s : Point, s ∈ hallway ↔ (s 0 ≤ 1 ∧ s 1 ≤ 1) ∧ (0 ≤ s 0 ∨ 0 ≤ s 1) :=
    mem_hallway_iff
  -- Endpoint normalisations of the paper path.
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathT : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hstrip : ∀ z : Point,
      z ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
    intro z
    have h := mem_stripParallelogram_iff (Real.pi / 2) z
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  -- Rewrite both endpoint arms and the family of hallways in the paper frame.
  have hzero : ((0 : ℝ) : Real.Angle) = (0 : Real.Angle) := Real.Angle.coe_zero
  have hgs : gerversSofa =
      ((fun s ↦ rotationMap ((0 : ℝ) : Real.Angle) s + paperGerverPath 0) ''
          horizontalHallway ∩
        (fun s ↦ rotationMap ((Real.pi / 2 : ℝ) : Real.Angle) s +
          paperGerverPath (Real.pi / 2)) '' verticalHallway) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    change rotateTranslate 0 (GerversSofa.p 0) '' horizontalHallway ∩
        rotateTranslate ((Real.pi / 2 : ℝ) : Real.Angle)
          (GerversSofa.p (Real.pi / 2)) '' verticalHallway ∩
        (⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' hallway) = _
    rw [← hzero, himg 0 hT0 horizontalHallway,
      himg (Real.pi / 2) hTT verticalHallway,
      Set.iInter₂_congr (fun t (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) => himg t ht hallway)]
  have hpaper : paperGerverSofa =
      {z : Point | 0 ≤ z 1 ∧ z 1 ≤ 1} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    change (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩ _ = _
    rw [Set.ext hstrip]
    rfl
  rw [hgs, hpaper]
  ext q
  have hn0 : inner ℝ (q - paperGerverPath 0) (normalVector ((0 : ℝ) : Real.Angle)) = q 0 := by
    rw [hpath0, sub_zero, inner_normalVector_zero]
  have hg0 : inner ℝ (q - paperGerverPath 0) (tangentVector ((0 : ℝ) : Real.Angle)) = q 1 := by
    rw [hpath0, sub_zero, inner_tangentVector_zero]
  have hnT : inner ℝ (q - paperGerverPath (Real.pi / 2))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = q 1 := by
    rw [inner_normalVector_pi_div_two]
    change q 1 - paperGerverPath (Real.pi / 2) 1 = q 1
    rw [hpathT, sub_zero]
  have hAhoriz := himage (fun a b => a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1) horizontalHallway hhoriz
  have hAvert := himage (fun a b => 0 ≤ a ∧ a ≤ 1 ∧ b ≤ 1) verticalHallway hvert
  have hAhall := himage (fun a b => (a ≤ 1 ∧ b ≤ 1) ∧ (0 ≤ a ∨ 0 ≤ b)) hallway hhall
  simp only [Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_ofPred_eq, hAhoriz, hAvert, hAhall,
    hn0, hg0, hnT]
  constructor
  · rintro ⟨⟨⟨-, hb0, hb1⟩, -⟩, hC⟩
    exact ⟨⟨hb0, hb1⟩, hC⟩
  · rintro ⟨⟨hb0, hb1⟩, hC⟩
    refine ⟨⟨⟨?_, hb0, hb1⟩, hb0, hb1, ?_⟩, hC⟩
    · have h := (hC 0 hT0).1.1
      rwa [hn0] at h
    · exact (hC (Real.pi / 2) hTT).1.2

theorem gerver_geometric_area_bounds :
    MeasurableSet gerverOuterCap ∧ volume gerverOuterCap < ⊤ ∧
    MeasurableSet gerverLiteralNiche ∧ volume gerverLiteralNiche < ⊤ ∧
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap ∧
    ClassicalResults.area gerverLiteralNiche ≤ (3301 : ℝ) / 5000 := by
  have hfin : volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) :=
    gerver_niche_volume_le
  refine ⟨measurableSet_gerverOuterCap, volume_gerverOuterCap_lt_top,
    measurableSet_gerverLiteralNiche, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top,
    gerverOuterCap_area_certified_lower_bound, ?_⟩
  calc ClassicalResults.area gerverLiteralNiche
      = (volume gerverLiteralNiche).toReal := rfl
    _ ≤ (ENNReal.ofReal ((3301 : ℝ) / 5000)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = (3301 : ℝ) / 5000 := ENNReal.toReal_ofReal (by norm_num)

theorem gerver_area_lower_bound :
    volume gerversSofa < ⊤ ∧ (11 : ℝ) / 5 ≤ ClassicalResults.area gerversSofa := by
  obtain ⟨-, hKtop, -, hNtop, hKarea, hNarea⟩ := gerver_geometric_area_bounds
  have hG : gerversSofa = gerverOuterCap \ gerverLiteralNiche :=
    gerver_canonical_paper_literal.1.trans gerver_canonical_paper_literal.2
  have hGtop : volume gerversSofa < ⊤ :=
    lt_of_le_of_lt (measure_mono (hG ▸ Set.sdiff_subset)) hKtop
  refine ⟨hGtop, ?_⟩
  -- The cap is covered by the sofa together with the niche, so areas are subadditive.
  have hcover : volume gerverOuterCap ≤ volume gerversSofa + volume gerverLiteralNiche := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    rw [hG]
    exact Set.subset_sdiff_union _ _
  have hreal : ClassicalResults.area gerverOuterCap ≤
      ClassicalResults.area gerversSofa + ClassicalResults.area gerverLiteralNiche := by
    have h := ENNReal.toReal_mono (by finiteness) hcover
    rwa [ENNReal.toReal_add hGtop.ne hNtop.ne] at h
  linarith only [hreal, hKarea, hNarea]

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.CapIdentification`.
* `Gerver.Niche.Identification`.
* `Gerver.SurfaceDensity`.
* `Gerver.VelocityAndCapArea`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Cap Identification
-/

public section

noncomputable section

namespace MovingSofa

private theorem gerver_cap_fiber_has_sofa_point
    (hKcomp : IsCompact gerverOuterCap) :
    ∀ q ∈ gerverOuterCap,
     ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1 := by
  intro q hq
  have hFcomp : IsCompact (gerverOuterCap ∩ {z : Point |
      inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
        inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))}) :=
    hKcomp.inter_right (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  obtain ⟨p, hpF, hpmax⟩ := hFcomp.exists_isMaxOn ⟨q, hq, rfl⟩
    (f := fun z : Point => inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    (continuous_id.inner continuous_const).continuousOn
  have hpx : p 0 = q 0 := by
    have h : inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) =
      inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) := hpF.2
    rwa [inner_normalVector_zero, inner_normalVector_zero] at h
  have hpy : q 1 ≤ p 1 := by
    have h : inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax ⟨hq, rfl⟩
    rwa [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at h
  have hnofill : ∀ (f : ℝ → Point) (I : Set ℝ), (∀ t ∈ I, f t ∈ gerverOuterCap) →
      p ∉ strictVerticalFill f I := by
    rintro f I hf ⟨t, ht, h0, -, h2⟩
    have hmem : f t ∈ gerverOuterCap ∩ {z : Point |
        inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
          inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))} := by
      refine ⟨hf t ht, ?_⟩
      change inner ℝ (f t) (normalVector ((0 : ℝ) : Real.Angle)) =
        inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))
      rw [inner_normalVector_zero, inner_normalVector_zero, ← h0, hpx]
    have hle : inner ℝ (f t) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax hmem
    rw [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at hle
    linarith
  obtain ⟨hroofD, hroofx, hroofB⟩ := gerver_niche_roof_membership
  refine ⟨p, ⟨hpF.1, ?_⟩, hpx, hpy⟩
  rw [gerver_niche_vertical_fills]
  rintro ((h | h) | h)
  · exact hnofill _ _ hroofD h
  · exact hnofill _ _ hroofx h
  · exact hnofill _ _ hroofB h

private theorem gerver_cap_contact_faces (Kb : ConvexBody Point)
    (hKset : (Kb : Set Point) = gerverOuterCap)
    (hKcap : IsCap (Real.pi / 2) Kb)
    (hC1 : ContDiff ℝ 1 (GerverSofa.Romik.path GerverSofa.PartB.params))
    (hAn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1)
    (hAt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (tangentVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
       (paperGerverVelocityComponents t).1)
    (hCn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (normalVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) -
       (paperGerverVelocityComponents t).2)
    (hCt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
     inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
     supportValue gerverOuterCap (t : Real.Angle) =
       inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
     supportValue gerverOuterCap ((Real.pi / 2 + t : ℝ) : Real.Angle) =
       inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hTpos : (0 : ℝ) < Real.pi / 2) :
    ∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
     (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
       exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
       exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
     paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
     paperGerverContacts (Real.pi / 2) 0 =
       (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
     paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
     paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2 := by
  -- a plane point is determined by its two frame coordinates
  have hpteq : ∀ (a : Real.Angle) (p q : Point),
      inner ℝ p (normalVector a) = inner ℝ q (normalVector a) →
      inner ℝ p (tangentVector a) = inner ℝ q (tangentVector a) → p = q := by
    intro a p q h1 h2
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p a,
      ← inner_normalVector_smul_add_inner_tangentVector_smul q a, h1, h2]
  have hdx : ∀ t : ℝ, HasDerivAt paperGerverPath (deriv paperGerverPath t) t := fun t => by
    rw [deriv_paperGerverPath hC1 t]
    exact hasDerivAt_paperGerverPath hC1 t
  -- exposed faces of the certified body, read in the cap's own description
  have hexp : ∀ (a : Real.Angle) (z : Point), z ∈ exposedEdge Kb a ↔
      (z ∈ gerverOuterCap ∧
        inner ℝ z (normalVector a) = supportValue gerverOuterCap a) := by
    intro a z
    constructor
    · intro h
      refine ⟨hKset ▸ h.1, ?_⟩
      have h2 : inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a := h.2
      rwa [hKset] at h2
    · intro h
      refine ⟨hKset ▸ h.1, ?_⟩
      change inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a
      rw [hKset]
      exact h.2
  have hsingleV : ∀ (a : Real.Angle) (p : Point), exposedEdge Kb a = {p} →
      (edgeVertices Kb a).1 = p ∧ (edgeVertices Kb a).2 = p := fun a p h =>
    ⟨Set.mem_singleton_iff.1 (h ▸ edgeVertices_fst_mem Kb a),
      Set.mem_singleton_iff.1 (h ▸ edgeVertices_snd_mem Kb a)⟩
  -- interior uniqueness in the normal family
  have hnormaledge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
      inner ℝ z (normalVector (t : Real.Angle)) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 →
      z = paperGerverContacts t 0 := by
    intro t ht z hz heq
    have hgd : HasDerivAt (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle)))
        ((inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
          (paperGerverVelocityComponents t).1) -
          inner ℝ z (tangentVector (t : Real.Angle))) t :=
      (((hdx t).inner ℝ (hasDerivAt_normalVector t)).add_const 1).sub
        (hasDerivAt_inner_normalVector z t)
    have hgmin : IsLocalMin (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle))) t := by
      refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
      intro s hs
      have h := (hz.2 s hs).1
      change (inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1) -
          inner ℝ z (normalVector (t : Real.Angle)) ≤
        (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
          inner ℝ z (normalVector (s : Real.Angle))
      linarith
    have hzero := hgmin.hasDerivAt_eq_zero hgd
    refine hpteq (t : Real.Angle) z (paperGerverContacts t 0) ?_ ?_
    · rw [hAn t]; exact heq
    · rw [hAt t]; linarith
  -- interior uniqueness in the tangent family
  have htangentedge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
      inner ℝ z (tangentVector (t : Real.Angle)) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 →
      z = paperGerverContacts t 2 := by
    intro t ht z hz heq
    have hzt : HasDerivAt (fun s : ℝ => inner ℝ z (tangentVector (s : Real.Angle)))
        (-inner ℝ z (normalVector (t : Real.Angle))) t := by
      simpa using (hasDerivAt_const t z).inner ℝ (hasDerivAt_tangentVector t)
    have hgd : HasDerivAt (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle)))
        ((inner ℝ (paperGerverPath t) (-normalVector (t : Real.Angle)) +
          (paperGerverVelocityComponents t).2) -
          -inner ℝ z (normalVector (t : Real.Angle))) t :=
      (((hdx t).inner ℝ (hasDerivAt_tangentVector t)).add_const 1).sub hzt
    have hgmin : IsLocalMin (fun s : ℝ =>
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle))) t := by
      refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
      intro s hs
      have h := (hz.2 s hs).2
      change (inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (t : Real.Angle)) ≤
        (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
          inner ℝ z (tangentVector (s : Real.Angle))
      linarith
    have hzero := hgmin.hasDerivAt_eq_zero hgd
    rw [inner_neg_right] at hzero
    refine hpteq (t : Real.Angle) z (paperGerverContacts t 2) ?_ ?_
    · rw [hCn t]; linarith
    · rw [hCt t]; exact heq
  -- the interior exposed faces are the two contact singletons
  have hedgeA : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      exposedEdge Kb (t : Real.Angle) = {paperGerverContacts t 0} := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨(hexp _ _).2 ⟨gerver_outer_contact_A t htI, ?_⟩, fun z hz => ?_⟩
    · rw [hAn t, (hsupK t htI).1]
    · rw [hexp] at hz
      exact hnormaledge t ht z hz.1 (by rw [hz.2, (hsupK t htI).1])
  have hedgeC : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      exposedEdge Kb ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2} := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
    have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
    have hsv : supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
      rw [hang]; exact (hsupK t htI).2
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨(hexp _ _).2 ⟨gerver_outer_contact_C t htI, ?_⟩, fun z hz => ?_⟩
    · rw [normalVector_add_pi_div_two_real, hCt t, hsv]
    · rw [hexp] at hz
      refine htangentedge t ht z hz.1 ?_
      have h := hz.2
      rwa [normalVector_add_pi_div_two_real, hsv] at h
  -- the four contact curves are continuous
  have hcontacts : Continuous paperGerverContacts := paperGerverContactData_properties.2.1
  have hcontA : Continuous fun s : ℝ => paperGerverContacts s 0 :=
    (continuous_apply 0).comp hcontacts
  have hcontC : Continuous fun s : ℝ => paperGerverContacts s 2 :=
    (continuous_apply 2).comp hcontacts
  -- vertex limits at the four endpoints
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have heventA : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsGT hTpos] with s hs
    exact ((hsingleV _ _ (hedgeA s hs)).1).symm
  have heventA' : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsLT hTpos] with s hs
    exact ((hsingleV _ _ (hedgeA s hs)).1).symm
  have hCshift : ∀ s : ℝ, s ∈ Set.Ioo (Real.pi / 2) Real.pi →
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    intro s hs
    have hs' : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hang : ((s : ℝ) : Real.Angle) =
        ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) := by rw [sub_add_cancel]
    rw [hang]
    exact ((hsingleV _ _ (hedgeC (s - Real.pi / 2) hs')).1).symm
  have heventC : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)),
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsGT (show Real.pi / 2 < Real.pi by linarith)] with s hs
    exact hCshift s hs
  have heventC' : ∀ᶠ s : ℝ in nhdsWithin Real.pi (Set.Iio Real.pi),
      paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
    filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 2 < Real.pi by linarith)] with s hs
    exact hCshift s hs
  have hcontCshift : Continuous fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2 :=
    hcontC.comp (continuous_id.sub continuous_const)
  refine ⟨⟨Kb, hKcap⟩, hKset, fun t ht => ⟨hedgeA t ht, hedgeC t ht⟩, ?_, ?_, ?_, ?_⟩
  · rw [← Real.Angle.coe_zero]
    refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb 0).1
    exact Filter.Tendsto.congr' heventA ((hcontA.tendsto 0).mono_left nhdsWithin_le_nhds)
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).2.2.2.1
    exact Filter.Tendsto.congr' heventA'
      ((hcontA.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds)
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).1
    have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
        (nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)))
        (nhds (paperGerverContacts 0 2)) := by
      have := (hcontCshift.tendsto (Real.pi / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (Real.pi / 2)))
      rwa [sub_self] at this
    exact Filter.Tendsto.congr' heventC h
  · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb Real.pi).2.2.2.1
    have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
        (nhdsWithin Real.pi (Set.Iio Real.pi))
        (nhds (paperGerverContacts (Real.pi / 2) 2)) := by
      have := (hcontCshift.tendsto Real.pi).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio Real.pi))
      rwa [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at this
    exact Filter.Tendsto.congr' heventC' h

private theorem gerver_literal_standard_position
    (hTpos : (0 : ℝ) < Real.pi / 2)
    (hTmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hGcomp : IsCompact gerverLiteralSofa)
    (hmotioncont : Continuous fun r : unitInterval =>
     rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
       (-paperGerverPath (r.val * (Real.pi / 2))))
    (hpath0 : paperGerverPath 0 = 0)
    (hpathTy : paperGerverPath (Real.pi / 2) 1 = 0)
    (hcapx1 : ∀ q ∈ gerverOuterCap, q 0 ≤ 1)
    (hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1)
    (hsv1 : supportValue gerverLiteralSofa ((Real.pi / 2 : ℝ) : Real.Angle) = 1) :
    IsStandardPosition gerverLiteralSofa (Real.pi / 2) := by
  -- ### Frame readers for the clockwise motion
  have hinnertan : ∀ (w : Point) (t : ℝ), inner ℝ w (tangentVector (t : Real.Angle)) =
      -(w 0 * Real.sin t) + w 1 * Real.cos t := by
    intro w t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hmapply : ∀ (t : ℝ) (v p : Point),
      rotateTranslate ((-t : ℝ) : Real.Angle) (-v) p =
        rotationMap ((-t : ℝ) : Real.Angle) (p - v) := by
    intro t v p
    change (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p + -v) =
      (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p - v)
    rw [← sub_eq_add_neg]
  have hrotinv : ∀ (t : ℝ) (w : Point),
      rotationMap ((-t : ℝ) : Real.Angle) (rotationMap ((t : ℝ) : Real.Angle) w) = w := by
    intro t w
    change (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle))
      ((EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)) w) = w
    rw [Real.Angle.coe_neg, ← Orientation.rotation_symm]
    exact (EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)).symm_apply_apply w
  have hcoord0 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 0 =
      inner ℝ w (normalVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_zero, inner_normalVector_real, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  have hcoord1 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 1 =
      inner ℝ w (tangentVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_one, hinnertan, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  refine ⟨hGcomp, ⟨fun r => rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
      (-paperGerverPath (r.val * (Real.pi / 2))),
    ⟨gerver_literal_connected, hGcomp.isClosed, ?_, ⟨0, ?_⟩, ?_, ?_, ?_, ?_⟩,
    fun r => -(r.val * (Real.pi / 2)),
    (continuous_subtype_val.mul continuous_const).neg,
    by simp, by simp, ?_⟩,
    hTpos, le_rfl, hsv1, hsv1⟩
  · exact hmotioncont
  · -- the motion starts at the identity
    intro p
    rw [hmapply]
    simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
      sub_zero, add_zero]
    change (EuclideanGeometry.o.rotation 0) p = p
    simp
  · -- each placement is a rotation followed by a translation
    intro r
    refine ⟨(((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle), fun p => ?_⟩
    rw [hmapply, hmapply]
    simp only [rotationMap, zero_sub, map_sub, map_neg]
    abel
  · -- the initial placement lands in the horizontal arm
    rintro _ ⟨z, hz, rfl⟩
    have heq : rotateTranslate
        ((-((0 : unitInterval).val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath ((0 : unitInterval).val * (Real.pi / 2))) z = z := by
      rw [hmapply]
      simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
        sub_zero]
      change (EuclideanGeometry.o.rotation 0) z = z
      simp
    rw [heq]
    exact mem_horizontalHallway_of_coordinates z (hcapx1 z hz.1)
      ⟨hz.1.1, hcapy1 z hz.1⟩
  · -- every intermediate placement lands in the hallway
    intro r
    rintro _ ⟨z, hz, rfl⟩
    have ht : r.val * (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨mul_nonneg r.2.1 hTpos.le, by
        nlinarith [r.2.2, hTpos]⟩
    have hzP : z ∈ paperGerverSofa := by rw [paperGerverSofa_eq_literal]; exact hz
    obtain ⟨w, hw, hwz⟩ :=
      Set.mem_iInter₂.1 hzP.2 (r.val * (Real.pi / 2)) ht
    rw [hmapply]
    have hzw : z - paperGerverPath (r.val * (Real.pi / 2)) =
        rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w := by
      rw [← hwz]
      change rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w +
          paperGerverPath (r.val * (Real.pi / 2)) -
          paperGerverPath (r.val * (Real.pi / 2)) =
        rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w
      abel
    rw [hzw, hrotinv]
    exact hw
  · -- the final placement lands in the vertical arm
    rintro _ ⟨z, hz, rfl⟩
    have hTm' : (1 : unitInterval).val * (Real.pi / 2) = Real.pi / 2 := by
      rw [Set.Icc.coe_one, one_mul]
    rw [hmapply]
    refine mem_verticalHallway_of_coordinates _ ⟨?_, ?_⟩ ?_
    · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
        inner_normalVector_pi_div_two, hpathTy, sub_zero]
      exact hz.1.1
    · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
        inner_normalVector_pi_div_two, hpathTy, sub_zero]
      exact hcapy1 z hz.1
    · rw [hcoord1, hTm', inner_sub_left]
      have h := (hz.1.2 (Real.pi / 2) hTmem).2
      linarith
  · -- the motion realizes the lifted clockwise angle
    intro r p
    rw [hmapply, hmapply]
    simp only [rotationMap, zero_sub, map_sub, map_neg]
    abel

private theorem gerver_literal_cap_eq
    (hsupG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverLiteralSofa (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverLiteralSofa ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1)
    (hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1) :
    capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap := by
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  have houter : ∀ t : ℝ,
      (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant =
        normalHalfPlane (t : Real.Angle)
            (supportValue gerverLiteralSofa (t : Real.Angle)) false false ∩
          normalHalfPlane ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
            (supportValue gerverLiteralSofa
              ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) false false :=
    fun t => (rotatingHallwayParts_formulas gerverLiteralSofa
      (t : Real.Angle)).2.2.2.2.2.2.2.1
  ext z
  constructor
  · rintro ⟨hstrip, hint⟩
    rw [mem_stripParallelogram_iff] at hstrip
    refine ⟨hstrip.1.1, fun t ht => ?_⟩
    have hq : z ∈ (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant :=
      Set.mem_iInter₂.1 hint t ht
    rw [houter t] at hq
    have h1 : inner ℝ z (normalVector (t : Real.Angle)) ≤
      supportValue gerverLiteralSofa (t : Real.Angle) := hq.1
    have h2 : inner ℝ z
        (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
      supportValue gerverLiteralSofa
        ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := hq.2
    rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2] at h2
    rw [(hsupG t ht).1] at h1
    exact ⟨h1, h2⟩
  · intro hz
    refine ⟨?_, Set.mem_iInter₂.2 fun t ht => ?_⟩
    · rw [mem_stripParallelogram_iff, inner_normalVector_pi_div_two]
      exact ⟨⟨hz.1, hcapy1 z hz⟩, hz.1, hcapy1 z hz⟩
    · rw [houter t]
      refine ⟨?_, ?_⟩
      · change inner ℝ z (normalVector (t : Real.Angle)) ≤
          supportValue gerverLiteralSofa (t : Real.Angle)
        rw [(hsupG t ht).1]
        exact (hz.2 t ht).1
      · change inner ℝ z
            (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
          supportValue gerverLiteralSofa
            ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
        rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2]
        exact (hz.2 t ht).2

theorem gerver_capSupport_identification :
    (∀ q ∈ gerverOuterCap, ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1) ∧
    paperGerverSofa = gerverLiteralSofa ∧
    IsStandardPosition gerverLiteralSofa (Real.pi / 2) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) = supportValue gerverOuterCap (s :
        Real.Angle)) ∧
    capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
        exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
      paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 0 =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
      paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2) ∧
    (∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue S (t : Real.Angle) =
          inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
        supportValue S ((Real.pi / 2 + t : ℝ) : Real.Angle) =
          inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- ### Path regularity and endpoints
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hC1 : ContDiff ℝ 1 (GerverSofa.Romik.path GerverSofa.PartB.params) := hreg.1
  have hpathcont : Continuous paperGerverPath := continuous_paperGerverPath hC1
  -- The clockwise motion used for the moving-sofa property, and its continuity.
  have hmotioncont : Continuous fun r : unitInterval =>
      rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath (r.val * (Real.pi / 2))) := by
    have hpair : Continuous fun r : unitInterval =>
        ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2))) :=
      (Real.Angle.continuous_coe.comp (continuous_subtype_val.mul continuous_const).neg).prodMk
        ((hpathcont.comp (continuous_subtype_val.mul continuous_const)).neg)
    have heq : (fun r : unitInterval =>
          rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
            (-paperGerverPath (r.val * (Real.pi / 2)))) =
        (fun q : Real.Angle × Point => (AffineIsometryEquiv.vaddConst ℝ q.2).trans
          (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv) ∘
        (fun r : unitInterval => ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2)))) := rfl
    rw [heq]
    exact continuous_vaddConst_trans_rotation.comp hpair
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathTy : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  -- ### Coordinate images and compactness
  have hKimg : gerverOuterCap =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.Romik.K0 GerverSofa.PartB.params := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext mem_gerverOuterCap_iff
  have hKcomp : IsCompact gerverOuterCap := by
    rw [hKimg]
    exact GerverSofa.PartC.Stage4.K_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  have hGimg : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext fun q =>
      and_congr (mem_gerverOuterCap_iff q) (not_congr (mem_gerverLiteralNiche_iff q))
  have hGcomp : IsCompact gerverLiteralSofa := by
    rw [hGimg]
    exact GerverSofa.PartC.Stage4.G_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  -- ### Contact coordinates in the moving frame
  have hvn : ∀ t : ℝ, inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := fun t => by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hAn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_normalVector_self, hvn t]
    ring
  have hAt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
        (paperGerverVelocityComponents t).1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_tangentVector_self, inner_normalVector_tangentVector]
    ring
  have hCn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) -
        (paperGerverVelocityComponents t).2 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_normalVector_self, hvn t]
    ring
  have hCt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_tangentVector_self,
      inner_normalVector_tangentVector]
    ring
  -- ### The cap is the outer path constraint set
  have hOPCS : outerPathConstraintSet
      (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val) = gerverOuterCap := by
    ext q
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t ht => h ⟨t, ht⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t => h t.val t.2⟩
  -- ### The two normalizing contacts
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [paperGerverVelocityComponents_eq_alphaBetaAt 0 h0mem]
    have hab : GerverSofa.PartC.alphaBetaAt 0 =
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params 0 := by
      rw [GerverSofa.PartC.alphaBetaAt]
      simp [GerverSofa.PartC.Stage4.phi_pos.le]
    have ha2 := GerverSofa.Romik.a2_eq_neg_quarter_of_equations GerverSofa.PartB.params_equations
    rw [hab]
    simp only [GerverSofa.Romik.alphaBeta1, Real.sin_zero, Real.cos_zero, ha2]
    ring
  have hA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 0)
    rw [hAt 0, hpath0, inner_zero_left, halpha0] at h
    linarith
  have hC0y : paperGerverContacts 0 2 1 = 1 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 2)
    rw [hCt 0, hpath0, inner_zero_left] at h
    linarith
  obtain ⟨Kb, hKset, hKcap⟩ := outerPathConstraintSet_isCap
    (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val)
    (by simpa using hpath0)
    ⟨paperGerverContacts 0 0, by rw [hOPCS]; exact gerver_outer_contact_A 0 h0mem, hA0y⟩
    ⟨paperGerverContacts 0 2, by rw [hOPCS]; exact gerver_outer_contact_C 0 h0mem, hC0y⟩
  rw [hOPCS] at hKset
  -- ### Conjunct 1: every cap fibre has a sofa point at least as high
  have hfiber := gerver_cap_fiber_has_sofa_point hKcomp
  -- ### The support values of the cap
  have hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).2
    rw [hpath0, inner_zero_left, inner_tangentVector_zero] at h
    linarith
  have hcapx1 : ∀ q ∈ gerverOuterCap, q 0 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).1
    rw [hpath0, inner_zero_left, inner_normalVector_zero] at h
    linarith
  have hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverOuterCap (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverOuterCap ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    have hAmem := gerver_outer_contact_A t ht
    have hCmem := gerver_outer_contact_C t ht
    have hang : ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        ((t + Real.pi / 2 : ℝ) : Real.Angle) := by rw [add_comm]
    refine ⟨?_, ?_⟩
    · simp only [supportValue]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 0, hAmem, hAn t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).1
    · rw [supportValue, hang, normalVector_add_pi_div_two_real]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 2, hCmem, hCt t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).2
  -- ### Conjunct 4: the sofa and the cap have the same upper support
  have hGne : gerverLiteralSofa.Nonempty := gerver_literal_connected.1
  have hsupeq : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) =
        supportValue gerverOuterCap (s : Real.Angle) := by
    intro s hs
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2
    refine (supportValue_eq_of_subset_of_inner_le hGne (fun z hz => hz.1)
      (s : Real.Angle) ?_).symm
    intro z hz
    obtain ⟨w, hw, hwx, hwy⟩ := hfiber z hz
    have h1 : inner ℝ z (normalVector (s : Real.Angle)) ≤
        inner ℝ w (normalVector (s : Real.Angle)) := by
      rw [inner_normalVector_real, inner_normalVector_real, hwx]
      have := mul_le_mul_of_nonneg_right hwy hsin
      linarith
    exact h1.trans (inner_le_supportValue_of_isCompact hGcomp hw _)
  have hsupG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverLiteralSofa (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverLiteralSofa ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hsupeq t ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩]
      exact (hsupK t ht).1
    · rw [hsupeq (Real.pi / 2 + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      exact (hsupK t ht).2
  -- ### Conjunct 3: standard position
  have hsv1 : supportValue gerverLiteralSofa ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    have h := (hsupG 0 h0mem).2
    rw [add_zero, hpath0, inner_zero_left] at h
    linarith
  have hstd := gerver_literal_standard_position hTpos hTmem hGcomp hmotioncont hpath0 hpathTy
    hcapx1 hcapy1 hsv1
  -- ### Conjunct 5: the paper cap of the sofa is the certified cap
  have hcapOf := gerver_literal_cap_eq hsupG hcapy1
  -- ### Conjunct 6: the cap representative and its contact faces
  have hfaces := gerver_cap_contact_faces Kb hKset hKcap hC1 hAn hAt hCn hCt hsupK hTpos
  refine ⟨hfiber, paperGerverSofa_eq_literal, hstd, hsupeq, hcapOf, hfaces, ?_⟩
  rintro S (rfl | rfl)
  · exact hsupK
  · exact hsupG

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Niche / Identification
-/

public section

noncomputable section

namespace MovingSofa

theorem gerver_paperNiche_identification :
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        supportingHallway paperGerverSofa (t : Real.Angle) ∧
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway ∧
      (rotatingHallwayParts gerverOuterCap (t : Real.Angle)).innerCorner = paperGerverPath t) ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      capNiche K = gerverLiteralNiche) ∧
    monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa ∧
    IsMonotoneSofa paperGerverSofa := by
  obtain ⟨-, hGeq, hstd, -, -, ⟨K, hKset, -⟩, hsup⟩ := gerver_capSupport_identification
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  -- ### The supporting placement is the paper motion
  have hplace : ∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement S (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    intro S hS t ht p
    rw [supportingPlacement, hangsum t, (hsup S hS t ht).1, (hsup S hS t ht).2,
      add_sub_cancel_right, add_sub_cancel_right, add_assoc,
      inner_normalVector_smul_add_inner_tangentVector_smul]
  have hplaceK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement gerverOuterCap (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t :=
    hplace gerverOuterCap (Or.inl rfl)
  have hplaceG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement paperGerverSofa (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    rw [hGeq]
    exact hplace gerverLiteralSofa (Or.inr rfl)
  have hhallG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceG t ht)
  have hhallK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceK t ht)
  -- ### The monotonization fixed point
  have hmono : monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa := by
    rw [monotonization, Set.iInter₂_congr hhallG]
    rfl
  refine ⟨fun t ht => ⟨(hhallK t ht).trans (hhallG t ht).symm, hhallG t ht, ?_⟩, ⟨K, hKset, ?_⟩,
    hmono, paperGerverSofa, Real.pi / 2, by rw [hGeq]; exact hstd, hmono.symm⟩
  · change supportingPlacement gerverOuterCap (t : Real.Angle) hallwayParts.innerCorner =
      paperGerverPath t
    rw [hplaceK t ht]
    change rotationMap (t : Real.Angle) 0 + paperGerverPath t = paperGerverPath t
    rw [rotationMap, map_zero, zero_add]
  -- ### The cap niche is the literal niche
  · have hfan : ∀ q : Point, q ∈ capFan (Real.pi / 2) ↔ 0 ≤ q 1 := by
      intro q
      have h : (q ∈ capFan (Real.pi / 2)) ↔
          ((0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ∧
            (0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))) := Iff.rfl
      rw [h, inner_normalVector_pi_div_two, and_self]
    have hquad : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ q : Point,
        q ∈ innerQuadrant gerverOuterCap t ↔
          inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
            inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0 := by
      intro t ht q
      have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
          ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
      have h : (q ∈ innerQuadrant gerverOuterCap t) ↔
          (inner ℝ q (normalVector (t : Real.Angle)) <
              supportValue gerverOuterCap (t : Real.Angle) - 1 ∧
            inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
              supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := Iff.rfl
      rw [h, normalVector_add_pi_div_two_real, hang,
        (hsup gerverOuterCap (Or.inl rfl) t ht).1, (hsup gerverOuterCap (Or.inl rfl) t ht).2,
        add_sub_cancel_right, add_sub_cancel_right, inner_sub_left, inner_sub_left,
        sub_neg, sub_neg]
    rw [capNiche, hKset]
    ext q
    constructor
    · rintro ⟨hq, hmem⟩
      obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.1 hmem
      exact ⟨(hfan q).1 hq, t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).1 hqt⟩
    · rintro ⟨hy, t, ht, hqt⟩
      exact ⟨(hfan q).2 hy,
        Set.mem_iUnion₂.2 ⟨t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).2 hqt⟩⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Surface densities of the certified Gerver cap

The certified Gerver cap carries the two envelope densities `GerverSofa.PartC.Stage2.rhoA` and
`rhoC` of the vendor development: its surface-area measure is `rhoA (t) dt` on the angular arc
`[0, π/2)` and `rhoC (t - π/2) dt` on `(π/2, π]`.

The argument is stage by stage.  On each of the five closed stages the selected (positive) vertex
of the cap is a globally analytic branch of the certified phase curves, with derivative
`rhoA t • v t` for the first contact and `-rhoC t • u t` for the third, so
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt` identifies the surface measure with
the exact Lebesgue density on that stage.  The stages are then glued with
`measure_angleImage_eq_of_union`; only the last `rhoA` stage needs an interior exhaustion,
because the positive vertex jumps at `π/2`.

The same stagewise phase curves describe the two *inner* contacts, because `B = A - u` and
`D = C - v` differ from the outer contacts by a frame vector
(`paperGerverContacts_one_eq_sub`, `paperGerverContacts_three_eq_sub`).  Subtracting the frame
vector from a phase curve therefore produces a globally differentiable branch curve for `B` on
the last two stages and for `D` on the first two, with the nonnegative speeds `1 - rhoA` and
`1 - rhoC` (`exists_branch_paperGerverContacts_one`,
`exists_branch_paperGerverContacts_three`); the two speed bounds are again coarse box bounds on
the certified parameters.
-/

/-! ### Coordinate transport of derivatives -/

public section

noncomputable section

open scoped NNReal

namespace MovingSofa

open MeasureTheory Set
open scoped ENNReal

/-- The vendor coordinate identification is homogeneous. -/
private theorem toPlane_smul (c : ℝ) (q : GerverSofa.Point) :
    GerverSofa.PartF.Coordinates.toPlane (c • q) =
      c • GerverSofa.PartF.Coordinates.toPlane q := by
  ext i
  fin_cases i <;> rfl

/-! ### The certified switching angles -/

/-- The paper's two switching angles are the vendor parameter angles, strictly ordered. -/
private theorem paperGerver_switchAngles :
    GerverSofa.PartB.params.phi = GerversSofa.φ ∧
      GerverSofa.PartB.params.theta = GerversSofa.θ ∧
      GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta ∧
      GerverSofa.PartB.params.theta < Real.pi / 4 := by
  obtain ⟨-, hphi, htheta, -, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  refine ⟨hphi', htheta', ?_, ?_⟩
  · rw [hphi', htheta']; exact hphitheta
  · rw [htheta']; exact hthetalt

/-! ### The contact curves as transported certified phase curves -/

/-- The first contact of the paper Gerver cap is the transported point `x + α v + u`. -/
private theorem paperGerverContacts_zero_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 0 =
      GerverSofa.PartF.Coordinates.toPlane (X t + (W t).1 • GerverSofa.v t + GerverSofa.u t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, Matrix.cons_val_zero, hw, hp]
  ext i
  fin_cases i <;> rfl

/-- The third contact of the paper Gerver cap is the transported point `x - β u + v`. -/
private theorem paperGerverContacts_two_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 2 =
      GerverSofa.PartF.Coordinates.toPlane (X t - (W t).2 • GerverSofa.u t + GerverSofa.v t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, hw, hp]
  ext i
  fin_cases i <;> rfl

open GerverSofa.PartC.Stage2 GerverSofa.Romik in
/-- On each of the five stages the two contact curves are transported analytic phase curves whose
derivatives are `rA • v` and `-rC • u` for continuous factors agreeing with `rhoA`, `rhoC`. -/
private theorem exists_phaseCurves_of_stage (j : Fin 5) :
    ∃ (PA PC : ℝ → GerverSofa.Point) (rA rC : ℝ → ℝ),
      (∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t) ∧
      (∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) ∧
      Continuous rA ∧ Continuous rC ∧
      (∀ t ∈ gerverStageIntervals j,
        paperGerverContacts t 0 = GerverSofa.PartF.Coordinates.toPlane (PA t) ∧
        paperGerverContacts t 2 = GerverSofa.PartF.Coordinates.toPlane (PC t)) ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes j.castSucc) (gerverStageTimes j.succ),
        rhoA t = rA t ∧ rhoC t = rC t) := by
  classical
  obtain ⟨hphi', htheta', hφθ', hθq'⟩ := paperGerver_switchAngles
  have heqs : Equations GerverSofa.PartB.params := GerverSofa.PartB.params_equations
  have hφθ : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact hφθ'
  have hθq : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact hθq'
  have hθη : GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.θ := by
    have := GerverSofa.PartC.switchOrder.theta_le_eta
    rw [htheta'] at this; exact this
  have hητ : Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.φ := by linarith
  have heta : GerverSofa.PartC.eta = Real.pi / 2 - GerversSofa.θ := by
    simp only [GerverSofa.PartC.eta, GerverSofa.PartC.T, htheta']
  have htau : GerverSofa.PartC.tau = Real.pi / 2 - GerversSofa.φ := by
    simp only [GerverSofa.PartC.tau, GerverSofa.PartC.T, hphi']
  have hvel : ∀ (i : Fin 5), ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t :=
    paperGerverContactData_properties.2.2.2
  fin_cases j
  · refine ⟨phaseA1, phaseC1, fun _ ↦ 0, fun _ ↦ 1 / 2, fun t ↦ A1_hasDerivAt_public t,
      fun t ↦ C1_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path1 GerverSofa.PartB.params t :=
        path_eq_path1_of_mem_Icc _ (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta1 GerverSofa.PartB.params t :=
        hvel 0 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA2, phaseC2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
        GerverSofa.PartC.params.b2 + 1 / 2,
      fun t ↦ t / 2 - GerverSofa.PartC.params.b1,
      fun t ↦ A2_hasDerivAt_public t, fun t ↦ C2_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path2 GerverSofa.PartB.params t :=
        path_eq_path2_of_mem_Icc heqs (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta2 GerverSofa.PartB.params t :=
        hvel 1 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA3, phaseC3, fun t ↦ 1 + GerverSofa.PartC.params.c1 - t,
      fun t ↦ 1 + GerverSofa.PartC.params.c2 + t,
      fun t ↦ A3_hasDerivAt_public t, fun t ↦ C3_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path3 GerverSofa.PartB.params t :=
        path_eq_path3_of_mem_Icc heqs hφθ' (by rw [htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta3 GerverSofa.PartB.params t :=
        hvel 2 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA4, phaseC4, fun t ↦ GerverSofa.PartC.params.d1 - t / 2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
        GerverSofa.PartC.params.d2 + 1 / 2,
      fun t ↦ A4_hasDerivAt_public t, fun t ↦ C4_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path4 GerverSofa.PartB.params t :=
        path_eq_path4_of_mem_Icc heqs hφθ' hθq' (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta4 GerverSofa.PartB.params t :=
        hvel 3 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA5, phaseC5, fun _ ↦ 1 / 2, fun _ ↦ 0, fun t ↦ A5_hasDerivAt_public t,
      fun t ↦ by simpa using C5_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · change ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path5 GerverSofa.PartB.params t :=
        path_eq_path5_of_mem_Icc heqs hφθ' hθq' (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta5 GerverSofa.PartB.params t :=
        hvel 4 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · change ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])

/-! ### Contact derivatives on the open stages -/

/-- A branch curve agreeing with a global curve on a closed stage computes the global derivative
at every interior parameter of that stage. -/
theorem hasDerivAt_of_eqOn_stage {G F : ℝ → Point} {w : ℝ → Point} {i : Fin 5}
    (hF : ∀ s, HasDerivAt F (w s) s) (hGF : ∀ t ∈ gerverStageIntervals i, G t = F t)
    {t : ℝ} (ht : t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)) :
    HasDerivAt G (w t) t :=
  (hF t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun u hu ↦ hGF u (Set.Ioo_subset_Icc_self hu))

/-- The transported phase curves of a stage are differentiable everywhere, with the two branch
speeds against the moving frame. -/
private theorem hasDerivAt_toPlane_phaseCurves {PA PC : ℝ → GerverSofa.Point}
    {rA rC : ℝ → ℝ} (hPA : ∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t)
    (hPC : ∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) :
    (∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PA u))
        (rA s • tangentVector (s : Real.Angle)) s) ∧
      ∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PC u))
        (-(rC s) • normalVector (s : Real.Angle)) s := by
  refine ⟨fun s ↦ ?_, fun s ↦ ?_⟩
  · have h := hasDerivAt_toPlane (hPA s)
    rwa [toPlane_smul] at h
  · have h := hasDerivAt_toPlane (hPC s)
    rwa [toPlane_smul] at h

/-- Inside each open stage the two contact curves are differentiable with the envelope
densities as their speed factors. -/
private theorem hasDerivAt_paperGerverContacts_of_mem_stage (j : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ)) :
    HasDerivAt (fun u ↦ paperGerverContacts u 0)
        (GerverSofa.PartC.Stage2.rhoA t • tangentVector (t : Real.Angle)) t ∧
      HasDerivAt (fun u ↦ paperGerverContacts u 2)
        (-(GerverSofa.PartC.Stage2.rhoC t) • normalVector (t : Real.Angle)) t := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, -, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  obtain ⟨hrA, hrC⟩ := hrho t (Set.Ioo_subset_Ioc_self ht)
  obtain ⟨hA, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  refine ⟨?_, ?_⟩
  · rw [hrA]
    exact hasDerivAt_of_eqOn_stage hA (fun u hu ↦ (hmem u hu).1) ht
  · rw [hrC]
    exact hasDerivAt_of_eqOn_stage hC (fun u hu ↦ (hmem u hu).2) ht

/-! ### Singleton faces have no surface atom -/

/-- A face whose positive tangent endpoint does not exceed its negative one carries no surface
atom: the atom is exactly the tangential gap between the two endpoints. -/
private theorem surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le
    (K : ConvexBody Point) (t : Real.Angle)
    (h : inner ℝ (edgeVertices K t).1 (tangentVector t) ≤
      inner ℝ (edgeVertices K t).2 (tangentVector t)) :
    surfaceAreaMeasure K {t} = 0 := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hsplit := (surfaceAreaMeasure_atom_length K t).2.2
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_tangentVector]
    norm_num
  have hinner : inner ℝ (edgeVertices K t).1 (tangentVector t) =
      inner ℝ (edgeVertices K t).2 (tangentVector t) +
        (surfaceAreaMeasure K {t}).toReal := by
    rw [hsplit, inner_add_left, real_inner_smul_left, hone, mul_one]
  have hle : (surfaceAreaMeasure K {t}).toReal ≤ 0 := by linarith
  have hzero : (surfaceAreaMeasure K {t}).toReal = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with h0 | htop
  · exact h0
  · exact absurd htop (measure_ne_top _ _)

/-! ### Measurability and boundedness of the two envelope densities -/

private theorem measurable_rhoA : Measurable GerverSofa.PartC.Stage2.rhoA := by
  unfold GerverSofa.PartC.Stage2.rhoA
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

private theorem measurable_rhoC : Measurable GerverSofa.PartC.Stage2.rhoC := by
  unfold GerverSofa.PartC.Stage2.rhoC
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

open GerverSofa.PartC.Stage2 in
/-- Each of the finitely many branch polynomials of the two envelope densities is continuous,
hence bounded on the compact physical interval. -/
private theorem exists_bound_rhoA_rhoC : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    rhoA t ≤ M ∧ rhoC t ≤ M := by
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), f t ≤ M := by
    intro f hf
    obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 (show (0 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos]))
      hf.continuousOn
    exact ⟨f x, fun t ht ↦ isMaxOn_iff.1 hmax t ht⟩
  obtain ⟨M1, h1⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
    GerverSofa.PartC.params.b2 + 1 / 2) (by fun_prop)
  obtain ⟨M2, h2⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c1 - t) (by fun_prop)
  obtain ⟨M3, h3⟩ := key (fun t ↦ GerverSofa.PartC.params.d1 - t / 2) (by fun_prop)
  obtain ⟨M4, h4⟩ := key (fun t ↦ t / 2 - GerverSofa.PartC.params.b1) (by fun_prop)
  obtain ⟨M5, h5⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c2 + t) (by fun_prop)
  obtain ⟨M6, h6⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
    GerverSofa.PartC.params.d2 + 1 / 2) (by fun_prop)
  refine ⟨max (max (max M1 M2) (max M3 M4)) (max (max M5 M6) 1), fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [rhoA]
    split_ifs
    · exact le_trans (by norm_num) (le_max_right _ _ |>.trans' (le_max_right _ _))
    · exact (h1 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    · exact (h2 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
    · exact (h3 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
  · rw [rhoC]
    split_ifs
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
    · exact (h4 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))
    · exact (h5 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
    · exact (h6 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))

/-! ### Elementary facts about the stage endpoints and the frame -/

/-- The two Gerver switch angles satisfy `0 < φ < θ < π/4`. -/
private theorem gerver_switch_angle_bounds :
    (0 : ℝ) < GerversSofa.φ ∧ GerversSofa.φ < GerversSofa.θ ∧ GerversSofa.θ < Real.pi / 4 := by
  obtain ⟨-, -, -, hpos, hlt, hq, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  refine ⟨selected_phi ▸ hpos, ?_, selected_theta ▸ hq⟩
  rw [← selected_phi, ← selected_theta]
  exact hlt

private theorem gerverStageTimes_nonneg (k : Fin 6) : 0 ≤ gerverStageTimes k := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · change (0 : ℝ) ≤ 0
    exact le_refl 0
  · change (0 : ℝ) ≤ GerversSofa.φ
    linarith
  · change (0 : ℝ) ≤ GerversSofa.θ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.θ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.φ
    linarith
  · change (0 : ℝ) ≤ Real.pi / 2
    linarith

private theorem gerverStageTimes_le_pi_div_two (k : Fin 6) : gerverStageTimes k ≤ Real.pi / 2 := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · change (0 : ℝ) ≤ Real.pi / 2
    linarith
  · change GerversSofa.φ ≤ Real.pi / 2
    linarith
  · change GerversSofa.θ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 - GerversSofa.φ ≤ Real.pi / 2
    linarith
  · change Real.pi / 2 ≤ Real.pi / 2
    exact le_refl _

private theorem gerverStageTimes_lt_succ (j : Fin 5) :
    gerverStageTimes j.castSucc < gerverStageTimes j.succ := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases j
  · change (0 : ℝ) < GerversSofa.φ
    linarith
  · change GerversSofa.φ < GerversSofa.θ
    linarith
  · change GerversSofa.θ < Real.pi / 2 - GerversSofa.θ
    linarith
  · change Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ
    linarith
  · change Real.pi / 2 - GerversSofa.φ < Real.pi / 2
    linarith

private theorem gerverStageTimes_four_lt_pi_div_two : gerverStageTimes 4 < Real.pi / 2 := by
  have h : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  linarith

/-! ### Almost every parameter lies in an open stage -/

/-- A parameter of the rotation interval that is none of the six stage times lies in an open
stage. -/
theorem mem_openStage_of_mem_Ico {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2))
    (hne : ∀ k : Fin 6, t ≠ gerverStageTimes k) :
    ∃ j : Fin 5, t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  have hlow : gerverStageTimes 0 < t :=
    lt_of_le_of_ne (gerverStageTimes_zero ▸ ht.1) fun h ↦ hne 0 h.symm
  have hhigh : t < gerverStageTimes 5 := ht.2
  rcases lt_or_gt_of_ne (hne 1) with h1 | h1
  · exact ⟨0, hlow, h1⟩
  · rcases lt_or_gt_of_ne (hne 2) with h2 | h2
    · exact ⟨1, h1, h2⟩
    · rcases lt_or_gt_of_ne (hne 3) with h3 | h3
      · exact ⟨2, h2, h3⟩
      · rcases lt_or_gt_of_ne (hne 4) with h4 | h4
        · exact ⟨3, h3, h4⟩
        · exact ⟨4, h4, hhigh⟩

/-- Almost every parameter of a measurable subset of the shifted rotation interval lies in a
shifted open stage. -/
theorem ae_mem_openStage (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc c (c + Real.pi / 2)) :
    ∀ᵐ u ∂volume.restrict S, ∃ j : Fin 5,
      u - c ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  refine ae_restrict_mem_of_countable_diff hS
    (((Set.finite_range gerverStageTimes).countable).image fun x ↦ x + c) ?_
  rintro u ⟨hu, hu'⟩
  by_contra hcon
  have hne : ∀ k : Fin 6, u - c ≠ gerverStageTimes k := by
    intro k hk
    exact hcon ⟨gerverStageTimes k, Set.mem_range_self k, by rw [← hk]; ring⟩
  have hmem : u - c ∈ Set.Ico (0 : ℝ) (Real.pi / 2) := by
    refine ⟨by linarith [(hSsub hu).1], ?_⟩
    have h5 : u - c ≠ gerverStageTimes 5 := hne 5
    rw [show gerverStageTimes 5 = Real.pi / 2 from rfl] at h5
    exact lt_of_le_of_ne (by linarith [(hSsub hu).2]) h5
  exact hu' (mem_openStage_of_mem_Ico hmem hne)

/-! ### Branch curves for the two inner contacts

The second contact `B = x + α v` is the first contact `A = x + α v + u` translated by `-u`, and
the fourth contact `D = x - β u` is the third contact `C = x - β u + v` translated by `-v`.  So
subtracting a frame vector from the transported phase curve of a stage produces a globally
differentiable branch curve for `B` and for `D`, whose speed against the frame is `1 - rhoA`
resp. `1 - rhoC`.  Both are nonnegative exactly where the inner contact is a genuine contact:
after the third stage time for `B` and before the second for `D`.
-/

/-- The second contact curve is the first one translated by `-u_t`. -/
theorem paperGerverContacts_one_eq_sub (t : ℝ) :
    paperGerverContacts t 1 = paperGerverContacts t 0 - normalVector (t : Real.Angle) := by
  change _ = paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle) + normalVector (t : Real.Angle) - normalVector _
  rw [add_sub_cancel_right]
  rfl

/-- The fourth contact curve is the third one translated by `-v_t`. -/
theorem paperGerverContacts_three_eq_sub (t : ℝ) :
    paperGerverContacts t 3 = paperGerverContacts t 2 - tangentVector (t : Real.Angle) := by
  change _ = paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) - tangentVector _
  rw [add_sub_cancel_right]
  rfl

open GerverSofa.PartC.Stage2 in
/-- After the third stage time the first contact never outruns the rotating frame: its tangential
speed `rhoA` is at most the unit speed of `u`.  On the fourth stage this is the coarse bound
`d₁ ≤ 33/25` against `t > π/2 - θ > 4/5`; on the fifth the speed is the constant `1/2`. -/
private theorem rhoA_le_one_of_gerverStageTimes_three_lt {t : ℝ}
    (ht : gerverStageTimes 3 < t) : rhoA t ≤ 1 := by
  have h1 : gerverStageTimes 1 = GerverSofa.PartB.params.phi := gerverStageTimes_one
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have h3 : gerverStageTimes 3 = GerverSofa.PartC.eta := gerverStageTimes_three
  have h4 : gerverStageTimes 4 = GerverSofa.PartC.tau := gerverStageTimes_four
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have h32 : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
  have hd1 := gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  have hpi := Real.pi_gt_three
  rw [rhoA]
  split_ifs with hphi htheta heta
  · exact absurd (h1 ▸ hphi) (by linarith)
  · exact absurd (h2 ▸ htheta) (by linarith)
  · exact absurd (h3 ▸ heta) (by linarith)
  · linarith
  · norm_num

open GerverSofa.PartC.Stage2 in
/-- Before the second stage time the third contact never outruns the rotating frame: its normal
speed `rhoC` is at most the unit speed of `v`.  On the first stage the speed is the constant
`1/2`; on the second this is the coarse bound `b₁ ≥ -53/100` against `t ≤ θ ≤ 7/10`. -/
private theorem rhoC_le_one_of_le_gerverStageTimes_two {t : ℝ}
    (ht : t ≤ gerverStageTimes 2) : rhoC t ≤ 1 := by
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have hb1 := gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  rw [rhoC]
  split_ifs with hphi htheta
  · norm_num
  · linarith
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)

/-- On each of the last two stages the second contact curve agrees with a globally differentiable
branch curve whose derivative is `-(g t) • v_t` for a continuous factor `g` that is nonnegative
on the stage. -/
theorem exists_branch_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 1 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, -, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨hA, -⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have h3i : gerverStageTimes 3 ≤ gerverStageTimes i.castSucc :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s) - normalVector (s : Real.Angle),
    fun s ↦ 1 - rA s, fun s ↦ ?_, continuous_const.sub hcA, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hA s).sub (hasDerivAt_normalVector s)).congr_deriv ?_
    module
  · have hrA := (hrho t ht).1
    linarith [rhoA_le_one_of_gerverStageTimes_three_lt (lt_of_le_of_lt h3i ht.1)]
  · rw [paperGerverContacts_one_eq_sub, (hmem t ht).1]

/-- On each of the first two stages the fourth contact curve agrees with a globally differentiable
branch curve whose derivative is `g t • u_t` for a continuous factor `g` that is nonnegative on
the stage. -/
theorem exists_branch_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (g s • normalVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 3 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨-, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have hi2 : gerverStageTimes i.succ ≤ gerverStageTimes 2 :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC s) - tangentVector (s : Real.Angle),
    fun s ↦ 1 - rC s, fun s ↦ ?_, continuous_const.sub hcC, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hC s).sub (hasDerivAt_tangentVector s)).congr_deriv ?_
    module
  · have hrC := (hrho t ht).2
    linarith [rhoC_le_one_of_le_gerverStageTimes_two (le_trans ht.2 hi2)]
  · rw [paperGerverContacts_three_eq_sub, (hmem t ht).2]

/-! ### The certified cap witness and its positive vertex curves -/

/-- The certified cap witness of support identification, together with the identification of its
positive vertex by the two contact curves on the whole closed parameter interval and the
vanishing of the surface atom at the included endpoint `0`.

Both included endpoint faces are singletons: at `0` the first contact is the anchor `(1, 0)`
and the cap lies in `0 ≤ q 1`, and at `π` the third contact has vanishing second coordinate,
so in each case the positive tangent endpoint cannot exceed the negative one. -/
private theorem exists_gerverCap_positiveVertex :
    ∃ K : CapSpace (Real.pi / 2),
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 ∧
      (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
        (edgeVertices K.val ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0) ∧
      (∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
        (edgeVertices K.val ((s : ℝ) : Real.Angle)).1 =
          paperGerverContacts (s - Real.pi / 2) 2) := by
  have hpi := Real.pi_gt_three
  have hTpos : (0 : ℝ) < Real.pi / 2 := by linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  obtain ⟨-, hpaper, -, -, hcapEq, ⟨K, hKset, hedges, hA0, -, hC0, hCT⟩, -⟩ :=
    gerver_capSupport_identification
  have hKupper : ∀ q ∈ (K.val : Set Point), 0 ≤ q 1 := by
    intro q hq
    rw [hKset] at hq
    exact hq.1
  -- the two included endpoint contacts lie on the lower fan boundary
  have hcontactA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := fromPlane_paperGerverContacts 0 h0mem 0
    have h2 : paperGerverContacts 0 0 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.A 0) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane (paperGerverContacts 0 0), h]
      rfl
    rw [h2, GerverSofa.PartC.Stage2.A_zero_eq_anchor]
    rfl
  have hcontactCTy : paperGerverContacts (Real.pi / 2) 2 1 = 0 := by
    have h := fromPlane_paperGerverContacts (Real.pi / 2) hTmem 2
    have h2 : paperGerverContacts (Real.pi / 2) 2 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.C (Real.pi / 2)) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane
        (paperGerverContacts (Real.pi / 2) 2), h]
      rfl
    rw [h2]
    exact GerverSofa.PartC.Stage2.C_T_snd_zero
  -- hence both included endpoint faces are singletons and carry no atom
  have hatom0 : surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    have hfst : (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 = paperGerverContacts 0 0 := by
      rw [Real.Angle.coe_zero]
      exact hA0.symm
    rw [inner_tangentVector_zero, inner_tangentVector_zero, hfst, hcontactA0y]
    exact hKupper _ (edgeVertices_snd_mem K.val _).1
  have hatompi : surfaceAreaMeasure K.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    rw [inner_tangentVector_pi, inner_tangentVector_pi, ← hCT, hcontactCTy]
    have h := hKupper _ (edgeVertices_fst_mem K.val ((Real.pi : ℝ) : Real.Angle)).1
    linarith
  refine ⟨K, by rw [hpaper, hcapEq]; exact hKset, hatom0, ?_, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, Real.Angle.coe_zero]
      exact hA0.symm
    · rw [edgeVertices_eq_of_exposedEdge_singleton (hedges t ⟨h, ht.2⟩).1]
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, sub_self]
      exact hC0.symm
    rcases eq_or_lt_of_le hs.2 with h2 | h2
    · have hatom := (surfaceAreaMeasure_atom_length K.val ((Real.pi : ℝ) : Real.Angle)).2.2
      rw [hatompi] at hatom
      simp only [ENNReal.toReal_zero, zero_smul, add_zero] at hatom
      rw [h2, show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring, hatom, ← hCT]
    · have htmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith, by linarith⟩
      have h := (hedges (s - Real.pi / 2) htmem).2
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      rw [edgeVertices_eq_of_exposedEdge_singleton h]

/-! ### The stagewise density identities -/

/-- On a subinterval of a single stage, strictly below the switch `π/2`, the surface measure of
an angular image is the `rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (j : Fin 5) (a b : ℝ) (hja : gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ gerverStageTimes j.succ) (hbT : b < Real.pi / 2)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : 0 ≤ a := le_trans (gerverStageTimes_nonneg _) hja
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s)) rA
    GerverSofa.PartC.Stage2.rhoA (fun s ↦ ?_) hcA ?_ ?_ ?_ S hS hSsub
  · have h := hasDerivAt_toPlane (hPA s)
    rw [toPlane_smul] at h
    exact h
  · intro s hs
    rw [hvertexA s ⟨le_trans ha0 hs.1, lt_of_le_of_lt hs.2 hbT⟩]
    exact (hmem s ⟨le_trans hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    exact (hrho s ⟨lt_of_le_of_lt hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s := by linarith [hs.1]
    have hsT : s ≤ Real.pi / 2 := by linarith [hs.2]
    exact GerverSofa.PartC.Stage2.rhoA_nonneg ⟨hs0, hsT⟩

/-- On a subinterval of a single shifted stage the surface measure of an angular image is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (j : Fin 5) (a b : ℝ) (hja : Real.pi / 2 + gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ Real.pi / 2 + gerverStageTimes j.succ)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : Real.pi / 2 ≤ a := le_trans (by linarith [gerverStageTimes_nonneg j.castSucc]) hja
  have hbpi : b ≤ Real.pi := by
    have := gerverStageTimes_le_pi_div_two j.succ
    linarith
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC (s - Real.pi / 2)))
    (fun s ↦ rC (s - Real.pi / 2))
    (fun u ↦ GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2)) (fun s ↦ ?_)
    (hcC.comp (continuous_id.sub continuous_const)) ?_ ?_ ?_ S hS hSsub
  · have hinner : HasDerivAt (fun x : ℝ ↦ x - Real.pi / 2) 1 s :=
      (hasDerivAt_id s).sub_const _
    have h1 : HasDerivAt (fun x : ℝ ↦ PC (x - Real.pi / 2))
        (-(rC (s - Real.pi / 2)) • GerverSofa.u (s - Real.pi / 2)) s := by
      simpa [Function.comp_def] using (hPC (s - Real.pi / 2)).scomp s hinner
    have h2 := hasDerivAt_toPlane h1
    rw [toPlane_smul] at h2
    have hangle : tangentVector ((s : ℝ) : Real.Angle) =
        -normalVector (((s - Real.pi / 2 : ℝ)) : Real.Angle) := by
      have h := tangentVector_add_pi_div_two (s - Real.pi / 2)
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      exact h
    rw [hangle, smul_neg, ← neg_smul]
    exact h2
  · intro s hs
    rw [hvertexC s ⟨le_trans ha0 hs.1, le_trans hs.2 hbpi⟩]
    exact (hmem (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    exact (hrho (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s - Real.pi / 2 := by linarith [hs.1]
    have hsT : s - Real.pi / 2 ≤ Real.pi / 2 := by linarith [hs.2, hbpi]
    exact GerverSofa.PartC.Stage2.rhoC_nonneg ⟨hs0, hsT⟩

/-! ### Exhausting the last stage of the first arc from inside -/

/-- The positive vertex jumps at `π/2`, so the last `rhoA` stage is reached by exhausting its
open interval by half-open subintervals. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage
    (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo (gerverStageTimes 4) (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have hpos : 0 < Real.pi / 2 - gerverStageTimes 4 := by linarith
  have hbnlt : ∀ n : ℕ, Real.pi / 2 -
      (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 := by
    intro n
    have h : 0 < (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) := by positivity
    linarith
  refine measure_angleImage_eq_of_iUnion
    (J := fun n : ℕ ↦ Set.Ioc (gerverStageTimes 4)
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2)))
    ?_ (fun n ↦ measurableSet_Ioc) ?_ S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have hmn' : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    have hd : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) ≤
        (Real.pi / 2 - gerverStageTimes 4) / ((m : ℝ) + 2) := by
      gcongr
    linarith
  · intro n S' hS' hS'sub
    exact surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 4 _ _
      (le_refl _) (hbnlt n).le (hbnlt n) S' hS' hS'sub
  · intro x hx
    have hx' := hSsub hx
    obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / 2 - gerverStageTimes 4) / (Real.pi / 2 - x))
    refine Set.mem_iUnion.2 ⟨n, ⟨hx'.1, ?_⟩⟩
    have h1 : 0 < Real.pi / 2 - x := by linarith [hx'.2]
    rw [div_lt_iff₀ h1] at hn
    have h4 : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [h1]
    linarith

/-! ### Gluing two adjacent arcs -/

/-- Two adjacent windows inside `[0, π/2]` on which the `rhoA` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi / 2)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Icc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioc_eq_Icc hxy hyz]
    exact hSsub

/-- Two adjacent windows inside `[π/2, π]` on which the `rhoC` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : Real.pi / 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Ioc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := Real.pi / 2) (d := Real.pi) (by linarith)
    (I := Set.Ioc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Ioc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Ioc_union_Ioc_eq_Ioc hxy hyz]
    exact hSsub

/-! ### The density identity on each full arc -/

/-- The surface measure of the angular image of any measurable subset of `[0, π/2)` is the
`rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA (K : ConvexBody Point)
    (hatom0 : surfaceAreaMeasure K {((0 : ℝ) : Real.Angle)} = 0)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have h1T : gerverStageTimes 1 < Real.pi / 2 := by linarith
  have h2T : gerverStageTimes 2 < Real.pi / 2 := by linarith
  have h3T : gerverStageTimes 3 < Real.pi / 2 := by linarith
  have h04 : gerverStageTimes 0 ≤ gerverStageTimes 4 := by linarith
  -- the left endpoint carries no atom
  have hzeroA : ∀ S, MeasurableSet S →
      S ⊆ Set.Icc (gerverStageTimes 0) (gerverStageTimes 0) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
    intro S hS hSsub
    have h1 : surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = 0 := by
      refine measure_mono_null ?_ hatom0
      rintro u ⟨x, hx, rfl⟩
      have hx' := hSsub hx
      rw [Set.Icc_self, Set.mem_singleton_iff, hT0] at hx'
      rw [hx']
      exact rfl
    have h2 : volume.withDensity
        (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S = 0 := by
      refine measure_mono_null hSsub ?_
      rw [Set.Icc_self]
      exact (withDensity_absolutelyContinuous volume _) (measure_singleton _)
    rw [h1, h2]
  -- glue the left endpoint and the first four stages
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 0) (gerverStageTimes 1)
    hT0.ge le_rfl hlt01.le h1T.le hzeroA
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 0 _ _
      (le_refl _) (le_refl _) h1T)
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 1) (gerverStageTimes 2)
    hT0.ge hlt01.le hlt12.le h2T.le hstep1
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 1 _ _
      (le_refl _) (le_refl _) h2T)
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 2) (gerverStageTimes 3)
    hT0.ge (by linarith) hlt23.le h3T.le hstep2
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 2 _ _
      (le_refl _) (le_refl _) h3T)
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 3) (gerverStageTimes 4)
    hT0.ge (by linarith) hlt34.le h4T.le hstep3
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 3 _ _
      (le_refl _) (le_refl _) h4T)
  -- glue the exhausted last stage
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc (gerverStageTimes 0) (gerverStageTimes 4))
    (J := Set.Ioo (gerverStageTimes 4) (Real.pi / 2))
    (fun u hu ↦ ⟨by linarith [hu.1, hT0], by linarith [hu.2, h4T]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1, hT0, h04], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioo ?_ hstep4
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage K hvertexA) S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioo_eq_Ico h04 h4T, hT0]
    exact hSsub

/-- The surface measure of the angular image of any measurable subset of `(π/2, π]` is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hT5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have hlt45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have hc0 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 0
    (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) (le_refl _) (le_refl _)
  have hc1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 1
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) (le_refl _) (le_refl _)
  have hc2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 2
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3) (le_refl _) (le_refl _)
  have hc3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 3
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4) (le_refl _) (le_refl _)
  have hc4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 4
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5) (le_refl _) (le_refl _)
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 2]) hc0 hc1
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 3]) hstep1 hc2
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 4]) hstep2 hc3
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 5]) hstep3 hc4
  refine hstep4 S hS ?_
  rw [hT0, hT5, add_zero]
  exact hSsub

theorem gerver_surface_densities :
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      ∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
        (∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (r t : ℝ) ≤ M ∧ (s t : ℝ) ≤ M) ∧
        (∀ i : Fin 5, ∀ t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ),
          HasDerivAt (fun u ↦ paperGerverContacts u 0)
            ((r t : ℝ) • tangentVector (t : Real.Angle)) t ∧
          HasDerivAt (fun u ↦ paperGerverContacts u 2)
            (-(s t : ℝ) • normalVector (t : Real.Angle)) t) := by
  obtain ⟨K, hKcap, hatom0, hvertexA, hvertexC⟩ := exists_gerverCap_positiveVertex
  obtain ⟨M, hM⟩ := exists_bound_rhoA_rhoC
  refine ⟨K, hKcap, fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoA t),
    fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoC t),
    ⟨measurable_real_toNNReal.comp measurable_rhoA,
      measurable_real_toNNReal.comp measurable_rhoC, ?_, ?_⟩,
    ⟨max M 0, fun t ht ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · exact surfaceAreaMeasure_restrict_eq_map_withDensity measurableSet_Ico
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA K.val hatom0 hvertexA)
  · rw [show Set.Ioc (Real.pi / 2) Real.pi =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2) from by
        rw [show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]]
    exact surfaceAreaMeasure_restrict_eq_map_add_withDensity
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoC K.val hvertexC)
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).1 le_rfl
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).2 le_rfl
  · intro i t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨le_trans (gerverStageTimes_nonneg _) ht.1.le,
        le_trans ht.2.le (gerverStageTimes_le_pi_div_two _)⟩
    obtain ⟨hA, hC⟩ := hasDerivAt_paperGerverContacts_of_mem_stage i ht
    rw [Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoA_nonneg htIcc),
      Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoC_nonneg htIcc)]
    exact ⟨hA, hC⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Velocity And Cap Area
-/

public section

noncomputable section

namespace MovingSofa

theorem gerver_strict_velocity (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (paperGerverVelocityComponents t).1 < 0 ∧ 0 < (paperGerverVelocityComponents t).2 ∧
    inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    0 < inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)) := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, -, -, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have hphi0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ha1lo, -, -, -, hb1lo, hb1hi, hb2lo, -, hc1lo, -, hc2lo, -, hd1lo, -, hd2lo, -,
      -, -, -, -, -, hphihi, -, hthetahi⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have hb1u : p.b1 ≤ -(1 / 2 : ℝ) := le_trans hb1hi (by norm_num)
  have hb1l : -(53 / 100 : ℝ) ≤ p.b1 := le_trans (by norm_num) hb1lo
  have hb2 : (9 : ℝ) / 10 ≤ p.b2 := le_trans (by norm_num) hb2lo
  have hc1 : (3 : ℝ) / 5 ≤ p.c1 := le_trans (by norm_num) hc1lo
  have hc2 : (-1 : ℝ) ≤ p.c2 := le_trans (by norm_num) hc2lo
  have hd1 : (13 : ℝ) / 10 ≤ p.d1 := le_trans (by norm_num) hd1lo
  have hd2 : -(53 / 100 : ℝ) ≤ p.d2 := le_trans (by norm_num) hd2lo
  have hphiu : p.phi ≤ (1 : ℝ) / 20 := le_trans hphihi (by norm_num)
  have hthetau : p.theta ≤ (7 : ℝ) / 10 := le_trans hthetahi (by norm_num)
  have hpilo : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpihi : Real.pi < (63 : ℝ) / 20 := by linarith only [Real.pi_lt_d2]
  -- The two strict first-phase estimates, also used on the reflected fifth phase.
  have hkeyA : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (alphaBeta1 p s).1 ≤ -(2 * s) := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsin0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hspi
    have hsinlo : s - s ^ 3 / 6 ≤ Real.sin s := Real.sin_ge_sub_cube hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hmul : (12 / 5 : ℝ) * Real.sin s ≤ 2 * p.a1 * Real.sin s := by
      nlinarith only [ha1, hsin0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
      mul_nonneg (sq_nonneg s) (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinlo, hcoslo, hquad, hcube, hs0]
  have hkeyB : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (343 : ℝ) / 250 ≤ (alphaBeta1 p s).2 := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsinhi : Real.sin s ≤ s := Real.sin_le hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hcos0 : 0 ≤ Real.cos s :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hs0, hpilo], by linarith only [hs20, hpilo]⟩
    have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * p.a1 * Real.cos s := by
      nlinarith only [ha1, hcos0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinhi, hcoslo, hquad, hs0, hs20]
  -- The fifth phase is the reflection of the first one through the angle `π/4`.
  have hrefl : ∀ s : ℝ, alphaBeta5 p (Real.pi / 2 - s) =
      (-(alphaBeta1 p s).2, -(alphaBeta1 p s).1) := by
    intro s
    dsimp [alphaBeta5, alphaBeta1]
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, he1, he2]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  have hmain : (paperGerverVelocityComponents t).1 < 0 ∧
      0 < (paperGerverVelocityComponents t).2 := by
    rcases le_or_gt t p.phi with hs1 | hs1
    · -- Phase 1: `α ≤ -2t < 0` and `β ≥ 343/250 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta1 p t := by
        rw [hval 0 t (by rw [hI0]; exact ⟨ht.1.le, hs1⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (1 : ℝ) / 20 := le_trans hs1 hphiu
      rw [hv]
      exact ⟨by linarith only [hkeyA t ht.1.le htu, ht.1],
        by linarith only [hkeyB t ht.1.le htu]⟩
    rcases le_or_gt t p.theta with hs2 | hs2
    · -- Phase 2: `α ≤ -t < 0` and `β ≥ 1813/2000 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta2 p t := by
        rw [hval 1 t (by rw [hI1]; exact ⟨hs1.le, hs2⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (7 : ℝ) / 10 := le_trans hs2 hthetau
      have hbt : 0 ≤ (p.b1 + 53 / 100) * t := mul_nonneg (by linarith only [hb1l]) ht.1.le
      have hst : 0 ≤ ((7 : ℝ) / 10 - t) * t := mul_nonneg (by linarith only [htu]) ht.1.le
      rw [hv]
      dsimp [alphaBeta2]
      exact ⟨by linarith only [hb1u, ht.1], by linarith only [hb2, hbt, hst, htu]⟩
    rcases le_or_gt t (Real.pi / 2 - p.theta) with hs3 | hs3
    · -- Phase 3: `α ≤ -t < 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta3 p t := by
        rw [hval 2 t (by rw [hI2]; exact ⟨hs2.le, hs3⟩)]
        simp [gerverBranchVelocityComponents, hp]
      rw [hv]
      dsimp [alphaBeta3]
      exact ⟨by linarith only [hc2, ht.1], by linarith only [hc1, ht.2, hpihi]⟩
    rcases le_or_gt t (Real.pi / 2 - p.phi) with hs4 | hs4
    · -- Phase 4: `-α > 69/100 > 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta4 p t := by
        rw [hval 3 t (by rw [hI3]; exact ⟨hs3.le, hs4⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htlo : (4 : ℝ) / 5 < t := by linarith only [hs3, hthetau, hpilo]
      have hthi : t < (8 : ℝ) / 5 := by linarith only [ht.2, hpihi]
      have hcoef : (9 : ℝ) / 10 ≤ p.d1 - t / 4 := by linarith only [hd1, hthi]
      have hprod : (18 : ℝ) / 25 < t * (p.d1 - t / 4) := by nlinarith only [htlo, hcoef]
      rw [hv]
      dsimp [alphaBeta4]
      exact ⟨by linarith only [hprod, hd2], by linarith only [hd1, hthi]⟩
    · -- Phase 5: the reflected first-phase estimates at `s = π/2 - t ∈ (0, φ]`.
      have hv : paperGerverVelocityComponents t = alphaBeta5 p t := by
        rw [hval 4 t (by rw [hI4]; exact ⟨hs4.le, ht.2.le⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have hs0 : 0 < Real.pi / 2 - t := by linarith only [ht.2]
      have hsu : Real.pi / 2 - t ≤ (1 : ℝ) / 20 := by linarith only [hs4, hphiu]
      have hA := hkeyA (Real.pi / 2 - t) hs0.le hsu
      have hB := hkeyB (Real.pi / 2 - t) hs0.le hsu
      have h5 := hrefl (Real.pi / 2 - t)
      rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring] at h5
      have hfst : (alphaBeta5 p t).1 = -(alphaBeta1 p (Real.pi / 2 - t)).2 := by rw [h5]
      have hsnd : (alphaBeta5 p t).2 = -(alphaBeta1 p (Real.pi / 2 - t)).1 := by rw [h5]
      rw [hv, hfst, hsnd]
      exact ⟨by linarith only [hB], by linarith only [hA, hs0]⟩
  exact ⟨hmain.1, hmain.2, hmain.1, hmain.2⟩

/-- The tangential velocity component is nonpositive on the whole closed rotation interval:
the strict inequality of `gerver_strict_velocity` holds on the open interval, and the
component is continuous, so the closed condition propagates to the two endpoints. -/
theorem paperGerverVelocityComponents_fst_nonpos {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : (paperGerverVelocityComponents t).1 ≤ 0 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | (paperGerverVelocityComponents s).1 ≤ 0} :=
    isClosed_le (continuous_fst.comp paperGerverContactData_properties.1) continuous_const
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

/-- The normal velocity component is nonnegative on the whole closed rotation interval; see
`paperGerverVelocityComponents_fst_nonpos` for the argument. -/
theorem paperGerverVelocityComponents_snd_nonneg {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ (paperGerverVelocityComponents t).2 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | 0 ≤ (paperGerverVelocityComponents s).2} :=
    isClosed_le continuous_const (continuous_snd.comp paperGerverContactData_properties.1)
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).2.1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

theorem gerver_cap_area_lower_bound :
    2 * GerverSofa.PartB.params.a1 ≤ ClassicalResults.area gerverOuterCap ∧
    (12 : ℝ) / 5 ≤ 2 * GerverSofa.PartB.params.a1 ∧ (11 : ℝ) / 5 < 12 / 5 := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  rw [hp]
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk51lo, hk51hi, -, -,
      ha1lo, ha1hi, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have ha1' : p.a1 ≤ (61 : ℝ) / 50 := le_trans ha1hi (by norm_num)
  have hk51 : -(51 : ℝ) / 50 ≤ p.k51 := le_trans (by norm_num) hk51lo
  have hk51' : p.k51 ≤ -1 := le_trans hk51hi (by norm_num)
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hk52 : p.k52 = (1 / 4 : ℝ) := k52_eq_quarter_of_equations heqs
  -- The two path endpoints: `x(0) = 0` and `x(π/2) = (1 - a₁ + k₅₁, 0)`.
  obtain ⟨-, hzero, -⟩ := gerver_direct_path_regularity p hmem heqs
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane (path GerverSofa.PartB.params 0) = 0
    rw [hp, hzero]
    ext i
    fin_cases i <;> rfl
  have hpathT : path p (Real.pi / 2) = (1 - p.a1 + p.k51, 0) := by
    rw [path_eq_path5_of_mem_Icc heqs h1 h2 ⟨by linarith, le_rfl⟩]
    simp only [path5, addK, rot, Real.cos_pi_div_two, Real.sin_pi_div_two, he1, he2, ha2, hk52,
      Prod.mk.injEq]
    constructor <;> ring
  have hxT0 : paperGerverPath (Real.pi / 2) 0 = 1 - p.a1 + p.k51 := by
    change (path GerverSofa.PartB.params (Real.pi / 2)).1 = _
    rw [hp, hpathT]
  have hxT1 : paperGerverPath (Real.pi / 2) 1 = 0 := by
    change (path GerverSofa.PartB.params (Real.pi / 2)).2 = _
    rw [hp, hpathT]
  -- The velocity components at the two endpoints.
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
    norm_num
  have hbeta0 : (paperGerverVelocityComponents 0).2 = 2 * p.a1 - 1 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
  have halphaT : (paperGerverVelocityComponents (Real.pi / 2)).1 = 1 - 2 * p.a1 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he1]
  have hbetaT : (paperGerverVelocityComponents (Real.pi / 2)).2 = 0 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he2, ha2]
    norm_num
  -- The four displayed cap contacts, in coordinates.
  have hpteq : ∀ z w : Point, z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w hz hw
    ext i
    fin_cases i
    · exact hz
    · exact hw
  have hA0 : paperGerverContacts 0 0 = (!₂[1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halpha0, hpath0]
  have hC0 : paperGerverContacts 0 2 = (!₂[1 - 2 * p.a1, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbeta0, hpath0]
  have hAT : paperGerverContacts (Real.pi / 2) 0 = (!₂[p.a1 + p.k51, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halphaT, hxT0, hxT1]
    ring
  have hCT : paperGerverContacts (Real.pi / 2) 2 = (!₂[p.k51 - p.a1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbetaT, hxT0, hxT1]
    ring
  -- The cap is a convex body, so it is convex and of finite area.
  obtain ⟨-, -, -, -, -, ⟨K, hKset, -⟩, -⟩ := gerver_capSupport_identification
  have hconv : Convex ℝ gerverOuterCap := hKset ▸ K.val.convex'
  have hcomp : IsCompact gerverOuterCap := hKset ▸ K.val.isCompact'
  -- The inscribed trapezoid and its area.
  have hsub := EuclideanSpace.horizontalTrapezoid_subset_of_convex hconv
    (l₀ := p.k51 - p.a1) (r₀ := 1) (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51)
    (hCT ▸ gerver_outer_contact_C (Real.pi / 2) ⟨by positivity, le_rfl⟩)
    (hA0 ▸ gerver_outer_contact_A 0 ⟨le_rfl, by positivity⟩)
    (hC0 ▸ gerver_outer_contact_C 0 ⟨le_rfl, by positivity⟩)
    (hAT ▸ gerver_outer_contact_A (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hvol := EuclideanSpace.volume_horizontalTrapezoid (l₀ := p.k51 - p.a1) (r₀ := 1)
    (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51) (by linarith) (by linarith)
  have hkey : ENNReal.ofReal (2 * p.a1) ≤ MeasureTheory.volume gerverOuterCap := by
    rw [show (2 * p.a1 : ℝ) =
      (1 - (p.k51 - p.a1) + (p.a1 + p.k51 - (1 - 2 * p.a1))) / 2 by ring, ← hvol]
    exact MeasureTheory.measure_mono hsub
  refine ⟨?_, by linarith, by norm_num⟩
  rw [ClassicalResults.area]
  exact (ENNReal.ofReal_le_iff_le_toReal hcomp.measure_lt_top.ne).1 hkey

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Polygon.BalancedContainment`.
* `Polygon.Polyline.Length.Basic`.
* `Polygon.Polyline.Length.Boundary`.
* `Polygon.Polyline.Length`.
* `Polygon.Balancing.Coefficients`.
* `Polygon.Balancing.Estimate`.
* `Polygon.Balancing`.
* `Polygon.EdgeNormals`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Balanced Containment
-/

public section

noncomputable section

namespace MovingSofa

/-- Balance bounds the polyline projections by the surface-area atoms. -/
theorem polygonCapPolyline_inner_le_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) (s : ℝ)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ ((capVertices K.val 0).1.2) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (surfaceAreaMeasure K.val.val {(u : Real.Angle)}).toReal *
        max (Real.sin (s - u)) 0 := by
  classical
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hmem (u : ℝ) (hu : u ∈ D) : u ∈ angleDomain Θ := by
    rw [← hD]
    exact hu
  have hb := (polygonCapPolyline K).inner_le_endpoint_add_sum_normal_lengths D
    (fun u hu ↦ angleDomain_subset_Ioo Θ (hmem u hu))
    (fun i ↦ by
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      refine ⟨t.val, ?_, ht⟩
      have := t.property
      simpa only [← hD, Finset.mem_coe] using this) s hq
  rw [hp.2.2.1] at hb
  convert hb using 2
  apply Finset.sum_congr rfl
  intro u hu
  have heq := hK ⟨u, hmem u hu⟩
  rw [heq, ENNReal.toReal_ofReal]
  · rfl
  · unfold polygonCapPolylineLength
    positivity

/-- A balanced polygon cap bounds every upper-normal projection of its polyline. -/
theorem polygonCapPolyline_inner_le_support_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤ supportValue K.val.val (s : Real.Angle) := by
  have hpoly := polygonCapPolyline_inner_le_of_balanced K hK D hD s hq
  have hsum := sum_surfaceAreaMeasure_mul_pos_sin_le K.val.val D
    (fun t ht ↦ angleDomain_subset_Ioo Θ (by rw [← hD]; exact ht)) hs
  have hstart := inner_negativeVertex_zero_le_positiveVertex K.val.val ⟨hs.1.le, hs.2.le⟩
  change inner ℝ q (normalVector (s : Real.Angle)) ≤
    inner ℝ (edgeVertices K.val.val 0).2 (normalVector (s : Real.Angle)) + _ at hpoly
  rw [real_inner_comm (normalVector (s : Real.Angle)) (edgeVertices K.val.val 0).2] at hpoly
  linarith

/-- The polyline of a balanced polygon cap lies inside the cap. -/
theorem polygonCapPolyline_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point) := by
  classical
  let D := Θ.directions ∪ Θ.directions.image (fun t ↦ t + Real.pi / 2) ∪
    {Θ.angle, Real.pi / 2}
  have hD : (D : Set ℝ) = angleDomain Θ := by
    simp [D, angleDomain]
  intro q hq
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq)
  have hfan : q ∈ capFan Θ.angle := by
    have hmem := frontier_subset_closure hfront
    rw [hp.2.2.2.2.1.closure_eq] at hmem
    exact hmem.1
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact polygonCapPolyline_inner_le_support_of_balanced K hK D hD
      (angleDomain_subset_Ioo Θ ht) hq
  rcases ha with rfl | rfl
  · change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.2

/-- A polygon niche lies in its cap whenever its upper boundary polyline does. -/
theorem polygonNiche_subset_of_polyline_subset {Θ : AngleSet}
    (K : PolygonCapSpace Θ)
    (hpoly : (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point)) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) := by
  intro q hq
  have hfan : q ∈ capFan Θ.angle := hq.1
  have hheight : q 1 < capBoundaryHeight K (q 0) := by
    by_contra hn
    have hmem : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := by
      rw [capFan_sdiff_polygonNiche_eq_epigraph K]
      exact le_of_not_gt hn
    exact hmem.2 hq
  let r := pointOnGraph (capBoundaryHeight K) (q 0)
  have hrx : r 0 = q 0 := by simp [r, pointOnGraph]
  have hry : q 1 < r 1 := by simpa [r, pointOnGraph] using hheight
  have hrfront : r ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [(capFan_sdiff_polygonNiche_closed_frontier K).2]
    exact ⟨q 0, rfl⟩
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  rw [hp.2.2.2.2.2.1] at hrfront
  have hrpoly : r ∈ (polygonCapPolyline K).carrier := by
    rcases hrfront with (hrleft | hrpoly) | hrright
    · obtain ⟨c, hc, hr⟩ := hrleft
      have hrzero : inner ℝ r (normalVector (Θ.angle : Real.Angle)) = 0 := by
        rw [hr, capVertices_angle_fst_eq K, inner_add_left,
          real_inner_smul_left, real_inner_smul_left]
        have hz : inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (normalVector (Θ.angle : Real.Angle)) = 0 := by
          rw [real_inner_comm (normalVector (Θ.angle : Real.Angle))]
          exact inner_normalVector_tangentVector Θ.angle
        rw [hz]
        ring
      have hqnonneg := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hqnonneg
      have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (by linarith [Θ.angle_le, Real.pi_pos])
      simp [normalVector, frame, PiLp.inner_apply, hrx] at hrzero hqnonneg
      exfalso
      nlinarith
    · exact hrpoly
    · obtain ⟨c, hc, hr⟩ := hrright
      have hrzero : r 1 = 0 := by
        rw [hr, capVertices_zero_snd_eq K]
        simp [normalVector, frame]
      have hqnonneg := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqnonneg
      simp [normalVector, frame, PiLp.inner_apply] at hqnonneg
      exfalso
      linarith
  exact K.val.mem_of_fst_eq_of_snd_le (hpoly hrpoly) hfan hrx.symm hry.le

/-- Every balanced polygon cap contains its polygon niche. -/
theorem polygonNiche_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) :=
  polygonNiche_subset_of_polyline_subset K (polygonCapPolyline_subset_of_balanced K hK)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Length / Basic
-/

public section

noncomputable section

namespace MovingSofa

/-- Extend the directional polyline-length function by zero outside the angle domain. -/
@[expose]
def polygonPolylineLengthAt {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then polygonCapPolylineLength K ⟨t, ht⟩ else 0

/-- The one-dimensional Hausdorff measure of the niche frontier inside a specified set. -/
@[expose]
def nicheBoundaryLength {Θ : AngleSet} (K : PolygonCapSpace Θ) (S : Set Point) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ S)).toReal

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Length / Boundary
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment_mc4d199c {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private theorem frontier_inter_open_eq_frontier_sdiff_open_on_interior
    {F X : Set Point} :
    frontier (F ∩ X) ∩ interior F = frontier (F \ X) ∩ interior F := by
  have hInt : IsOpen (interior F) := isOpen_interior
  calc
    frontier (F ∩ X) ∩ interior F =
        frontier ((F ∩ X) ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier (X ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
    _ = frontier X ∩ interior F := frontier_inter_open_inter hInt
    _ = frontier Xᶜ ∩ interior F := by rw [frontier_compl]
    _ = frontier (Xᶜ ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier ((F \ X) ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
    _ = frontier (F \ X) ∩ interior F := frontier_inter_open_inter hInt

private theorem frontier_inter_open_symmDiff_subset_frontier
    {F X : Set Point} (hF : IsClosed F) :
    (frontier (F ∩ X) \ frontier (F \ X)) ∪
        (frontier (F \ X) \ frontier (F ∩ X)) ⊆ frontier F := by
  have heq := frontier_inter_open_eq_frontier_sdiff_open_on_interior (F := F) (X := X)
  intro p hp
  by_contra hpF
  have hmemF_of_left (hpN : p ∈ frontier (F ∩ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F ∩ X) := frontier_subset_closure hpN
    exact hF.closure_eq ▸ closure_mono Set.inter_subset_left hpcl
  have hmemF_of_right (hpC : p ∈ frontier (F \ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F \ X) := frontier_subset_closure hpC
    exact hF.closure_eq ▸ closure_mono Set.sdiff_subset hpcl
  rcases hp with hp | hp
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_left hp.1)).not.mp hpF
    have : p ∈ frontier (F \ X) ∩ interior F := heq ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_right hp.1)).not.mp hpF
    have : p ∈ frontier (F ∩ X) ∩ interior F := heq.symm ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1

private theorem measure_eq_of_symmDiff_subset_null
    (μ : Measure Point) {A B E : Set Point}
    (hsub : (A \ B) ∪ (B \ A) ⊆ E) (hE : μ E = 0) : μ A = μ B := by
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inl hp)) hE
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inr hp)) hE

/-- The fan clipping the niche is closed. -/
theorem isClosed_capFan (ω : ℝ) : IsClosed (capFan ω) := by
  unfold capFan normalHalfPlane
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop))

/-- The inward quadrant of a supporting hallway is open. -/
theorem isOpen_innerQuadrant (S : Set Point) (t : ℝ) :
    IsOpen (innerQuadrant S t) := by
  unfold innerQuadrant normalHalfPlane
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) continuous_const)

private theorem frontier_normalHalfPlane_lower_strict_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h false true) ⊆ normalLine t h := by
  change frontier {p : Point | inner ℝ p (normalVector t) < h} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_lt_subset_eq (by fun_prop) continuous_const

private theorem frontier_normalHalfPlane_upper_closed_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h true false) ⊆ normalLine t h := by
  change frontier {p : Point | h ≤ inner ℝ p (normalVector t)} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_ge_subset_eq continuous_const (by fun_prop)

private def polygonCapBoundaryLines {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    Finset (Real.Angle × ℝ) := by
  classical
  exact {(((Θ.angle : ℝ) : Real.Angle), 0),
      (((Real.pi / 2 : ℝ) : Real.Angle), 0)} ∪
    Θ.directions.biUnion fun t ↦
      {(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
        (((t + Real.pi / 2 : ℝ) : Real.Angle),
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)}

private theorem frontier_capFan_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (Θ.angle : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      (Θ.angle : Real.Angle) 0 hp'.1
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Θ.angle : ℝ) : Real.Angle), 0), by simp [polygonCapBoundaryLines], hline⟩
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      ((Real.pi / 2 : ℝ) : Real.Angle) 0 hp'.2
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Real.pi / 2 : ℝ) : Real.Angle), 0),
      by simp [polygonCapBoundaryLines], hline⟩

private theorem frontier_innerQuadrant_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    frontier (innerQuadrant K.val.val t) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  classical
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) hp'.1
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
      ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) hp'.2
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t + Real.pi / 2 : ℝ) : Real.Angle),
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1), ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩

private theorem frontier_polygonComplement_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle \ polygonNiche Θ K.val) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  let X : Set Point := ⋃ t ∈ Θ.directions, innerQuadrant K.val.val t
  have hset : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hset, Set.sdiff_eq]
  intro p hp
  have hp' := frontier_inter_subset (capFan Θ.angle) Xᶜ hp
  rcases hp' with hp | hp
  · exact frontier_capFan_subset_boundaryLines K hp.1
  · have hpX : p ∈ frontier X := by simpa [frontier_compl] using hp.2
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun t ↦ innerQuadrant K.val.val t) hpX
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hmem
    exact frontier_innerQuadrant_subset_boundaryLines K ht hpt

private theorem real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
    {v : Point} (hv : v ≠ 0) {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hvs : inner ℝ v (normalVector (s : Real.Angle)) = 0)
    (hvt : inner ℝ v (normalVector (t : Real.Angle)) = 0) : s = t := by
  apply eq_of_inner_sub_normalVector_eq_zero_of_ne (a := 0) (b := v) hs ht hv.symm
  · simpa using hvs
  · simpa using hvt

private theorem normalLine_inter_normalLine_subsingleton {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  have hv : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsorth : inner ℝ (p - q) (normalVector (s : Real.Angle)) = 0 := by
    have hps : inner ℝ p (normalVector (s : Real.Angle)) = c := hp.1
    have hqs : inner ℝ q (normalVector (s : Real.Angle)) = c := hq.1
    rw [inner_sub_left, hps, hqs, sub_self]
  have htorth : inner ℝ (p - q) (normalVector (t : Real.Angle)) = 0 := by
    have hpt : inner ℝ p (normalVector (t : Real.Angle)) = d := hp.2
    have hqt : inner ℝ q (normalVector (t : Real.Angle)) = d := hq.2
    rw [inner_sub_left, hpt, hqt, sub_self]
  exact hst (real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi hv hs ht hsorth htorth)

private theorem hausdorffMeasure_normalLine_inter_normalLine_eq_zero {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    Measure.hausdorffMeasure 1
      (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (normalLine_inter_normalLine_subsingleton hs ht hst).countable.measure_zero _

private theorem openRay_inter_hyperplane_subsingleton {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    (openRay p v ∩ {q | inner ℝ q n = c}).Subsingleton := by
  rintro x ⟨⟨r, hr, rfl⟩, hxr⟩ y ⟨⟨s, hs, rfl⟩, hyr⟩
  have hrs : r * inner ℝ v n = s * inner ℝ v n := by
    simp only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] at hxr hyr
    linarith
  rw [mul_right_cancel₀ hvn hrs]

private theorem hausdorffMeasure_openRay_inter_hyperplane_eq_zero {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    Measure.hausdorffMeasure 1 (openRay p v ∩ {q | inner ℝ q n = c}) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (openRay_inter_hyperplane_subsingleton hvn).countable.measure_zero _

private theorem hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
      (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c) = 0 := by
  apply measure_mono_null (t :=
    (normalLine (ω : Real.Angle) 0 ∩ normalLine (t : Real.Angle) c) ∪
      (normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (t : Real.Angle) c))
  · rintro p ⟨hp, hpt⟩
    have hp' := frontier_inter_subset
      (normalHalfPlane (ω : Real.Angle) 0 true false)
      (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
    rcases hp' with hp' | hp'
    · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
    · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩
  · rw [measure_union_null]
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero hω ht htω.symm
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero
        ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm

private theorem frontier_capFan_inter_normalLine_countable
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c).Countable := by
  refine ((normalLine_inter_normalLine_subsingleton hω ht htω.symm
      (c := 0) (d := c)).countable.union
    (normalLine_inter_normalLine_subsingleton
      (s := Real.pi / 2) (t := t) (c := 0) (d := c)
      ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm).countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (ω : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩

private theorem hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (htω : t ≠ Θ.angle)
    (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  have hC : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hC, hN]
  apply measure_eq_of_symmDiff_subset_null (E :=
    frontier (capFan Θ.angle) ∩ normalLine (t : Real.Angle) c)
  · intro p hp
    rcases hp with hp | hp
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inl ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpC
      exact hp.2 ⟨hpC, hp.1.2⟩
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inr ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpN
      exact hp.2 ⟨hpN, hp.1.2⟩
  · exact hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ ht htω htT

private theorem hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (hleft : inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0)
    (hright : inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0) :
    Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) c) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  let L := openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))
  let R := openRay ((capVertices K.val 0).1.2) (normalVector 0)
  have hnullL : Measure.hausdorffMeasure 1
      (L ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hleft
  have hnullR : Measure.hausdorffMeasure 1
      (R ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hright
  apply measure_eq_of_symmDiff_subset_null
    (E := (L ∩ normalLine (t : Real.Angle) c) ∪
      (R ∩ normalLine (t : Real.Angle) c))
  · intro q hq
    rcases hq with hq | hq
    · rw [hp.2.2.2.2.2.1] at hq
      rcases hq.1.1 with hL | hR
      · rcases hL with hL | hcarrier
        · exact Or.inl ⟨hL, hq.1.2⟩
        · exact False.elim (hq.2 ⟨hcarrier, hq.1.2⟩)
      · exact Or.inr ⟨hR, hq.1.2⟩
    · exact False.elim (hq.2 ⟨by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1), hq.1.2⟩)
  · rw [measure_union_null hnullL hnullR]

private theorem edge_direction_ne_zero (p : XMonotonePolylineData)
    (i : Fin p.edges) : p.vertices i.succ - p.vertices i.castSucc ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hcoord := congrArg (fun q : Point ↦ q 0) h
  exact (ne_of_gt (p.increasing i.castSucc_lt_succ)) hcoord

private theorem IsCapPolyline.edge_subset_boundaryLine {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) (i : Fin p.edges) :
    ∃ l ∈ polygonCapBoundaryLines K,
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        normalLine l.1 l.2 := by
  classical
  simpa only [normalLine] using EuclideanGeometry.exists_segment_subset_hyperplane_of_finite_cover
    (I := polygonCapBoundaryLines K) (n := fun l ↦ normalVector l.1) (c := Prod.snd)
    (a := p.vertices i.castSucc) (b := p.vertices i.succ)
    (sub_ne_zero.mp (edge_direction_ne_zero p i)).symm (by
      intro q hq
      have hcarrier : q ∈ p.carrier := by
        rw [XMonotonePolylineData.carrier]
        exact Set.mem_iUnion.mpr ⟨i, hq⟩
      have hfrontier : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hcarrier)
      exact frontier_polygonComplement_subset_boundaryLines K hfrontier)

private theorem IsCapPolyline.edge_subset_bLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩ htI hlorth hi
      simpa [heq] using hline
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le, (Θ.interior s hs).1, Real.pi_pos]

private theorem IsCapPolyline.edge_subset_dLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have hsI : s ∈ Set.Ioo 0 Real.pi :=
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le]
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      have hst : s = t := by linarith
      simpa [hst] using hline

private theorem polygonCapPolyline_spec {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    IsCapPolyline K (polygonCapPolyline K) := by
  exact (polygonCap_polyline K).choose_spec

private theorem polygonCapPolyline_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) (supportValue K.val.val (t : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_bLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := by
    exact Or.inl (Or.inl ht)
  rw [show normalLine (t : Real.Angle)
      (supportValue K.val.val (t : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonCapPolyline_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_dLine_of_orthogonal ht i hi)
  have htDomain : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [show normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem tangentVector_angle_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0 := by
  have hsin : 0 < Real.sin (Θ.angle - t) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [(Θ.interior t ht).2])
    (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    (t : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - t) =
    -inner ℝ (normalVector (t : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem tangentVector_angle_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  have hneg : -Real.pi < Θ.angle - (t + Real.pi / 2) := by
    linarith [(Θ.interior t ht).2, Real.pi_pos]
  have hzero : Θ.angle - (t + Real.pi / 2) < 0 := by
    linarith [(Θ.interior t ht).1, Θ.angle_le]
  have hsin : Real.sin (Θ.angle - (t + Real.pi / 2)) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt hzero hneg
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    ((t + Real.pi / 2 : ℝ) : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - (t + Real.pi / 2)) =
    -inner ℝ (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem normalVector_zero_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, (Θ.interior t ht).1],
      (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  simpa [Real.cos_neg] using hcos.ne'

private theorem normalVector_zero_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (Θ.interior t ht).1
    (by linarith [(Θ.interior t ht).2, Θ.angle_le, Real.pi_pos])
  rw [show 0 - (t + Real.pi / 2) = -(t + Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_add_pi_div_two]
  exact neg_ne_zero.mpr hsin.ne'

private theorem polygonNiche_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (ne_of_lt (Θ.interior t ht).2) (ne_of_lt
        ((Θ.interior t ht).2.trans_le Θ.angle_le)),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_ne_zero ht)]
  exact polygonCapPolyline_bLine_length K ht

private theorem polygonNiche_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1]),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_add_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_add_ne_zero ht)]
  exact polygonCapPolyline_dLine_length K ht

private theorem frontier_innerQuadrant_inter_bLine_subset_bRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).bRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_bRay_iff]
  refine ⟨hp.2, ?_⟩
  apply closure_minimal (t := {q | inner ℝ q (tangentVector (t : Real.Angle)) ≤
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1})
      (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
      (frontier_subset_closure hp.1)
  change q ∈ innerQuadrant s t at hq
  have h := hq.2
  change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two] at h
  exact h.le

private theorem frontier_innerQuadrant_inter_dLine_subset_dRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).dRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_dRay_iff]
  refine ⟨?_, ?_⟩
  · apply closure_minimal (t := {q | inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue s (t : Real.Angle) - 1})
        (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
        (frontier_subset_closure hp.1)
    change q ∈ innerQuadrant s t at hq
    have h := hq.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue s (t : Real.Angle) - 1 at h
    exact h.le
  · have hline := hp.2
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hline
    rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hline
    exact hline

private theorem frontier_innerQuadrant_inter_bLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htI hst
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htI
    (by linarith [(Θ.interior s hs).1, (Θ.interior t ht).2, Θ.angle_le])
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_innerQuadrant_inter_dLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htTI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htTI
    (by linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le])
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htTI
    (by
      intro h
      apply hst
      linarith)
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_polygonNiche_bLine_sdiff_bRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay).Countable := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (ne_of_lt (Θ.interior t ht).2)
      (ne_of_lt ((Θ.interior t ht).2.trans_le Θ.angle_le))
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_bLine_subset_bRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_bLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem frontier_polygonNiche_dLine_sdiff_dRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay).Countable := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1])
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_dLine_subset_dRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_dLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem rotatingHallwayParts_bRay_subset_bLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).bRay ⊆
      normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) := by
  intro p hp
  exact (mem_rotatingHallwayParts_bRay_iff s (t : Real.Angle) p).mp hp |>.1

private theorem rotatingHallwayParts_dRay_subset_dLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).dRay ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  intro p hp
  have h := (mem_rotatingHallwayParts_dRay_iff s (t : Real.Angle) p).mp hp |>.2
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two]
  exact h

private theorem polygonNiche_bRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay)).toReal =
      polygonPolylineLengthAt K t := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  have hRL : R ⊆ L := rotatingHallwayParts_bRay_subset_bLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_bLine_sdiff_bRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_bLine_length K ht

private theorem polygonNiche_dRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay)).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  have hRL : R ⊆ L := rotatingHallwayParts_dRay_subset_dLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_dLine_sdiff_dRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_dLine_length K ht

private theorem exposedEdge_bottom_eq_segment_zero_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = 0 := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.2.1] at h
      simpa only [inner_normalVector_three_pi_div_two, neg_eq_zero] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hqx : 0 ≤ q 0 := by
      have h := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
        add_zero] at h
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem exposedEdge_left_eq_segment_zero_left {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val Θ.angle).2.1 := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
  have hnormal : normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -normalVector (Θ.angle : Real.Angle) := normalVector_add_pi Θ.angle
  have htangent : tangentVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -tangentVector (Θ.angle : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, frame, Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hCK : C ∈ (K.val.val : Set Point) := by
    rw [hCeq]
    exact supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K.val hω
  have hCedge : C ∈ exposedEdge K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, hnormal, hCeq, inner_neg_right,
      real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).1 = 0 := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqn : inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.1, hnormal, inner_neg_right] at h
      linarith
    let μ := inner ℝ q (tangentVector (Θ.angle : Real.Angle))
    have hqeq : μ • tangentVector (Θ.angle : Real.Angle) = q := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        q (Θ.angle : Real.Angle)
      rw [hqn, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hqy := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
      have hcoord := congrArg (fun p : Point ↦ p 1) hqeq
      change μ * Real.cos Θ.angle = q 1 at hcoord
      have hqy' : 0 ≤ q 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hqy
      rw [← hcoord] at hqy'
      exact nonneg_of_mul_nonneg_left hqy' (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
    rw [htangent, inner_neg_right]
    simpa using neg_nonpos.mpr hμ
  have hsnd : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqL := inner_le_supportValue K.val.val hq.1
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    rw [show ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
      (Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hqL
    change inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤ L at hqL
    rw [htangent, hCeq, inner_neg_right, inner_neg_right, real_inner_smul_left,
      inner_tangentVector_self]
    linarith
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd, segment_symm]

private theorem exposedEdge_bottom_eq_segment_left_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ (capVertices K.val Θ.angle).2.1 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hCK : C ∈ (K.val.val : Set Point) := by
    exact (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have hCedge : C ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hCeq, inner_normalVector_three_pi_div_two]
    simp [hω, tangentVector, frame]
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (Real.pi : Real.Angle)
    have hC := (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).2
    change inner ℝ C
      (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) at hC
    have hang : ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
        (Real.pi : Real.Angle) := by
      congr 1
      rw [hω]
      ring
    rw [hang] at hC
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx.trans_eq hC.symm
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem XMonotonePolylineData.carrier_fst_mem_Icc
    (p : XMonotonePolylineData) {q : Point} (hq : q ∈ p.carrier) :
    q 0 ∈ Set.Icc ((p.vertices 0) 0) ((p.vertices (Fin.last p.edges)) 0) := by
  rw [XMonotonePolylineData.carrier] at hq
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  have hi := fst_mem_Icc_of_mem_segment_mc4d199c (p.increasing i.castSucc_lt_succ).le hqi
  exact ⟨(p.increasing.monotone (Fin.zero_le i.castSucc)).trans hi.1,
    hi.2.trans (p.increasing.monotone (Fin.le_last i.succ))⟩

private theorem mem_segment_of_fst_mem_Icc_of_mem_normalLine
    {a b q : Point} {t c : ℝ} (hab : a 0 < b 0)
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (ha : a ∈ normalLine (t : Real.Angle) c)
    (hb : b ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c)
    (hx : q 0 ∈ Set.Icc (a 0) (b 0)) : q ∈ segment ℝ a b := by
  let r := (q 0 - a 0) / (b 0 - a 0)
  have hden : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hxcoord : (a + r • (b - a)) 0 = q 0 := by
    dsimp [r]
    field_simp
    ring
  have hline : a + r • (b - a) ∈ normalLine (t : Real.Angle) c := by
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c
    change inner ℝ a (normalVector (t : Real.Angle)) = c at ha
    change inner ℝ b (normalVector (t : Real.Angle)) = c at hb
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero]
  ext i
  fin_cases i
  · exact hxcoord
  · change (a + r • (b - a)) 1 = q 1
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c at hline
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hline hq
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hxcoord ⊢
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hline - hq - Real.cos t * hxcoord

private theorem eq_of_fst_eq_of_mem_normalLine {p q : Point} {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (hp : p ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c) (hx : p 0 = q 0) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · change p 1 = q 1
    change inner ℝ p (normalVector (t : Real.Angle)) = c at hp
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hp hq
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hp - hq - Real.cos t * hx

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  have hA0support : 0 < supportValue K.val.val (0 : Real.Angle) := by
    obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
      (Θ.angle : Real.Angle)
    have huy : u 1 ≤ 1 := by
      have huy' := inner_le_supportValue K.val.val huK
        ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [K.val.property.2.2.2.1] at huy'
      simpa [normalVector, frame, PiLp.inner_apply] using huy'
    rw [K.val.property.2.2.1] at hu
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin_lt : Real.sin Θ.angle < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
    have hux : 0 < u 0 := by
      simp [normalVector, frame, PiLp.inner_apply] at hu
      have hsin : 0 ≤ Real.sin Θ.angle :=
        (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
      have hmul := mul_le_mul_of_nonneg_left huy hsin
      nlinarith
    exact hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  have hA0 : 0 < A 0 := by
    rw [hAeq]
    simpa [normalVector, frame] using hA0support
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hA0
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ (capVertices K.val 0).1.2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [capVertices_zero_snd_eq K]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    rw [hp.2.1, hp.2.2.1] at hxbounds
    refine ⟨?_, hxbounds.2⟩
    have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
    have hfan : q ∈ capFan Θ.angle :=
      (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at h
      simpa [normalVector, frame, PiLp.inner_apply] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have h := hfan.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
      add_zero] at h
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos

private theorem polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω, segment_symm]
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq.1)
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hfan : q ∈ capFan Θ.angle :=
    (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
  have hxbounds := p.carrier_fst_mem_Icc hq.1
  rw [hp.2.1, hp.2.2.1] at hxbounds
  have hq0 : q 0 ≤ 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hline
    have hqy := hfan.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
    have hqy' : 0 ≤ q 1 := by
      simpa [normalVector, frame, PiLp.inner_apply] using hqy
    simp [normalVector, frame, PiLp.inner_apply] at hline
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])
    nlinarith
  have hCline : C ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    change inner ℝ C (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0line : (0 : Point) ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    simp [normalLine]
  by_cases hCstrict : C 0 < 0
  · exact mem_segment_of_fst_mem_Icc_of_mem_normalLine hCstrict
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hCline h0line hq.2 ⟨hxbounds.1, hq0⟩
  · have hCzero : C 0 = 0 := le_antisymm hC0 (le_of_not_gt hCstrict)
    have hqzero : q 0 = C 0 := by linarith [hxbounds.1, hq0]
    have hqC := eq_of_fst_eq_of_mem_normalLine
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hq.2 hCline hqzero
    rw [hqC]
    exact left_mem_segment ℝ C 0

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · change inner ℝ C (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hCeq]
    simp [hω, tangentVector, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ A (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hAeq]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    simpa [hp.2.1, hp.2.2.1] using hxbounds

private theorem IsCapPolyline.edge_subset_fanLine_of_orthogonal
    {Θ : AngleSet} {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) 0 := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have hωI : Θ.angle ∈ Set.Ioo 0 Real.pi :=
    ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
  have hTI : Real.pi / 2 ∈ Set.Ioo 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hline
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hTI hωI hlorth hi
        simpa [heq] using hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).2]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).1, Θ.angle_le, Real.pi_pos]
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hωI hTI hlorth hi
        simpa [heq] using hline
      · exact hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).2, Θ.angle_le]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).1]

private theorem polygonCapPolyline_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) 0
    (fun i hi ↦ hp.edge_subset_fanLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := Or.inr ht
  rw [show normalLine (t : Real.Angle) 0 =
      {q | inner ℝ q (normalVector (t : Real.Angle)) = 0} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
      add_zero] at hb
    simp only [wedgeEndpoints]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
      PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one, gt_iff_lt]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgap
  have hqx_nonneg : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
      add_zero] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan) hcosω
  have hApos : 0 < (capVertices K.val 0).1.2 0 :=
    hqx_nonneg.trans_lt (hqx_endpoint.trans hendpoint_A)
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hApos
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hqx_nonneg, (hqx_endpoint.trans hendpoint_A).le⟩

private theorem mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    {a b q : Point} {t : Real.Angle} {c : ℝ}
    (hab : inner ℝ a (tangentVector t) < inner ℝ b (tangentVector t))
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c)
    (hq : q ∈ normalLine t c)
    (hx : inner ℝ q (tangentVector t) ∈
      Set.Icc (inner ℝ a (tangentVector t)) (inner ℝ b (tangentVector t))) :
    q ∈ segment ℝ a b := by
  let r := (inner ℝ q (tangentVector t) - inner ℝ a (tangentVector t)) /
    (inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t))
  have hden : 0 < inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t) :=
    sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hn : inner ℝ (a + r • (b - a)) (normalVector t) =
      inner ℝ q (normalVector t)
      := by
    change inner ℝ a (normalVector t) = c at ha
    change inner ℝ b (normalVector t) = c at hb
    change inner ℝ q (normalVector t) = c at hq
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero, hq]
  have htangent : inner ℝ (a + r • (b - a)) (tangentVector t) =
      inner ℝ q (tangentVector t)
      := by
    rw [inner_add_left, real_inner_smul_left, inner_sub_left]
    dsimp [r]
    field_simp
    ring
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (a + r • (b - a)) t,
    ← inner_normalVector_smul_add_inner_tangentVector_smul q t, hn, htangent]

private theorem polygonNiche_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqcoord_endpoint : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Θ.angle - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
      ring_nf
    rw [hinner] at hd
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Θ.angle - t) := by
      simp only [wedgeEndpoints, real_inner_smul_left]
      rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (tangentVector (Θ.angle : Real.Angle)) = 1 by
          exact inner_tangentVector_self Θ.angle, mul_one]
    rw [hendpoint]
    exact (lt_div_iff₀ hcosδ).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector (Θ.angle : Real.Angle)) := by
    simpa [wedgeGaps, inner_sub_left] using hgap
  have hqcoord_nonneg : 0 ≤ inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
    have hfan := hq.1.1.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hfan
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = Real.cos Θ.angle := by
      simp [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two]
    rw [hinner] at hfan
    exact nonneg_of_mul_nonneg_left hfan hcosω
  have hCpos : 0 < inner ℝ (capVertices K.val Θ.angle).2.1
      (tangentVector (Θ.angle : Real.Angle)) :=
    hqcoord_nonneg.trans_lt (hqcoord_endpoint.trans hendpoint_C)
  apply mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    (t := (Θ.angle : Real.Angle)) (c := 0) (by simpa using hCpos)
  · simp [normalLine]
  · have hCeq := capVertices_angle_fst_eq K
    change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm,
      inner_normalVector_tangentVector, mul_zero]
  · exact hq.2
  · exact ⟨by simpa using hqcoord_nonneg, (hqcoord_endpoint.trans hendpoint_C).le⟩

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgapA : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hgapC : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
      add_zero] at hb
    simp only [wedgeEndpoints]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
      PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one, gt_iff_lt]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgapA
  have hqcoord_endpoint : inner ℝ q
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q ((Real.pi / 2 : ℝ) : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Real.pi / 2 - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
    rw [hinner] at hd
    have hcosEq : Real.cos (Θ.angle - t) = Real.cos (Real.pi / 2 - t) := by
      rw [hω]
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Real.pi / 2 - t) := by
      calc
        _ = (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (Θ.angle - t) := by
          rw [show tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) =
              tangentVector (Θ.angle : Real.Angle) by rw [hω]]
          simp only [wedgeEndpoints, real_inner_smul_left]
          rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (tangentVector (Θ.angle : Real.Angle)) = 1 by
              exact inner_tangentVector_self Θ.angle, mul_one]
        _ = _ := by rw [hcosEq]
    rw [hendpoint]
    have hcosT : 0 < Real.cos (Real.pi / 2 - t) := by simpa [hω] using hcosδ
    exact (lt_div_iff₀ hcosT).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← hω]
    simpa [wedgeGaps, inner_sub_left] using hgapC
  have hCx_lt_qx : (capVertices K.val Θ.angle).2.1 0 < q 0 := by
    have h := hqcoord_endpoint.trans hendpoint_C
    simp [tangentVector, frame, PiLp.inner_apply, hω] at h
    simpa [hω] using h
  have hqx_lt_Ax : q 0 < (capVertices K.val 0).1.2 0 :=
    hqx_endpoint.trans hendpoint_A
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hCx_lt_qx.le, hqx_lt_Ax.le⟩

private theorem mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
    (t : ℝ) (c : ℝ) {q : Point} (hq : q ∈ normalLine (t : Real.Angle) c) :
    q ∈ frontier (normalHalfPlane (t : Real.Angle) c true false) := by
  have hqH : q ∈ normalHalfPlane (t : Real.Angle) c true false := by
    change c ≤ inner ℝ q (normalVector (t : Real.Angle))
    exact hq.ge
  apply (mem_frontier_iff_notMem_interior hqH).mpr
  intro hqInt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hqInt
  let e := ε / 2
  let z := q - e • normalVector (t : Real.Angle)
  have he : 0 < e := half_pos hε
  have hzball : z ∈ Metric.ball q ε := by
    change dist z q < ε
    simp [z, norm_smul, norm_normalVector_real, abs_of_pos he]
    dsimp [e]
    linarith
  have hz := interior_subset (hball hzball)
  change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hz
  change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
  dsimp [z] at hz
  rw [inner_sub_left, real_inner_smul_left, inner_normalVector_self, mul_one, hq] at hz
  linarith

private theorem capFan_inter_fanLine_subset_frontier {Θ : AngleSet} {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    capFan Θ.angle ∩ normalLine (t : Real.Angle) 0 ⊆ frontier (capFan Θ.angle) := by
  intro q hq
  apply (mem_frontier_iff_notMem_interior hq.1).mpr
  intro hqInt
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · have hInt := interior_mono Set.inter_subset_left hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      Θ.angle 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.1).mp hfront hInt
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    have hInt := interior_mono Set.inter_subset_right hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      (Real.pi / 2) 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.2).mp hfront hInt

private theorem frontier_innerQuadrant_inter_fanLine_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (frontier (innerQuadrant K.val.val s) ∩ normalLine (t : Real.Angle) 0).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htI : t ∈ Set.Ioo 0 Real.pi := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
    · rw [Set.mem_singleton_iff.mp ht]
      exact ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hst : s ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ne_of_lt (Θ.interior s hs).2
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_lt ((Θ.interior s hs).2.trans_le Θ.angle_le)
  have hsTt : s + Real.pi / 2 ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · intro heq
      linarith [(Θ.interior s hs).1, Θ.angle_le]
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_gt (by linarith [(Θ.interior s hs).1])
  refine ((normalLine_inter_normalLine_subsingleton hsI htI hst
      (c := supportValue K.val.val (s : Real.Angle) - 1) (d := 0)).countable.union
    (normalLine_inter_normalLine_subsingleton hsTI htI hsTt
      (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      (d := 0)).countable).mono ?_
  rintro q ⟨hqfront, hqline⟩
  have hfront := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      false true) hqfront
  rcases hfront with hfront | hfront
  · exact Or.inl ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.1,
      hqline⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.2,
      hqline⟩

private theorem frontier_polygonNiche_inter_fanLine_eq_niche_inter
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  rw [hN]
  apply measure_eq_of_symmDiff_subset_null (E := frontier X ∩ normalLine (t : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · refine ⟨?_, hq.1.2⟩
      rw [← closure_sdiff_interior]
      refine ⟨closure_mono Set.inter_subset_right (frontier_subset_closure hq.1.1), ?_⟩
      intro hqInt
      have hqX : q ∈ X := interior_subset hqInt
      have hqF : q ∈ capFan Θ.angle := by
        have hqcl := frontier_subset_closure hq.1.1
        exact (isClosed_capFan Θ.angle).closure_eq ▸
          closure_mono Set.inter_subset_left hqcl
      exact hq.2 ⟨⟨hqF, hqX⟩, hq.1.2⟩
    · have hqFront : q ∈ frontier (capFan Θ.angle ∩ X) := by
        apply (mem_frontier_iff_notMem_interior hq.1.1).mpr
        intro hqInt
        have hqFInt := interior_mono Set.inter_subset_left hqInt
        exact (mem_frontier_iff_notMem_interior hq.1.1.1).mp
          (capFan_inter_fanLine_subset_frontier ht ⟨hq.1.1.1, hq.1.2⟩) hqFInt
      exact (hq.2 ⟨hqFront, hq.1.2⟩).elim
  · have hcount : (frontier X ∩ normalLine (t : Real.Angle) 0).Countable := by
      refine (Set.Countable.biUnion Θ.directions.countable_toSet fun s hs ↦
        frontier_innerQuadrant_inter_fanLine_countable K hs ht).mono ?_
      rintro q ⟨hqX, hqline⟩
      have hqUnion := Finset.frontier_biUnion_subset Θ.directions
        (fun s ↦ innerQuadrant K.val.val s) hqX
      obtain ⟨s, hs, hqs⟩ := Set.mem_iUnion₂.mp hqUnion
      exact Set.mem_iUnion₂.mpr ⟨s, hs, ⟨hqs, hqline⟩⟩
    have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
    exact hcount.measure_zero (Measure.hausdorffMeasure 1)

private theorem capVertices_zero_fst_pos_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    0 < (capVertices K.val 0).1.2 0 := by
  obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
    (Θ.angle : Real.Angle)
  have huy : u 1 ≤ 1 := by
    have huy' := inner_le_supportValue K.val.val huK
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.1] at huy'
    simpa [normalVector, frame, PiLp.inner_apply] using huy'
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
  have hsin_lt : Real.sin Θ.angle < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
  have hux : 0 < u 0 := by
    rw [K.val.property.2.2.1] at hu
    simp [normalVector, frame, PiLp.inner_apply] at hu
    have hsin : 0 ≤ Real.sin Θ.angle :=
      (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
    have hmul := mul_le_mul_of_nonneg_left huy hsin
    nlinarith
  have hsupport : 0 < supportValue K.val.val (0 : Real.Angle) :=
    hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  rw [capVertices_zero_snd_eq K]
  simpa [normalVector, frame] using hsupport

private theorem hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩
          normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let L := openRay C (tangentVector (Θ.angle : Real.Angle))
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  apply measure_eq_of_symmDiff_subset_null (E :=
    L ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · exact ⟨hqL, hq.1.2⟩
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · rcases hqR with ⟨r, hr, hqr⟩
        have hD := hq.1.1.1
        rw [exposedEdge_bottom_eq_segment_zero_right K hω] at hD
        have hApos : 0 < A 0 := capVertices_zero_fst_pos_of_lt K hω
        have hqx := (fst_mem_Icc_of_mem_segment_mc4d199c hApos.le hD).2
        have hqx' : A 0 < q 0 := by
          rw [hqr]
          simp [A, normalVector, frame]
          linarith
        linarith
    · have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      simpa [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two] using hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (Θ.angle : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let R := openRay A (normalVector 0)
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
      tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hCcoord : 0 ≤ inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
    rw [hCeq, real_inner_smul_left]
    rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) = 1 by
        exact inner_tangentVector_self Θ.angle, mul_one]
    exact hL
  apply measure_eq_of_symmDiff_subset_null (E :=
    R ∩ normalLine (Θ.angle : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Θ.angle) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · rcases hqL with ⟨r, hr, hqr⟩
          have hD := hq.1.1.1
          rw [exposedEdge_left_eq_segment_zero_left K hω] at hD
          rcases hD with ⟨u, v, hu, hv, huv, hqseg⟩
          have hvle : v ≤ 1 := by linarith
          have hqcoord_le : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤
              inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
            rw [← hqseg, inner_add_left, real_inner_smul_left,
              real_inner_smul_left, inner_zero_left, mul_zero, zero_add]
            exact mul_le_of_le_one_left hCcoord hvle
          have hqcoord_gt : inner ℝ C (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
            change inner ℝ (capVertices K.val Θ.angle).2.1
                (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle))
            rw [hqr, inner_add_left, real_inner_smul_left]
            rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
              (tangentVector (Θ.angle : Real.Angle)) = 1 by
                exact inner_tangentVector_self Θ.angle]
            simp only [mul_one, lt_add_iff_pos_right]
            exact hr
          exact (not_lt_of_ge hqcoord_le hqcoord_gt).elim
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · exact ⟨hqR, hq.1.2⟩
    · have hD := polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (normalVector 0)
        (normalVector (Θ.angle : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
        inner_normalVector_normalVector, zero_sub, Real.cos_neg]
      exact hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 =
      (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  ext q
  constructor
  · intro hq
    have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1
    have hqFrontF := capFan_inter_fanLine_subset_frontier
      (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.2⟩
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.2⟩
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      apply (mem_frontier_iff_notMem_interior hqC).mpr
      intro hqInt
      exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
        (interior_mono Set.sdiff_subset hqInt)
    rw [hp.2.2.2.2.2.1] at hqFrontC
    rcases hqFrontC with hqL | hqR
    · rcases hqL with hqL | hqcarrier
      · rcases hqL with ⟨r, hr, hqr⟩
        have hD := hq.1.1
        rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
        have hqx := fst_mem_Icc_of_mem_segment_mc4d199c
          (polygonCap_left_x_lt_right_x K).le hD
        have hqx' : q 0 < C 0 := by
          rw [hqr]
          simp only [Fin.isValue, hω, tangentVector, frame, Real.Angle.cos_coe, Real.cos_pi_div_two,
            Real.Angle.sin_coe, Real.sin_pi_div_two, PiLp.add_apply, PiLp.smul_apply,
            Matrix.cons_val_zero, smul_eq_mul, mul_neg, mul_one, add_lt_iff_neg_left,
            Left.neg_neg_iff, C]
          exact hr
        exact (not_lt_of_ge (by simpa [C] using hqx.1) hqx').elim
      · exact ⟨hqcarrier, hq.2⟩
    · rcases hqR with ⟨r, hr, hqr⟩
      have hD := hq.1.1
      rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
      have hqx := fst_mem_Icc_of_mem_segment_mc4d199c
        (polygonCap_left_x_lt_right_x K).le hD
      have hqx' : A 0 < q 0 := by
        rw [hqr]
        simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_zero,
          Real.Angle.sin_zero, neg_zero,
          PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one,
          lt_add_iff_pos_right, A]
        exact hr
      exact (not_lt_of_ge (by simpa [A] using hqx.2) hqx').elim
  · intro hq
    have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
      K hω hq
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
      hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
    exact ⟨⟨hD, hqC.2⟩, hq.2⟩

private theorem segment_subset_normalLine {a b : Point} {t : Real.Angle} {c : ℝ}
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c) :
    segment ℝ a b ⊆ normalLine t c := by
  rintro q ⟨u, v, hu, hv, huv, rfl⟩
  change inner ℝ (u • a + v • b) (normalVector t) = c
  change inner ℝ a (normalVector t) = c at ha
  change inner ℝ b (normalVector t) = c at hb
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ha, hb]
  linear_combination c * huv

private theorem hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (hDline : exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (t : Real.Angle) 0)
    (hNsub : polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))
    (hcomp : Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      (Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let D := exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle)
  let M := polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0
  have hdiff : D \ M =
      (D \ polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0 := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨hq.1, fun hqN ↦ hq.2 ⟨hqN, hDline hq.1⟩⟩, hDline hq.1⟩
    · intro hq
      exact ⟨hq.1.1, fun hqM ↦ hq.1.2 hqM.1⟩
  have hNMeas : MeasurableSet (polygonNiche Θ K.val) := by
    exact (isClosed_capFan Θ.angle).measurableSet.inter
      (isOpen_iUnion fun s ↦ isOpen_iUnion fun _ ↦
        isOpen_innerQuadrant K.val.val s).measurableSet
  have hMMeas : MeasurableSet M :=
    hNMeas.inter (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hDfinite : μ D ≠ ⊤ := by
    dsimp [μ, D]
    rw [exposedEdge_eq_segment_edgeVertices, MeasureTheory.hausdorffMeasure_segment,
      edist_dist]
    simp
  have hreal := MeasureTheory.measureReal_sdiff (μ := μ) hNsub hMMeas hDfinite
  change (μ (D \ M)).toReal = (μ D).toReal - (μ M).toReal at hreal
  rw [hdiff] at hreal
  have hcompReal := congrArg ENNReal.toReal hcomp
  dsimp [μ, D, M] at hreal hcompReal ⊢
  rw [hcompReal] at hreal
  linarith

private theorem bottom_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem left_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (Θ.angle : Real.Angle) 0 := by
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [capVertices_angle_fst_eq K, real_inner_smul_left,
      show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector (Θ.angle : Real.Angle)) = 0 by
          rw [real_inner_comm, inner_normalVector_tangentVector], mul_zero]

private theorem bottom_exposedEdge_subset_fanLine_of_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply segment_subset_normalLine
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem polygonNiche_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      polygonPolylineLengthAt K t := by
  by_cases hω : Θ.angle < Real.pi / 2
  · rcases Set.mem_insert_iff.mp ht with rfl | ht
    · rw [← polygonCapPolyline_fanLine_length K (by simp)]
      exact hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
        (left_exposedEdge_subset_fanLine_of_lt K hω)
        (polygonNiche_inter_left_subset_exposedEdge_of_lt K hω)
        (hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt K hω)
    · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
      subst t
      rw [← polygonCapPolyline_fanLine_length K (by simp)]
      apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
      · convert bottom_exposedEdge_subset_fanLine_of_lt K hω using 1; ring_nf
      · convert polygonNiche_inter_bottom_subset_exposedEdge_of_lt K hω using 1; ring_nf
      · convert hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
          K hω using 1; ring_nf
  · have hωeq : Θ.angle = Real.pi / 2 := le_antisymm Θ.angle_le (le_of_not_gt hω)
    have htT : t = Real.pi / 2 := by
      rcases Set.mem_insert_iff.mp ht with ht | ht
      · exact ht.trans hωeq
      · exact Set.mem_singleton_iff.mp ht
    subst t
    rw [← polygonCapPolyline_fanLine_length K (by simp)]
    apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
    · convert bottom_exposedEdge_subset_fanLine_of_eq K hωeq using 1; ring_nf
    · convert polygonNiche_inter_bottom_subset_exposedEdge_of_eq K hωeq using 1; ring_nf
    · convert congrArg (Measure.hausdorffMeasure 1)
        (bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq K hωeq) using 1;
        ring_nf

/-- The niche trace on a fan line is the lower face length minus polyline length. -/
theorem polygonNiche_fanLine_lengths {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t := by
  have hN := polygonNiche_fanLine_length K ht
  have hatom := congrArg ENNReal.toReal
    (surfaceAreaMeasure_atom_length K.val.val
      ((t + Real.pi : ℝ) : Real.Angle)).1
  rw [← hatom] at hN
  refine ⟨?_, hN⟩
  unfold nicheBoundaryLength
  rw [frontier_polygonNiche_inter_fanLine_eq_niche_inter K ht]
  exact hN

/-- Inner-wall and inner-ray niche lengths agree with the corresponding polyline lengths. -/
theorem polygonNiche_wall_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ Θ.directions) :
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
      polygonPolylineLengthAt K (t + Real.pi / 2) ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have hf := rotatingHallwayParts_formulas
    (K.val.val : Set Point) (t : Real.Angle)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.1]
    exact polygonNiche_bLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_bRay_length K ht
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.2.2.1]
    exact polygonNiche_dLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_dRay_length K ht

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Length
-/

public section

noncomputable section

namespace MovingSofa

theorem polygonCap_polyline_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (∀ t ∈ Θ.directions,
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
        polygonPolylineLengthAt K (t + Real.pi / 2) ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
        polygonPolylineLengthAt K (t + Real.pi / 2)) ∧
    (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (MeasureTheory.Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t) := by
  exact ⟨fun _ ht ↦ polygonNiche_wall_lengths K ht,
    fun _ ht ↦ polygonNiche_fanLine_lengths K ht⟩

private lemma polygonCapPolyline_sum_length_mul_sin {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have h := p.sum_normal_lengths_mul_sin D
    (fun t ht ↦ angleDomain_subset_Ioo Θ ((hmem t).mp ht)) (by
      intro i
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      exact ⟨t.val, (hmem t.val).mpr t.property, ht⟩)
  have heq : ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [polygonPolylineLengthAt, dite_eq_left ((hmem t).mp ht), polygonCapPolylineLength]
    rfl
  rw [heq, h, hp.2.1, hp.2.2.1]

theorem polygonCap_not_balanced_positive {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (h : ¬ IsBalancedPolygonCap K) :
    ∃ t : angleDomain Θ,
      ENNReal.ofReal (polygonCapPolylineLength K t) <
        surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} := by
  classical
  by_contra hnot
  push Not at hnot
  have hfinite : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union (Set.toFinite _)
  let D := hfinite.toFinset
  have hD : (D : Set ℝ) = angleDomain Θ := hfinite.coe_toFinset
  have hne : D.Nonempty := by
    refine ⟨Θ.angle, ?_⟩
    change Θ.angle ∈ hfinite.toFinset
    simp [angleDomain]
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have hpoly (t : angleDomain Θ) : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have htop (t : ℝ) : surfaceAreaMeasure K.val.val {(t : Real.Angle)} ≠ ⊤ := by
    rw [(surfaceAreaMeasure_atom_length K.val.val (t : Real.Angle)).2.1]
    exact ENNReal.ofReal_ne_top
  have hle (t : ℝ) (ht : t ∈ D) :
      (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal ≤ polygonPolylineLengthAt K t := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnot ⟨t, (hmem t).mp ht⟩)
    simpa [polygonPolylineLengthAt, (hmem t).mp ht, ENNReal.toReal_ofReal
      (hpoly ⟨t, (hmem t).mp ht⟩)] using hh
  have hsum : ∑ t ∈ D,
      (polygonPolylineLengthAt K t -
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal) * Real.sin t = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, polygonCapPolyline_sum_length_mul_sin K D hD]
    have hh := K.sum_hausdorffMeasure_exposedEdge_mul_sin D hne hD
    have heq : ∑ t ∈ D,
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal * Real.sin t =
        ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
      simpa only [(surfaceAreaMeasure_atom_length K.val.val _).1] using hh
    rw [heq, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun t ht ↦
    mul_nonneg (sub_nonneg.mpr (hle t ht))
      (Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).1
        (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).2).le)).mp hsum
  apply h
  intro t
  have ht := (hmem t.val).mpr t.property
  have hz := hzero t.val ht
  have hs := Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ t.property).1
    (angleDomain_subset_Ioo Θ t.property).2
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs.ne')
  apply (ENNReal.toReal_eq_toReal_iff' (htop t.val) ENNReal.ofReal_ne_top).mp
  simpa [polygonPolylineLengthAt, t.property, ENNReal.toReal_ofReal (hpoly t)] using heq.symm

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Balancing / Coefficients
-/

public section

noncomputable section
namespace MovingSofa

/-- A convex body's frontier on a supporting line is its exposed edge. -/
theorem frontier_inter_supportingLine_eq_exposedEdge (K : ConvexBody Point)
    (t : Real.Angle) :
    frontier (K : Set Point) ∩ normalLine t (supportValue K t) = exposedEdge K t := by
  ext p
  constructor
  · rintro ⟨hp, hline⟩
    exact ⟨K.isCompact.isClosed.closure_subset (frontier_subset_closure hp), hline⟩
  · intro hp
    refine ⟨mem_frontier_of_mem_of_isExteriorNormal K (a := t) hp.1 ?_, hp.2⟩
    intro q hq
    change inner ℝ (q - p) (normalVector t) ≤ 0
    rw [inner_sub_left, show inner ℝ p (normalVector t) = supportValue K t from hp.2]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)

/-- The surface-area atom is the length of the frontier on its supporting line. -/
theorem hausdorffMeasure_frontier_inter_supportingLine (K : ConvexBody Point)
    (t : Real.Angle) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K : Set Point) ∩ normalLine t (supportValue K t)) =
      surfaceAreaMeasure K {t} := by
  rw [frontier_inter_supportingLine_eq_exposedEdge]
  exact (surfaceAreaMeasure_atom_length K t).1.symm

/-- An endpoint cap's lower wall has the surface-area atom of the opposite normal. -/
theorem hausdorffMeasure_frontier_inter_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K.val.val : Set Point) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) =
      surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)} := by
  have htSupport : supportValue K.val.val (t : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      exact K.val.property.2.2.2.1
  have htOpposite :
      supportValue K.val.val ((t + Real.pi : ℝ) : Real.Angle) = 0 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      convert K.val.property.2.2.2.2.2.1 using 1
      ring_nf
  rw [htSupport, sub_self, show normalLine (t : Real.Angle) 0 =
      normalLine ((t + Real.pi : ℝ) : Real.Angle) 0 by
    ext p
    change inner ℝ p (normalVector (t : Real.Angle)) = 0 ↔
      inner ℝ p (normalVector ((t : Real.Angle) + Real.pi)) = 0
    rw [normalVector_add_pi_angle]
    simp]
  rw [← htOpposite]
  exact hausdorffMeasure_frontier_inter_supportingLine K.val.val _

/-- Away from endpoint normals, the niche boundary on the lower wall has polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      polygonCapPolylineLength K t := by
  rw [show polygonCapPolylineLength K t = polygonPolylineLengthAt K t.val by
    simp [polygonPolylineLengthAt, t.property]]
  rcases t.property with htInner | htEndpoint
  · rcases htInner with htDirection | ⟨s, hs, hst⟩
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (t.val : Real.Angle)).2.2.2.2.1
      rw [← hline]
      exact ((polygonCap_polyline_lengths K).1 t.val htDirection).1
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (s : Real.Angle)).2.2.2.2.2.2.1
      rw [← hst]
      change nicheBoundaryLength K
          (normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
            (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)) =
        polygonPolylineLengthAt K (s + Real.pi / 2)
      have hline' :
          (rotatingHallwayParts (K.val.val : Set Point) (s : Real.Angle)).d =
            normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
              (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
        simpa only [Real.Angle.coe_add] using hline
      rw [← hline']
      exact ((polygonCap_polyline_lengths K).1 s hs).2.2.1
  · exact False.elim (ht htEndpoint)

/-- At an endpoint normal, the lower-wall niche length is the opposite-face length
minus the polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t := by
  have htSupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · rw [ht]
      exact K.val.property.2.2.1
    · rw [Set.mem_singleton_iff.mp ht]
      exact K.val.property.2.2.2.1
  rw [htSupport, sub_self]
  simpa [polygonPolylineLengthAt, t.property] using
    (polygonCap_polyline_lengths K).2 t.val ht |>.1

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Balancing / Estimate
-/

public section

noncomputable section

namespace MovingSofa

private def polygonCapSupportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    PolygonHeightSpace Θ :=
  fun s ↦ supportValue K.val.val (s.val : Real.Angle)

private theorem raisedPolygonSupport_eq_update {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    raisedPolygonSupport K t varepsilon =
      Function.update (polygonCapSupportHeight K) t
        (polygonCapSupportHeight K t + varepsilon) := by
  classical
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  by_cases hst : s = t
  · subst s
    simp
  · simp [Function.update, hst]

private theorem raisedPolygonSupport_zero {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : raisedPolygonSupport K t 0 = polygonCapSupportHeight K := by
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  simp

private theorem update_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon) =
      fun s ↦ Function.update h t (h t + varepsilon) s - 1 := by
  classical
  change angleDomain Θ → ℝ at h
  funext s
  by_cases hst : s = t
  · subst s
    simp
    ring
  · simp [Function.update, hst]

private theorem polygonHeightCap_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (polygonCapSupportHeight K) = K.val.val := by
  let K' : PolygonCapTranslateSpace Θ :=
    ⟨K.val.val, ⟨K, 0, by simp⟩⟩
  change polygonHeightCap
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = K.val.val
  exact polygonHeightCap_of_translate K'

private theorem polygonHeightNiche_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (polygonCapSupportHeight K) = polygonNiche Θ K.val := by
  change polygonHeightNiche
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = polygonNiche Θ K.val
  exact (polygonHeightNiche_of_cap K).1

private theorem independentWallCap_update_eq_of_not_endpoint {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  classical
  calc
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
        independentWallCap (Function.update h t (h t + varepsilon))
          (fun s ↦ Function.update h t (h t + varepsilon) s - 1) := by
      ext p
      simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
      apply and_congr
      · apply forall_congr'
        intro s
        apply forall_congr'
        intro hs
        have hst : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
          intro hst
          apply ht
          have hval : s = t.val := congrArg Subtype.val hst
          rwa [hval] at hs
        simp [polygonHeightValue, Function.update, hst]
      · rfl
    _ = polygonHeightCap (Function.update h t (h t + varepsilon)) :=
      independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallCap_update_both_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallCap (Function.update h t (h t + varepsilon))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallNiche_update_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallNiche
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightNiche (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallNiche_sub_one (Θ := Θ) _

/-- The balancing area estimate when the perturbed normal is not an endpoint. -/
theorem polygonCap_balancing_estimate_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have htInner : t.val ∈ (Θ.directions : Set ℝ) ∪
      ((fun s : ℝ ↦ s + Real.pi / 2) '' Θ.directions) := by
    rcases t.property with htInner | htEndpoint
    · exact htInner
    · exact False.elim (ht htEndpoint)
  have hcMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨ic, hic⟩ := hcMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, false, true⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inl ⟨t.val, htInner, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cc, etac, hCc, hetac, hcap⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 ic t hic
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  have hcapCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc ic).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hic]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_not_endpoint K t ht
  refine ⟨Cc + Cn, min etac etan, add_nonneg hCc hCn, lt_min hetac hetan, ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonC : |varepsilon| ≤ etac := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_left _ _)
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_right _ _)
  have hc := hcap varepsilon hvarepsilonC
  have hn := hniche varepsilon hvarepsilonN
  rw [hcapCoeff, independentWallCap_update_eq_of_not_endpoint h t varepsilon ht] at hc
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp only [hin, Bool.false_eq_true, ite_false, one_mul] at hn
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cc + Cn) * varepsilon ^ 2
  calc
    _ = |(ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon) -
      (ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon)| := by ring_nf
    _ ≤ |ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon| +
      |ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon| := abs_sub _ _
    _ ≤ Cc * varepsilon ^ 2 + Cn * varepsilon ^ 2 := add_le_add hc hn
    _ = (Cc + Cn) * varepsilon ^ 2 := by ring

/-- The balancing area estimate for a simultaneous endpoint-wall displacement. -/
theorem polygonCap_balancing_estimate_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have hcuMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨icu, hicu⟩ := hcuMem
  have hclMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨icl, hicl⟩ := hclMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cu, etau, hCu, hetau, hcapUpper⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 icu t hicu
  obtain ⟨Cl, etal, hCl, hetal, hcapLower⟩ :=
    polygonCap_lower_wall_area_variation h Hc hHc hSc.1 icl t hicl
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  obtain ⟨R, epsilonZero, hR, hepsilonZero, huniform⟩ :=
    polygonPerturbation_uniform_bounds Θ h
  have hupperCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icu).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicu]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hlowerCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icl).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicl]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_lowerLine_of_endpoint K ht)
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_endpoint K t ht
  let eta := min etau (min etal (min etan (min epsilonZero 1)))
  refine ⟨Cu + Cl + Cn, eta, add_nonneg (add_nonneg hCu hCl) hCn,
    lt_min hetau (lt_min hetal (lt_min hetan (lt_min hepsilonZero zero_lt_one))), ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonU : |varepsilon| ≤ etau := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonL : |varepsilon| ≤ etal := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonZero : varepsilon ≤ epsilonZero :=
    hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonOne : varepsilon ≤ 1 :=
    hvarepsilonEta.trans (by simp [eta])
  have hu := hcapUpper varepsilon hvarepsilonU
  have hl := hcapLower varepsilon hvarepsilonL
  have hn := hniche varepsilon hvarepsilonN
  rw [hupperCoeff] at hu
  rw [hlowerCoeff] at hl
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp only [hin, ↓reduceIte, Real.Angle.coe_add, neg_mul, one_mul, neg_sub] at hn
  have hchangeUpper (s : angleDomain Θ) :
      |Function.update h t (h t + varepsilon) s - h s| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself : Function.update h t (h t + varepsilon) t = h t + varepsilon :=
        Function.update_self t (h t + varepsilon) h
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hchangeLower (s : angleDomain Θ) :
      |Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) s -
        (h s - 1)| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself :
          Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) t =
            h t - 1 + varepsilon :=
        Function.update_self t (h t - 1 + varepsilon) (fun r ↦ h r - 1)
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hbound (upper lower : PolygonHeightSpace Θ)
      (hupper : upper = h ∨ upper = Function.update h t (h t + varepsilon))
      (hlower : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) :
      independentWallCap upper lower ⊆ Metric.closedBall 0 R := by
    apply (huniform upper lower ?_ ?_).1
    · rcases hupper with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeUpper
    · rcases hlower with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeLower
  have hadd := independentWallCap_area_update_add h t varepsilon R
    hvarepsilon hvarepsilonOne hbound
  rw [independentWallCap_update_both_eq h t varepsilon,
    independentWallCap_sub_one (Θ := Θ)] at hadd
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cu + Cl + Cn) * varepsilon ^ 2
  let upperResidual :=
    ClassicalResults.area
        (independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1)) -
      ClassicalResults.area (polygonHeightCap h) -
      (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon
  let lowerResidual :=
    ClassicalResults.area
        (independentWallCap h
          (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon))) -
      ClassicalResults.area (polygonHeightCap h) +
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal * varepsilon
  let nicheResidual :=
    ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
      ClassicalResults.area (polygonHeightNiche h) +
      ((surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon
  have hn' : |nicheResidual| ≤ Cn * varepsilon ^ 2 := by
    dsimp [nicheResidual]
    convert hn using 1
    ring_nf
  have hresidual :
      (ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
          ClassicalResults.area
            (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
        (ClassicalResults.area (polygonHeightCap h) -
          ClassicalResults.area (polygonHeightNiche h)) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon =
      upperResidual + lowerResidual - nicheResidual := by
    dsimp [upperResidual, lowerResidual, nicheResidual]
    linarith [hadd]
  rw [hresidual]
  calc
    |upperResidual + lowerResidual - nicheResidual| ≤
        |upperResidual + lowerResidual| + |nicheResidual| := abs_sub _ _
    _ ≤ (|upperResidual| + |lowerResidual|) + |nicheResidual| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (Cu * varepsilon ^ 2 + Cl * varepsilon ^ 2) + Cn * varepsilon ^ 2 := by
      exact add_le_add (add_le_add hu hl) hn'
    _ = (Cu + Cl + Cn) * varepsilon ^ 2 := by ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Balancing
-/

public section

noncomputable section

namespace MovingSofa

private lemma exists_pos_lt_of_quadratic_error {f : ℝ → ℝ} {a C η δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hη : 0 < η) (hδ : 0 < δ)
    (herror : ∀ ε, 0 ≤ ε → ε ≤ η → |f ε - f 0 - a * ε| ≤ C * ε ^ 2) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ f 0 < f ε := by
  let ε := min (η / 2) (min (δ / 2) (a / (2 * (C + 1))))
  have hε : 0 < ε := lt_min (half_pos hη)
    (lt_min (half_pos hδ) (div_pos ha (by positivity)))
  have hεη : ε ≤ η := (min_le_left _ _).trans (by linarith)
  have hεδ : ε < δ := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith))
  have hεa : ε ≤ a / (2 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : ε * (2 * (C + 1)) ≤ a :=
    (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hεa
  have hsmall : C * ε < a := by nlinarith
  have hquad : C * ε ^ 2 < a * ε := by nlinarith [mul_pos (sub_pos.mpr hsmall) hε]
  have hlower := (abs_le.mp (herror ε hε.le hεη)).1
  exact ⟨ε, hε, hεδ, by linarith⟩

/-- A support-height increment has the balancing first-order area term. -/
theorem polygonCap_balancing_estimate {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ η →
      |polygonHeightArea (raisedPolygonSupport K t ε) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * ε| ≤ C * ε ^ 2 := by
  by_cases ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_balancing_estimate_of_endpoint K t ht
  · exact polygonCap_balancing_estimate_of_not_endpoint K t ht

/-- A maximum polygon cap has balanced boundary coefficients. -/
theorem maximumPolygonCap_balanced {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) : IsBalancedPolygonCap K := by
  classical
  by_contra hnot
  obtain ⟨t, ht⟩ := polygonCap_not_balanced_positive K hnot
  have hnonneg : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have hfinite : surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} ≠ ⊤ := by
    let := (surfaceAreaMeasure_face_union K.val.val).1
    exact MeasureTheory.measure_ne_top _ _
  have hpos : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} :=
    lt_of_le_of_lt zero_le ht
  have hgain : 0 < (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
      polygonCapPolylineLength K t := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).mpr ht
    rw [ENNReal.toReal_ofReal hnonneg] at hh
    exact sub_pos.mpr hh
  obtain ⟨C, η, hC, hη, herror⟩ := polygonCap_balancing_estimate K t
  obtain ⟨δ, hδ, hfeasible⟩ := polygonCap_positive_height_increment K t hpos
  obtain ⟨ε, hε, hεδ, harea⟩ := exists_pos_lt_of_quadratic_error hgain hC hη hδ herror
  obtain ⟨K', hK'⟩ := hfeasible ε hε hεδ
  obtain ⟨L, v, htranslate⟩ := K'.property
  have hreduce := polygonHeightArea_le_translateArea (raisedPolygonSupport K t ε) K' hK'.symm
  rw [(polygonTranslateExtensions_eq L v K' htranslate).2] at hreduce
  have hzero : raisedPolygonSupport K t 0 =
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) := by
    funext s
    simp [raisedPolygonSupport]
  rw [hzero, (polygonHeightNiche_of_cap K).2] at harea
  exact (not_lt_of_ge (hK.2 L)) (harea.trans_le hreduce)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Edge normals and contact vertices of a finite half-plane intersection

A convex body presented as a finite intersection of closed half-planes has only finitely many
possible contact points and only finitely many possible proper edge normals. This file records
both facts in the form used by the discrete estimates on polygon caps:

* `exists_active_constraint_of_mem_notMem_interior`: a boundary point activates a constraint;
* `exists_active_constraint_of_forall_notMem_add_smul`: a direction that immediately leaves the
  body activates a constraint increasing along it;
* `properEdgeNormal_eq_constraint_or_add_pi`: a nondegenerate exposed edge has a constraint
  normal, up to half a turn;
* `properEdgeNormal_eq_constraint`: the same, without the antipodal alternative;
* `PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal` and
  `PolygonCapSpace.properEdgeNormal_mem_allowed`: the polygon-cap versions;
* `finiteConstraintVertices`: the finite set of transversal constraint-line intersections, which
  contains every singleton exposed edge;
* `PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero`: the surface measure of a
  polygon cap is carried by its proper edge normals.
-/

public section

noncomputable section

namespace MovingSofa

/-- A point of a finite half-plane intersection off its interior lies on an active constraint. -/
theorem exists_active_constraint_of_mem_notMem_interior
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x : Point} (hxS : x ∈ S) (hxint : x ∉ interior S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 := by
  by_contra h
  push Not at h
  apply hxint
  rw [hS, hC.interior_biInter]
  simp only [Set.mem_iInter]
  intro c hc
  have hxc : inner ℝ x (normalVector c.1) < c.2 := by
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact lt_of_le_of_ne hle (h c hc)
  have hUopen : IsOpen {p : Point | inner ℝ p (normalVector c.1) < c.2} :=
    isOpen_lt (by fun_prop) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hUopen.mem_nhds hxc)
  intro p hp
  change inner ℝ p (normalVector c.1) < c.2 at hp
  change inner ℝ p (normalVector c.1) ≤ c.2
  exact hp.le

/-- A nondegenerate exposed edge has the normal angle of one of the constraints, up to half a
turn. -/
theorem properEdgeNormal_eq_constraint_or_add_pi
    (K : ConvexBody Point) (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 ∨ t = c.1 + (Real.pi : Real.Angle) := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hxedge : midpoint ℝ p q ∈ exposedEdge K t :=
    (convex_exposedEdge K t).segment_subset hp hq (midpoint_mem_segment p q)
  have hxfront : midpoint ℝ p q ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hxedge
    exact hxedge.1
  obtain ⟨c, hcC, hcx⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hxedge.1 hxfront.2
  refine ⟨c, hcC, ?_⟩
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
  rw [midpoint_eq_smul_add, inner_smul_left, inner_add_left] at hcx
  norm_num at hcx
  have hpcEq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqcEq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpcEq, hqcEq, sub_self]
  exact normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc

/-- If a direction immediately leaves a finite intersection of closed half-planes at a point of
it, some constraint is active there and increases along that direction. -/
theorem exists_active_constraint_of_forall_notMem_add_smul
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x w : Point} (hxS : x ∈ S) (hw : ∀ r : ℝ, 0 < r → x + r • w ∉ S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 ∧ 0 < inner ℝ w (normalVector c.1) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ c ∈ C, inner ℝ x (normalVector c.1) ≤ c.2 := by
    intro c hc
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact hle
  have hall : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ c ∈ C,
      inner ℝ (x + r • w) (normalVector c.1) ≤ c.2 := by
    refine hC.eventually_all.mpr ?_
    intro c hc
    by_cases hact : inner ℝ x (normalVector c.1) = c.2
    · have hwc : inner ℝ w (normalVector c.1) ≤ 0 := hcon c hc hact
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [inner_add_left, real_inner_smul_left, hact]
      have hrw : r * inner ℝ w (normalVector c.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) hwc
      linarith
    · have hlt : inner ℝ x (normalVector c.1) < c.2 := lt_of_le_of_ne (hmem c hc) hact
      have hcont : Continuous fun r : ℝ ↦ inner ℝ (x + r • w) (normalVector c.1) := by
        fun_prop
      have h0 : inner ℝ (x + (0 : ℝ) • w) (normalVector c.1) < c.2 := by simpa using hlt
      have hev := (hcont.tendsto 0).eventually (gt_mem_nhds h0)
      exact (hev.filter_mono nhdsWithin_le_nhds).mono fun r hr ↦ hr.le
  obtain ⟨r, hrall, hrpos⟩ := (hall.and self_mem_nhdsWithin).exists
  refine hw r hrpos ?_
  rw [hS]
  refine Set.mem_iInter.2 fun c ↦ Set.mem_iInter.2 fun hc ↦ ?_
  change inner ℝ (x + r • w) (normalVector c.1) ≤ c.2
  exact hrall c hc

/-- The normal of a nondegenerate exposed edge of a finite intersection of closed half-planes is
itself a constraint normal. -/
theorem properEdgeNormal_eq_constraint (K : ConvexBody Point)
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hx : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ exposedEdge K t :=
    (convex_exposedEdge K t) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hout : ∀ r : ℝ, 0 < r →
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q + r • normalVector t ∉ (K : Set Point) := by
    intro r hr hmemK
    have hle := inner_le_supportValue K hmemK t
    rw [inner_add_left, real_inner_smul_left, inner_normalVector_self_angle, mul_one,
      hx.2] at hle
    linarith
  obtain ⟨c, hcC, hact, hpos⟩ :=
    exists_active_constraint_of_forall_notMem_add_smul C hC _ hK hx.1 hout
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
    change inner ℝ p (normalVector c.1) ≤ c.2 at h
    exact h
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
    change inner ℝ q (normalVector c.1) ≤ c.2 at h
    exact h
  have hmid : inner ℝ ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) (normalVector c.1) =
      (inner ℝ p (normalVector c.1) + inner ℝ q (normalVector c.1)) / 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [hmid] at hact
  have hpceq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqceq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpceq, hqceq, sub_self]
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc with h | h
  · exact ⟨c, hcC, h⟩
  · exfalso
    rw [h, normalVector_add_pi_angle, inner_neg_left, inner_normalVector_self_angle] at hpos
    linarith

/-- The allowed normal set of a polygon cap is finite. -/
theorem finite_polygonCapNormals (Θ : AngleSet) :
    (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
      capLowerNormals Θ.angle).Finite := by
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact ((Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
        ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
  exact (hdomain.image _).union ((Set.finite_singleton _).insert _)

/-- Every nondegenerate exposed edge of a polygon cap has an allowed or antipodal normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
        capLowerNormals Θ.angle ∪
      ((fun u : Real.Angle ↦ u + (Real.pi : Real.Angle)) ''
        (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
          capLowerNormals Θ.angle)) := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc | htc⟩ :=
    properEdgeNormal_eq_constraint_or_add_pi K.val.val C hC hKC t ht
  · exact Or.inl (htc ▸ hCN c hcC)
  · exact Or.inr ⟨c.1, hCN c hcC, htc.symm⟩

/-- Every proper edge normal of a polygon cap is an allowed normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc⟩ := properEdgeNormal_eq_constraint K.val.val C hC hKC t ht
  exact htc ▸ hCN c hcC

/-- The finitely many transversal intersection points of a finite constraint family. -/
def finiteConstraintVertices (C : Set (Real.Angle × ℝ)) : Set Point := by
  classical
  exact ⋃ c ∈ C, ⋃ d ∈ C,
    if c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) then ∅
    else normalLine c.1 c.2 ∩ normalLine d.1 d.2

/-- A finite constraint family has finitely many transversal intersection points. -/
theorem finite_finiteConstraintVertices (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) : (finiteConstraintVertices C).Finite := by
  classical
  unfold finiteConstraintVertices
  refine hC.biUnion fun c _ ↦ hC.biUnion fun d _ ↦ ?_
  split_ifs with hparallel
  · exact Set.finite_empty
  · apply Set.Subsingleton.finite
    intro p hp q hq
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq] at hp hq
    by_contra hpq
    have hcorth : inner ℝ (p - q) (normalVector c.1) = 0 := by
      rw [inner_sub_left, hp.1, hq.1, sub_self]
    have hdorth : inner ℝ (p - q) (normalVector d.1) = 0 := by
      rw [inner_sub_left, hp.2, hq.2, sub_self]
    exact hparallel (normalVector_eq_or_eq_add_pi_of_orthogonal
      (sub_ne_zero.mpr hpq) hcorth hdorth)

/-- A singleton exposed edge of a finite half-plane intersection is a constraint vertex. -/
theorem singleton_exposedEdge_mem_finiteConstraintVertices
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {t : Real.Angle} {p : Point} (hp : exposedEdge K t = {p}) :
    p ∈ finiteConstraintVertices C := by
  classical
  have hpedge : p ∈ exposedEdge K t := by rw [hp]; exact Set.mem_singleton p
  have hpfront : p ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hpedge
    exact hpedge.1
  obtain ⟨c, hc, hpc⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hpedge.1 hpfront.2
  by_contra hnot
  have hparallel (d : Real.Angle × ℝ) (hd : d ∈ C)
      (hpd : inner ℝ p (normalVector d.1) = d.2) :
      c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) := by
    by_contra hnon
    apply hnot
    unfold finiteConstraintVertices
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, Set.mem_iUnion.2 ⟨d,
      Set.mem_iUnion.2 ⟨hd, by simp only [hnon, ↓reduceIte]; exact ⟨hpc, hpd⟩⟩⟩⟩⟩
  have horth : inner ℝ (tangentVector c.1) (normalVector c.1) = 0 := by
    induction c.1 using Real.Angle.induction_on with
    | _ r => rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvne : tangentVector c.1 ≠ 0 := by
    have hvself : inner ℝ (tangentVector c.1) (tangentVector c.1) = 1 := by
      induction c.1 using Real.Angle.induction_on with
      | _ r => exact inner_tangentVector_self r
    intro hv
    simp [hv] at hvself
  have hevent : ∀ᶠ r : ℝ in nhds 0, p + r • tangentVector c.1 ∈ (K : Set Point) := by
    have hall : ∀ᶠ r : ℝ in nhds 0, ∀ d ∈ C,
        inner ℝ (p + r • tangentVector c.1) (normalVector d.1) ≤ d.2 := by
      apply hC.eventually_all.mpr
      intro d hd
      by_cases hpd : inner ℝ p (normalVector d.1) = d.2
      · have hvd : inner ℝ (tangentVector c.1) (normalVector d.1) = 0 := by
          rcases hparallel d hd hpd with heq | heq
          · rwa [← heq]
          · have hnn : normalVector d.1 = -normalVector c.1 := by
              rw [heq, normalVector_add_pi_angle, neg_neg]
            rw [hnn, inner_neg_right, horth, neg_zero]
        exact Filter.Eventually.of_forall fun r ↦ by
          rw [inner_add_left, real_inner_smul_left, hvd, mul_zero, add_zero, hpd]
      · have hple : inner ℝ p (normalVector d.1) ≤ d.2 := by
          have hm := hpedge.1
          rw [hK] at hm
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hm d) hd
        have hlt : inner ℝ p (normalVector d.1) < d.2 := lt_of_le_of_ne hple hpd
        have hcont : Continuous
            (fun r : ℝ ↦ inner ℝ (p + r • tangentVector c.1) (normalVector d.1)) := by
          fun_prop
        have hzero : inner ℝ (p + (0 : ℝ) • tangentVector c.1) (normalVector d.1) < d.2 := by
          simpa using hlt
        filter_upwards [(hcont.tendsto 0).eventually (gt_mem_nhds hzero)] with r hr
        exact hr.le
    filter_upwards [hall] with r hr
    rw [hK]
    exact Set.mem_iInter.2 fun d ↦ Set.mem_iInter.2 fun hd ↦ hr d hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hplus : p + (ε / 2) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hminus : p + (-(ε / 2)) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hplusle := inner_le_supportValue K hplus t
  have hminusle := inner_le_supportValue K hminus t
  rw [inner_add_left, real_inner_smul_left, hpedge.2] at hplusle hminusle
  have hvt : inner ℝ (tangentVector c.1) (normalVector t) = 0 := by nlinarith
  have hplusface : p + (ε / 2) • tangentVector c.1 ∈ exposedEdge K t := by
    refine ⟨hplus, ?_⟩
    change inner ℝ (p + (ε / 2) • tangentVector c.1) (normalVector t) = supportValue K t
    rw [inner_add_left, real_inner_smul_left, hvt, mul_zero, add_zero, hpedge.2]
  rw [hp, Set.mem_singleton_iff] at hplusface
  have hzero : (ε / 2) • tangentVector c.1 = 0 :=
    add_left_cancel (show p + (ε / 2) • tangentVector c.1 = p + 0 by simpa using hplusface)
  exact hvne ((smul_eq_zero.mp hzero).resolve_left (ne_of_gt (by positivity)))

/-- The transversal constraint vertices form a one-dimensional null set. -/
theorem finiteConstraintVertices_measure_zero (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) :
    MeasureTheory.Measure.hausdorffMeasure 1 (finiteConstraintVertices C) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (finite_finiteConstraintVertices C hC).measure_zero _

/-- Surface measure of a finite intersection of closed half-planes is carried by its proper
edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  have hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite := by
    apply (hC.image Prod.fst).subset
    intro t ht
    obtain ⟨c, hc, heq⟩ := properEdgeNormal_eq_constraint K C hC hK t ht
    exact ⟨c, hc, heq.symm⟩
  apply surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    K hN (finiteConstraintVertices C) (finiteConstraintVertices_measure_zero C hC)
  intro p hp
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
  have hsingle : exposedEdge K t = {(edgeVertices K t).1} := by
    rw [exposedEdge_eq_segment_edgeVertices, ht, segment_same]
  have hpeq : p = (edgeVertices K t).1 := by simpa [hsingle] using hp
  exact hpeq ▸ singleton_exposedEdge_mem_finiteConstraintVertices C hC K hK hsingle

/-- Surface measure of a polygon cap is carried by its proper edge normals. -/
theorem PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    surfaceAreaMeasure K.val.val
      {t | (edgeVertices K.val.val t).1 = (edgeVertices K.val.val t).2} = 0 := by
  obtain ⟨C, hC, _, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    C hC K.val.val hKC

end MovingSofa

end

end

end

end

end

end
