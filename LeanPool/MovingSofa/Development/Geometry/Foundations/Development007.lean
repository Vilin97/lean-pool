/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development006

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development005






public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001



public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.ProjIcc
/-!
# Moving sofa: related mathematical developments

* `Polygon.Foundations.Development002`.
* `Bounds.Foundations.Development003`.
* `Cap.Foundations.Development005`.
* `Sofa.Foundations.Development001`.
* `Cap.Foundations.Development006`.
* `Bounds.Foundations.Development004`.
* `Cap.Foundations.Development007`.
* `Area.Foundations.Development003`.
* `Bounds.Foundations.Development005`.
* `Bounds.Foundations.Development006`.
* `Motion.Foundations.Development002`.
* `Sofa.Foundations.Development002`.
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

* `Polygon.Approximation`.
* `Polygon.CapWidthBound`.
* `Polygon.DiscreteCapData`.
* `Polygon.Height.Properties`.
* `Polygon.Nef.Slices`.
* `Polygon.Nef.Variation.LocalSlices`.
* `Polygon.Nef.Variation.Area`.
* `Polygon.Nef.Variation.Boundary`.
* `Polygon.Nef.Variation`.
* `Polygon.Nef.SignedVariation`.
* `Polygon.Height.WallVariation`.
* `Polygon.RightAngleGrid`.
* `Polygon.Translation`.
* `Polygon.Height.Reconstruction`.
* `Polygon.Height.PositiveIncrement.Contacts`.
* `Polygon.Height.PositiveIncrement`.
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
# Polygon / Approximation
-/

public section

noncomputable section

namespace MovingSofa

/-- Membership in a polygon cap is given by the strip and selected support inequalities. -/
theorem mem_angleCap_iff (Θ : AngleSet) (K : CapSpace Θ.angle) (p : Point) :
    p ∈ angleCap Θ K ↔
      ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle)) ∧
          inner ℝ p (normalVector (Θ.angle : Real.Angle)) ≤ 1)) ∧
      ∀ t ∈ Θ.directions,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle) ∧
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  simp only [angleCap, Set.mem_inter_iff, Set.mem_iInter, mem_stripParallelogram_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  rw [(rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.2.2.2.2.2.2.1]
  rfl

/-- The polygon-cap approximation contains the original cap. -/
theorem subset_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (K.val : Set Point) ⊆ angleCap Θ K := by
  intro p hp
  apply (mem_angleCap_iff Θ K p).mpr
  refine ⟨(mem_stripParallelogram_iff _ _).mp (K.subset_stripParallelogram hp), ?_⟩
  intro t _
  exact ⟨inner_le_supportValue K.val hp _, inner_le_supportValue K.val hp _⟩

/-- A polygon cap is the intersection of its selected support half-planes. -/
theorem angleCap_eq_iInter_supportValue (Θ : AngleSet) (K : CapSpace Θ.angle) :
    angleCap Θ K = ⋂ t ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
        normalHalfPlane t (supportValue K.val t) false false := by
  ext p
  simp only [Set.mem_iInter, mem_angleCap_iff]
  constructor
  · rintro ⟨⟨hy, hw⟩, ht⟩ u hu
    change inner ℝ p (normalVector u) ≤ supportValue K.val u
    rcases hu with ⟨u, hu, rfl⟩ | hu
    · rcases hu with (hu | ⟨t, ht', rfl⟩) | hu
      · exact (ht u hu).1
      · exact (ht t ht').2
      · rcases hu with rfl | hu
        · rw [K.property.2.2.1]
          exact hw.2
        · have heq : u = Real.pi / 2 := hu
          subst u
          rw [K.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hy.2
    · rcases hu with rfl | hu
      · rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
        exact neg_nonpos.mpr hw.1
      · have heq : u = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := hu
        subst u
        rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two]
        exact neg_nonpos.mpr hy.1
  · intro hp
    have ht (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩)
    have ht' (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)
    have hw := hp (Θ.angle : Real.Angle)
      (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)
    have hy := hp ((Real.pi / 2 : ℝ) : Real.Angle)
      (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)
    have hl := hp ((Θ.angle + Real.pi : ℝ) : Real.Angle) (Or.inr (Or.inl rfl))
    have hb := hp ((3 * Real.pi / 2 : ℝ) : Real.Angle) (Or.inr (Or.inr rfl))
    change inner ℝ p (normalVector _) ≤ supportValue K.val _ at hw hy hl hb
    rw [K.property.2.2.1] at hw
    rw [K.property.2.2.2.1] at hy
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
    rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hb
    have hy' : p 1 ≤ 1 := by simpa [normalVector, frame, PiLp.inner_apply] using hy
    exact ⟨⟨⟨by linarith, hy'⟩, by linarith, hw⟩, fun t h ↦ ⟨ht t h, ht' t h⟩⟩

/-- Polygon-cap approximations are closed. -/
theorem isClosed_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsClosed (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  exact isClosed_le (by fun_prop) continuous_const

/-- Polygon-cap approximations are convex. -/
theorem convex_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Convex ℝ (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply convex_iInter
  intro t
  apply convex_iInter
  intro _
  apply convex_halfSpace_le
  exact ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩

/-- Polygon-cap approximation preserves support at every selected normal. -/
theorem supportValue_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle)
    {t : Real.Angle}
    (ht : t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) :
    supportValue (angleCap Θ K) t = supportValue K.val t := by
  have hbound : ∀ p ∈ angleCap Θ K, inner ℝ p (normalVector t) ≤ supportValue K.val t := by
    intro p hp
    rw [angleCap_eq_iInter_supportValue] at hp
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hp t) ht
  have hbd : BddAbove ((fun p ↦ inner ℝ p (normalVector t)) '' angleCap Θ K) := by
    refine ⟨supportValue K.val t, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  apply le_antisymm
  · apply csSup_le ((K.val.nonempty.mono (subset_angleCap Θ K)).image _)
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact le_csSup hbd ⟨p, subset_angleCap Θ K hp, rfl⟩

/-- Polygon-cap approximation fixes caps with the prescribed normals. -/
theorem angleCap_eq_self (Θ : AngleSet) (P : PolygonCapSpace Θ) :
    angleCap Θ P.val = (P.val.val : Set Point) := by
  rw [angleCap_eq_iInter_supportValue, ← P.property.eq_iInter_supportValue]

/-- An interior selected direction bounds the polygon cap, including at right angle. -/
theorem isBounded_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Bornology.IsBounded (angleCap Θ K) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  let l := -supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) / Real.sin t
  let r := supportValue K.val (t : Real.Angle) / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + 1, ?_⟩
  intro p hp
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ K p).mp hp
  obtain ⟨ha, hb⟩ := hnormals t ht
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg hc.le hy.1]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_nonneg hs.le hy.1]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

/-- Polygon-cap approximations are compact. -/
theorem isCompact_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsCompact (angleCap Θ K) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_angleCap Θ K, isBounded_angleCap Θ K⟩

theorem angleCap_properties (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (∃ P : PolygonCapSpace Θ, (P.val.val : Set Point) = angleCap Θ K) ∧
    (K.val : Set Point) ⊆ angleCap Θ K ∧
    (∀ t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
      supportValue (angleCap Θ K) t = supportValue (K.val : Set Point) t) ∧
    (∀ P : PolygonCapSpace Θ, angleCap Θ P.val = (P.val.val : Set Point)) := by
  refine ⟨?_, subset_angleCap Θ K, fun _ ht ↦ supportValue_angleCap Θ K ht,
    angleCap_eq_self Θ⟩
  let L : ConvexBody Point := ⟨angleCap Θ K, convex_angleCap Θ K,
    isCompact_angleCap Θ K, K.val.nonempty.mono (subset_angleCap Θ K)⟩
  let N := ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hrepr : HasHalfPlaneRepresentation L N := by
    refine ⟨(fun t ↦ (t, supportValue K.val t)) '' N, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · simp only [Set.biInter_image]
      exact angleCap_eq_iInter_supportValue Θ K
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · right
      constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
  have hrepr' : HasHalfPlaneRepresentation L
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪ capLowerNormals Θ.angle) := by
    obtain ⟨C, hC, hLC⟩ := hrepr
    refine ⟨C, ?_, hLC⟩
    intro c hc
    rcases hC c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hsupp (t : Real.Angle) (ht : t ∈ N) : supportValue L t = supportValue K.val t :=
    supportValue_angleCap Θ K ht
  have hcap : IsCap Θ.angle L := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hrepr'⟩
    · rw [hsupp _ (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)]
      exact K.property.2.2.1
    · rw [hsupp _ (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)]
      exact K.property.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inl rfl))]
      exact K.property.2.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inr rfl))]
      exact K.property.2.2.2.2.2.1
  exact ⟨⟨⟨L, hcap⟩, hrepr⟩, rfl⟩

theorem polygonNiche_angleCap (Θ : AngleSet) (K P : CapSpace Θ.angle)
    (hP : (P.val : Set Point) = angleCap Θ K) :
    polygonNiche Θ K = polygonNiche Θ P ∧ polygonNiche Θ K ⊆ capNiche K := by
  refine ⟨?_, polygonNiche_subset_capNiche Θ K⟩
  have hs := (angleCap_properties Θ K).2.2.1
  have hq (t : ℝ) (ht : t ∈ Θ.directions) :
      innerQuadrant (K.val : Set Point) t = innerQuadrant (P.val : Set Point) t := by
    unfold innerQuadrant
    rw [hP, hs (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩),
      hs ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)]
  unfold polygonNiche
  congr 1
  exact Set.iUnion_congr fun t ↦ Set.iUnion_congr fun ht ↦ hq t ht

theorem polygonArea_upperBound (Θ : AngleSet) :
    (∀ K : PolygonCapSpace Θ, polygonAreaFunctional Θ K.val =
      ClassicalResults.area (K.val.val : Set Point) -
        ClassicalResults.area (polygonNiche Θ K.val)) ∧
    (∀ K : CapSpace Θ.angle, capAreaFunctional K ≤ polygonAreaFunctional Θ K) := by
  constructor
  · intro K
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ K.val).2.2.2 K]
  · intro K
    obtain ⟨P, hP⟩ := (angleCap_properties Θ K).1
    have hcap : ClassicalResults.area (K.val : Set Point) ≤
        ClassicalResults.area (angleCap Θ K) := by
      apply ENNReal.toReal_mono
      · rw [← hP]
        exact P.val.val.isCompact.measure_ne_top
      · exact MeasureTheory.measure_mono (angleCap_properties Θ K).2.1
    have hniche : ClassicalResults.area (polygonNiche Θ K) ≤
        ClassicalResults.area (capNiche K) := by
      apply ENNReal.toReal_mono (niche_uniform_bounds.1 Θ.angle K).2.2.1.ne
      exact MeasureTheory.measure_mono (polygonNiche_angleCap Θ K P.val hP).2
    exact sub_le_sub hcap hniche

/-- A maximum polygon cap dominates every cap under the polygon area functional. -/
theorem polygonAreaFunctional_le_maximum (Θ : AngleSet) (P : PolygonCapSpace Θ)
    (hP : IsMaximumPolygonCap Θ P) (K : CapSpace Θ.angle) :
    polygonAreaFunctional Θ K ≤ polygonAreaFunctional Θ P.val := by
  obtain ⟨Q, hQ⟩ := (angleCap_properties Θ K).1
  have hn := (polygonNiche_angleCap Θ K Q.val hQ).1
  have harea : polygonAreaFunctional Θ Q.val = polygonAreaFunctional Θ K := by
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ Q.val).2.2.2 Q, hQ, hn]
  rw [← harea]
  exact hP.2 Q

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
# Polygon / Cap Width Bound
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped Pointwise

private theorem directionalWidth_zero (K : ConvexBody Point) :
    directionalWidth K 0 = horizontalMax K - horizontalMin K := by
  simp only [directionalWidth, zero_add]
  rw [← Real.Angle.coe_zero, supportValue_zero_eq_horizontalMax,
    supportValue_pi_eq_neg_horizontalMin, ← sub_eq_add_neg]

private theorem volume_coordinate_open_rectangle (l r b t : ℝ) :
    volume {p : Point | p 0 ∈ Set.Ioo l r ∧ p 1 ∈ Set.Ioo b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet :
      NullMeasurableSet (Set.Ioo l r ×ˢ Set.Ioo b t) (volume : Measure (ℝ × ℝ)))
  simpa [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Set.preimage, Set.prod] using h

private theorem cap_horizontalWidth_le_of_cos_pos {ω : ℝ} (K : CapSpace ω)
    (hc : 0 < Real.cos ω) :
    directionalWidth (K.val : Set Point) 0 ≤ (1 + Real.sin ω) / Real.cos ω := by
  have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi K.property.1.le
    (K.property.2.1.trans (by linarith [Real.pi_pos]))
  have hx (p : Point) (hp : p ∈ (K.val : Set Point)) :
      -Real.sin ω / Real.cos ω ≤ p 0 ∧ p 0 ≤ 1 / Real.cos ω := by
    obtain ⟨hy, hv⟩ := (mem_stripParallelogram_iff ω p).mp (K.subset_stripParallelogram hp)
    simp [normalVector, frame, PiLp.inner_apply] at hv
    constructor
    · apply (div_le_iff₀ hc).mpr
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hy.2)]
    · apply (le_div_iff₀ hc).mpr
      nlinarith [mul_nonneg hs hy.1]
  have hmax : horizontalMax K.val ≤ 1 / Real.cos ω :=
    csSup_le (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).2)
  have hmin : -Real.sin ω / Real.cos ω ≤ horizontalMin K.val :=
    le_csInf (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).1)
  rw [directionalWidth_zero]
  calc
    horizontalMax K.val - horizontalMin K.val ≤
        1 / Real.cos ω - -Real.sin ω / Real.cos ω := sub_le_sub hmax hmin
    _ = (1 + Real.sin ω) / Real.cos ω := by ring

private theorem wedge_rectangle_inequalities {s c a b x y : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hs1 : s ≤ 1) (hc1 : c ≤ 1)
    (hL : 0 < a / c + b / s)
    (hx : x ∈ Set.Ioo (-b / s + (a / c + b / s) / 4)
      (a / c - (a / c + b / s) / 4))
    (hy : y ∈ Set.Ioo 0 ((a / c + b / s) * s * c / 4)) :
    0 ≤ y ∧ c * x + s * y < a ∧ -s * x + c * y < b := by
  let L := a / c + b / s
  have hLc : 0 ≤ L * c / 4 := by dsimp [L]; positivity
  have hLs : 0 ≤ L * s / 4 := by dsimp [L]; positivity
  have hyc : y < L * c / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = s * (L * c / 4) := by ring
      _ ≤ 1 * (L * c / 4) := mul_le_mul_of_nonneg_right hs1 hLc
      _ = L * c / 4 := one_mul _
  have hys : y < L * s / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = c * (L * s / 4) := by ring
      _ ≤ 1 * (L * s / 4) := mul_le_mul_of_nonneg_right hc1 hLs
      _ = L * s / 4 := one_mul _
  have hsy : s * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hy.1.le]
  have hcy : c * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hy.1.le]
  have hright : (x + L / 4) * c < a :=
    (lt_div_iff₀ hc).mp (by dsimp [L]; linarith [hx.2])
  have hleft : -b < (x - L / 4) * s :=
    (div_lt_iff₀ hs).mp (by dsimp [L]; linarith [hx.1])
  exact ⟨hy.1.le, by nlinarith, by nlinarith⟩

private theorem polygonNiche_area_ge_rectangle (Θ : AngleSet)
    (hΘ : Θ.angle = Real.pi / 2) {t : ℝ} (ht : t ∈ Θ.directions)
    (K : CapSpace Θ.angle) (hs : 0 < Real.sin t) (hc : 0 < Real.cos t)
    (hL : 0 < (supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) :
    ((supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ^ 2 *
      Real.sin t * Real.cos t / 8 ≤ ClassicalResults.area (polygonNiche Θ K) := by
  let a := supportValue K.val (t : Real.Angle) - 1
  let b := supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  let L := a / Real.cos t + b / Real.sin t
  let R : Set Point := {p | p 0 ∈ Set.Ioo (-b / Real.sin t + L / 4)
    (a / Real.cos t - L / 4) ∧ p 1 ∈ Set.Ioo 0 (L * Real.sin t * Real.cos t / 4)}
  have hsub : R ⊆ polygonNiche Θ K := by
    intro p hp
    have hineq := wedge_rectangle_inequalities hs hc (Real.sin_le_one t) (Real.cos_le_one t)
      hL hp.1 hp.2
    refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    · rw [hΘ]
      simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hineq.1
    · simpa [innerQuadrant, normalHalfPlane, normalVector, frame, PiLp.inner_apply,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add, a, b] using hineq.2
  have hwidth : a / Real.cos t - L / 4 - (-b / Real.sin t + L / 4) = L / 2 := by
    dsimp [L]
    ring
  have harea : ClassicalResults.area R = L ^ 2 * Real.sin t * Real.cos t / 8 := by
    change (volume R).toReal = _
    rw [volume_coordinate_open_rectangle, hwidth, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show 0 ≤ L / 2 by dsimp [L, a, b]; positivity),
      ENNReal.toReal_ofReal (show 0 ≤ L * Real.sin t * Real.cos t / 4 by
        dsimp [L, a, b]; positivity)]
    ring
  rw [← harea]
  exact ENNReal.toReal_mono (niche_uniform_bounds.2.1 Θ K).2.2.1.ne (measure_mono hsub)

theorem polygonCap_width_bound (ω t : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (ht : t ∈ Set.Ioo 0 ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Θ : AngleSet), Θ.angle = ω → t ∈ Θ.directions →
      ∀ K : PolygonCapSpace Θ, 0 ≤ polygonAreaFunctional Θ K.val →
        directionalWidth (K.val.val : Set Point) (0 : Real.Angle) ≤ c := by
  rcases lt_or_eq_of_le hω' with hlt | rfl
  · have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hlt⟩
    have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω.le
      (by linarith [Real.pi_pos])
    refine ⟨(1 + Real.sin ω) / Real.cos ω, div_pos (by linarith) hc, ?_⟩
    intro Θ hΘ _ K _
    have hcΘ : 0 < Real.cos Θ.angle := by simpa only [hΘ] using hc
    simpa only [hΘ] using cap_horizontalWidth_le_of_cos_pos K.val hcΘ
  · have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    let D := 1 / Real.cos t + 1 / Real.sin t
    let C := max (2 * D) (32 / (Real.sin t * Real.cos t))
    have hC : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hs hc)) (le_max_right _ _)
    refine ⟨C, hC, ?_⟩
    intro Θ hΘ htΘ K hnonneg
    by_contra hwidth
    have hdC : C < directionalWidth (K.val.val : Set Point) 0 := lt_of_not_ge hwidth
    rw [directionalWidth_zero] at hdC
    let d := horizontalMax K.val.val - horizontalMin K.val.val
    have hd0 : 0 < d := hC.trans hdC
    let a := supportValue K.val.val (t : Real.Angle) - 1
    let b := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
    let L := a / Real.cos t + b / Real.sin t
    have hsupport := CapSpace.horizontal_le_supportValue K.val hs.le hc.le
    simp only [Real.Angle.coe_add] at hsupport
    have ha : horizontalMax K.val.val - 1 / Real.cos t ≤ a / Real.cos t := by
      apply (le_div_iff₀ hc).mpr
      rw [sub_mul, div_mul_cancel₀ _ hc.ne']
      dsimp [a]
      linarith [hsupport.1]
    have hb : -horizontalMin K.val.val - 1 / Real.sin t ≤ b / Real.sin t := by
      apply (le_div_iff₀ hs).mpr
      rw [sub_mul, div_mul_cancel₀ _ hs.ne']
      dsimp [b]
      linarith [hsupport.2]
    have hLd : d - D ≤ L := by dsimp [L, d, D]; linarith
    have hdD : 2 * D < d := (le_max_left _ _).trans_lt hdC
    have hdlarge : 32 / (Real.sin t * Real.cos t) < d := (le_max_right _ _).trans_lt hdC
    have hhalf : d / 2 < L := by linarith
    have hL : 0 < L := (half_pos hd0).trans hhalf
    have hlower := polygonNiche_area_ge_rectangle Θ hΘ htΘ K.val hs hc hL
    have hsq : (d / 2) ^ 2 < L ^ 2 := (sq_lt_sq₀ (half_pos hd0).le hL.le).mpr hhalf
    have hsq' := mul_lt_mul_of_pos_right hsq (mul_pos hs hc)
    have hdlarge' : 32 < d * (Real.sin t * Real.cos t) :=
      (div_lt_iff₀ (mul_pos hs hc)).mp hdlarge
    have hquad : d < L ^ 2 * Real.sin t * Real.cos t / 8 := by
      nlinarith [mul_pos hd0 (sub_pos.mpr hdlarge')]
    have harea := K.val.area_le_horizontalWidth
    have hidentity := (polygonArea_upperBound Θ).1 K
    change L ^ 2 * Real.sin t * Real.cos t / 8 ≤ _ at hlower
    change ClassicalResults.area (K.val.val : Set Point) ≤ d at harea
    rw [hidentity] at hnonneg
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
# Polygon / Discrete Cap Data
-/

public section

noncomputable section

namespace MovingSofa

/-- The uniformly spaced interior directions for a right-angle polygonal approximation. -/
@[expose]
def rightAngleSet (n : ℕ) (hn : 2 ≤ n) : AngleSet :=
  uniformAngleSet (Real.pi / 2) (by positivity) le_rfl n hn

/-- The angular mesh size `π/(2n)`. -/
@[expose]
def polygonStepSize (n : ℕ) : ℝ := (Real.pi / 2) / n

/-- The cap maximizes the polygonal functional on a uniform mesh with a power-of-two step
count. -/
@[expose]
def IsMaximumPolygonCapSteps (n : ℕ) (K : RightAngleCapSpace) : Prop :=
  ∃ hn : 2 ≤ n, (∃ k : ℕ, n = 2 ^ k) ∧
    ∃ P : PolygonCapSpace (rightAngleSet n hn),
      P.val = K ∧ IsMaximumPolygonCap (rightAngleSet n hn) P

/-- The two piecewise scalar functions used in the arm-length inequalities. -/
@[expose]
def magicFunctions : (NNReal → ℝ) × (NNReal → ℝ) :=
  (fun x ↦ max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2),
   fun x ↦ (x : ℝ) - max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2))

/-- The magic function `m₀` is nondecreasing: it is `3 * x / 2 - 1` on `[0, 1]`, `x / 2` on
`[1, 2]`, and constant equal to `1` afterwards. -/
theorem magicFunctions_snd_monotone : Monotone magicFunctions.2 := by
  intro a b hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  simp only [magicFunctions, max_def]
  rcases abs_cases ((a : ℝ) - 1) with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
    rcases abs_cases ((b : ℝ) - 1) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
      rw [ha1, hb1] <;> split_ifs <;> linarith

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
# Polygon / Height / Properties
-/

public section

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightValue (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) t =
      supportValue K.val.val (t : Real.Angle) := by
  simp [polygonHeightValue, ht]

private theorem polygonHeightFan_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightFan (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      capFan Θ.angle := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext q
  simp only [polygonHeightFan, Set.mem_iInter, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1]
  simp [capFan]

private theorem polygonHeightNiche_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      polygonNiche Θ K.val := by
  unfold polygonHeightNiche polygonNiche
  rw [polygonHeightFan_supportValue K]
  congr 1
  apply Set.iUnion_congr
  intro t
  apply Set.iUnion_congr
  intro ht
  have htD : t ∈ angleDomain Θ := by simp [angleDomain, ht]
  have htTD : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [polygonHeightValue_supportValue K htD, polygonHeightValue_supportValue K htTD]
  rfl

private theorem polygonHeightParallelogram_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightParallelogram (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      (stripParallelogram Θ.angle).1 := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext p
  simp only [polygonHeightParallelogram, Set.mem_iInter, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  tauto

private theorem polygonHeightCap_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      angleCap Θ K.val := by
  unfold polygonHeightCap
  rw [polygonHeightParallelogram_supportValue K]
  ext p
  rw [mem_angleCap_iff]
  simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, Set.mem_iInter]
  apply and_congr_right
  intro _
  constructor
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl (Or.inl ht)
    have htTD : t + Real.pi / 2 ∈ angleDomain Θ := Or.inl (Or.inr ⟨t, ht, rfl⟩)
    have h₁ := h t (Or.inl ht)
    have h₂ := h (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
    rw [polygonHeightValue_supportValue K htD] at h₁
    rw [polygonHeightValue_supportValue K htTD] at h₂
    exact ⟨h₁, h₂⟩
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl ht
    rw [polygonHeightValue_supportValue K htD]
    rcases ht with ht | ⟨s, hs, rfl⟩
    · exact (h t ht).1
    · exact (h s hs).2

private theorem mem_polygonHeightCap_supportValue_image_add {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q p : Point) :
    p + q ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) ↔
    p ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
    Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inl ht)]
    simp [normalHalfPlane, inner_add_left]

private theorem polygonHeightNiche_supportValue_image_add {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (q : Point) :
    polygonHeightNiche (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [← polygonHeightNiche_supportValue K]
  simp only [Set.mem_image, add_left_inj, exists_eq_right]
  simp only [polygonHeightNiche, polygonHeightFan, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_iUnion]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply exists_congr
    intro t
    apply exists_congr
    intro ht
    rw [hval t (Or.inl (Or.inl ht)),
      hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]

theorem polygonHeightCap_of_translate {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    polygonHeightCap (polygonTranslateHeight K) = K.val := by
  obtain ⟨P, q, hK⟩ := K.property
  unfold polygonTranslateHeight
  rw [hK]
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [mem_polygonHeightCap_supportValue_image_add, polygonHeightCap_supportValue, angleCap_eq_self]
  simp

theorem polygonTranslateHeight_injective (Θ : AngleSet) :
    Function.Injective (polygonTranslateHeight (Θ := Θ)) := by
  intro K L h
  apply Subtype.ext
  rw [← polygonHeightCap_of_translate K, ← polygonHeightCap_of_translate L, h]

theorem polygonHeightNiche_of_cap {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val :
      Real.Angle)) =
      polygonNiche Θ K.val ∧
    polygonHeightArea (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) =
      polygonAreaFunctional Θ K.val := by
  refine ⟨polygonHeightNiche_supportValue K, ?_⟩
  unfold polygonHeightArea polygonAreaFunctional
  rw [polygonHeightCap_supportValue K, polygonHeightNiche_supportValue K]

theorem polygonTranslateExtensions_eq {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q : Point) (K' : PolygonCapTranslateSpace Θ)
    (hK : K'.val = (fun p ↦ p + q) '' (K.val.val : Set Point)) :
    (polygonTranslateExtensions K').1 = (fun p ↦ p + q) '' polygonNiche Θ K.val ∧
    (polygonTranslateExtensions K').2 = polygonAreaFunctional Θ K.val := by
  have hn : polygonHeightNiche (polygonTranslateHeight K') =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
    unfold polygonTranslateHeight
    rw [hK]
    exact polygonHeightNiche_supportValue_image_add K q
  refine ⟨hn, ?_⟩
  change ClassicalResults.area (polygonHeightCap (polygonTranslateHeight K')) -
    ClassicalResults.area (polygonHeightNiche (polygonTranslateHeight K')) = _
  rw [polygonHeightCap_of_translate K', hn, hK, ClassicalResults.area_image_add,
    ClassicalResults.area_image_add]
  unfold polygonAreaFunctional
  rw [angleCap_eq_self]

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
# Polygon / Nef / Slices
-/

public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

/-- Convert normal and tangent coordinates into a point in the frame at angle `a`. -/
def framePoint (a : Real.Angle) (x y : ℝ) : Point :=
  rotationMap a !₂[x, y]

lemma framePoint_eq (a : Real.Angle) (x y : ℝ) :
    framePoint a x y = x • normalVector a + y • tangentVector a := by
  ext j
  fin_cases j <;>
    simp [framePoint, rotationMap, Orientation.rotation_apply,
      rightAngleRotation_apply, normalVector, tangentVector, frame]
  <;> ring

@[simp] lemma inner_framePoint_normalVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector a) = x := by
  rw [framePoint, inner_rotationMap_normalVector]
  rfl

@[simp] lemma inner_framePoint_tangentVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (tangentVector a) = y := by
  rw [framePoint, inner_rotationMap_tangentVector]
  rfl

@[simp] lemma norm_tangentVector_angle (a : Real.Angle) : ‖tangentVector a‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [tangentVector, frame, Fin.sum_univ_two]
  nlinarith [Real.Angle.cos_sq_add_sin_sq a]

/-- The normal-normal coefficient for changing between two oriented frames. -/
def frameNormalCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (normalVector a) (normalVector b)

/-- The tangent-normal coefficient for changing between two oriented frames. -/
def frameTangentCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (tangentVector a) (normalVector b)

lemma inner_framePoint_normalVector_eq (a b : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector b) =
      frameNormalCoeff a b * x + frameTangentCoeff a b * y := by
  rw [framePoint_eq, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  simp only [frameNormalCoeff, frameTangentCoeff]
  ring

/-- Select the half-plane side required by a Boolean cell’s membership pattern. -/
def cellUpper {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Bool :=
  if P j then (H j).upper else !(H j).upper

/-- Solve the wall equation for the tangent coordinate at a fixed normal coordinate. -/
def frameBoundaryValue (a : Real.Angle) (H : PlanarHalfPlaneData) (x : ℝ) : ℝ :=
  (H.height - frameNormalCoeff a H.angle * x) / frameTangentCoeff a H.angle

lemma frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    frameBoundaryValue a H x - frameBoundaryValue a H z =
      -(frameNormalCoeff a H.angle / frameTangentCoeff a H.angle) * (x - z) := by
  simp only [frameBoundaryValue]
  ring

lemma abs_frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    |frameBoundaryValue a H x - frameBoundaryValue a H z| =
      |frameNormalCoeff a H.angle / frameTangentCoeff a H.angle| * |x - z| := by
  rw [frameBoundaryValue_sub, abs_mul, abs_neg]

/-- The wall bounds a Boolean cell’s slice from above in the selected frame. -/
def isUpperEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ 0 < frameTangentCoeff a (H j).angle) ∨
    (cellUpper H P j = true ∧ frameTangentCoeff a (H j).angle < 0)

/-- The wall bounds a Boolean cell’s slice from below in the selected frame. -/
def isLowerEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ frameTangentCoeff a (H j).angle < 0) ∨
    (cellUpper H P j = true ∧ 0 < frameTangentCoeff a (H j).angle)

/-- The affine wall functions imposing upper bounds on the slice. -/
def upperBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isUpperEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

/-- The affine wall functions imposing lower bounds on the slice. -/
def lowerBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isLowerEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

/-- The minimum of all upper wall functions, capped by the truncation height `R`. -/
def upperEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (upperBoundaryFunctions a H P).foldr (fun f r ↦ min (f x) r) R

/-- The maximum of all lower wall functions, bounded below by `-R`. -/
def lowerEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (lowerBoundaryFunctions a H P).foldr (fun f r ↦ max (f x) r) (-R)

/-- The sum of absolute wall slopes, bounding the variation of slice envelopes. -/
def slopeBound {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData) : ℝ :=
  ∑ j, |frameNormalCoeff a (H j).angle / frameTangentCoeff a (H j).angle|

lemma slopeBound_nonneg {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) : 0 ≤ slopeBound a H := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma abs_upperEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |upperEnvelope a H P R x - upperEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_min_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

lemma abs_lowerEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |lowerEnvelope a H P R x - lowerEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_max_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

/-- The nonnegative difference between the truncated upper and lower slice envelopes. -/
def cellSliceLength {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  max (upperEnvelope a H P R x - lowerEnvelope a H P R x) 0

lemma abs_cellSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
      (2 * slopeBound a H) * |x - z| := by
  unfold cellSliceLength
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc
      |(upperEnvelope a H P R x - lowerEnvelope a H P R x) -
          (upperEnvelope a H P R z - lowerEnvelope a H P R z)| ≤
          |upperEnvelope a H P R x - upperEnvelope a H P R z| +
            |lowerEnvelope a H P R x - lowerEnvelope a H P R z| := by
              rw [sub_sub_sub_comm]
              exact abs_sub _ _
      _ ≤ slopeBound a H * |x - z| + slopeBound a H * |x - z| :=
        add_le_add (abs_upperEnvelope_sub_le a H P R x z)
          (abs_lowerEnvelope_sub_le a H P R x z)
      _ = (2 * slopeBound a H) * |x - z| := by ring
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
      (abs_nonneg _)

lemma continuous_cellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R : ℝ) :
    Continuous (cellSliceLength a H P R) := by
  let K : NNReal :=
    ⟨2 * slopeBound a H, mul_nonneg (by norm_num) (slopeBound_nonneg a H)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) fun x z ↦ ?_).continuous
  change |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
    (2 * slopeBound a H) * |x - z|
  exact abs_cellSliceLength_sub_le a H P R x z

/-- The closed Boolean cell’s slice at a fixed normal coordinate, truncated to `[-R, R]`. -/
def closedCellSlice {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ closedBooleanCell H P} ∩ Set.Icc (-R) R

/-- Every wall parallel to the slice is satisfied at the selected normal coordinate. -/
def parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    framePoint a x 0 ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false

lemma mem_closedCellSlice_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x y : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    y ∈ closedCellSlice a H P R x ↔
      lowerEnvelope a H P R x ≤ y ∧ y ≤ upperEnvelope a H P R x := by
  classical
  rw [closedCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc,
    lowerEnvelope, upperEnvelope, List.foldr_max_apply_le_iff, List.le_foldr_min_apply_iff]
  constructor
  · rintro ⟨hycell, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter] at hycell
    refine ⟨⟨hyR.1, ?_⟩, hyR.2, ?_⟩
    · intro f hf
      simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff_of_neg hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff₀ hb).2
        nlinarith
    · intro f hf
      simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff₀ hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff_of_neg hb).2
        nlinarith
  · rintro ⟨⟨hyRneg, hylower⟩, hyR, hyupper⟩
    refine ⟨?_, hyRneg, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter]
    intro j
    change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false
    by_cases hb0 : frameTangentCoeff a (H j).angle = 0
    · have hj := hparallel j hb0
      cases hu : cellUpper H P j <;>
        simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hj ⊢ <;>
        rw [inner_framePoint_normalVector_eq] at hj ⊢ <;>
        simp only [hb0, mul_zero, zero_mul, add_zero] at hj ⊢ <;>
        exact hj
    · rcases lt_or_gt_of_ne hb0 with hb | hb
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isLowerEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (div_le_iff_of_neg hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isUpperEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (le_div_iff_of_neg hb).mp hjbound
          nlinarith
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isUpperEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (le_div_iff₀ hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isLowerEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (div_le_iff₀ hb).mp hjbound
          nlinarith

lemma volume_closedCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    (MeasureTheory.volume (closedCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  have hset : closedCellSlice a H P R x =
      Set.Icc (lowerEnvelope a H P R x) (upperEnvelope a H P R x) := by
    ext y
    simpa [Set.mem_Icc] using mem_closedCellSlice_iff a H P R x y hparallel
  rw [hset, Real.volume_Icc]
  unfold cellSliceLength
  by_cases h : 0 ≤ upperEnvelope a H P R x - lowerEnvelope a H P R x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have h' : upperEnvelope a H P R x - lowerEnvelope a H P R x ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos h', max_eq_right h']
    rfl

/-- The actual Boolean membership cell’s slice, truncated to `[-R, R]`. -/
def booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ booleanCell (fun j ↦ (H j).carrier) P} ∩ Set.Icc (-R) R

/-- No wall parallel to the slice has its boundary at the selected normal coordinate. -/
def noParallelBoundaryAt {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    frameNormalCoeff a (H j).angle * x ≠ (H j).height

/-- The tangent coordinates at which the slice meets a wall boundary. -/
def cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Set ℝ :=
  ⋃ j, {y | inner ℝ (framePoint a x y) (normalVector (H j).angle) = (H j).height}

lemma finite_cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) (hx : noParallelBoundaryAt a H x) :
    (cellSliceBoundaryExceptions a H x).Finite := by
  classical
  unfold cellSliceBoundaryExceptions
  apply Set.Finite.iUnion Set.finite_univ
  · intro j _
    apply Set.Subsingleton.finite
    intro y hy z hz
    simp only [Set.mem_ofPred_eq, inner_framePoint_normalVector_eq] at hy hz
    by_cases hb : frameTangentCoeff a (H j).angle = 0
    · exact (hx j hb (by simpa [hb] using hy)).elim
    · rcases lt_or_gt_of_ne hb with hb | hb <;> nlinarith
  · simp

lemma volume_booleanCellSlice_eq_closedCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hx : noParallelBoundaryAt a H x) :
    MeasureTheory.volume (booleanCellSlice a H P R x) =
      MeasureTheory.volume (closedCellSlice a H P R x) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero :=
    (finite_cellSliceBoundaryExceptions a H x hx).measure_zero MeasureTheory.volume
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mp hycell, hyR⟩
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mpr hycell, hyR⟩

lemma volume_booleanCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x)
    (hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x hx]
  exact volume_closedCellSlice_toReal a H P R x hparallel

lemma normalVector_eq_frameCombination (a b : Real.Angle) :
    normalVector b = frameNormalCoeff a b • normalVector a +
      frameTangentCoeff a b • tangentVector a := by
  symm
  simpa only [frameNormalCoeff, frameTangentCoeff, real_inner_comm] using
    inner_normalVector_smul_add_inner_tangentVector_smul (normalVector b) a

lemma normalLine_eq_of_frameTangentCoeff_eq_zero {a b : Real.Angle} {h k : ℝ}
    (hb : frameTangentCoeff a b = 0) (hk : frameNormalCoeff a b * h = k) :
    normalLine b k = normalLine a h := by
  have hvec : normalVector b = frameNormalCoeff a b • normalVector a := by
    rw [normalVector_eq_frameCombination a b, hb, zero_smul, add_zero]
  have hcoeff : frameNormalCoeff a b ≠ 0 := by
    intro hc
    have : normalVector b = 0 := by simp [hvec, hc]
    have hnorm : ‖normalVector b‖ = 1 := by
      simpa only [b.coe_toReal] using norm_normalVector_real b.toReal
    rw [this, norm_zero] at hnorm
    norm_num at hnorm
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, hvec, inner_smul_right]
  rw [← hk]
  constructor <;> intro hp
  · exact (mul_left_cancel₀ hcoeff hp)
  · exact congrArg (frameNormalCoeff a b * ·) hp

@[simp] lemma frameNormalCoeff_self (a : Real.Angle) : frameNormalCoeff a a = 1 := by
  simpa only [frameNormalCoeff, a.coe_toReal] using inner_normalVector_self a.toReal

lemma measurableSet_booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) :
    MeasurableSet (booleanCellSlice a H P R x) := by
  apply MeasurableSet.inter _ measurableSet_Icc
  have hcont : Continuous (fun y ↦ framePoint a x y) := by
    simp_rw [framePoint_eq]
    fun_prop
  exact (measurableSet_booleanCell H P).preimage hcont.measurable

/-- The envelope slice length when parallel walls are feasible, and zero otherwise. -/
def actualCellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : ℝ := by
  classical
  exact if parallelCellFeasible a H P x then cellSliceLength a H P R x else 0

lemma closedCellSlice_eq_empty_of_not_parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : ¬parallelCellFeasible a H P x) :
    closedCellSlice a H P R x = ∅ := by
  classical
  unfold parallelCellFeasible at hparallel
  push Not at hparallel
  obtain ⟨j, hb, hj⟩ := hparallel
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hycell := hy.1
  simp only [closedBooleanCell, Set.mem_iInter] at hycell
  have hjy := hycell j
  change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
    (cellUpper H P j) false at hjy
  cases hu : cellUpper H P j <;>
    simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
      Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, zero_mul, add_zero]
      at hj hjy
  · exact hj hjy
  · exact hj hjy

lemma volume_booleanCellSlice_toReal_eq_actual {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (_hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      actualCellSliceLength a H P R x := by
  by_cases hp : parallelCellFeasible a H P x
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    exact volume_booleanCellSlice_toReal a H P R x hp _hx
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x _hx,
      closedCellSlice_eq_empty_of_not_parallelCellFeasible a H P R x hp,
      MeasureTheory.measure_empty]
    rfl

/-- The measurable equivalence between the Euclidean plane and a pair of real coordinates. -/
def frameCoordinates : Point ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

lemma frameCoordinates_measurePreserving :
    MeasureTheory.MeasurePreserving frameCoordinates MeasureTheory.volume
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
  rw [← MeasureTheory.Measure.volume_eq_prod]
  convert EuclideanSpace.volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

lemma framePoint_measurePreserving (a : Real.Angle) :
    MeasureTheory.MeasurePreserving (fun p : ℝ × ℝ ↦ framePoint a p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume := by
  have hcoordinates : MeasureTheory.MeasurePreserving frameCoordinates.symm
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume :=
    frameCoordinates_measurePreserving.symm frameCoordinates
  have hrotation : MeasureTheory.MeasurePreserving
      (EuclideanGeometry.o.rotation a : Point → Point) :=
    LinearIsometryEquiv.measurePreserving _
  convert hrotation.comp hcoordinates using 1
  funext p
  rfl

lemma volume_toReal_eq_integral_frameSlice (a : Real.Angle) {S : Set Point}
    (hS : MeasurableSet S) (hSfinite : MeasureTheory.volume S ≠ ⊤) :
    (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
  let f : ℝ × ℝ → Point := fun p ↦ framePoint a p.1 p.2
  have hf := framePoint_measurePreserving a
  have hpre : MeasurableSet (f ⁻¹' S) := hS.preimage hf.measurable
  have hmeasure : MeasureTheory.volume (f ⁻¹' S) = MeasureTheory.volume S :=
    hf.measure_preimage hS.nullMeasurableSet
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      MeasureTheory.volume) (f ⁻¹' S) =
      ∫⁻ x : ℝ, MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) :=
    MeasureTheory.Measure.prod_apply hpre
  have hsectionMeas : Measurable
      (fun x : ℝ ↦ MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))) :=
    measurable_measure_prodMk_left hpre
  have hsectionFinite : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) < ⊤ :=
    MeasureTheory.Measure.ae_measure_lt_top hpre (by
      rw [← MeasureTheory.Measure.volume_eq_prod, hmeasure]
      exact hSfinite)
  rw [← hmeasure]
  calc
    (MeasureTheory.volume (f ⁻¹' S)).toReal =
        (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          MeasureTheory.volume) (f ⁻¹' S)).toReal := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = (∫⁻ x : ℝ,
        MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      congrArg ENNReal.toReal hprod
    _ = ∫ x : ℝ,
        (MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      (MeasureTheory.integral_toReal hsectionMeas.aemeasurable hsectionFinite).symm
    _ = ∫ x : ℝ,
        (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
      rfl

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Local Slices
-/

public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

/-- Replace one wall by a closed upper-bound wall at auxiliary height `M`. -/
def auxiliaryHalfPlaneFamily {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) : Fin n → PlanarHalfPlaneData :=
  Function.update H i
    { angle := (H i).angle, height := M, upper := false, strict := false }

@[simp] lemma auxiliaryHalfPlaneFamily_self {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (M : ℝ) :
    auxiliaryHalfPlaneFamily H i M i =
      { angle := (H i).angle, height := M, upper := false, strict := false } := by
  simp [auxiliaryHalfPlaneFamily]

lemma auxiliaryHalfPlaneFamily_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i j : Fin n) (M : ℝ) (hji : j ≠ i) :
    auxiliaryHalfPlaneFamily H i M j = H j := by
  simp [auxiliaryHalfPlaneFamily, Function.update_of_ne hji]

lemma noParallelBoundaryAt_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀) :
    noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i (|(H i).height| + ε₀ + R + 1)) (H i).height := by
  intro j hb
  by_cases hji : j = i
  · subst j
    simp only [auxiliaryHalfPlaneFamily_self, frameNormalCoeff_self]
    have hh : (H i).height < |(H i).height| + ε₀ + R + 1 := by
      linarith [le_abs_self (H i).height]
    simpa only [one_mul] using ne_of_lt hh
  · rw [auxiliaryHalfPlaneFamily_of_ne H i j _ hji] at hb ⊢
    intro heq
    have hline : (H j).boundaryLine = (H i).boundaryLine := by
      exact normalLine_eq_of_frameTangentCoeff_eq_zero hb heq
    exact hji (hLines hline)

lemma eventually_parallel_inequalities_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ j, frameTangentCoeff a (H j).angle = 0 →
      (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
          frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
        ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
          (H j).height ≤ frameNormalCoeff a (H j).angle * h) := by
  suffices ∀ᶠ x in 𝓝 h, ∀ j ∈ (Set.univ : Set (Fin n)),
      frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h) by
    exact this.mono fun x hx j ↦ hx j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hb : frameTangentCoeff a (H j).angle = 0
  · have hne := hh j hb
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hev : ∀ᶠ x in 𝓝 h,
          frameNormalCoeff a (H j).angle * x < (H j).height :=
        (continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const hlt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
    · have hev : ∀ᶠ x in 𝓝 h,
          (H j).height < frameNormalCoeff a (H j).angle * x :=
        continuousAt_const.eventually_lt (continuousAt_const.mul continuousAt_id) hgt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
  · exact Filter.Eventually.of_forall fun _ hb' ↦ (hb hb').elim

lemma eventually_parallelCellFeasible_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h := by
  filter_upwards [eventually_parallel_inequalities_iff a H h hh] with x hx
  intro P
  constructor <;> intro hp j hb
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mp hj
    · exact hiff.2.mp hj
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mpr hj
    · exact hiff.2.mpr hj

lemma exists_parallel_stability_radius {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∃ ε > 0, ∀ x, |x - h| ≤ ε →
      noParallelBoundaryAt a H x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) := by
  have hev : ∀ᶠ x in 𝓝 h,
      (∀ j, frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h)) ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :=
    (eventually_parallel_inequalities_iff a H h hh).and
      (eventually_parallelCellFeasible_iff a H h hh)
  rcases (Metric.mem_nhds_iff.mp hev) with ⟨r, hr, hball⟩
  refine ⟨r / 2, by positivity, ?_⟩
  intro x hx
  have hxr : x ∈ Metric.ball h r := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |x - h| ≤ r / 2 := hx
      _ < r := by linarith
  have hstable := hball hxr
  refine ⟨?_, hstable.2⟩
  intro j hb heq
  have hj := hstable.1 j hb
  apply hh j hb
  apply le_antisymm
  · exact hj.1.mp (by rw [heq])
  · exact hj.2.mp (by rw [heq])

lemma setMembershipPattern_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) (p : Point)
    (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    setMembershipPattern (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    rw [auxiliaryHalfPlaneFamily_self] at hp
    simp [setMembershipPattern, hp]
  · simp [setMembershipPattern, auxiliaryHalfPlaneFamily_of_ne H i j M hji,
      Function.update_of_ne hji]

lemma mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M : ℝ) (p : Point) (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    p ∈ activeBooleanRegion E H i ↔
      ∃ P ∈ activeBooleanPatterns E i,
        p ∈ booleanCell (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) P := by
  classical
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hactive
    unfold IsActiveBooleanPattern at hactive
    let P := setMembershipPattern
      (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p
    have hP : P = Function.update
        (setMembershipPattern (fun j ↦ (H j).carrier) p) i true :=
      setMembershipPattern_auxiliary H i M p hp
    refine ⟨P, ?_, (mem_booleanCell_iff _ _ _).mpr rfl⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsActiveBooleanPattern
    rw [hP]
    simpa only [Function.update_idem] using hactive
  · rintro ⟨P, hP, hcell⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP
    have hpattern := (mem_booleanCell_iff _ P p).mp hcell
    have haux := setMembershipPattern_auxiliary H i M p hp
    unfold IsActiveBooleanPattern at hP ⊢
    rw [hpattern] at haux
    rw [haux] at hP
    simpa only [Function.update_idem] using hP

/-- The slice of the region where the selected Boolean wall is active, truncated to `[-R, R]`. -/
def activeRegionSlice {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ activeBooleanRegion E H i} ∩ Set.Icc (-R) R

lemma frameSlice_perturbSdiff_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε x : ℝ)
    (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (x ∈ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} =
        activeRegionSlice (H i).angle E H i R x) ∧
    (x ∉ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} = ∅) := by
  constructor
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
      inner_framePoint_normalVector, hx, true_and, activeRegionSlice]
    constructor
    · intro hy
      refine ⟨hy, ?_⟩
      have hdiff : framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε := by
        rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
        exact ⟨by simpa using hx, hy⟩
      have hball := hBound δ hδ hdiff.1
      have hynorm := abs_real_inner_le_norm (framePoint (H i).angle x y)
        (tangentVector (H i).angle)
      rw [inner_framePoint_tangentVector, norm_tangentVector_angle, mul_one] at hynorm
      have hpR : ‖framePoint (H i).angle x y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_left] using hball
      exact abs_le.mp (hynorm.trans hpR)
    · exact fun hy ↦ hy.1
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp [hx]

lemma activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    activeRegionSlice (H i).angle E H i R x =
      ⋃ P ∈ activeBooleanPatterns E i,
        booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x := by
  classical
  ext y
  have haux : framePoint (H i).angle x y ∈
      (auxiliaryHalfPlaneFamily H i M i).carrier := by
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hxM]
  rw [activeRegionSlice, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary E H i M _ haux]
  simp only [Set.mem_iUnion, booleanCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨P, hP, hyP⟩, hyR⟩
    exact ⟨P, ⟨hP, hyP, hyR⟩⟩
  · rintro ⟨P, hP, hyP, hyR⟩
    exact ⟨⟨P, hP, hyP⟩, hyR⟩

lemma measure_activeRegionSlice_eq_sum {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x) =
      ∑ P ∈ activeBooleanPatterns E i,
        MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) := by
  rw [activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary E H i M R x hxM]
  apply MeasureTheory.measure_biUnion_finset
  · intro P hP Q hQ hPQ
    change Disjoint
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x)
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) Q R x)
    rw [Set.disjoint_left]
    intro y hyP hyQ
    apply hPQ
    have hcellP := hyP.1
    have hcellQ := hyQ.1
    have hp := (mem_booleanCell_iff _ P _).mp hcellP
    have hq := (mem_booleanCell_iff _ Q _).mp hcellQ
    exact hp.symm.trans hq
  · intro P _
    exact measurableSet_booleanCellSlice _ _ _ _ _

/-- Sum the feasible slice lengths over patterns where the selected wall is active. -/
def activeSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : ℝ :=
  ∑ P ∈ activeBooleanPatterns E i, actualCellSliceLength a H P R x

/-- Sum slice lengths while freezing all parallel-wall feasibility decisions at the reference
height. -/
def frozenActiveSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R h x : ℝ) : ℝ := by
  classical
  exact ∑ P ∈ activeBooleanPatterns E i,
    if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0

lemma continuous_frozenActiveSliceLength {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h : ℝ) :
    Continuous (frozenActiveSliceLength a E H i R h) := by
  classical
  unfold frozenActiveSliceLength
  apply continuous_finsetSum
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · simpa [hp] using continuous_cellSliceLength a H P R
  · simpa [hp] using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))

lemma activeSliceLength_eq_frozen_of_stable {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x : ℝ)
    (hstable : ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :
    activeSliceLength a E H i R x = frozenActiveSliceLength a E H i R h x := by
  classical
  unfold activeSliceLength frozenActiveSliceLength
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · have hpx := (hstable P).mpr hp
    simp [actualCellSliceLength, hp, hpx]
  · have hpx : ¬parallelCellFeasible a H P x := fun hx ↦ hp ((hstable P).mp hx)
    simp [actualCellSliceLength, hp, hpx]

lemma abs_frozenActiveSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x z : ℝ) :
    |frozenActiveSliceLength a E H i R h x -
        frozenActiveSliceLength a E H i R h z| ≤
      ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) * |x - z| := by
  classical
  unfold frozenActiveSliceLength
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ P ∈ activeBooleanPatterns E i,
        ((if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
          if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0)| ≤
        ∑ P ∈ activeBooleanPatterns E i,
          |(if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
            if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _P ∈ activeBooleanPatterns E i,
        (2 * slopeBound a H) * |x - z| := by
      apply Finset.sum_le_sum
      intro P hP
      by_cases hp : parallelCellFeasible a H P h
      · simpa [hp] using abs_cellSliceLength_sub_le a H P R x z
      · simp only [hp, ↓reduceIte, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
          (abs_nonneg _)
    _ = ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) *
        |x - z| := by
      simp
      ring

lemma volume_activeRegionSlice_toReal_eq_activeSliceLength {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M)
    (hx : noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    (MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x)).toReal =
      activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [measure_activeRegionSlice_eq_sum E H i M R x hxM]
  unfold activeSliceLength
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro P hP
    exact volume_booleanCellSlice_toReal_eq_actual _ _ _ _ _ hx
  · intro P hP
    apply ne_of_lt
    calc
      MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) ≤
          MeasureTheory.volume (Set.Icc (-R) R) :=
        MeasureTheory.measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (R - -R) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Area
-/

public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma volume_perturbSdiff_toReal_eq_integral_slice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ) (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (MeasureTheory.volume
      (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        (MeasureTheory.volume
          (activeRegionSlice (H i).angle E H i R x)).toReal := by
  let S := perturbNefHeight E H i δ \ perturbNefHeight E H i ε
  have hS : MeasurableSet S :=
    MeasurableSet.diff (measurableSet_perturbNefHeight E H i δ)
      (measurableSet_perturbNefHeight E H i ε)
  have hSfinite : MeasureTheory.volume S ≠ ⊤ := by
    apply ne_of_lt
    calc
      MeasureTheory.volume S ≤ MeasureTheory.volume (perturbNefHeight E H i δ) :=
        MeasureTheory.measure_mono Set.sdiff_subset
      _ ≤ MeasureTheory.volume (Metric.closedBall (0 : Point) R) :=
        MeasureTheory.measure_mono (hBound δ hδ)
      _ < ⊤ := MeasureTheory.measure_closedBall_lt_top
  rw [show (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume
        {y : ℝ | framePoint (H i).angle x y ∈ S}).toReal by
    exact volume_toReal_eq_integral_frameSlice (H i).angle hS hSfinite]
  rw [← MeasureTheory.integral_indicator
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ heightInterval (H i).strict (H i).height δ ε
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).1 hx]
    simp [hx]
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).2 hx]
    simp [hx]

lemma area_perturb_sub_eq_integral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hxM : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε, x ≤ M)
    (hxregular : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε,
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [area_perturb_sub_eq_volume_sdiff hE H i hSide R ε₀ δ ε hεδ hδ hε hBound,
    volume_perturbSdiff_toReal_eq_integral_slice hE H i hSide R ε₀ δ ε hδ hBound]
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)
  intro x hx
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R x
    (hxM x hx) (hxregular x hx)

lemma area_perturb_sub_eq_intervalIntegral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ)
    (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hregular : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) =
        ∫ x in (H i).height..(H i).height + δ,
          activeSliceLength (H i).angle E
            (auxiliaryHalfPlaneFamily H i M) i R x := by
  intro δ hδ
  have hδε₀ : |δ| ≤ ε₀ := hδ.trans (min_le_left _ _)
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
  by_cases hδ0 : 0 ≤ δ
  · have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M δ 0 hδ0 hδε₀ hzero hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith [le_abs_self δ])
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδ0] at hformula
    simpa using hformula
  · have hδle : δ ≤ 0 := le_of_not_ge hδ0
    have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M 0 δ hδle hzero hδε₀ hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith)
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδle] at hformula
    simp only [add_zero] at hformula
    rw [intervalIntegral.integral_symm] at hformula
    linarith

lemma area_perturb_remainder_le {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hstable : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P x ↔
            parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P
              (H i).height)) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R
            (H i).height * δ| ≤
        (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := by
  intro δ hδ
  let a := (H i).angle
  let h := (H i).height
  let G := frozenActiveSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h
  let L := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have harea := area_perturb_sub_eq_intervalIntegral_activeSliceLength
    hE H i hSide R ε₀ M ρ hε₀ hρ hM hBound (fun x hx ↦ (hstable x hx).1) δ hδ
  have hGh : activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h = G h := by
    apply activeSliceLength_eq_frozen_of_stable
    intro P
    rfl
  have hFG : (∫ x in h..h + δ,
      activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R x) =
      ∫ x in h..h + δ, G x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply activeSliceLength_eq_frozen_of_stable
    apply (hstable x ?_).2
    rw [abs_le]
    rcases Set.mem_uIcc.mp hx with hx | hx <;>
      constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
  rw [show (H i).angle = a by rfl, show (H i).height = h by rfl] at harea ⊢
  rw [hFG] at harea
  rw [hGh]
  have hGint : IntervalIntegrable G MeasureTheory.volume h (h + δ) :=
    (continuous_frozenActiveSliceLength a E
      (auxiliaryHalfPlaneFamily H i M) i R h).intervalIntegrable h (h + δ)
  have hcint : IntervalIntegrable (fun _ : ℝ ↦ G h) MeasureTheory.volume h (h + δ) :=
    continuous_const.intervalIntegrable h (h + δ)
  have hremainder :
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) - G h * δ =
        ∫ x in h..h + δ, (G x - G h) := by
    rw [intervalIntegral.integral_sub hGint hcint,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [← harea]
    ring
  have hL : 0 ≤ L :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  rw [hremainder, ← Real.norm_eq_abs]
  calc
    ‖∫ x in h..h + δ, (G x - G h)‖ ≤ (L * |δ|) * |(h + δ) - h| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs]
      calc
        |G x - G h| ≤ L * |x - h| := by
          exact abs_frozenActiveSliceLength_sub_le a E
            (auxiliaryHalfPlaneFamily H i M) i R h x h
        _ ≤ L * |δ| := by
          apply mul_le_mul_of_nonneg_left _ hL
          rw [abs_le]
          rcases Set.mem_uIoc.mp hx with hx | hx <;>
            constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
    _ = L * δ ^ 2 := by
      rw [show (h + δ) - h = δ by ring]
      calc
        L * |δ| * |δ| = L * |δ| ^ 2 := by ring
        _ = L * δ ^ 2 := by rw [sq_abs]
    _ = (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := rfl

end MovingSofa.Nef

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
# Polygon / Nef / Variation / Boundary
-/

public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma tendsto_sub_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.sub
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma tendsto_add_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma sub_smul_normalVector_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p - t • normalVector H.angle ∈ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_sub_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma add_smul_normalVector_not_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p + t • normalVector H.angle ∉ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_add_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma mem_frontier_booleanSet_of_active {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hactive : IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let qminus : ℕ → Point := fun k ↦
    p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  let qplus : ℕ → Point := fun k ↦
    p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  have hminus_lim : Filter.Tendsto qminus Filter.atTop (𝓝 p) :=
    tendsto_sub_one_div_normalVector p (H i).angle
  have hplus_lim : Filter.Tendsto qplus Filter.atTop (𝓝 p) :=
    tendsto_add_one_div_normalVector p (H i).angle
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hminus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) j = P j :=
    hminus_lim.eventually hlocal
  have hplus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) j = P j :=
    hplus_lim.eventually hlocal
  have hminus_mem : ∀ᶠ k in Filter.atTop,
      qminus k ∈ booleanSet E (fun j ↦ (H j).carrier) := by
    filter_upwards [hminus_local] with k hk
    have hki : qminus k ∈ (H i).carrier :=
      sub_smul_normalVector_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) =
        Function.update P i true := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qminus k)) = true
    rw [hpattern]
    exact hactive.2
  have hplus_mem : ∀ᶠ k in Filter.atTop,
      qplus k ∈ (booleanSet E (fun j ↦ (H j).carrier))ᶜ := by
    filter_upwards [hplus_local] with k hk
    have hki : qplus k ∉ (H i).carrier :=
      add_smul_normalVector_not_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) =
        Function.update P i false := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qplus k)) ≠ true
    rw [hpattern, hactive.1]
    decide
  rw [frontier_eq_closure_inter_closure]
  exact ⟨mem_closure_of_tendsto hminus_lim hminus_mem,
    mem_closure_of_tendsto hplus_lim hplus_mem⟩

lemma not_mem_frontier_booleanSet_of_not_active {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (p : Point)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hinactive : ¬IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∉ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let X := booleanSet E (fun j ↦ (H j).carrier)
  have heq : E (Function.update P i false) = E (Function.update P i true) :=
    (not_isActiveBooleanPattern_iff hE i P).mp hinactive
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hevent : ∀ᶠ q in 𝓝 p,
      (q ∈ X ↔ E (Function.update P i false) = true) := by
    filter_upwards [hlocal] with q hq
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) q =
        Function.update P i
          (setMembershipPattern (fun r ↦ (H r).carrier) q i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update_of_ne hji] using hq j hji
    change (E (setMembershipPattern (fun r ↦ (H r).carrier) q) = true ↔ _)
    rw [hpattern]
    cases hqi : setMembershipPattern (fun r ↦ (H r).carrier) q i
    · rfl
    · simp [heq]
  cases hvalue : E (Function.update P i false)
  · have hcompl : Xᶜ ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior Xᶜ := mem_interior_iff_mem_nhds.mpr hcompl
    have hpcompl : p ∈ Xᶜ := interior_subset hinter
    have hnot : p ∉ frontier Xᶜ :=
      (mem_interior_iff_notMem_frontier hpcompl).mp hinter
    simpa [X] using hnot
  · have hset : X ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior X := mem_interior_iff_mem_nhds.mpr hset
    have hp : p ∈ X := interior_subset hinter
    exact (mem_interior_iff_notMem_frontier hp).mp hinter

lemma mem_frontier_booleanSet_iff_mem_activeBooleanRegion {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) ↔
      p ∈ activeBooleanRegion E H i := by
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hfrontier
    by_contra hinactive
    exact (not_mem_frontier_booleanSet_of_not_active hE H i p hother hinactive)
      hfrontier
  · intro hactive
    exact mem_frontier_booleanSet_of_active E H i hupper p hline hother hactive

/-- The truncated slice of the Boolean set’s frontier along a selected wall boundary. -/
def frontierLineSlice {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R : ℝ) : Set ℝ :=
  {y | framePoint (H i).angle (H i).height y ∈
    frontier (booleanSet E (fun j ↦ (H j).carrier))} ∩ Set.Icc (-R) R

lemma volume_frontierLineSlice_eq_activeRegionSlice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    MeasureTheory.volume (frontierLineSlice E H i R) =
      MeasureTheory.volume (activeRegionSlice (H i).angle E H i R (H i).height) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero := (finite_cellSliceBoundaryExceptions (H i).angle
    (auxiliaryHalfPlaneFamily H i M) (H i).height hno).measure_zero
      MeasureTheory.volume
  have heq : ∀ y,
      y ∉ cellSliceBoundaryExceptions (H i).angle
          (auxiliaryHalfPlaneFamily H i M) (H i).height →
        (y ∈ frontierLineSlice E H i R ↔
          y ∈ activeRegionSlice (H i).angle E H i R (H i).height) := by
    intro y hy
    let p := framePoint (H i).angle (H i).height y
    have hline : p ∈ (H i).boundaryLine := by
      change inner ℝ p (normalVector (H i).angle) = (H i).height
      exact inner_framePoint_normalVector _ _ _
    have hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine := by
      intro j hji hj
      apply hy
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change inner ℝ p (normalVector (H j).angle) = (H j).height at hj
      simpa [p, auxiliaryHalfPlaneFamily_of_ne H i j M hji] using hj
    have hfrontier := mem_frontier_booleanSet_iff_mem_activeBooleanRegion
      hE H i hupper p hline hother
    constructor
    · rintro ⟨hyfrontier, hyR⟩
      exact ⟨hfrontier.mp hyfrontier, hyR⟩
    · rintro ⟨hyactive, hyR⟩
      exact ⟨hfrontier.mpr hyactive, hyR⟩
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mp hy.1)
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mpr hy.1)

lemma lineMap_framePoint (a : Real.Angle) (h y : ℝ) :
    AffineMap.lineMap (framePoint a h 0) (framePoint a h 1) y =
      framePoint a h y := by
  simp only [AffineMap.lineMap_apply_module', framePoint_eq, zero_smul,
    add_zero, one_smul]
  module

lemma dist_framePoint_zero_one (a : Real.Angle) (h : ℝ) :
    dist (framePoint a h 0) (framePoint a h 1) = 1 := by
  rw [dist_eq_norm]
  simp only [framePoint_eq, zero_smul, add_zero, one_smul]
  rw [show h • normalVector a - (h • normalVector a + tangentVector a) =
      -tangentVector a by module]
  simp [norm_tangentVector_angle]

lemma frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine =
      AffineMap.lineMap
        (framePoint (H i).angle (H i).height 0)
        (framePoint (H i).angle (H i).height 1) ''
          frontierLineSlice E H i R := by
  ext p
  constructor
  · rintro ⟨hpfrontier, hpline⟩
    let y := inner ℝ p (tangentVector (H i).angle)
    have hpnormal : inner ℝ p (normalVector (H i).angle) = (H i).height := hpline
    have hparam : framePoint (H i).angle (H i).height y = p := by
      rw [framePoint_eq, ← hpnormal]
      exact inner_normalVector_smul_add_inner_tangentVector_smul p (H i).angle
    have hpball : p ∈ Metric.closedBall (0 : Point) R := by
      have hpclosure : p ∈ closure (booleanSet E (fun j ↦ (H j).carrier)) :=
        frontier_subset_closure hpfrontier
      exact (closure_minimal hBound Metric.isClosed_closedBall) hpclosure
    have hynorm := abs_real_inner_le_norm p (tangentVector (H i).angle)
    rw [norm_tangentVector_angle, mul_one] at hynorm
    have hpnorm : ‖p‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hpball
    have hyR : y ∈ Set.Icc (-R) R := abs_le.mp (hynorm.trans hpnorm)
    refine ⟨y, ⟨?_, ?_⟩⟩
    · exact ⟨by simpa [frontierLineSlice, hparam] using hpfrontier, hyR⟩
    · rw [lineMap_framePoint, hparam]
  · rintro ⟨y, hy, rfl⟩
    rw [lineMap_framePoint]
    refine ⟨hy.1, ?_⟩
    change inner ℝ (framePoint (H i).angle (H i).height y)
      (normalVector (H i).angle) = (H i).height
    exact inner_framePoint_normalVector _ _ _

lemma hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine) =
      MeasureTheory.volume (frontierLineSlice E H i R) := by
  rw [frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice
    E H i R hBound, MeasureTheory.hausdorffMeasure_lineMap_image,
    MeasureTheory.hausdorffMeasure_real]
  have hdist := dist_framePoint_zero_one (H i).angle (H i).height
  have hnndist : nndist
      (framePoint (H i).angle (H i).height 0)
      (framePoint (H i).angle (H i).height 1) = 1 := by
    apply NNReal.eq
    simpa using hdist
  rw [hnndist, one_smul]

lemma hausdorffMeasure_frontier_toReal_eq_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hM : (H i).height ≤ M)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    (MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩
        (H i).boundaryLine)).toReal =
      activeSliceLength (H i).angle E
        (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
  rw [hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice E H i R hBound,
    volume_frontierLineSlice_eq_activeRegionSlice hE H i hupper M R hno]
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R
    (H i).height hM hno

end MovingSofa.Nef

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
# Polygon / Nef / Variation
-/

public section

noncomputable section

namespace MovingSofa

open Filter Topology
open Nef

theorem simpleNefPolygon_area_variation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = false) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  let M := |(H i).height| + ε₀ + R + 1
  have hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height := by
    exact noParallelBoundaryAt_auxiliary H i hLines R ε₀ hR hε₀
  rcases exists_parallel_stability_radius (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height hno with
    ⟨ρ, hρ, hstable⟩
  let C := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))
  let ε := min ε₀ ρ
  refine ⟨C, ε, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  · exact lt_min hε₀ hρ
  · exact min_le_left _ _
  · intro δ hδ
    have hM : (H i).height + ε₀ ≤ M := by
      dsimp [M]
      linarith [le_abs_self (H i).height]
    have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
    have hBoundZero := hBound 0 hzero
    rw [perturbNefHeight_zero] at hBoundZero
    have hcoefficient :
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal =
        activeSliceLength (H i).angle E
          (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
      rw [perturbNefHeight_zero]
      exact hausdorffMeasure_frontier_toReal_eq_activeSliceLength
        hE H i hSide M R (le_trans (le_add_of_nonneg_right hε₀.le) hM)
          hBoundZero hno
    have hremainder := area_perturb_remainder_le hE H i hSide R ε₀ M ρ
      hε₀ hρ hM hBound hstable δ hδ
    rw [hcoefficient]
    exact hremainder

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
# Polygon / Nef / Signed Variation
-/

public section

noncomputable section
namespace MovingSofa

private def PlanarHalfPlaneData.reverseOrientation
    (H : PlanarHalfPlaneData) : PlanarHalfPlaneData :=
  ⟨H.angle + ((Real.pi : ℝ) : Real.Angle), -H.height, !H.upper, H.strict⟩

private theorem PlanarHalfPlaneData.carrier_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.carrier = H.carrier := by
  ext p
  simp only [reverseOrientation, carrier, normalHalfPlane, Set.mem_ofPred_eq,
    normalVector_add_pi_angle, inner_neg_right]
  cases H.upper <;> cases H.strict <;> simp

private theorem PlanarHalfPlaneData.boundaryLine_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.boundaryLine = H.boundaryLine := by
  ext p
  simp [reverseOrientation, boundaryLine, normalLine, normalVector_add_pi_angle]

private theorem PlanarHalfPlaneData.carrier_reverseOrientation_add_height
    (H : PlanarHalfPlaneData) (δ : ℝ) :
    ({H.reverseOrientation with height := H.reverseOrientation.height + δ}).carrier =
      ({H with height := H.height + -δ}).carrier := by
  have heq : {H.reverseOrientation with height := H.reverseOrientation.height + δ} =
      ({H with height := H.height + -δ}).reverseOrientation := by
    cases H
    simp [reverseOrientation, add_comm]
  rw [heq, carrier_reverseOrientation]

private theorem perturbNefHeight_reverseOrientation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E (fun j ↦ (H j).reverseOrientation) i δ =
      perturbNefHeight E H i (-δ) := by
  unfold perturbNefHeight
  congr 1
  funext j
  split_ifs
  · exact PlanarHalfPlaneData.carrier_reverseOrientation_add_height _ _
  · exact PlanarHalfPlaneData.carrier_reverseOrientation _

/-- Quadratic area variation when the moved half-plane is a lower constraint. -/
theorem simpleNefPolygon_area_variation_lower {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = true) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) +
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  have hLines' : Function.Injective (fun j ↦ (H j).reverseOrientation.boundaryLine) := by
    simpa only [PlanarHalfPlaneData.boundaryLine_reverseOrientation] using hLines
  have hSide' : (H i).reverseOrientation.upper = false := by
    simp [PlanarHalfPlaneData.reverseOrientation, hSide]
  obtain ⟨C, ε, hC, hε, hε₀', h⟩ := simpleNefPolygon_area_variation E
    (fun j ↦ (H j).reverseOrientation) i hE hLines' hSide' R ε₀ hR hε₀ (by
      intro δ hδ
      rw [perturbNefHeight_reverseOrientation]
      exact hBound (-δ) (by simpa only [abs_neg] using hδ))
  refine ⟨C, ε, hC, hε, hε₀', fun δ hδ ↦ ?_⟩
  have hb := h (-δ) (by simpa only [abs_neg] using hδ)
  simpa only [perturbNefHeight_reverseOrientation, neg_neg, neg_zero,
    PlanarHalfPlaneData.boundaryLine_reverseOrientation, mul_neg, sub_neg_eq_add,
    neg_sq] using hb
/-- Signed quadratic area variation for either orientation of a simple Nef wall. -/
theorem simpleNefPolygon_area_variation_signed {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  cases hs : (H i).upper
  · simpa only [hs, Bool.false_eq_true, ite_false, one_mul] using
      simpleNefPolygon_area_variation E H i hE hLines hs R ε₀ hR hε₀ hBound
  · simpa only [hs, ite_true, neg_one_mul, neg_mul, one_mul, sub_neg_eq_add] using
      simpleNefPolygon_area_variation_lower E H i hE hLines hs R ε₀ hR hε₀ hBound

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
# Polygon / Height / Wall Variation
-/

public section

noncomputable section
namespace MovingSofa

private theorem endpoint_wall_changes_disjoint (a : Real.Angle) (h ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (p ∈ normalHalfPlane a (h + ε) false false ↔
      p ∈ normalHalfPlane a h false false) ∨
    (p ∈ normalHalfPlane a (h - 1 + ε) true false ↔
      p ∈ normalHalfPlane a (h - 1) true false) := by
  change (inner ℝ p (normalVector a) ≤ h + ε ↔ inner ℝ p (normalVector a) ≤ h) ∨
    (h - 1 + ε ≤ inner ℝ p (normalVector a) ↔ h - 1 ≤ inner ℝ p (normalVector a))
  by_cases hp : inner ℝ p (normalVector a) ≤ h
  · left
    constructor <;> intro _ <;> linarith
  · right
    constructor <;> intro _ <;> linarith

private theorem area_add_of_indicator_add_eq (A B C D : Set Point)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAfin : MeasureTheory.volume A ≠ ⊤) (hBfin : MeasureTheory.volume B ≠ ⊤)
    (hCfin : MeasureTheory.volume C ≠ ⊤) (hDfin : MeasureTheory.volume D ≠ ⊤)
    (h : ∀ p, A.indicator (fun _ ↦ (1 : ℝ)) p + B.indicator (fun _ ↦ (1 : ℝ)) p =
      C.indicator (fun _ ↦ (1 : ℝ)) p + D.indicator (fun _ ↦ (1 : ℝ)) p) :
    ClassicalResults.area A + ClassicalResults.area B =
      ClassicalResults.area C + ClassicalResults.area D := by
  have hint (S : Set Point) (hm : MeasurableSet S) (hf : MeasureTheory.volume S ≠ ⊤) :
      MeasureTheory.Integrable (S.indicator (fun _ ↦ (1 : ℝ))) :=
    (MeasureTheory.integrableOn_const hf).integrable_indicator hm
  have heq := congrArg (fun f : Point → ℝ ↦ ∫ p, f p) (funext h)
  rw [MeasureTheory.integral_add (hint A hA hAfin) (hint B hB hBfin),
    MeasureTheory.integral_add (hint C hC hCfin) (hint D hD hDfin)] at heq
  have harea (S : Set Point) (hm : MeasurableSet S) :
      (∫ p, S.indicator (fun _ ↦ (1 : ℝ)) p) = ClassicalResults.area S :=
    MeasureTheory.integral_indicator_one hm
  simpa only [harea A hA, harea B hB, harea C hC, harea D hD] using heq
private def BooleanFunction.all (n : ℕ) : BooleanFunction n :=
  fun P ↦ decide (∀ i, P i = true)

private theorem BooleanFunction.all_monotone (n : ℕ) :
    IsMonotoneBooleanFunction (BooleanFunction.all n) := by
  intro P Q hPQ hP
  simp only [BooleanFunction.all, decide_eq_true_eq] at hP ⊢
  exact fun i ↦ hPQ i (hP i)

private theorem booleanSet_all {n : ℕ} (H : Fin n → Set Point) :
    booleanSet (BooleanFunction.all n) H = ⋂ i, H i := by
  classical
  ext p
  simp [booleanSet, BooleanFunction.all]

private theorem independentWallCap_eq_booleanSet {Θ : AngleSet}
    (h upper lower : PolygonHeightSpace Θ) {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (hH : Set.range H = polygonCapWalls h)
    (F : PlanarHalfPlaneData → Set Point)
    (hupper : ∀ t ∈ angleDomain Θ,
      F ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      F ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
    independentWallCap upper lower =
      booleanSet (BooleanFunction.all n) (fun i ↦ F (H i)) := by
  rw [booleanSet_all]
  ext p
  have hrange : (∀ i, p ∈ F (H i)) ↔ ∀ W ∈ polygonCapWalls h, p ∈ F W := by
    rw [← hH]
    simp
  simp only [Set.mem_iInter]
  rw [hrange]
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hend, hint⟩ W hW
    rcases hW with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [hupper t ht]
      rcases ht with ht | ht
      · exact hint t ht
      · exact (hend t ht).1
    · rw [hlower t ht]
      exact (hend t ht).2
  · intro hall
    constructor
    · intro t ht
      constructor
      · rw [← hupper t (Or.inr ht)]
        exact hall _ (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · rw [← hlower t ht]
        exact hall _ (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      rw [← hupper t (Or.inl ht)]
      exact hall _ (Or.inl ⟨t, Or.inl ht, rfl⟩)

private def BooleanFunction.niche (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) : BooleanFunction n := by
  classical
  exact fun P ↦ decide ((∀ t, P (endpoint t) = true) ∧
    ∃ t, P (left t) = true ∧ P (right t) = true)

private theorem BooleanFunction.niche_monotone (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) :
    IsMonotoneBooleanFunction (BooleanFunction.niche Θ endpoint left right) := by
  classical
  intro P Q hPQ hP
  simp only [BooleanFunction.niche, decide_eq_true_eq] at hP ⊢
  obtain ⟨he, t, hl, hr⟩ := hP
  exact ⟨fun s ↦ hPQ _ (he s), t, hPQ _ hl, hPQ _ hr⟩

private theorem independentWallNiche_eq_booleanSet {Θ : AngleSet}
    (lower : PolygonHeightSpace Θ) {n : ℕ} (H : Fin n → Set Point)
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) true false)
    (hl : ∀ t, H (left t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) false true)
    (hr : ∀ t, H (right t) =
      normalHalfPlane ((t.val + Real.pi / 2 : ℝ) : Real.Angle)
        (polygonHeightValue lower (t.val + Real.pi / 2)) false true) :
    independentWallNiche lower =
      booleanSet (BooleanFunction.niche Θ endpoint left right) H := by
  classical
  ext p
  simp only [independentWallNiche, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_iUnion, booleanSet, Set.mem_ofPred_eq, BooleanFunction.niche,
    decide_eq_true_eq, he, hl, hr]
  constructor
  · rintro ⟨he, t, ht, hl, hr⟩
    exact ⟨fun s ↦ he s.val s.property, ⟨t, ht⟩, hl, hr⟩
  · rintro ⟨he, t, hl, hr⟩
    exact ⟨fun s hs ↦ he ⟨s, hs⟩, t.val, t.property, hl, hr⟩

private theorem exists_polygonNiche_wall_indices {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h) :
    ∃ (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
      (left right : {t : ℝ // t ∈ Θ.directions} → Fin n),
      (∀ t, H (endpoint t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩) ∧
      (∀ t, H (left t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩) ∧
      (∀ t, H (right t) =
        ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
          polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩) := by
  classical
  have hpre (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
      ∃ i, H i = W := by
    change W ∈ Set.range H
    rwa [hH]
  have he (t : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩ :=
    hpre _ (Or.inr ⟨t.val, t.property, rfl⟩)
  have hl (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val, Or.inl t.property, rfl⟩)
  have hr (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val + Real.pi / 2, Or.inr ⟨t.val, t.property, rfl⟩, rfl⟩)
  choose endpoint he using he
  choose left hl using hl
  choose right hr using hr
  exact ⟨endpoint, left, right, he, hl, hr⟩

private def PlanarHalfPlaneData.moveWall (W : PlanarHalfPlaneData) (δ : ℝ)
    (V : PlanarHalfPlaneData) : PlanarHalfPlaneData := by
  classical
  exact if V = W then {V with height := V.height + δ} else V

private theorem perturbNefHeight_eq_moveWall {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (hH : Function.Injective H) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ =
      booleanSet E (fun j ↦ ((H i).moveWall δ (H j)).carrier) := by
  classical
  unfold perturbNefHeight
  congr 1
  funext j
  simp only [PlanarHalfPlaneData.moveWall, hH.eq_iff]

/-- Angles in a polygon angle domain have distinct classes modulo a full turn. -/
theorem angleDomain_coe_injective (Θ : AngleSet) :
    Function.Injective (fun t : angleDomain Θ ↦ (t.val : Real.Angle)) := by
  intro s t hst
  apply Subtype.ext
  have hs := angleDomain_subset_Ioo Θ s.property
  have ht := angleDomain_subset_Ioo Θ t.property
  exact ((normalLine_eq_iff_of_mem_Ioo (c := 0) (d := 0) hs ht).mp
    (congrArg (fun a ↦ normalLine a 0) hst)).1

private theorem polygonHeightValue_update {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (δ : ℝ) (s : ℝ) (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (Function.update h t (h t + δ)) s =
      polygonHeightValue h s + if s = t.val then δ else 0 := by
  classical
  by_cases hst : s = t.val
  · subst s
    simp [polygonHeightValue, Function.update]
  · have hne : (⟨s, hs⟩ : angleDomain Θ) ≠ t := by
      intro heq
      exact hst (congrArg Subtype.val heq)
    simp [polygonHeightValue, Function.update, hs, hst, hne]

private theorem perturbNefHeight_cap_upper {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq, polygonHeightValue_update h t δ s hs]
    split_ifs with hst
    · rfl
    · simp only [add_zero]
      rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem perturbNefHeight_cap_lower {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hsD⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq,
      polygonHeightValue_update (fun s ↦ h s - 1) t δ s hsD]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem polygonCap_singleWall_uniform_bounds {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
        Set.range H = polygonCapWalls h → Function.Injective H →
        ∀ (i : Fin n) (t : angleDomain Θ),
          (H i = ⟨(t.val : Real.Angle), h t, false, false⟩ ∨
            H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) →
          ∀ δ : ℝ, |δ| ≤ ε₀ →
            perturbNefHeight (BooleanFunction.all n) H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨R, ε₀, hR, hε₀, ?_⟩
  intro n H hH hHinj i t hi δ hδ
  have hupdate (f : PolygonHeightSpace Θ) :
      ∀ s, |Function.update f t (f t + δ) s - f s| ≤ ε₀ := by
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]
  rcases hi with hi | hi
  · rw [perturbNefHeight_cap_upper h H hH hHinj i t hi δ]
    exact (hb _ _ (hupdate h) (by intro s; simpa using le_of_lt hε₀)).1
  · rw [perturbNefHeight_cap_lower h H hH hHinj i t hi δ]
    exact (hb _ _ (by intro s; simpa using le_of_lt hε₀)
      (hupdate (fun s ↦ h s - 1))).1

private theorem perturbNefHeight_niche {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hangle : Function.Injective (fun j ↦ (H j).angle))
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩)
    (hl : ∀ t, H (left t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩)
    (hr : ∀ t, H (right t) =
      ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩)
    (i : Fin n) (t : angleDomain Θ) (hi : (H i).angle = (t.val : Real.Angle)) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.niche Θ endpoint left right) H i δ =
      independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  have hwall (j : Fin n) (s : ℝ) (hs : s ∈ angleDomain Θ) (upper strict : Bool)
      (hj : H j = ⟨(s : Real.Angle), polygonHeightValue h s - 1, upper, strict⟩) :
      (if j = i then {H j with height := (H j).height + δ} else H j).carrier =
        normalHalfPlane (s : Real.Angle)
          (polygonHeightValue (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) s)
          upper strict := by
    have hji : j = i ↔ s = t.val := by
      constructor
      · intro hji
        have ha : (s : Real.Angle) = (t.val : Real.Angle) := by
          rw [← hi, ← hji, hj]
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        apply hangle
        simp only [hj, hi, hst]
    simp only [hji, hj, polygonHeightValue_update (fun s ↦ h s - 1) t δ s hs]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hs]
  unfold perturbNefHeight
  symm
  apply independentWallNiche_eq_booleanSet _ _ endpoint left right
  · intro s
    exact hwall _ s.val (Or.inr s.property) true false (he s)
  · intro s
    exact hwall _ s.val (Or.inl (Or.inl s.property)) false true (hl s)
  · intro s
    exact hwall _ (s.val + Real.pi / 2)
      (Or.inl (Or.inr ⟨s.val, s.property, rfl⟩)) false true (hr s)

private theorem exists_angle_of_mem_polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
    ∃ s : angleDomain Θ, W.angle = (s.val : Real.Angle) ∧ W.height = h s - 1 := by
  rcases hW with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨⟨s, Or.inl hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inl hs]
  · refine ⟨⟨s, Or.inr hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inr hs]

private theorem polygonNicheWalls_angle_injective {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    Function.Injective (fun j ↦ (H j).angle) := by
  intro i j hij
  obtain ⟨s, hs, hsheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  obtain ⟨t, ht, htheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H j) (hH ▸ Set.mem_range_self j)
  have hst : s = t := angleDomain_coe_injective Θ (hs.symm.trans (hij.trans ht))
  apply hLines
  simp only [PlanarHalfPlaneData.boundaryLine, hij, hsheight, htheight, hst]

private theorem exists_polygonNiche_perturbation_formula {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      ∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  obtain ⟨endpoint, left, right, he, hl, hr⟩ := exists_polygonNiche_wall_indices h H hH
  refine ⟨BooleanFunction.niche Θ endpoint left right,
    BooleanFunction.niche_monotone Θ endpoint left right, ?_⟩
  intro i
  obtain ⟨t, ht, _⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  refine ⟨t, ht, fun δ ↦ ?_⟩
  exact perturbNefHeight_niche h H (polygonNicheWalls_angle_injective h H hH hLines)
    endpoint left right he hl hr i t ht δ

/-- The niche with every lower wall shifted by one is the height-defined niche. -/
theorem independentWallNiche_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallNiche (fun s ↦ h s - 1) = polygonHeightNiche h := by
  have hv (s : ℝ) (hs : s ∈ angleDomain Θ) :
      polygonHeightValue (fun s ↦ h s - 1) s = polygonHeightValue h s - 1 := by
    simp [polygonHeightValue, hs]
  unfold independentWallNiche polygonHeightNiche polygonHeightFan
  congr 1
  · apply Set.iInter_congr
    intro s
    apply Set.iInter_congr
    intro hs
    rw [hv s (Or.inr hs)]
  · apply Set.iUnion_congr
    intro s
    apply Set.iUnion_congr
    intro hs
    rw [hv s (Or.inl (Or.inl hs)),
      hv (s + Real.pi / 2) (Or.inl (Or.inr ⟨s, hs, rfl⟩))]

private theorem exists_polygonNiche_stable_presentation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ (E : BooleanFunction n) (R ε₀ : ℝ),
      IsMonotoneBooleanFunction E ∧ 0 < R ∧ 0 < ε₀ ∧
      polygonHeightNiche h = booleanSet E (fun j ↦ (H j).carrier) ∧
      (∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) ∧
      ∀ i δ, |δ| ≤ ε₀ → perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨E, hE, htransport⟩ := exists_polygonNiche_perturbation_formula h H hH hLines
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨E, R, ε₀, hE, hR, hε₀, ?_, htransport, ?_⟩
  · have hW : (⟨(Θ.angle : Real.Angle), polygonHeightValue h Θ.angle - 1,
        true, false⟩ : PlanarHalfPlaneData) ∈ Set.range H := by
      rw [hH]
      exact Or.inr ⟨Θ.angle, by simp, rfl⟩
    obtain ⟨i, _⟩ := hW
    obtain ⟨t, _, ht⟩ := htransport i
    have hz := ht 0
    simpa [perturbNefHeight, independentWallNiche_sub_one] using hz.symm
  · intro i δ hδ
    obtain ⟨t, _, ht⟩ := htransport i
    rw [ht δ]
    apply (hb h _ (by intro s; simpa using le_of_lt hε₀) ?_).2
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for any wall in a polygon-height niche presentation. -/
theorem polygonNiche_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) (i : Fin n) :
    ∃ (t : angleDomain Θ) (C η : ℝ), (H i).angle = (t.val : Real.Angle) ∧
      0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
        |ClassicalResults.area
            (independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
          ClassicalResults.area (polygonHeightNiche h) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (polygonHeightNiche h) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  classical
  obtain ⟨E, R, ε₀, hE, hR, hε₀, hbase, htransport, hbound⟩ :=
    exists_polygonNiche_stable_presentation h H hH hLines
  obtain ⟨t, ht, hmove⟩ := htransport i
  have hz : perturbNefHeight E H i 0 = polygonHeightNiche h := by
    simpa [perturbNefHeight] using hbase.symm
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_signed
    E H i hE hLines R ε₀ hR hε₀ (hbound i)
  refine ⟨t, C, η, ht, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- The cap with every lower endpoint wall shifted by one is the height-defined cap. -/
theorem independentWallCap_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun s ↦ h s - 1) = polygonHeightCap h := by
  unfold independentWallCap polygonHeightCap polygonHeightParallelogram
  congr 1
  apply Set.iInter_congr
  intro s
  apply Set.iInter_congr
  intro hs
  have hsD : s ∈ angleDomain Θ := Or.inr hs
  simp [polygonHeightValue, hsD]

/-- Quadratic area variation for one upper wall of a polygon-height cap. -/
theorem polygonCap_upper_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1)) -
        ClassicalResults.area (polygonHeightCap h) -
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_upper h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    rw [hmove 0]
    have hu : Function.update h t (h t + 0) = h := by
      funext s
      simp only [Function.update, add_zero, eq_rec_constant, dite_eq_ite, ite_eq_right_iff]
      rintro rfl
      rfl
    rw [hu, independentWallCap_sub_one]
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inl hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for one lower endpoint wall of a polygon-height cap. -/
theorem polygonCap_lower_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
        ClassicalResults.area (polygonHeightCap h) +
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_lower h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    simpa [independentWallCap_sub_one] using hmove 0
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_lower
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inr hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

private theorem mem_independentWallCap_congr {Θ : AngleSet}
    (upper upper' lower lower' : PolygonHeightSpace Θ) (p : Point)
    (hu : ∀ s : angleDomain Θ,
      (inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper s ↔
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper' s))
    (hl : ∀ s : angleDomain Θ,
      (lower s ≤ inner ℝ p (normalVector (s.val : Real.Angle)) ↔
        lower' s ≤ inner ℝ p (normalVector (s.val : Real.Angle)))) :
    p ∈ independentWallCap upper lower ↔ p ∈ independentWallCap upper' lower' := by
  have hu' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper s) false false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper' s) false false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hu ⟨s, hs⟩
  have hl' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower s) true false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower' s) true false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hl ⟨s, hs⟩
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mp (he s hs).1,
      (hl' s (Or.inr hs)).mp (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mp (hi s hs)⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mpr (he s hs).1,
      (hl' s (Or.inr hs)).mpr (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mpr (hi s hs)⟩

private theorem independentWallCap_indicator_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p =
      (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p := by
  classical
  have hsplit := endpoint_wall_changes_disjoint (t.val : Real.Angle) (h t) ε hε hε' p
  have hI (A B : Set Point) (hab : p ∈ A ↔ p ∈ B) :
      A.indicator (fun _ ↦ (1 : ℝ)) p = B.indicator (fun _ ↦ (1 : ℝ)) p := by
    by_cases ha : p ∈ A
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hab.mp ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (fun hb ↦ ha (hab.mpr hb))]
  change (_ ↔ _) ∨ (_ ↔ _) at hsplit
  rcases hsplit with hu | hl
  · have hu' (s : angleDomain Θ) :
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ Function.update h t (h t + ε) s ↔
          inner ℝ p (normalVector (s.val : Real.Angle)) ≤ h s := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hu
      · simp [Function.update, hst]
    have heq (lower : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr (Function.update h t (h t + ε)) h lower lower p
        hu' (fun _ ↦ Iff.rfl)
    exact (congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)))) rfl).trans
      ((add_comm _ _).trans (congrArg₂ (fun a b : ℝ ↦ a + b)
        (hI _ _ (heq (fun s ↦ h s - 1))).symm rfl))
  · have hl' (s : angleDomain Θ) :
        Function.update (fun s ↦ h s - 1) t (h t - 1 + ε) s ≤
            inner ℝ p (normalVector (s.val : Real.Angle)) ↔
          h s - 1 ≤ inner ℝ p (normalVector (s.val : Real.Angle)) := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hl
      · simp [Function.update, hst]
    have heq (upper : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr upper upper
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) (fun s ↦ h s - 1) p
        (fun _ ↦ Iff.rfl) hl'
    exact congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update h t (h t + ε)))) (hI _ _ (heq h)).symm

end MovingSofa

namespace MovingSofa

private theorem isClosed_independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) :
    IsClosed (independentWallCap upper lower) := by
  have hu (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c false false) :=
    isClosed_le (by fun_prop) continuous_const
  have hl (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c true false) :=
    isClosed_le continuous_const (by fun_prop)
  unfold independentWallCap
  exact (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ (hu _ _).inter (hl _ _)).inter
    (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ hu _ _)

/-- Simultaneous endpoint-wall variation is the sum of the two independent variations. -/
theorem independentWallCap_area_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε R : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hbound : ∀ (upper lower : PolygonHeightSpace Θ),
      (upper = h ∨ upper = Function.update h t (h t + ε)) →
      (lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) →
      independentWallCap upper lower ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) +
      ClassicalResults.area (independentWallCap h (fun s ↦ h s - 1)) =
      ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)) +
      ClassicalResults.area (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) := by
  have hf (upper lower : PolygonHeightSpace Θ)
      (hu : upper = h ∨ upper = Function.update h t (h t + ε))
      (hl : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) :
      MeasureTheory.volume (independentWallCap upper lower) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (hbound upper lower hu hl))
      MeasureTheory.measure_closedBall_lt_top)
  apply area_add_of_indicator_add_eq
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact hf _ _ (Or.inr rfl) (Or.inr rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inr rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inr rfl)
  · exact independentWallCap_indicator_update_add h t ε hε hε'

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
# Polygon / Right Angle Grid
-/

public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Directions in the right-angle grid are positive integer multiples of its step size. -/
theorem mem_rightAngleSet_directions_iff (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    t ∈ (rightAngleSet n hn).directions ↔
      ∃ i : ℕ, i ∈ Finset.Ioo 0 n ∧ t = i * polygonStepSize n := by
  simp only [rightAngleSet, uniformAngleSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring

/-- No grid direction lies strictly between the predecessor of a grid point and the point. -/
theorem rightAngleSet_direction_le_pred_or_ge (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t - polygonStepSize n ∨ t ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  by_cases hji : j < i
  · left
    have hnat : j + 1 ≤ i := hji
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hnat
    nlinarith
  · right
    have hij : i ≤ j := Nat.le_of_not_gt hji
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ.le

/-- No grid direction lies strictly between a grid point and its successor. -/
theorem rightAngleSet_direction_le_or_succ_le (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t ∨ t + polygonStepSize n ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hδ : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  by_cases hji : j ≤ i
  · left
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hji) hδ.le
  · right
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hji))
    nlinarith

/-- Every interior grid direction stays at least one step from both endpoints. -/
theorem rightAngleSet_direction_bounds (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    polygonStepSize n ≤ t ∧ t ≤ Real.pi / 2 - polygonStepSize n := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi0
  have hin1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hi1 hδ.le
  · have hstep : (n : ℝ) * polygonStepSize n = Real.pi / 2 := by
      simp only [polygonStepSize]
      field_simp
    nlinarith

/-- The two lower normals of a right-angle polygon cap coincide at `3π/2`. -/
theorem rightAngle_polygon_normals_eq (n : ℕ) (hn : 2 ≤ n) :
    ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain (rightAngleSet n hn)) ∪
        capLowerNormals (rightAngleSet n hn).angle =
      (fun r : ℝ ↦ (r : Real.Angle)) ''
        (angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) := by
  ext a
  simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ha)
    · exact ⟨r, Or.inl hr, rfl⟩
    · simp only [capLowerNormals, rightAngleSet, uniformAngleSet,
        Set.mem_insert_iff] at ha
      rcases ha with ha | ha
      · subst a
        refine ⟨3 * Real.pi / 2, Or.inr rfl, ?_⟩
        congr 1
        ring
      · subst a
        exact ⟨3 * Real.pi / 2, Or.inr rfl, rfl⟩
  · rintro ⟨r, hr | rfl, rfl⟩
    · exact Or.inl ⟨r, hr, rfl⟩
    · right
      simp [capLowerNormals, rightAngleSet, uniformAngleSet]

/-- The predecessor of a right-angle grid direction is zero or again a grid direction. -/
theorem rightAngleSet_sub_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t - polygonStepSize n = 0 ∨
      t - polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  by_cases hi1 : i = 1
  · left
    subst hi1
    push_cast
    ring
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i - 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [Nat.cast_sub (by omega)]
      push_cast
      ring

/-- The successor of a right-angle grid direction is the terminal angle or a grid direction. -/
theorem rightAngleSet_add_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t + polygonStepSize n = Real.pi / 2 ∨
      t + polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hi1 : i + 1 = n
  · left
    have : ((i : ℝ) + 1) = (n : ℝ) := by exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) hi1
    simp only [polygonStepSize]
    field_simp
    linarith [this]
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i + 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · push_cast
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
# Polygon / Translation
-/

public section

noncomputable section

namespace MovingSofa

theorem polygonCapTranslate_iff (Θ : AngleSet) (K : ConvexBody Point) :
    (∃ K' : PolygonCapTranslateSpace Θ, K'.val = (K : Set Point)) ↔
      (supportValue K (Θ.angle : Real.Angle) +
        supportValue K ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1) ∧
      (supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) +
        supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1) ∧
      ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
        (∀ c ∈ constraints, c.1 ∈
          ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) ∧
        (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  classical
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hNfinite : N.Finite := by
    apply Set.Finite.union
    · apply Set.Finite.image
      simp only [angleDomain]
      exact ((Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
          ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
    · simp [capLowerNormals]
  constructor
  · rintro ⟨K', hK'eq⟩
    obtain ⟨P, q, hPq⟩ := K'.property
    have hKeq : (K : Set Point) = (fun p ↦ p + q) '' (P.val.val : Set Point) := by
      rw [← hK'eq, hPq]
    have hsupp (t : Real.Angle) :
        supportValue K t = supportValue P.val.val t + inner ℝ q (normalVector t) := by
      rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
      exact supportValue_image_add P.val.val q t
    have hopen := P.val.property
    refine ⟨?_, ?_, ?_⟩
    · rw [hsupp, hsupp, hopen.2.2.1, hopen.2.2.2.2.1, normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      rw [hsupp]
      rw [← hang]
      rw [hsupp, hopen.2.2.2.1]
      rw [show supportValue P.val.val (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) = 0 by
        rw [hang]; exact hopen.2.2.2.2.2.1]
      rw [normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hrepr : HasHalfPlaneRepresentation K N := by
        rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
        exact P.property.translate q
      exact hrepr.finite_constraints hNfinite
  · rintro ⟨hwidthω, hwidthT, C, hCfinite, hCN, hKC⟩
    let v : Point := if h : Θ.angle = Real.pi / 2 then
      !₂[0, 1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    else
      !₂[(1 - supportValue K (Θ.angle : Real.Angle) -
          (1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin Θ.angle) /
          Real.cos Θ.angle,
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    have hvT : inner ℝ v (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
    have hvω : inner ℝ v (normalVector (Θ.angle : Real.Angle)) =
        1 - supportValue K (Θ.angle : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simpa [h] using hvT
      · have hlt : Θ.angle < Real.pi / 2 := lt_of_le_of_ne Θ.angle_le h
        have hcos : Real.cos Θ.angle ≠ 0 := (Real.cos_pos_of_mem_Ioo
          ⟨lt_trans (neg_neg_of_pos (by positivity : 0 < Real.pi / 2)) Θ.angle_pos,
            hlt⟩).ne'
        simp [v, h, normalVector, frame, PiLp.inner_apply]
        field_simp [hcos]
        ring
    let L := ConvexBody.translate K v
    have hsupp (t : Real.Angle) :
        supportValue L t = supportValue K t + inner ℝ v (normalVector t) :=
      supportValue_image_add K v t
    have htopω : supportValue L (Θ.angle : Real.Angle) = 1 := by
      rw [hsupp, hvω]
      ring
    have htopT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
      rw [hsupp, hvT]
      ring
    have hbotω : supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 0 := by
      rw [hsupp, normalVector_add_pi, inner_neg_right]
      rw [hvω]
      linarith
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    have hbotT : supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
      rw [← hang, hsupp, normalVector_add_pi, inner_neg_right]
      rw [hang, hvT]
      linarith
    have hKrepr : HasHalfPlaneRepresentation K N := ⟨C, hCN, hKC⟩
    have hLrepr : HasHalfPlaneRepresentation L N := hKrepr.translate v
    have hangleDomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
      rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
      · left
        exact ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · right
        constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
      · rcases ht with (rfl | rfl)
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
    have hNsubset : N ⊆
        ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle := by
      rintro t (ht | ht)
      · obtain ⟨s, hs, rfl⟩ := ht
        exact Or.inl ⟨s, hangleDomain hs, rfl⟩
      · exact Or.inr ht
    have hLcapRepr : HasHalfPlaneRepresentation L
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle) := by
      obtain ⟨D, hDN, hLD⟩ := hLrepr
      exact ⟨D, fun c hc ↦ hNsubset (hDN c hc), hLD⟩
    have hLcap : IsCap Θ.angle L :=
      ⟨Θ.angle_pos, Θ.angle_le, htopω, htopT, hbotω, hbotT, hLcapRepr⟩
    let P : PolygonCapSpace Θ := ⟨⟨L, hLcap⟩, hLrepr⟩
    refine ⟨⟨(K : Set Point), ?_⟩, rfl⟩
    refine ⟨P, -v, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x + v, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy

theorem polygonHeightArea_le_translateArea {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : PolygonCapTranslateSpace Θ) (hK : polygonHeightCap h = K.val) :
    polygonHeightArea h ≤ (polygonTranslateExtensions K).2 := by
  obtain ⟨P, q, hPq⟩ := K.property
  let C := ConvexBody.translate P.val.val q
  have hC : (C : Set Point) = K.val := hPq.symm
  have hBody : polygonHeightCap h = (C : Set Point) := hK.trans hC.symm
  have hw := (polygonCapTranslate_iff Θ C).1 ⟨K, hC.symm⟩
  let g := polygonTranslateHeight K
  have hle : ∀ t, g t ≤ h t := by
    intro t
    change supportValue K.val (t.val : Real.Angle) ≤ h t
    rw [← hC]
    simpa only [polygonHeightValue, dite_eq_left t.property] using
      supportValue_le_polygonHeightValue h C hBody t.property
  have heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue g t = polygonHeightValue h t := by
    intro t ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hg : polygonHeightValue g t = supportValue C (t : Real.Angle) := by
      simp only [g, polygonTranslateHeight, polygonHeightValue, dite_eq_left htD]
      rw [hC]
    rw [hg]
    apply supportValue_eq_polygonHeightValue_of_width_one h C hBody ht
    rcases ht with rfl | ht
    · exact hw.1
    · have ht : t = Real.pi / 2 := ht
      subst t
      simpa only [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring] using hw.2.1
  have hsub := polygonHeightNiche_mono_of_eq_endpoints hle heq
  have harea : ClassicalResults.area (polygonHeightNiche g) ≤
      ClassicalResults.area (polygonHeightNiche h) := by
    apply ENNReal.toReal_mono (isBounded_polygonHeightNiche h).measure_lt_top.ne
    exact MeasureTheory.measure_mono hsub
  change ClassicalResults.area (polygonHeightCap h) -
      ClassicalResults.area (polygonHeightNiche h) ≤
    ClassicalResults.area (polygonHeightCap g) - ClassicalResults.area (polygonHeightNiche g)
  rw [hK, polygonHeightCap_of_translate K]
  exact sub_le_sub_left harea _

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
# Polygon / Height / Reconstruction
-/

public section

noncomputable section

namespace MovingSofa

private theorem isClosed_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    IsClosed (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply IsClosed.inter
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      (isClosed_normalHalfPlane _ _ false).inter (isClosed_normalHalfPlane _ _ true)
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      isClosed_normalHalfPlane _ _ false

private theorem convex_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Convex ℝ (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply Convex.inter
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      (convex_normalHalfPlane _ _ false).inter (convex_normalHalfPlane _ _ true)
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      convex_normalHalfPlane _ _ false

private theorem normalHalfPlane_upper_eq_lower_add_pi (t c : ℝ) :
    normalHalfPlane (t : Real.Angle) c true false =
      normalHalfPlane ((t + Real.pi : ℝ) : Real.Angle) (-c) false false := by
  ext p
  change c ≤ inner ℝ p (normalVector (t : Real.Angle)) ↔
    inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ -c
  rw [normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith

private theorem polygonHeightCap_halfPlaneRepresentation {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    HasHalfPlaneRepresentation (polygonHeightCap h)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
  let C : Set (Real.Angle × ℝ) :=
    ((fun t : ℝ ↦ ((t : Real.Angle), polygonHeightValue h t)) '' angleDomain Θ) ∪
      ((fun t : ℝ ↦ (((t + Real.pi : ℝ) : Real.Angle),
        -(polygonHeightValue h t - 1))) '' ({Θ.angle, Real.pi / 2} : Set ℝ))
  refine ⟨C, ?_, ?_⟩
  · rintro c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · right
      rcases ht with rfl | rfl
      · exact Or.inl rfl
      · change (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) ∈ capLowerNormals Θ.angle
        rw [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring]
        simp [capLowerNormals]
  · ext p
    simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
      Set.mem_iInter, C, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hendpoint, hinterior⟩ c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rcases ht with (ht | ht) | ht
        · exact (hinterior t (Or.inl ht))
        · obtain ⟨s, hs, rfl⟩ := ht
          exact hinterior (s + Real.pi / 2) (Or.inr ⟨s, hs, rfl⟩)
        · exact (hendpoint t ht).1
      · rw [← normalHalfPlane_upper_eq_lower_add_pi]
        exact (hendpoint t ht).2
    · intro hall
      constructor
      · intro t ht
        constructor
        · exact hall ((t : Real.Angle), polygonHeightValue h t)
            (Or.inl ⟨t, Or.inr ht, rfl⟩)
        · rw [normalHalfPlane_upper_eq_lower_add_pi]
          exact hall (((t + Real.pi : ℝ) : Real.Angle), -(polygonHeightValue h t - 1))
            (Or.inr ⟨t, ht, rfl⟩)
      · intro t ht
        exact hall ((t : Real.Angle), polygonHeightValue h t)
          (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem polygonHeightCap_upper_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ} (ht : t ∈ angleDomain Θ) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue h t := by
  exact polygonHeightCap_subset_normalHalfPlane h ht hp

private theorem polygonHeightCap_lower_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  change p ∈ polygonHeightParallelogram h ∩ _ at hp
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp.1 t) ht).2

/-- Attainment of both endpoint strip bounds reconstructs a translated polygon cap. -/
theorem exists_polygonCapTranslate_eq_polygonHeightCap {Θ : AngleSet}
    (h : PolygonHeightSpace Θ)
    (hbounded : Bornology.IsBounded (polygonHeightCap h))
    (hupper : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t - 1) :
    ∃ K' : PolygonCapTranslateSpace Θ, K'.val = polygonHeightCap h := by
  obtain ⟨p, hp, _⟩ := hupper (Real.pi / 2) (by simp)
  let L : ConvexBody Point := {
    carrier := polygonHeightCap h
    convex' := convex_polygonHeightCap h
    isCompact' := Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_polygonHeightCap h, hbounded⟩
    nonempty' := ⟨p, hp⟩ }
  have hsuppUpper (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L (t : Real.Angle) = polygonHeightValue h t := by
    obtain ⟨q, hq, hqeq⟩ := hupper t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      exact polygonHeightCap_upper_bound h hx (Or.inr ht)
    · simpa only [hqeq] using inner_le_supportValue L hq (t : Real.Angle)
  have hsuppLower (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) =
        -(polygonHeightValue h t - 1) := by
    obtain ⟨q, hq, hqeq⟩ := hlower t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      change inner ℝ x (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤
        -(polygonHeightValue h t - 1)
      rw [normalVector_add_pi, inner_neg_right]
      exact neg_le_neg (polygonHeightCap_lower_bound h hx ht)
    · have hle := inner_le_supportValue L hq ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hqeq] at hle
      exact hle
  have hwidthω : supportValue L (Θ.angle : Real.Angle) +
      supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1 := by
    rw [hsuppUpper Θ.angle (by simp), hsuppLower Θ.angle (by simp)]
    ring
  have hangle : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hwidthT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) +
      supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    rw [← hangle, hsuppUpper (Real.pi / 2) (by simp),
      hsuppLower (Real.pi / 2) (by simp)]
    ring
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hlowerNormals : (capLowerNormals Θ.angle).Finite := by
    simp [capLowerNormals]
  have hrepr : HasHalfPlaneRepresentation (L : Set Point)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
    exact polygonHeightCap_halfPlaneRepresentation h
  obtain ⟨C, hCfinite, hCN, hLC⟩ :=
    hrepr.finite_constraints
      (hdomain.image _ |>.union hlowerNormals)
  exact (polygonCapTranslate_iff Θ L).mpr
    ⟨hwidthω, hwidthT, C, hCfinite, hCN, hLC⟩

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
# Polygon / Height / Positive Increment / Contacts
-/

public section

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) (ε : ℝ) {s : ℝ}
    (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (raisedPolygonSupport K t ε) s =
      supportValue K.val.val (s : Real.Angle) +
        if (⟨s, hs⟩ : angleDomain Θ) = t then ε else 0 := by
  simp [polygonHeightValue, raisedPolygonSupport, hs]

private theorem mem_polygonHeightCap_raised_of_mem_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  have hupper (s : ℝ) (hs : s ∈ angleDomain Θ) :
      inner ℝ p (normalVector (s : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) s := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε hs]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro s hs
    constructor
    · exact hupper s (Or.inr hs)
    · change polygonHeightValue (raisedPolygonSupport K t ε) s - 1 ≤
        inner ℝ p (normalVector (s : Real.Angle))
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs)]
      have hne : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
        intro heq
        apply ht
        have hval : s = t.val := congrArg Subtype.val heq
        simpa [← hval] using hs
      rw [ite_eq_right hne]
      simp only [add_zero]
      rcases hs with rfl | rfl
      · have hlower := inner_le_supportValue K.val.val hp
          ((Θ.angle + Real.pi : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
        rw [K.val.property.2.2.1]
        linarith
      · have hlower := inner_le_supportValue K.val.val hp
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
        rw [K.val.property.2.2.2.1]
        simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro s hs
    exact hupper s (Or.inl hs)

private theorem raisedPolygonSupport_endpoint_contacts_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s - 1) := by
  have hne (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
    intro heq
    apply ht
    have hval : s = t.val := congrArg Subtype.val heq
    simpa [← hval] using hs
  have hvalue (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      polygonHeightValue (raisedPolygonSupport K t ε) s =
        supportValue K.val.val (s : Real.Angle) := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs), ite_eq_right (hne s hs),
      add_zero]
  constructor
  · intro s hs
    obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
      (s : Real.Angle)
    exact ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp,
      hpinner.trans (hvalue s hs).symm⟩
  · intro s hs
    rcases hs with rfl | rfl
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((Θ.angle + Real.pi : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [normalVector_add_pi, inner_neg_right,
        K.val.property.2.2.2.2.1] at hpinner
      rw [hvalue Θ.angle (by simp), K.val.property.2.2.1]
      linarith
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hpinner
      rw [hvalue (Real.pi / 2) (by simp), K.val.property.2.2.2.1]
      simpa [normalVector, frame, PiLp.inner_apply] using hpinner

private theorem independentWallCap_self_sub_one_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun t ↦ h t - 1) = polygonHeightCap h := by
  ext p
  simp only [independentWallCap, polygonHeightCap, polygonHeightParallelogram,
    Set.mem_inter_iff, Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    simp only [polygonHeightValue, dite_eq_left htD]
  · rfl

private theorem polygonHeightCap_raised_bounded {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ →
      Bornology.IsBounded (polygonHeightCap (raisedPolygonSupport K t ε)) := by
  let h : PolygonHeightSpace Θ :=
    fun s ↦ supportValue K.val.val (s.val : Real.Angle)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  let hε' := raisedPolygonSupport K t ε
  let lower : PolygonHeightSpace Θ := fun s ↦ hε' s - 1
  have hu (s : angleDomain Θ) : |hε' s - h s| ≤ ε₀ := by
    change |(supportValue K.val.val (s.val : Real.Angle) + if s = t then ε else 0) -
      supportValue K.val.val (s.val : Real.Angle)| ≤ ε₀
    split_ifs
    · simpa using hε
    · simp [hε₀.le]
  have hl (s : angleDomain Θ) : |lower s - (h s - 1)| ≤ ε₀ := by
    simpa only [lower, sub_sub_sub_cancel_right] using hu s
  have hsub := (hbound hε' lower hu hl).1
  rw [independentWallCap_self_sub_one_eq] at hsub
  exact Metric.isBounded_closedBall.subset hsub

/-- A sufficiently small interior height increase yields a translated polygon cap. -/
theorem polygonCap_positive_height_increment_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨ε₀, hε₀, hbounded⟩ := polygonHeightCap_raised_bounded K t
  refine ⟨ε₀, hε₀, fun ε hε hεlt ↦ ?_⟩
  have hcontacts := raisedPolygonSupport_endpoint_contacts_of_not_endpoint
    K t hε.le ht
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hεlt.le⟩)) hcontacts.1 hcontacts.2

private theorem midpoint_mem_strict_support_of_face {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point} {t c : ℝ} (ht : t ∈ angleDomain Θ)
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hat : inner ℝ a (normalVector (t : Real.Angle)) = c)
    (hbt : inner ℝ b (normalVector (t : Real.Angle)) = c)
    (hab : a ≠ b) :
    let m := (2 : ℝ)⁻¹ • (a + b)
    m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t : Real.Angle)) = c ∧
      ∀ s ∈ angleDomain Θ, s ≠ t →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  dsimp
  have hm : (2 : ℝ)⁻¹ • (a + b) ∈ (K.val.val : Set Point) := by
    rw [smul_add]
    exact K.val.val.convex ha hb (by norm_num) (by norm_num) (by norm_num)
  have hmt : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (t : Real.Angle)) =
      c := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real, hat, hbt]
    ring
  refine ⟨hm, hmt, ?_⟩
  intro s hs hst
  have hle := inner_le_supportValue K.val.val hm (s : Real.Angle)
  apply lt_of_le_of_ne hle
  intro heq
  have hae := inner_le_supportValue K.val.val ha (s : Real.Angle)
  have hbe := inner_le_supportValue K.val.val hb (s : Real.Angle)
  have hmavg : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (s : Real.Angle)) =
      (2 : ℝ)⁻¹ * (inner ℝ a (normalVector (s : Real.Angle)) +
        inner ℝ b (normalVector (s : Real.Angle))) := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real]
  have haeq : inner ℝ a (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hbeq : inner ℝ b (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbt, hat, sub_self]
  have horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbeq, haeq, sub_self]
  exact hst (eq_of_inner_sub_normalVector_eq_zero_of_ne
    (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht) hab horths hortht)

private theorem exists_pos_uniform_strict_support_gap {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (m : Point) (t : angleDomain Θ)
    (hstrict : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      inner ℝ m (normalVector (s : Real.Angle)) <
        supportValue K.val.val (s : Real.Angle)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)) := by
  let gap : ℝ → ℝ := fun s ↦ if s = t.val then 1 else
    supportValue K.val.val (s : Real.Angle) - inner ℝ m (normalVector (s : Real.Angle))
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun s : ℝ ↦ s + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hnonempty : (angleDomain Θ).Nonempty := ⟨Θ.angle, by simp [angleDomain]⟩
  obtain ⟨δ, hδ, hδle⟩ := hdomain.isCompact.exists_pos_forall_le hnonempty
    (hdomain.continuousOn gap) (fun s hs ↦ by
      dsimp only [gap]
      split_ifs with heq
      · positivity
      · linarith [hstrict s hs heq])
  refine ⟨δ, hδ, ?_⟩
  intro s hs hne
  simpa [gap, hne] using hδle s hs

private theorem cos_sub_nonneg_of_mem_endpoints {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : 0 ≤ Real.cos (s - t) := by
  apply Real.cos_nonneg_of_mem_Icc
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]

private theorem add_smul_normal_mem_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (m : Point) (hm : m ∈ (K.val.val : Set Point))
    (hmLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ m (normalVector (t.val : Real.Angle)))
    (hmUpper : inner ℝ m (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle))
    {δ ε : ℝ} (hδ : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεδ : ε < δ) :
    m + ε • normalVector (t.val : Real.Angle) ∈
      polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        linarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub]
        have hcos := Real.cos_le_one (t.val - r)
        rw [inner_normalVector_normalVector]
        have hgap := hδ r hrD hrt
        nlinarith
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
        inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle))
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        nlinarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        have hbase : supportValue K.val.val (r : Real.Angle) - 1 ≤
            inner ℝ m (normalVector (r : Real.Angle)) := by
          rcases hr with rfl | rfl
          · have hl := inner_le_supportValue K.val.val hm
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
            rw [K.val.property.2.2.1]
            linarith
          · have hl := inner_le_supportValue K.val.val hm
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hl
            rw [K.val.property.2.2.2.1]
            simpa [normalVector, frame, PiLp.inner_apply] using hl
        have hcos := cos_sub_nonneg_of_mem_endpoints htendpoint hr
        rw [inner_normalVector_normalVector]
        exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hε.le hcos))
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
        (normalVector (r : Real.Angle)) ≤
      polygonHeightValue (raisedPolygonSupport K t ε) r
    rw [hval, inner_add_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    by_cases hrt : r = t.val
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
      rw [ite_eq_left hsub, hrt, inner_normalVector_self]
      linarith
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
        intro heq
        exact hrt (congrArg Subtype.val heq)
      rw [ite_eq_right hsub]
      have hcos := Real.cos_le_one (t.val - r)
      rw [inner_normalVector_normalVector]
      have hgap := hδ r hrD hrt
      nlinarith

private theorem mem_raisedPolygonSupport_of_endpoint_of_le_inner {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) {ε : ℝ} (hε : 0 ≤ ε)
    (hinner : ε ≤ inner ℝ p (normalVector (t.val : Real.Angle))) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hvalue := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ p (normalVector (r : Real.Angle)) ≤
          polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hvalue]
      exact (inner_le_supportValue K.val.val hp _).trans
        (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
          inner ℝ p (normalVector (r : Real.Angle))
      rw [hvalue]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt]
        have hsupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
          rcases ht with ht | ht
          · simpa [ht] using K.val.property.2.2.1
          · have ht' : t.val = Real.pi / 2 := by simpa using ht
            simpa [ht'] using K.val.property.2.2.2.1
        rw [hsupport]
        simpa using hinner
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        rcases hr with rfl | rfl
        · have hlower := inner_le_supportValue K.val.val hp
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
          rw [K.val.property.2.2.1]
          linarith
        · have hlower := inner_le_supportValue K.val.val hp
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
          rw [K.val.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    rw [polygonHeightValue_raisedPolygonSupport K t ε hrD]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))

private theorem moved_upper_lower_contacts {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (u l : Point) (hu : u ∈ (K.val.val : Set Point))
    (huval : inner ℝ u (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle))
    (hl : l ∈ (K.val.val : Set Point))
    (hlval : inner ℝ l (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle) - 1)
    {δu δl ε : ℝ}
    (hδu : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δu ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ u (normalVector (s : Real.Angle)))
    (hδl : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δl ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ l (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεu : ε < δu) (hεl : ε < δl) :
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val) ∧
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val - 1) := by
  have huLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ u (normalVector (t.val : Real.Angle)) := by linarith
  have hlUpper : inner ℝ l (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle) := by linarith
  have hu' := add_smul_normal_mem_raisedPolygonSupport K t ht u hu huLower huval.le
    hδu hε hεu
  have hl' := add_smul_normal_mem_raisedPolygonSupport K t ht l hl hlval.ge hlUpper
    hδl hε hεl
  have hvalue : polygonHeightValue (raisedPolygonSupport K t ε) t.val =
      supportValue K.val.val (t.val : Real.Angle) + ε := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε t.property]
    simp
  constructor
  · refine ⟨u + ε • normalVector (t.val : Real.Angle), hu', ?_⟩
    rw [inner_add_left, inner_smul_left, huval, inner_normalVector_self, hvalue]
    simp
  · refine ⟨l + ε • normalVector (t.val : Real.Angle), hl', ?_⟩
    rw [inner_add_left, inner_smul_left, hlval, inner_normalVector_self, hvalue]
    simp
    ring

private theorem exists_upperFace_midpoint_strict {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at ht
      exact ENNReal.ofReal_pos.mp ht
    exact dist_ne_zero.mp hdist.ne'
  let m := (2 : ℝ)⁻¹ • (a + b)
  have hm := midpoint_mem_strict_support_of_face K t.property
    haedge.1 hbedge.1 haedge.2 hbedge.2 hab
  exact ⟨m, hm⟩

private theorem stripParallelogram_top_inner_angle (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) :
    inner ℝ (stripParallelogram Θ.angle).2.2 (normalVector (Θ.angle : Real.Angle)) = 1 := by
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
      (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
    simpa [show Real.pi / 4 - Θ.angle / 2 =
        (Real.pi / 2 - Θ.angle) / 2 by ring]
      using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
  have htan := Real.tan_eq_sin_div_cos Θ.angle
  simp [stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
  field_simp [hc.ne']
  ring

private theorem stripParallelogram_top_sub_vertical_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - tangentVector 0 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have haFan : a ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ a (normalVector (Θ.angle : Real.Angle))
      dsimp [a]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω]
      simp only [tangentVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
        normalVector, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        mul_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, zero_add, sub_nonneg,
        ge_iff_le]
      exact Real.sin_le_one Θ.angle
    · change 0 ≤ inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
        PiLp.inner_apply]
  apply K.val.mem_of_mem_capFan_of_le_supportValue haFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hale : inner ℝ a (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show a = o - tangentVector 0 by rfl, inner_sub_left]
    apply sub_le_self
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (Θ.angle_le.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hs.1,
          hs.2.trans (by linarith [Θ.angle_le, Real.pi_pos])⟩
    simpa [tangentVector, normalVector, frame, PiLp.inner_apply] using
      Real.sin_nonneg_of_mem_Icc hsI
  exact hale.trans ho_le

private theorem stripParallelogram_top_sub_normal_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle) ∈
      (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have hbFan : b ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ b (normalVector (Θ.angle : Real.Angle))
      dsimp [b]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [b]
      have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
        simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
      rw [inner_sub_left, hoT]
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two,
        Real.sin_pi_div_two, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, zero_add, sub_nonneg, ge_iff_le]
      exact Real.sin_le_one Θ.angle
  apply K.val.mem_of_mem_capFan_of_le_supportValue hbFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hble : inner ℝ b (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show b = o - normalVector (Θ.angle : Real.Angle) by rfl, inner_sub_left]
    apply sub_le_self
    rw [inner_normalVector_normalVector]
    apply Real.cos_nonneg_of_mem_Icc
    rcases hs with hs | hs
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
  exact hble.trans ho_le

private theorem exists_lowerFace_midpoint_strict_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have hzero := zero_mem_cap_of_lt K.val hΘ
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    let b := (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle)
    have hb := stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
    have hbnormal : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
      dsimp [b]
      rw [inner_sub_left, stripParallelogram_top_inner_angle Θ hΘ,
        inner_normalVector_self, sub_self]
    have hbne : (0 : Point) ≠ b := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).2.1
      rw [← show b = (stripParallelogram Θ.angle).2.2 -
        normalVector (Θ.angle : Real.Angle) by rfl, ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 1) hgap
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
      simp only [Fin.isValue, PiLp.zero_apply, tangentVector, frame, Real.Angle.cos_coe,
        Real.Angle.sin_coe, PiLp.smul_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, smul_eq_mul, zero_eq_mul] at hcoord
      rcases hcoord with hgapzero | hcoszero
      · exact hgappos.ne' hgapzero
      · exact hcos.ne' hcoszero
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero hb
      (by simp) (by simpa [htval, K.val.property.2.2.1] using hbnormal) hbne
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + b), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.1]
      ring
    · simpa [htval] using hm.2.2
  · have htval : t.val = Real.pi / 2 := ht
    let a := (stripParallelogram Θ.angle).2.2 - tangentVector 0
    have ha := stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
    have hanormal : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
      simp [a, stripParallelogram, tangentVector, normalVector, frame, PiLp.inner_apply]
    have hane : (0 : Point) ≠ a := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).1
      rw [← show a = (stripParallelogram Θ.angle).2.2 - tangentVector 0 by rfl,
        ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 0) hgap
      simp [normalVector, frame] at hcoord
      linarith
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero ha
      (by simp) (by simpa [htval, K.val.property.2.2.2.1] using hanormal) hane
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + a), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.2.1]
      ring
    · simpa [htval] using hm.2.2

private theorem sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2) {p : Point}
    (hp : p ∈ (K.val.val : Set Point))
    (hpT : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1) :
    p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val.val : Set Point) := by
  apply K.val.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector (Θ.angle : Real.Angle))
      rw [hΘ, inner_sub_left, hpT, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      rw [inner_sub_left, hpT, inner_normalVector_self, sub_self]
  · intro s hs
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by rw [hΘ] at hs; linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by rw [hΘ] at hs; linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc hsI
    have hle : inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector (s : Real.Angle)) ≤ inner ℝ p (normalVector (s : Real.Angle)) := by
      rw [inner_sub_left]
      apply sub_le_self
      rw [inner_normalVector_normalVector]
      simpa [Real.cos_pi_div_two_sub] using hsin
    exact hle.trans (inner_le_supportValue K.val.val hp (s : Real.Angle))

private theorem exists_lowerFace_midpoint_strict_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · exact ht
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  let a' := a - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  let b' := b - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at hmass
      exact ENNReal.ofReal_pos.mp hmass
    exact dist_ne_zero.mp hdist.ne'
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have haSupport : inner ℝ a (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := haedge.2
    simpa [htval, K.val.property.2.2.2.1] using haSupport
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have hbSupport : inner ℝ b (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := hbedge.2
    simpa [htval, K.val.property.2.2.2.1] using hbSupport
  have ha' : a' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ haedge.1 haT
  have hb' : b' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ hbedge.1 hbT
  have ha'normal : inner ℝ a' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [a']
    rw [inner_sub_left, haT, inner_normalVector_self, sub_self]
  have hb'normal : inner ℝ b' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [b']
    rw [inner_sub_left, hbT, inner_normalVector_self, sub_self]
  have hab' : a' ≠ b' := by
    intro heq
    apply hab
    dsimp [a', b'] at heq
    exact sub_left_injective heq
  have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property ha' hb'
    ha'normal hb'normal hab'
  refine ⟨(2 : ℝ)⁻¹ • (a' + b'), hm.1, ?_, hm.2.2⟩
  rw [hm.2.1, htval, K.val.property.2.2.2.1]
  ring

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_lt K hΘ t ht
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho : o ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have ha : a ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
  have hb : b ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
    stripParallelogram_top_inner_angle Θ hΘ
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
      PiLp.inner_apply]
  have hbω : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
    dsimp [b]
    rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
  let gap := 1 - Real.sin Θ.angle
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgappos : 0 < gap := by
    have hcosSq : 0 < Real.cos Θ.angle ^ 2 := sq_pos_of_pos hcos
    have htrig := Real.sin_sq_add_cos_sq Θ.angle
    have hsinle := Real.sin_le_one Θ.angle
    dsimp [gap]
    nlinarith
  have haω : inner ℝ a (normalVector (Θ.angle : Real.Angle)) = gap := by
    dsimp [a, gap]
    rw [inner_sub_left, hoω]
    simp [tangentVector, normalVector, frame, PiLp.inner_apply]
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = gap := by
    dsimp [b, gap]
    rw [inner_sub_left, hoT]
    simp [normalVector, frame, PiLp.inner_apply]
  refine ⟨min δu (min δl (min 1 gap)), by positivity, ?_⟩
  intro ε hε hεlt
  have hεu : ε < δu := hεlt.trans_le (min_le_left _ _)
  have hεl : ε < δl := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεgap : ε < gap :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε hεu hεl
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ho hε.le
      rw [htval, hoω]
      exact hε1.le
    have haMem : a ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ha hε.le
      rw [htval, haω]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) (Real.pi / 2) = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Real.pi / 2, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.1
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        exact ⟨o, hoMem, hoT.trans hother.symm⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.2
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        refine ⟨a, haMem, ?_⟩
        rw [haT, hother]
        ring
  · have htval : t.val = Real.pi / 2 := by simpa using ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) ho hε.le
      rw [htval, hoT]
      exact hε1.le
    have hbMem : b ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) hb hε.le
      rw [htval, hbT]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) Θ.angle = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Θ.angle, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        exact ⟨o, hoMem, hoω.trans hother.symm⟩
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.1
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        refine ⟨b, hbMem, ?_⟩
        rw [hbω, hother]
        ring
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.2

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_eq K hΘ t ht hmass
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · simpa using ht
  refine ⟨min δu δl, by positivity, ?_⟩
  intro ε hε hεlt
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε (hεlt.trans_le (min_le_left _ _))
      (hεlt.trans_le (min_le_right _ _))
  constructor
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.1
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.2

/-- A sufficiently small endpoint height increase preserves both unit widths. -/
theorem polygonCap_positive_height_increment_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨εb, hεb, hbounded⟩ := polygonHeightCap_raised_bounded K t
  obtain ⟨εc, hεc, hcontacts⟩ : ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 < ε → ε < εc →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
    rcases lt_or_eq_of_le Θ.angle_le with hΘ | hΘ
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_lt K hΘ t ht hmass
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_eq K hΘ t ht hmass
  refine ⟨min εb εc, by positivity, ?_⟩
  intro ε hε hεlt
  have hb : ε < εb := hεlt.trans_le (min_le_left _ _)
  have hc : ε < εc := hεlt.trans_le (min_le_right _ _)
  have hcontact := hcontacts ε hε hc
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hb.le⟩)) hcontact.1 hcontact.2

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
# Polygon / Height / Positive Increment
-/

public section

noncomputable section

namespace MovingSofa

theorem polygonCap_positive_height_increment {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  by_cases htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_positive_height_increment_of_endpoint K t htendpoint ht
  · exact polygonCap_positive_height_increment_of_not_endpoint K t htendpoint

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

* `Bounds.LegComputation`.
* `Bounds.Lower.Profile`.
* `Bounds.NicheLimits`.
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
# Bounds / Leg Computation
-/

public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem rightAngle_allowedReal_gap_left (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t - polygonStepSize n + Real.pi / 2 - Real.pi)
        (t - polygonStepSize n + Real.pi / 2) ∨
    r ∈ Set.Icc (t + Real.pi / 2) (t + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_pred_or_ge n hn hq ht with hqle | hqge
      · left
        constructor
        · linarith [Real.pi_pos]
        · linarith
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

private theorem rightAngle_allowedReal_gap_right (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t + Real.pi / 2 - Real.pi) (t + Real.pi / 2) ∨
      r ∈ Set.Icc (t + polygonStepSize n + Real.pi / 2)
        (t + polygonStepSize n + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_or_succ_le n hn hq ht with hqle | hqge
      · left
        constructor <;> linarith [Real.pi_pos]
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

/-- The preceding shifted grid support is attained at the negative left-wall contact. -/
private theorem rightAngle_supportValue_prev_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.2
        (normalVector ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t - polygonStepSize n + Real.pi / 2
  let b := t + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_left n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_snd_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_left K.val.val a b
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (a : Real.Angle)) = supportValue K.val.val (a : Real.Angle) at hinter
  change supportValue K.val.val (a : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (b : Real.Angle)).2 (normalVector (a : Real.Angle))
  rw [← heq, hinter]

/-- The next shifted support is attained at the positive contact, including the final grid point. -/
private theorem rightAngle_supportValue_next_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.1
        (normalVector ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t + Real.pi / 2
  let b := t + polygonStepSize n + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp only [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_right n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_fst_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_right K.val.val a b
    (show Real.sin (b - a) ≠ 0 by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [a, b] <;> linarith)
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (b : Real.Angle)) = supportValue K.val.val (b : Real.Angle) at hinter
  change supportValue K.val.val (b : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (a : Real.Angle)).1 (normalVector (b : Real.Angle))
  rw [← heq, hinter]

private theorem one_sub_cos_div_cos_eq_tan_mul_tan_half {δ : ℝ}
    (hδ0 : 0 < δ) (hδT : δ < Real.pi / 2) :
    (1 - Real.cos δ) / Real.cos δ = Real.tan δ * Real.tan (δ / 2) := by
  have hc : Real.cos δ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδT⟩)
  have hch : Real.cos (δ / 2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hc, hch]
  have htwo : δ = 2 * (δ / 2) := by ring
  have hcos : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 :=
    (congrArg Real.cos htwo).trans (Real.cos_two_mul_eq_one_sub _)
  have hsin : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) :=
    (congrArg Real.sin htwo).trans (Real.sin_two_mul _)
  rw [hcos, hsin]
  ring

private theorem polygonStepSize_mem_Ioo (n : ℕ) (hn : 2 ≤ n) :
    polygonStepSize n ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · simp only [polygonStepSize]
    positivity
  · simp only [polygonStepSize]
    apply (div_lt_iff₀ hnpos).2
    nlinarith [Real.pi_pos]

private theorem rightAngle_bRay_prev_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.2
  let g := (tangentArmLengths K.val t).2.2
  let u := t - δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have hnormal : normalVector (u : Real.Angle) =
      Real.sin δ • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 - δ)
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
    have hu : u = t + (Real.pi / 2 - δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.2 +
          (tangentArmLengths K.val t).2.2 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t).2.2.2
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_prev_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (g - 1) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left,
      inner_add_right, inner_smul_right, inner_normalVector_self,
      inner_normalVector_tangentVector, real_inner_comm, inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((g - 1) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (g - 1) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (g - 1) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

private theorem rightAngle_bRay_next_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.1
  let g := (tangentArmLengths K.val t).2.1
  let u := t + δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have hnormal : normalVector (u : Real.Angle) =
      (-Real.sin δ) • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 + δ)
    simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, add_zero] at h
    have hu : u = t + (Real.pi / 2 + δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.1 +
          (tangentArmLengths K.val t).2.1 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t).2.2.1
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_next_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (1 - g) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left, inner_add_right, inner_smul_right,
      inner_normalVector_self, inner_normalVector_tangentVector, real_inner_comm,
      inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (1 - g + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((1 - g) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (1 - g) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (1 - g) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (1 - g + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

theorem maximumPolygonCap_leg_lengths (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn))
    (t : ℝ) (ht : t ∈ (rightAngleSet n hn).directions) :
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) ∧
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  exact ⟨rightAngle_bRay_prev_leg_length n hn K ht,
    rightAngle_bRay_next_leg_length n hn K ht⟩

/-- The face line of a convex body meets the two adjacent inner-wall half-planes in a set whose
length is at most `2 tan(δ/2)` less the face length. -/
theorem hausdorffMeasure_faceLine_inter_innerWalls_le (K : ConvexBody Point)
    (t δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < Real.pi) :
    Measure.hausdorffMeasure 1
        ({p : Point | inner ℝ p (normalVector (t : Real.Angle)) =
            supportValue (K : Set Point) (t : Real.Angle) - 1} ∩
          (normalHalfPlane ((t - δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1) true false ∩
            normalHalfPlane ((t + δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1) true false)) ≤
      ENNReal.ofReal (max 0 (2 * Real.tan (δ / 2) -
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal)) := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 hδ
  have hhalfcos : 0 < Real.cos (δ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hhalfsin : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have htanhalf : (1 - Real.cos δ) / Real.sin δ = Real.tan (δ / 2) := by
    have h1 : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
      have h := Real.sin_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    have h2 : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    rw [Real.tan_eq_sin_div_cos, h1, h2, div_eq_div_iff (by positivity) hhalfcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq (δ / 2)]
  have hneg : t - (t + δ) = -δ := by ring
  have hpos : t - (t - δ) = δ := by ring
  have hAn : inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_fst_mem K _).2
  have hBn : inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_snd_mem K _).2
  have hApb := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hBmb := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t - δ : ℝ) : Real.Angle)
  rw [inner_normalVector_eq_frame_rotate _ t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
    hAn] at hApb
  rw [inner_normalVector_eq_frame_rotate _ t (t - δ), hpos, hBn] at hBmb
  have hAB := (surfaceAreaMeasure_atom_length K (t : Real.Angle)).2.2
  have hgap : inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) =
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
    rw [hAB, inner_add_left, real_inner_smul_left, inner_tangentVector_self, mul_one]
  refine le_trans (hausdorffMeasure_le_of_frame_bounds (t := t)
    (e := supportValue (K : Set Point) (t : Real.Angle) - 1)
    (lo := inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
      Real.tan (δ / 2))
    (hi := inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
      Real.tan (δ / 2)) ?_) (le_of_eq ?_)
  · rintro p ⟨hline, hprev, hnext⟩
    have hpn : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue (K : Set Point) (t : Real.Angle) - 1 := hline
    change supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t - δ : ℝ) : Real.Angle)) at hprev
    change supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + δ : ℝ) : Real.Angle)) at hnext
    rw [inner_normalVector_eq_frame_rotate p t (t - δ), hpos, hpn] at hprev
    rw [inner_normalVector_eq_frame_rotate p t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
      hpn] at hnext
    have hkeyU : (inner ℝ p (tangentVector (t : Real.Angle)) -
        inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))) *
          Real.sin δ ≤ 1 - Real.cos δ := by nlinarith [hprev, hBmb]
    have hkeyL : (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
        inner ℝ p (tangentVector (t : Real.Angle))) * Real.sin δ ≤ 1 - Real.cos δ := by
      nlinarith [hnext, hApb]
    have hU := (le_div_iff₀ hsin).mpr hkeyU
    have hL := (le_div_iff₀ hsin).mpr hkeyL
    rw [htanhalf] at hU hL
    exact ⟨hpn, by linarith, by linarith⟩
  · have hlen : inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        Real.tan (δ / 2) -
        (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
          Real.tan (δ / 2)) =
        2 * Real.tan (δ / 2) - (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
      rw [hgap]
      ring
    rw [hlen]

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
# Bounds / Lower / Profile
-/

public section

noncomputable section

namespace MovingSofa

/-- Integrate the reflected arm profile through the second magic function and add one. -/
@[expose]
def armIntegralOperator (f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := 1 + ∫ u in (0 : ℝ)..(x : ℝ),
    magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))
  continuous_toFun := by
    have hf : Continuous (fun u : ℝ ↦
        magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity)
          (Real.pi / 2 - u)))) := by
      unfold magicFunctions
      fun_prop
    exact continuous_const.add
      ((intervalIntegral.differentiable_integral_of_continuous hf).continuous.comp
        continuous_subtype_val)

/-- Iteratively improve the nonnegative arm lower bound by taking the maximum with its
integral update. -/
@[expose]
def armLowerBoundSequence : ℕ → C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)
  | 0 => ⟨fun _ ↦ 0, continuous_const⟩
  | n + 1 =>
      ⟨fun x ↦ max (armLowerBoundSequence n x)
          (Real.toNNReal (armIntegralOperator (armLowerBoundSequence n) x)),
        (armLowerBoundSequence n).continuous.max
          (continuous_real_toNNReal.comp (armIntegralOperator (armLowerBoundSequence
            n)).continuous)⟩

/-- The continuous profile `max (1 - x) c` on the quarter-turn interval. -/
@[expose]
def lowerBoundProfile (c : Set.Icc (0 : ℝ) 1) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := max (1 - (x : ℝ)) (c : ℝ)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).max continuous_const

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
# Bounds / Niche Limits
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Support values converge under Hausdorff convergence of caps. -/
theorem tendsto_supportValue_of_hausdorff {ω : ℝ}
    (K : ℕ → CapSpace ω) (L : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ supportValue (K i).val (t : Real.Angle)) atTop
      (𝓝 (supportValue L.val (t : Real.Angle))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro i
  simpa only [Real.dist_eq, vectorSupport, supportValue] using
    (compactSet_support_continuity (K i).val L.val (K i).val.nonempty
      (K i).val.isCompact L.val.nonempty L.val.isCompact).2.1
        (normalVector (t : Real.Angle)) (norm_normalVector_real t)

private theorem volume_normalLine_eq_zero (t c : ℝ) :
    volume {p : Point | inner ℝ p (normalVector (t : Real.Angle)) = c} = 0 := by
  let u := normalVector (t : Real.Angle)
  let f : Point →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap
  let A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f
  have hA : (A : Set Point) = {p : Point | inner ℝ p u = c} := by
    ext p
    simp [A, f, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hA]
  apply Measure.addHaar_affineSubspace
  intro htop
  have hp : (c + 1) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hA] at hp
  have hu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_normalVector_real]
    norm_num
  change inner ℝ ((c + 1) • u) u = c at hp
  rw [real_inner_smul_left, hu, mul_one] at hp
  linarith

private theorem eventually_lt_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x < f i ↔ x < a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi h
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_lt_of_ge hi.le) (not_lt_of_ge h.le)

private theorem ae_eventually_mem_polygonNiche_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ polygonNiche Θ (K i) ↔ p ∈ polygonNiche Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle) - 1)
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (p ∈ innerQuadrant (K i).val t ↔ p ∈ innerQuadrant L.val t) := by
    have h₁ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim t).sub_const 1) (hp t ht).1
    have h₂ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2)).sub_const 1)
      (hp t ht).2
    filter_upwards [h₁, h₂] with i h₁ h₂
    exact and_congr h₁ h₂
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [polygonNiche, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mp hqt⟩
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mpr hqt⟩

private theorem eventually_le_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x ≤ f i ↔ x ≤ a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi.le h.le
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_le_of_gt hi) (not_le_of_gt h)

private theorem ae_eventually_mem_angleCap_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ angleCap Θ (K i) ↔ p ∈ angleCap Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle))
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue (K i).val (t : Real.Angle) ↔
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue L.val (t : Real.Angle)) ∧
      (inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ↔
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) :=
    (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim t) (hp t ht).1).and
      (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim
        (t + Real.pi / 2)) (hp t ht).2)
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [mem_angleCap_iff]
  apply and_congr_right
  intro _
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦ and_congr (hi t ht).1 (hi t ht).2

private theorem exists_angleCap_norm_bound (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∃ R : ℝ, ∀ i p, p ∈ angleCap Θ (K i) → ‖p‖ ≤ R := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim t)).exists_norm_le
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2))).exists_norm_le
  let l := -|B| / Real.sin t
  let r := |A| / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M + 1, fun i p hp ↦ ?_⟩
  have haBound : supportValue (K i).val (t : Real.Angle) ≤ |A| :=
    (le_abs_self _).trans ((hA _ (Set.mem_range_self i)).trans (le_abs_self A))
  have hbBound : supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤ |B| :=
    (le_abs_self _).trans ((hB _ (Set.mem_range_self i)).trans (le_abs_self B))
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ (K i) p).mp hp
  obtain ⟨ha, hb⟩ := hnormals t ht
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg hc.le hy.1]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_nonneg hs.le hy.1]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

private theorem tendsto_polygonNiche_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (polygonNiche Θ L))) := by
  obtain ⟨R, hR, _, hpoly⟩ := niche_uniform_bounds.2.2 (fun _ ↦ Θ.angle) K L.val hlim
  let C := Metric.closedBall (0 : Point) (2 * R)
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : polygonNiche Θ (K i) ⊆ C := by
    intro p hp
    obtain ⟨hx, hy, hh⟩ := hpoly i Θ (K i) rfl hp
    change dist p 0 ≤ 2 * R
    rw [dist_zero_right]
    have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hR).mpr hx
    have hy2 := (sq_le_sq₀ hy hR).mpr hh
    have hn := EuclideanSpace.norm_sq_eq p
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
    nlinarith [norm_nonneg p, sq_nonneg R]
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (polygonNiche Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((polygonNiche Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_polygonNiche_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ polygonNiche Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ polygonNiche Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (polygonNiche Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (polygonNiche Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (measurableSet_polygonNiche Θ (K i))).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ polygonNiche Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (polygonNiche Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (polygonNiche Θ P) := by
    exact integral_indicator_one (measurableSet_polygonNiche Θ P)
  simpa only [harea] using hconv

private theorem tendsto_angleCap_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (angleCap Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (angleCap Θ L))) := by
  obtain ⟨R, hR⟩ := exists_angleCap_norm_bound Θ K L hlim
  let C := Metric.closedBall (0 : Point) R
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : angleCap Θ (K i) ⊆ C := by
    intro p hp
    simpa only [C, Metric.mem_closedBall, dist_zero_right] using hR i p hp
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (angleCap Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((angleCap Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_angleCap_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ angleCap Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ angleCap Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (angleCap Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (angleCap Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (isClosed_angleCap Θ (K i)).measurableSet).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ angleCap Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (angleCap Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (angleCap Θ P) := by
    exact integral_indicator_one (isClosed_angleCap Θ P).measurableSet
  simpa only [harea] using hconv

theorem polygonArea_continuity (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i)))
      atTop (𝓝 (ClassicalResults.area (polygonNiche Θ L))) ∧
    Tendsto (fun i ↦ polygonAreaFunctional Θ (K i))
      atTop (𝓝 (polygonAreaFunctional Θ L)) := by
  exact ⟨tendsto_polygonNiche_area Θ K L hlim,
    (tendsto_angleCap_area Θ K L hlim).sub (tendsto_polygonNiche_area Θ K L hlim)⟩

private theorem polygonNiche_mono_directions (Θ Ψ : AngleSet)
    (K : CapSpace Θ.angle) (L : CapSpace Ψ.angle)
    (hangle : Θ.angle = Ψ.angle) (hcarrier : (K.val : Set Point) = (L.val : Set Point))
    (hsub : Θ.directions ⊆ Ψ.directions) :
    polygonNiche Θ K ⊆ polygonNiche Ψ L := by
  rintro p ⟨hp, hq⟩
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, hsub ht, ?_⟩⟩
  · simpa only [hangle] using hp
  · simpa only [hcarrier] using hpt

/-- Every niche point belongs to all sufficiently fine uniform polygon niches. -/
theorem eventually_mem_polygonNiche_of_mem_capNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) {p : Point} (hp : p ∈ capNiche K) :
    ∀ᶠ i in atTop, p ∈ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K := by
  obtain ⟨hfan, hq⟩ := hp
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  have hopen : IsOpen {s : ℝ | p ∈ innerQuadrant K.val s} := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_const.inner continuous_normalVector_real)
        ((continuous_supportValue_real K.val).sub continuous_const)
    · exact isOpen_lt
        (continuous_const.inner (continuous_normalVector_real.comp
          (continuous_id.add continuous_const)))
        (((continuous_supportValue_real K.val).comp
          (continuous_id.add continuous_const)).sub continuous_const)
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hpt)
  have hat' : max 0 a < t := max_lt ht.1 hat
  have htb' : t < min ω b := lt_min ht.2 htb
  filter_upwards [eventually_exists_uniformAngleSet_mem_Ioo ω hω hω' n hn hmono
    (le_max_left 0 a) (hat'.trans htb') (min_le_left ω b)] with i hi
  obtain ⟨s, hs, hsa, hsb⟩ := hi
  refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨s, hs, hab ?_⟩⟩
  exact ⟨(le_max_right 0 a).trans_lt hsa, hsb.trans_le (min_le_right ω b)⟩

private theorem iUnion_uniform_polygonNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) :
    (⋃ i, polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) = capNiche K := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i ↦
      polygonNiche_subset_capNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K
  · intro p hp
    obtain ⟨i, hi⟩ := (eventually_mem_polygonNiche_of_mem_capNiche ω hω hω' n hn hmono K hp).exists
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

private theorem tendsto_uniform_polygonNiche_area (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k) (K : CapSpace ω) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K)) atTop
      (𝓝 (ClassicalResults.area (capNiche K))) := by
  have hmon : Monotone (fun i ↦ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) := by
    intro i j hij
    exact polygonNiche_mono_directions
      (uniformAngleSet ω hω hω' (n i) (hn i))
      (uniformAngleSet ω hω hω' (n j) (hn j)) K K rfl rfl
      (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hij)
  have hlim := tendsto_measure_iUnion_atTop (μ := volume) hmon
  rw [iUnion_uniform_polygonNiche ω hω hω' n hn hmono K] at hlim
  exact (ENNReal.tendsto_toReal (niche_uniform_bounds.1 ω K).2.2.1.ne).comp hlim

theorem maximizingPolygon_nicheArea_limit (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    (P : ∀ i, PolygonCapSpace (uniformAngleSet ω hω hω' (n i) (hn i)))
    (hmax : ∀ i, IsMaximumPolygonCap _ (P i)) (K : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point)
      (K.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) (P i).val))
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
  let Θ (i : ℕ) := uniformAngleSet ω hω hω' (n i) (hn i)
  have hupper (i : ℕ) :
      ClassicalResults.area (polygonNiche (Θ i) (P i).val) ≤
        ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K := by
    have hmax' := polygonAreaFunctional_le_maximum (Θ i) (P i) (hmax i) K
    have hbound := (polygonArea_upperBound (Θ i)).2 K
    have harea := (polygonArea_upperBound (Θ i)).1 (P i)
    have h := hbound.trans hmax'
    rw [harea] at h
    exact le_sub_comm.mp h
  have hupperlim : Tendsto
      (fun i ↦ ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K)
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
    convert (convexArea_hausdorff_continuity (fun i ↦ (P i).val.val) K.val hlim).sub_const
      (capAreaFunctional K) using 1
    simp only [capAreaFunctional, sub_sub_cancel]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hex := (tendsto_uniform_polygonNiche_area ω hω hω' n hn hmono hdyadic
      K).eventually_const_lt ha
    obtain ⟨m, hm⟩ := hex.exists
    have hfixed := (polygonArea_continuity (Θ m) (fun i ↦ (P i).val) K hlim).1
    filter_upwards [hfixed.eventually_const_lt hm, eventually_ge_atTop m] with i hi hmi
    have hsub : polygonNiche (Θ m) (P i).val ⊆ polygonNiche (Θ i) (P i).val :=
      polygonNiche_mono_directions (Θ m) (Θ i) (P i).val (P i).val rfl rfl
        (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hmi)
    have hle : ClassicalResults.area (polygonNiche (Θ m) (P i).val) ≤
        ClassicalResults.area (polygonNiche (Θ i) (P i).val) :=
      ENNReal.toReal_mono (niche_uniform_bounds.2.1 (Θ i) (P i).val).2.2.1.ne (measure_mono hsub)
    exact hi.trans_le hle
  · intro b hb
    filter_upwards [hupperlim.eventually_lt_const hb] with i hi
    exact (hupper i).trans_lt hi

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

* `Cap.NicheLimit`.
* `Cap.Reflection`.
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
# Cap / Niche Limit
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- Containment of uniformly approximating polygon niches persists in the cap limit. -/
theorem capNiche_subset_of_uniform_polygonNiche_subset {ω : ℝ} (K : CapSpace ω)
    (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i) (hmono : StrictMono n)
    (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    (P : ∀ i, PolygonCapSpace
      (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)))
    (hcontain : ∀ i, polygonNiche
      (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)) (P i).val ⊆
        ((P i).val.val : Set Point))
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point)
      (K.val : Set Point)) atTop (𝓝 0)) : capNiche K ⊆ (K.val : Set Point) := by
  intro p hp
  obtain ⟨m, hm⟩ := (eventually_mem_polygonNiche_of_mem_capNiche ω K.property.1
    K.property.2.1 n hn hmono K hp).exists
  obtain ⟨hfan, hquad⟩ := hm
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hquad
  change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val (t : Real.Angle) - 1 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hpt
  have htend := tendsto_supportValue_of_hausdorff (fun i ↦ (P i).val) K hlim t
  have htend' := tendsto_supportValue_of_hausdorff (fun i ↦ (P i).val) K hlim
    (t + Real.pi / 2)
  apply ConvexBody.mem_of_tendsto_hausdorffDist p (fun i ↦ (P i).val.val) K.val _ hlim
  filter_upwards [(htend.sub_const 1).eventually_const_lt hpt.1,
    (htend'.sub_const 1).eventually_const_lt hpt.2, eventually_ge_atTop m] with i hi hi' hmi
  apply hcontain i
  refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨t, ?_, ?_⟩⟩
  · exact uniformAngleSet_directions_mono_of_dyadic ω K.property.1 K.property.2.1
      n hn hmono.monotone hdyadic hmi ht
  · exact ⟨hi, hi'⟩

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
# Cap / Reflection
-/

public section

noncomputable section

namespace MovingSofa

/-- Reflect about the line through the origin and the distinguished parallelogram point. -/
@[expose]
def mirrorReflection (ω : ℝ) (p : Point) : Point :=
  (2 * inner ℝ p (stripParallelogram ω).2.2 /
    inner ℝ (stripParallelogram ω).2.2 (stripParallelogram ω).2.2) •
      (stripParallelogram ω).2.2 - p

/-- Reflect every interior wall direction about half the terminal angle. -/
@[expose]
def reflectedAngleSet (Θ : AngleSet) : AngleSet where
  angle := Θ.angle
  angle_pos := Θ.angle_pos
  angle_le := Θ.angle_le
  directions := Θ.directions.image (fun t ↦ Θ.angle - t)
  nonempty := Θ.nonempty.image _
  interior := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hs0, hsω⟩ := Θ.interior s hs
    constructor <;> linarith

private theorem mirrorReflection_eq_capReflection_m152940c (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    mirrorReflection ω = capReflection ω := by
  change stripTopReflection ω = capReflection ω
  exact stripTopReflection_eq_capReflection ω hω0 hωle

private theorem reflectedAngle_mem_polygonNormals (Θ : AngleSet) (a : Real.Angle)
    (ha : a ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪
      capLowerNormals Θ.angle) :
    reflectedAngle Θ.angle a ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain (reflectedAngleSet Θ)) ∪
        capLowerNormals Θ.angle := by
  rcases ha with ha | ha
  · obtain ⟨t, ht, rfl⟩ := ha
    left
    rw [reflectedAngle_coe]
    refine ⟨Θ.angle + Real.pi / 2 - t, ?_, rfl⟩
    simp only [angleDomain, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_coe] at ht ⊢
    rcases ht with (ht | ht) | ht
    · left
      right
      refine ⟨Θ.angle - t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, by ring⟩
    · obtain ⟨s, hs, rfl⟩ := ht
      left
      left
      exact Finset.mem_image.mpr ⟨s, hs, by ring⟩
    · rcases ht with rfl | rfl
      · exact Or.inr (Or.inr (by simp))
      · apply Or.inr
        apply Or.inl
        change Θ.angle + Real.pi / 2 - Real.pi / 2 = Θ.angle
        ring
  · right
    simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · right
      exact reflectedAngle_at_omega_add_pi Θ.angle
    · left
      exact reflectedAngle_at_three_pi_div_two Θ.angle

private theorem reflectedBody_polygonRepresentation (Θ : AngleSet)
    (K : PolygonCapSpace Θ) :
    HasHalfPlaneRepresentation (reflectedBody Θ.angle K.val.val)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain (reflectedAngleSet Θ)) ∪
        capLowerNormals Θ.angle) := by
  exact K.property.reflectedBody fun a ha ↦ reflectedAngle_mem_polygonNormals Θ a ha

private def reflectedPolygonCap (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    PolygonCapSpace (reflectedAngleSet Θ) :=
  ⟨⟨reflectedBody Θ.angle K.val.val, reflectedBody_isCap K.val⟩,
    reflectedBody_polygonRepresentation Θ K⟩

private theorem polygonNiche_reflection (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    polygonNiche (reflectedAngleSet Θ) (reflectedPolygonCap Θ K).val =
      capReflection Θ.angle '' polygonNiche Θ K.val := by
  unfold polygonNiche
  rw [Set.image_inter (capReflection Θ.angle).injective,
    capReflection_image_capFan]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    change p ∈ innerQuadrant (reflectedBody Θ.angle K.val.val) (Θ.angle - s) at hp
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨s, hs, ?_⟩, rfl⟩
    simpa only [sub_sub_cancel] using hq
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    apply Set.mem_iUnion₂.mpr
    refine ⟨Θ.angle - s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    change capReflection Θ.angle q ∈
      innerQuadrant (reflectedBody Θ.angle K.val.val) (Θ.angle - s)
    rw [innerQuadrant_reflection]
    exact ⟨q, by simpa only [sub_sub_cancel], rfl⟩

private theorem polygonAreaFunctional_reflectedPolygonCap
    (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    polygonAreaFunctional (reflectedAngleSet Θ) (reflectedPolygonCap Θ K).val =
      polygonAreaFunctional Θ K.val := by
  unfold polygonAreaFunctional
  rw [angleCap_eq_self, angleCap_eq_self, polygonNiche_reflection]
  change ClassicalResults.area (capReflection Θ.angle '' (K.val.val : Set Point)) -
      ClassicalResults.area (capReflection Θ.angle '' polygonNiche Θ K.val) = _
  rw [area_image_capReflection Θ.angle (K.val.val : Set Point)
      K.val.val.isCompact.measurableSet,
    area_image_capReflection Θ.angle (polygonNiche Θ K.val)
      (measurableSet_polygonNiche Θ K.val)]

private def reflectedPolygonCapBack (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) : PolygonCapSpace Θ :=
  ⟨⟨reflectedBody Θ.angle L.val.val, reflectedBody_isCap L.val⟩, by
    simpa [reflectedAngleSet, Finset.image_image] using
      reflectedBody_polygonRepresentation (reflectedAngleSet Θ) L⟩

private theorem polygonNiche_reflection_back (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) :
    polygonNiche Θ (reflectedPolygonCapBack Θ L).val =
      capReflection Θ.angle '' polygonNiche (reflectedAngleSet Θ) L.val := by
  unfold polygonNiche
  change capFan Θ.angle ∩
      (⋃ t ∈ Θ.directions, innerQuadrant (reflectedBody Θ.angle L.val.val) t) =
    capReflection Θ.angle ''
      (capFan Θ.angle ∩
        ⋃ t ∈ (reflectedAngleSet Θ).directions, innerQuadrant L.val.val t)
  rw [Set.image_inter (capReflection Θ.angle).injective,
    capReflection_image_capFan]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    change p ∈ innerQuadrant (reflectedBody Θ.angle L.val.val) t at hp
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨Θ.angle - t, ?_, hq⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_⟩
    rw [innerQuadrant_reflection]
    exact ⟨q, hq, rfl⟩

private theorem polygonAreaFunctional_reflectedPolygonCapBack (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) :
    polygonAreaFunctional Θ (reflectedPolygonCapBack Θ L).val =
      polygonAreaFunctional (reflectedAngleSet Θ) L.val := by
  unfold polygonAreaFunctional
  rw [angleCap_eq_self, angleCap_eq_self, polygonNiche_reflection_back]
  change ClassicalResults.area (capReflection Θ.angle '' (L.val.val : Set Point)) -
      ClassicalResults.area
        (capReflection Θ.angle '' polygonNiche (reflectedAngleSet Θ) L.val) = _
  rw [area_image_capReflection Θ.angle (L.val.val : Set Point)
      L.val.val.isCompact.measurableSet,
    area_image_capReflection Θ.angle (polygonNiche (reflectedAngleSet Θ) L.val)
      (measurableSet_polygonNiche (reflectedAngleSet Θ) L.val)]

private theorem mirrorReflection_stripTop (ω : ℝ) :
    mirrorReflection ω (stripParallelogram ω).2.2 =
      (stripParallelogram ω).2.2 := by
  change stripTopReflection ω (stripParallelogram ω).2.2 = _
  exact stripTopReflection_stripTop ω

theorem maximumPolygonCap_mirror (Θ : AngleSet) (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) :
    ∃ P : PolygonCapSpace (reflectedAngleSet Θ),
      (P.val.val : Set Point) = mirrorReflection Θ.angle '' (K.val.val : Set Point) ∧
      IsMaximumPolygonCap (reflectedAngleSet Θ) P := by
  let P := reflectedPolygonCap Θ K
  refine ⟨P, ?_, ?_⟩
  · change capReflection Θ.angle '' (K.val.val : Set Point) =
      mirrorReflection Θ.angle '' (K.val.val : Set Point)
    rw [mirrorReflection_eq_capReflection_m152940c Θ.angle Θ.angle_pos Θ.angle_le]
  · constructor
    · change (stripParallelogram Θ.angle).2.2 ∈
        capReflection Θ.angle '' (K.val.val : Set Point)
      refine ⟨(stripParallelogram Θ.angle).2.2, hK.1, ?_⟩
      rw [← mirrorReflection_eq_capReflection_m152940c Θ.angle Θ.angle_pos Θ.angle_le,
        mirrorReflection_stripTop]
    · intro L
      calc
        polygonAreaFunctional (reflectedAngleSet Θ) L.val =
            polygonAreaFunctional Θ (reflectedPolygonCapBack Θ L).val :=
          (polygonAreaFunctional_reflectedPolygonCapBack Θ L).symm
        _ ≤ polygonAreaFunctional Θ K.val := hK.2 (reflectedPolygonCapBack Θ L)
        _ = polygonAreaFunctional (reflectedAngleSet Θ) P.val :=
          (polygonAreaFunctional_reflectedPolygonCap Θ K).symm

private def castPolygonCap {Θ Φ : AngleSet} (h : Θ = Φ)
    (K : PolygonCapSpace Θ) : PolygonCapSpace Φ :=
  cast (congrArg PolygonCapSpace h) K

@[simp] private theorem castPolygonCap_coe {Θ Φ : AngleSet} (h : Θ = Φ)
    (K : PolygonCapSpace Θ) :
    ((castPolygonCap h K).val.val : Set Point) = (K.val.val : Set Point) := by
  subst h
  rfl

private theorem isMaximumPolygonCap_castPolygonCap {Θ Φ : AngleSet} (h : Θ = Φ)
    {K : PolygonCapSpace Θ} (hK : IsMaximumPolygonCap Θ K) :
    IsMaximumPolygonCap Φ (castPolygonCap h K) := by
  subst h
  exact hK

private theorem reflectedAngleSet_uniformAngleSet (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ) (hn : 2 ≤ n) :
    reflectedAngleSet (uniformAngleSet ω hω hω' n hn) =
      uniformAngleSet ω hω hω' n hn := by
  unfold reflectedAngleSet uniformAngleSet
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.mp hj
    apply Finset.mem_image.mpr
    refine ⟨n - j, Finset.mem_Ioo.mpr ⟨Nat.sub_pos_of_lt hjn, ?_⟩, ?_⟩
    · omega
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hjn.le]
    field_simp
  · intro ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.mp hj
    apply Finset.mem_image.mpr
    refine ⟨ω - (j : ℝ) / n * ω, ?_, by ring⟩
    apply Finset.mem_image.mpr
    refine ⟨n - j, Finset.mem_Ioo.mpr ⟨Nat.sub_pos_of_lt hjn, by omega⟩, ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hjn.le]
    field_simp

theorem balancedMaximumCap_mirror {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) :
    ∃ P : CapSpace ω,
      (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) ∧
      IsBalancedMaximumCap P := by
  obtain ⟨n, hn, hmono, hdyadic, Q, hQmax, hQlim⟩ := hK
  let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
  have hM : mirrorReflection ω = capReflection ω :=
    mirrorReflection_eq_capReflection_m152940c ω K.property.1 K.property.2.1
  have hmirror : (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) := by
    change capReflection ω '' (K.val : Set Point) = mirrorReflection ω '' (K.val : Set Point)
    rw [hM]
  refine ⟨P, hmirror, n, hn, hmono, hdyadic, ?_⟩
  have hR (i : ℕ) : ∃ R : PolygonCapSpace
      (uniformAngleSet ω P.property.1 P.property.2.1 (n i) (hn i)),
      (R.val.val : Set Point) = mirrorReflection ω '' (Q i).val.val ∧
        IsMaximumPolygonCap _ R := by
    have heq := reflectedAngleSet_uniformAngleSet ω K.property.1 K.property.2.1
      (n i) (hn i)
    let W := maximumPolygonCap_mirror _ (Q i) (hQmax i)
    let R := castPolygonCap heq W.choose
    refine ⟨R, ?_, ?_⟩
    · rw [castPolygonCap_coe]
      simpa [W, uniformAngleSet] using W.choose_spec.1
    · exact isMaximumPolygonCap_castPolygonCap heq W.choose_spec.2
  let R : ∀ i, PolygonCapSpace
      (uniformAngleSet ω P.property.1 P.property.2.1 (n i) (hn i)) :=
    fun i ↦ (hR i).choose
  refine ⟨R, ?_, ?_⟩
  · exact fun i ↦ (hR i).choose_spec.2
  · apply hQlim.congr'
    filter_upwards [] with i
    rw [(hR i).choose_spec.1, hmirror, hM]
    exact (Metric.hausdorffDist_image (capReflection ω).isometry).symm

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

* `Sofa.Support`.
* `Sofa.Cap`.
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
# Sofa / Support
-/

public section

noncomputable section

namespace MovingSofa

theorem standardPosition_subset_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : s ⊆ monotonization s ω := by
  have hω : ω ∈ Set.Ioc 0 (Real.pi / 2) := ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hcommon := movingSofa_commonSubset s ω hs.2.1 hω
  have hs_ne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  have hshape : s ⊆ (stripParallelogram ω).1 := by
    have htranslated :=
      (exists_standardPosition_translation s ω hs.2.1 hω).2.2.2 (0 : Point)
    have hstandard :
        IsStandardPosition ((fun p : Point ↦ p + (0 : Point)) '' s) ω := by
      simpa using hs
    simpa using htranslated hstandard
  rw [monotonization]
  intro p hp
  refine ⟨hshape hp, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  exact subset_supportingHallway s (t : Real.Angle) hs_ne hcommon.1
    (hcommon.2.2.2.1 t ht) hp

theorem standardPosition_subset_cap (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    s ⊆ monotonization s ω ∧ monotonization s ω ⊆ capOfSofa s ω := by
  refine ⟨standardPosition_subset_monotonization s ω hs, ?_⟩
  rw [monotonization, capOfSofa]
  rintro p ⟨hpP, hpL⟩
  refine ⟨hpP, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  apply supportingHallway_subset_outerQuadrant s (t : Real.Angle)
  exact Set.mem_iInter.1 (Set.mem_iInter.1 hpL t) ht

private theorem inner_le_supportValue_of_mem_capOfSofa {s : Set Point} {ω t : ℝ}
    (ht : t ∈ capUpperAngles ω) {p : Point} (hp : p ∈ capOfSofa s ω) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue s (t : Real.Angle) := by
  rcases ht with ht | ht
  · have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
    obtain ⟨q, hq, rfl⟩ := hq
    rw [inner_supportingPlacement_normalVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.1]
  · have ht' : t - Real.pi / 2 ∈ Set.Icc 0 ω := by
      constructor <;> linarith [ht.1, ht.2]
    have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 (t - Real.pi / 2)) ht'
    obtain ⟨q, hq, rfl⟩ := hq
    have ha : (t : Real.Angle) = ((t - Real.pi / 2 : ℝ) : Real.Angle) +
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add, sub_add_cancel]
    rw [ha, normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.2]

theorem standardPosition_support_eq (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    (∀ t ∈ capUpperAngles ω,
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle)) ∧
    (∀ t ∈ Set.Icc 0 ω,
      supportingHallway (monotonization s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle) ∧
      supportingHallway (capOfSofa s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle)) := by
  have hs_ne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hnorm := hs.2.2.2.2.1
    simp [he, supportValue] at hnorm
  obtain ⟨hsm, hmc⟩ := standardPosition_subset_cap s ω hs
  have hsupport (t : ℝ) (ht : t ∈ capUpperAngles ω) :
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) := by
    have hc (p : Point) (hp : p ∈ capOfSofa s ω) :=
      inner_le_supportValue_of_mem_capOfSofa ht hp
    exact ⟨supportValue_eq_of_subset_of_inner_le hs_ne hsm _ (fun p hp ↦ hc p (hmc hp)),
      supportValue_eq_of_subset_of_inner_le hs_ne (hsm.trans hmc) _ hc⟩
  refine ⟨hsupport, ?_⟩
  intro t ht
  have ht' : t + Real.pi / 2 ∈ capUpperAngles ω :=
    Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₀ := hsupport t (Or.inl ht)
  have h₁ := hsupport (t + Real.pi / 2) ht'
  simp only [Real.Angle.coe_add] at h₁
  constructor
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.1, h₁.1]
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.2, h₁.2]

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
# Sofa / Cap
-/

public section

noncomputable section

namespace MovingSofa

private theorem capOfSofa_halfPlaneRepresentation (s : Set Point) (ω : ℝ) (hω : 0 ≤ ω) :
    HasHalfPlaneRepresentation (capOfSofa s ω)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω) := by
  let U : Set (Real.Angle × ℝ) :=
    (fun t : ℝ ↦ ((t : Real.Angle), supportValue s (t : Real.Angle))) '' capUpperAngles ω
  let B : Set (Real.Angle × ℝ) :=
    {(((ω : ℝ) : Real.Angle), 1),
      (((Real.pi / 2 : ℝ) : Real.Angle), 1),
      (((ω + Real.pi : ℝ) : Real.Angle), 0),
      (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)}
  refine ⟨U ∪ B, ?_, ?_⟩
  · rintro c (hc | hc)
    · obtain ⟨t, ht, rfl⟩ := hc
      exact Or.inl ⟨t, ht, rfl⟩
    · rcases hc with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨ω, Or.inl ⟨hω, le_rfl⟩, rfl⟩
      · exact Or.inl ⟨Real.pi / 2, Or.inr ⟨le_rfl, le_add_of_nonneg_left hω⟩, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · ext p
    simp only [Set.mem_iInter]
    constructor
    · intro hp c hc
      rcases hc with hc | hc
      · obtain ⟨φ, hφ, rfl⟩ := hc
        change inner ℝ p (normalVector (φ : Real.Angle)) ≤ supportValue s _
        rcases hφ with hφ | hφ
        · have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 φ) hφ
          rw [(rotatingHallwayParts_formulas s (φ : Real.Angle)).2.2.2.2.2.2.2.1]
            at hout
          exact hout.1
        · let t := φ - Real.pi / 2
          have ht : t ∈ Set.Icc 0 ω := by
            constructor <;> dsimp [t] <;> linarith [hφ.1, hφ.2]
          have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
          rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
            at hout
          have hang : ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
              (φ : Real.Angle) := by
            rw [← Real.Angle.coe_add]
            congr 1
            dsimp [t]
            ring
          have hout' := hout.2
          change inner ℝ p (normalVector ((t : Real.Angle) +
            ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _ at hout'
          simpa [hang] using hout'
      · rcases hc with rfl | rfl | rfl | rfl
        · exact ((mem_stripParallelogram_iff ω p).1 hp.1).2.2
        · simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply,
            Fin.sum_univ_two] using ((mem_stripParallelogram_iff ω p).1 hp.1).1.2
        · change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ 0
          rw [normalVector_add_pi, inner_neg_right]
          exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).2.1
        · simpa [normalHalfPlane, inner_normalVector_three_pi_div_two] using
            neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).1.1
    · intro hp
      have hupper (φ : ℝ) (hφ : φ ∈ capUpperAngles ω) :
          inner ℝ p (normalVector (φ : Real.Angle)) ≤ supportValue s (φ : Real.Angle) :=
        hp ((φ : Real.Angle), supportValue s (φ : Real.Angle))
          (Or.inl ⟨φ, hφ, rfl⟩)
      have hω' := hp (((ω : ℝ) : Real.Angle), 1) (Or.inr (Or.inl rfl))
      have hπ := hp (((Real.pi / 2 : ℝ) : Real.Angle), 1)
        (Or.inr (Or.inr (Or.inl rfl)))
      have hlowerω := hp (((ω + Real.pi : ℝ) : Real.Angle), 0)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have hlowerπ := hp (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨(mem_stripParallelogram_iff ω p).2 ?_, ?_⟩
      · change inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1 at hω'
        change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 at hπ
        change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ 0 at hlowerω
        change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 at hlowerπ
        rw [normalVector_add_pi, inner_neg_right] at hlowerω
        rw [inner_normalVector_three_pi_div_two] at hlowerπ
        have hπ' : p 1 ≤ 1 := by
          simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hπ
        exact ⟨⟨by linarith, hπ'⟩, by linarith, hω'⟩
      · refine Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_
        rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
        refine ⟨hupper t (Or.inl ht), ?_⟩
        have hshift : t + Real.pi / 2 ∈ capUpperAngles ω :=
          Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        change inner ℝ p (normalVector ((t : Real.Angle) +
          ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _
        simpa only [Real.Angle.coe_add] using hupper (t + Real.pi / 2) hshift

private theorem isBounded_capOfSofa (s : Set Point) (ω : ℝ)
    (hω : 0 < ω) (hωπ : ω ≤ Real.pi / 2) : Bornology.IsBounded (capOfSofa s ω) := by
  let t := ω / 2
  let A := supportValue s (t : Real.Angle)
  let B := supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle)
  have ht : t ∈ Set.Icc 0 ω := by
    constructor <;> dsimp [t] <;> linarith
  have htI : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> dsimp [t] <;> linarith [Real.pi_pos]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo htI
  have hsine : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by dsimp [t]; linarith)
    (by dsimp [t]; linarith [Real.pi_pos])
  refine (isBounded_iff_forall_norm_le).2 ⟨|A / Real.cos t| +
    |B / Real.sin t| + 1, ?_⟩
  intro p hp
  have hstrip := (mem_stripParallelogram_iff ω p).1 hp.1
  have hout := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
    at hout
  have h₀ := hout.1
  have h₁ := hout.2
  change inner ℝ p (normalVector (t : Real.Angle)) ≤ A at h₀
  change inner ℝ p (normalVector ((t : Real.Angle) +
    ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ B at h₁
  rw [normalVector_add_pi_div_two] at h₁
  simp only [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h₀ h₁
  have hxhi : p 0 ≤ A / Real.cos t := (le_div_iff₀ hc).2 (by
    have := mul_nonneg hstrip.1.1 hsine.le
    nlinarith)
  have hxlo : -(B / Real.sin t) ≤ p 0 := by
    rw [← neg_div]
    apply (div_le_iff₀ hsine).2
    have := mul_nonneg hstrip.1.1 hc.le
    nlinarith
  have hxabs : |p 0| ≤ |A / Real.cos t| + |B / Real.sin t| := by
    rw [abs_le]
    constructor
    · calc
        -(|A / Real.cos t| + |B / Real.sin t|) ≤ -(B / Real.sin t) := by
          have hA := abs_nonneg (A / Real.cos t)
          have hB := le_abs_self (B / Real.sin t)
          linarith
        _ ≤ p 0 := hxlo
    · calc
        p 0 ≤ A / Real.cos t := hxhi
        _ ≤ |A / Real.cos t| + |B / Real.sin t| := by
          have hA := le_abs_self (A / Real.cos t)
          have hB := abs_nonneg (B / Real.sin t)
          linarith
  have hyabs : |p 1| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hstrip.1.1], hstrip.1.2⟩
  have hpdecomp : p = p 0 • (!₂[1, 0] : Point) + p 1 • !₂[0, 1] := by
    ext i
    fin_cases i <;> simp
  have he₀ : ‖(!₂[1, 0] : Point)‖ = 1 := by
    have h : (!₂[1, 0] : Point) = normalVector (0 : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame]
    rw [h]
    exact norm_normalVector_real 0
  have he₁ : ‖(!₂[0, 1] : Point)‖ = 1 := by
    have h : (!₂[0, 1] : Point) = normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame]
    rw [h]
    exact norm_normalVector_real (Real.pi / 2)
  rw [hpdecomp]
  calc
    ‖p 0 • (!₂[1, 0] : Point) + p 1 • !₂[0, 1]‖ ≤
        ‖p 0 • (!₂[1, 0] : Point)‖ + ‖p 1 • (!₂[0, 1] : Point)‖ := norm_add_le _ _
    _ = |p 0| + |p 1| := by simp [norm_smul, he₀, he₁]
    _ ≤ |A / Real.cos t| + |B / Real.sin t| + 1 := add_le_add hxabs hyabs

private theorem mem_capOfSofa_of_mem_strip_of_upper {s : Set Point} {ω : ℝ} {p : Point}
    (hp : p ∈ (stripParallelogram ω).1)
    (hupper : ∀ t ∈ capUpperAngles ω,
      inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue s (t : Real.Angle)) :
    p ∈ capOfSofa s ω := by
  refine ⟨hp, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.1]
  refine ⟨hupper t (Or.inl ht), ?_⟩
  have hshift : t + Real.pi / 2 ∈ capUpperAngles ω :=
    Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  change inner ℝ p (normalVector ((t : Real.Angle) +
    ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _
  simpa only [Real.Angle.coe_add] using hupper (t + Real.pi / 2) hshift

private theorem supportValue_eq_zero_of_nonpos_of_attains_zero (K : ConvexBody Point)
    (a : Real.Angle) (hupper : ∀ p ∈ K, inner ℝ p (normalVector a) ≤ 0)
    {q : Point} (hq : q ∈ K) (hqzero : inner ℝ q (normalVector a) = 0) :
    supportValue K a = 0 := by
  apply le_antisymm
  · exact supportValue_le_of_subset_normalHalfPlane K a 0 hupper
  · simpa only [hqzero] using inner_le_supportValue K hq a

private theorem standardPosition_right_cap_lower_support (s : Set Point)
    (hs : IsStandardPosition s (Real.pi / 2)) (K : ConvexBody Point)
    (hK : (K : Set Point) = capOfSofa s (Real.pi / 2))
    (hs_ne : s.Nonempty) :
    supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨p, hp, hpeq⟩ := (hs.1.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (hs_ne.image
        (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hpT : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue s _ at hpeq
    simpa only [hs.2.2.2.2.2] using hpeq
  let q := p - tangentVector (0 : Real.Angle)
  have hqy : q 1 = 0 := by
    have hpcoord : p 1 = 1 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hpT
    simp [q, tangentVector, frame, hpcoord]
  have hqP : q ∈ (stripParallelogram (Real.pi / 2)).1 := by
    rw [mem_stripParallelogram_iff]
    have hqn : inner ℝ q
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hqy
    exact ⟨⟨by rw [hqy], by rw [hqy]; norm_num⟩,
      by rw [hqn], by rw [hqn]; norm_num⟩
  have hq : q ∈ capOfSofa s (Real.pi / 2) := by
    apply mem_capOfSofa_of_mem_strip_of_upper hqP
    intro u hu
    have hsu : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi
      (by rcases hu with hu | hu <;> linarith [hu.1])
      (by rcases hu with hu | hu <;> linarith [hu.2, Real.pi_pos])
    calc
      inner ℝ q (normalVector (u : Real.Angle)) =
          inner ℝ p (normalVector (u : Real.Angle)) - Real.sin u := by
            simp [q, tangentVector, normalVector, frame, PiLp.inner_apply,
              Fin.sum_univ_two]
            ring
      _ ≤ inner ℝ p (normalVector (u : Real.Angle)) := sub_le_self _ hsu
      _ ≤ supportValue s (u : Real.Angle) :=
        inner_le_supportValue_of_isCompact hs.1 hp _
  apply supportValue_eq_zero_of_nonpos_of_attains_zero K
  · intro z hz
    change z ∈ (K : Set Point) at hz
    rw [hK] at hz
    have hz0 := ((mem_stripParallelogram_iff (Real.pi / 2) z).1 hz.1).1.1
    simpa [inner_normalVector_three_pi_div_two] using neg_nonpos.mpr hz0
  · exact hK.symm ▸ hq
  · simpa [inner_normalVector_three_pi_div_two] using congrArg Neg.neg hqy

theorem standardPosition_cap (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    ∃ K : CapSpace ω, (K.val : Set Point) = capOfSofa s ω := by
  have hs_ne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  have hω0 : 0 ≤ ω := hs.2.2.1.le
  obtain ⟨D, hDN, hC⟩ := capOfSofa_halfPlaneRepresentation s ω hω0
  have hclosed : IsClosed (capOfSofa s ω) := by
    rw [hC]
    exact isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
      isClosed_normalHalfPlane c.1 c.2 false
  have hconvex : Convex ℝ (capOfSofa s ω) := by
    rw [hC]
    exact convex_iInter fun c ↦ convex_iInter fun _ ↦
      convex_normalHalfPlane c.1 c.2 false
  have hscap : s ⊆ capOfSofa s ω :=
    let h := standardPosition_subset_cap s ω hs
    h.1.trans h.2
  have hne : (capOfSofa s ω).Nonempty := hs_ne.mono hscap
  let K : ConvexBody Point := {
    carrier := capOfSofa s ω
    convex' := hconvex
    isCompact' := Metric.isCompact_iff_isClosed_bounded.2
      ⟨hclosed, isBounded_capOfSofa s ω hs.2.2.1 hs.2.2.2.1⟩
    nonempty' := hne }
  have hsupport := (standardPosition_support_eq s ω hs).1
  have hKω : supportValue K (ω : Real.Angle) = 1 := by
    change supportValue (capOfSofa s ω) (ω : Real.Angle) = 1
    rw [(hsupport ω (Or.inl ⟨hω0, le_rfl⟩)).2, hs.2.2.2.2.1]
  have hKπ : supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    change supportValue (capOfSofa s ω) ((Real.pi / 2 : ℝ) : Real.Angle) = 1
    rw [(hsupport (Real.pi / 2) (Or.inr ⟨le_rfl,
      le_add_of_nonneg_left hω0⟩)).2, hs.2.2.2.2.2]
  by_cases hright : ω = Real.pi / 2
  · subst ω
    have hbottom := standardPosition_right_cap_lower_support s hs K rfl hs_ne
    have hsame : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    refine ⟨⟨K, hs.2.2.1, hs.2.2.2.1, hKω, hKπ, ?_, hbottom,
      ⟨D, hDN, ?_⟩⟩, rfl⟩
    · simpa [hsame] using hbottom
    · exact hC
  · have hlt : ω < Real.pi / 2 := lt_of_le_of_ne hs.2.2.2.1 hright
    let o := (stripParallelogram ω).2.2
    have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hs.2.2.1, Real.pi_pos], hlt⟩
    obtain ⟨pω, hpω, hpωeq⟩ := (hs.1.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
        (hs_ne.image (fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))))
    obtain ⟨pT, hpT, hpTeq⟩ := (hs.1.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
        (hs_ne.image
          (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
    have hpω' : inner ℝ pω (normalVector (ω : Real.Angle)) = 1 := by
      change inner ℝ pω (normalVector (ω : Real.Angle)) = supportValue s _ at hpωeq
      simpa only [hs.2.2.2.2.1] using hpωeq
    have hpT' : inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
      change inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue s _ at hpTeq
      simpa only [hs.2.2.2.2.2] using hpTeq
    have hpωT : inner ℝ pω (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
      simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using
        ((mem_stripParallelogram_iff ω pω).1 (hscap hpω).1).1.2
    have hpTω : inner ℝ pT (normalVector (ω : Real.Angle)) ≤ 1 :=
      ((mem_stripParallelogram_iff ω pT).1
        (hscap hpT).1).2.2
    have hoω : inner ℝ o (normalVector (ω : Real.Angle)) = 1 := by
      have hgap : Real.tan (Real.pi / 4 - ω / 2) =
          (Real.cos ω)⁻¹ - Real.tan ω := by
        simpa [show Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 by ring]
          using Real.tan_pi_div_two_sub_div_two ω ⟨hω0, hlt⟩
      have htan := Real.tan_eq_sin_div_cos ω
      simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
      field_simp [hc.ne']
      ring
    have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
      simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
    have hou (u : ℝ) (hu : u ∈ capUpperAngles ω) :
        inner ℝ o (normalVector (u : Real.Angle)) ≤ supportValue s (u : Real.Angle) := by
      rcases hu with hu | hu
      · let c := Real.cos u / Real.cos ω
        let d := Real.sin (ω - u) / Real.cos ω
        have hd0 : 0 ≤ d := div_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hu.2)
            (by linarith [hu.1, hs.2.2.2.1, Real.pi_pos])) hc.le
        have hdecomp : normalVector (u : Real.Angle) =
            c • normalVector (ω : Real.Angle) -
              d • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
          ext i
          fin_cases i
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
            ring
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoω, hoT]
        apply (inner_le_supportValue_of_isCompact hs.1 hpω (u : Real.Angle)).trans'
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpω']
        simpa only [mul_one] using
          sub_le_sub_left (mul_le_mul_of_nonneg_left hpωT hd0) c
      · let c := Real.sin (u - ω) / Real.cos ω
        let d := -Real.cos u / Real.cos ω
        have hd0 : 0 ≤ d := div_nonneg
          (neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le hu.1
            (by linarith [hu.2, hs.2.2.2.1, Real.pi_pos]))) hc.le
        have hdecomp : normalVector (u : Real.Angle) =
            c • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) -
              d • normalVector (ω : Real.Angle) := by
          ext i
          fin_cases i
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
          · simp [c, d, normalVector, frame, Real.sin_sub]
            field_simp [hc.ne']
            ring
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoT, hoω]
        apply (inner_le_supportValue_of_isCompact hs.1 hpT (u : Real.Angle)).trans'
        rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpT']
        simpa only [mul_one] using
          sub_le_sub_left (mul_le_mul_of_nonneg_left hpTω hd0) c
    let q₀ := o - tangentVector (0 : Real.Angle)
    have hsinω0 : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω0
      (by linarith [hs.2.2.2.1, Real.pi_pos])
    have hsinω1 : Real.sin ω ≤ 1 := Real.sin_le_one ω
    have hq₀P : q₀ ∈ (stripParallelogram ω).1 := by
      rw [mem_stripParallelogram_iff]
      have hq₀y : q₀ 1 = 0 := by
        simp [q₀, o, stripParallelogram, tangentVector, frame]
      have hq₀n : inner ℝ q₀ (normalVector (ω : Real.Angle)) = 1 - Real.sin ω := by
        rw [inner_sub_left, hoω]
        simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      exact ⟨⟨by rw [hq₀y], by rw [hq₀y]; norm_num⟩,
        by rw [hq₀n]; exact sub_nonneg.mpr hsinω1,
        by rw [hq₀n]; linarith⟩
    have hq₀ : q₀ ∈ capOfSofa s ω := by
      apply mem_capOfSofa_of_mem_strip_of_upper hq₀P
      intro u hu
      have hsu : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi
        (by rcases hu with hu | hu <;> linarith [hu.1])
        (by rcases hu with hu | hu <;> linarith [hu.2, hs.2.2.2.1])
      calc
        inner ℝ q₀ (normalVector (u : Real.Angle)) =
            inner ℝ o (normalVector (u : Real.Angle)) - Real.sin u := by
              simp [q₀, tangentVector, normalVector, frame, PiLp.inner_apply,
                Fin.sum_univ_two]
              ring
        _ ≤ inner ℝ o (normalVector (u : Real.Angle)) := sub_le_self _ hsu
        _ ≤ supportValue s (u : Real.Angle) := hou u hu
    let qω := o - normalVector (ω : Real.Angle)
    have hqωP : qω ∈ (stripParallelogram ω).1 := by
      rw [mem_stripParallelogram_iff]
      have hqωn : inner ℝ qω (normalVector (ω : Real.Angle)) = 0 := by
        rw [inner_sub_left, hoω, inner_normalVector_self]
        norm_num
      have hqωy : qω 1 = 1 - Real.sin ω := by
        simp [qω, o, stripParallelogram, normalVector, frame]
      exact ⟨⟨by rw [hqωy]; linarith, by rw [hqωy]; linarith⟩,
        by rw [hqωn], by rw [hqωn]; norm_num⟩
    have hqω : qω ∈ capOfSofa s ω := by
      apply mem_capOfSofa_of_mem_strip_of_upper hqωP
      intro u hu
      have hcos : 0 ≤ Real.cos (ω - u) := Real.cos_nonneg_of_mem_Icc
        ⟨by rcases hu with hu | hu <;> linarith [hu.2, hs.2.2.2.1],
          by rcases hu with hu | hu <;> linarith [hu.1, hs.2.2.1]⟩
      calc
        inner ℝ qω (normalVector (u : Real.Angle)) =
            inner ℝ o (normalVector (u : Real.Angle)) - Real.cos (ω - u) := by
              simp [qω, inner_sub_left, inner_normalVector_normalVector]
        _ ≤ inner ℝ o (normalVector (u : Real.Angle)) := sub_le_self _ hcos
        _ ≤ supportValue s (u : Real.Angle) := hou u hu
    have hlowerT : supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
      apply supportValue_eq_zero_of_nonpos_of_attains_zero K
      · intro p hp
        change p ∈ capOfSofa s ω at hp
        have := ((mem_stripParallelogram_iff ω p).1 hp.1).1.1
        simpa [inner_normalVector_three_pi_div_two] using neg_nonpos.mpr this
      · exact hq₀
      · simp [q₀, o, stripParallelogram, inner_normalVector_three_pi_div_two,
          tangentVector, frame]
    have hlowerω : supportValue K ((ω + Real.pi : ℝ) : Real.Angle) = 0 := by
      apply supportValue_eq_zero_of_nonpos_of_attains_zero K
      · intro p hp
        change p ∈ capOfSofa s ω at hp
        rw [normalVector_add_pi, inner_neg_right]
        exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp.1).2.1
      · exact hqω
      · rw [normalVector_add_pi, inner_neg_right]
        have hqωn : inner ℝ qω (normalVector (ω : Real.Angle)) = 0 := by
          rw [inner_sub_left, hoω, inner_normalVector_self]
          norm_num
        rw [hqωn, neg_zero]
    exact ⟨⟨K, hs.2.2.1, hs.2.2.2.1, hKω, hKπ, hlowerω, hlowerT,
      ⟨D, hDN, hC⟩⟩, rfl⟩

theorem standardPosition_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) (K : CapSpace ω)
    (hK : (K.val : Set Point) = capOfSofa s ω) :
    monotonization s ω = (K.val : Set Point) \ capNiche K := by
  have hsupport := (standardPosition_support_eq s ω hs).1
  have hparts (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
      supportingHallway s (t : Real.Angle) =
        (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant \
          innerQuadrant (K.val : Set Point) t := by
    obtain ⟨h, _⟩ := rotatingHallwayParts_formulas s (t : Real.Angle)
    have h₀ := (hsupport t (Or.inl ht)).2
    have ht' : t + Real.pi / 2 ∈ capUpperAngles ω :=
      Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h₁ := (hsupport (t + Real.pi / 2) ht').2
    simp only [Real.Angle.coe_add] at h₁
    rw [h, rotatingHallwayParts_innerQuadrant]
    simp only [innerQuadrant, hK, h₀, h₁, Real.Angle.coe_add]
  ext p
  constructor
  · intro hp
    have hpH (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
        p ∈ (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant \
          innerQuadrant (K.val : Set Point) t := by
      rw [← hparts t ht]
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
    have hpK : p ∈ (K.val : Set Point) := by
      rw [hK]
      exact ⟨hp.1, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ (hpH t ht).1⟩
    refine ⟨hpK, ?_⟩
    rintro ⟨_, hN⟩
    obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hN
    exact (hpH t ⟨ht.1.le, ht.2.le⟩).2 hq
  · rintro ⟨hpK, hpN⟩
    have hpC : p ∈ capOfSofa s ω := hK ▸ hpK
    have hpF := K.subset_capFan hpK
    refine ⟨hpC.1, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    rw [hparts t ht]
    refine ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hpC.2 t) ht, ?_⟩
    intro hq
    have ht0 : t ≠ 0 := by
      rintro rfl
      have h := hq.2
      change inner ℝ p (normalVector ((0 + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K.val ((0 + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
      rw [zero_add, K.property.2.2.2.1] at h
      have hf := hpF.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hf
      linarith
    have htω : t ≠ ω := by
      intro he
      subst t
      have h := hq.1
      change inner ℝ p (normalVector (ω : Real.Angle)) <
        supportValue K.val (ω : Real.Angle) - 1 at h
      rw [K.property.2.2.1] at h
      have hf := hpF.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hf
      linarith
    exact hpN ⟨hpF, Set.mem_iUnion₂.mpr
      ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htω⟩, hq⟩⟩

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

* `Cap.Connectedness`.
* `Cap.MirrorFeatures`.
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
# Cap / Connectedness
-/

public section

noncomputable section

namespace MovingSofa

private theorem isOpen_capNiche_subtype {ω : ℝ} (K : CapSpace ω) :
    IsOpen {p : capFan ω | (p : Point) ∈ capNiche K} := by
  let U : Set Point := ⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.val : Set Point) t
  have hU : IsOpen U := isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ by
    apply IsOpen.inter
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  have heq : {p : capFan ω | (p : Point) ∈ capNiche K} =
      Subtype.val ⁻¹' U := by
    ext p
    change ((p : Point) ∈ capNiche K) ↔ (p : Point) ∈ U
    simp only [capNiche, Set.mem_inter_iff, p.property, true_and, U]
  rw [heq]
  exact hU.preimage continuous_subtype_val

private theorem capNiche_disjoint_upperBoundary_of_subset {ω : ℝ} (K : CapSpace ω)
    (hsub : capNiche K ⊆ (K.val : Set Point)) :
    Disjoint (capNiche K) (capUpperBoundary K) := by
  rw [Set.disjoint_left]
  intro p hpN hpδ
  let z : capFan ω := ⟨p, hpN.1⟩
  have hzopen : z ∈ {q : capFan ω | (q : Point) ∈ capNiche K} := hpN
  have hzint : z ∈ interior {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (isOpen_capNiche_subtype K |>.mem_nhds hzopen)
      (fun q hq ↦ hsub hq)
  have hzfront : z ∈ frontier {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
    rw [capUpperBoundary_relativeBoundary] at hpδ
    obtain ⟨q, hq, hqp⟩ := hpδ
    have : q = z := Subtype.ext hqp
    simpa [this] using hq
  have hzK : z ∈ {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := hsub hpN
  exact (mem_frontier_iff_notMem_interior hzK).1 hzfront hzint

private theorem mem_interior_capFan_of_pos {ω : ℝ} {p : Point}
    (hω : 0 < inner ℝ p (normalVector (ω : Real.Angle)))
    (hπ : 0 < inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))) :
    p ∈ interior (capFan ω) := by
  let U := normalHalfPlane (ω : Real.Angle) 0 true true ∩
    normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true true
  have hU : IsOpen U := (isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt continuous_const (by fun_prop))
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · exact ⟨hω, hπ⟩
  · rintro q ⟨hqω, hqπ⟩
    change 0 < inner ℝ q (normalVector (ω : Real.Angle)) at hqω
    change 0 < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqπ
    change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) ∧
      0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    exact ⟨hqω.le, hqπ.le⟩

private theorem innerCorner_mem_interior_capFan_of_mem_capWedge {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω) {q : Point} (hq : q ∈ capWedge K t) :
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω) := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  rcases hq with ⟨hqFan, hqQuad⟩
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  change q ∈ supportingPlacement (K.val : Set Point) (t : Real.Angle) ''
    hallwayParts.innerQuadrant at hqQuad
  obtain ⟨a, ha, hqa⟩ := hqQuad
  change a 0 < 0 ∧ a 1 < 0 at ha
  have hqQuad : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    constructor
    · rw [← hqa, inner_supportingPlacement_normalVector]
      linarith [ha.1]
    · rw [← hqa, inner_supportingPlacement_tangentVector]
      change a 1 + supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 < _
      linarith [ha.2]
  let d := q - z
  have hdu : inner ℝ d (normalVector (t : Real.Angle)) < 0 := by
    rw [inner_sub_left]
    linarith [hqQuad.1, hzu]
  have hdv : inner ℝ d (tangentVector (t : Real.Angle)) < 0 := by
    rw [inner_sub_left]
    linarith [hqQuad.2, hzv]
  have hdφ (φ : ℝ) : inner ℝ d (normalVector (φ : Real.Angle)) =
      inner ℝ d (normalVector (t : Real.Angle)) * Real.cos (φ - t) +
        inner ℝ d (tangentVector (t : Real.Angle)) * Real.sin (φ - t) := by
    nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul d (t : Real.Angle)]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_normalVector]
    have hc : Real.cos (t - φ) = Real.cos (φ - t) := by
      rw [show t - φ = -(φ - t) by ring, Real.cos_neg]
    rw [hc]
    have hs : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.sin (φ - t) := by
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_sub]
      ring
    rw [hs]
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos], by linarith [ht.1, K.property.2.1]⟩
  apply mem_interior_capFan_of_pos
  · change 0 < inner ℝ z (normalVector (ω : Real.Angle))
    have hdω : inner ℝ d (normalVector (ω : Real.Angle)) < 0 := by
      rw [hdφ]
      exact add_neg (mul_neg_of_neg_of_pos hdu hcosδ)
        (mul_neg_of_neg_of_pos hdv hsinδ)
    have hqω : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) := hqFan.1
    change inner ℝ (q - z) (normalVector (ω : Real.Angle)) < 0 at hdω
    rw [inner_sub_left] at hdω
    linarith
  · change 0 < inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    have hdπ : inner ℝ d (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 := by
      rw [hdφ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      exact add_neg (mul_neg_of_neg_of_pos hdu hsint)
        (mul_neg_of_neg_of_pos hdv hcost)
    have hqπ : 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hqFan.2
    change inner ℝ (q - z) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 at hdπ
    rw [inner_sub_left] at hdπ
    linarith

private theorem exists_mem_capNiche_not_mem_of_innerCorner {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω)
    (hzFan : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω))
    (hzK : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
      (K.val : Set Point)) :
    ∃ q, q ∈ capNiche K ∧ q ∉ (K.val : Set Point) := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzFan
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp K.val.isClosed.isOpen_compl z hzK
  let e := min ε δ / 2
  have he : 0 < e := half_pos (lt_min hε hδ)
  let q := z - e • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  have hdist : dist q z = e := by
    simp [q, norm_smul, norm_normalVector_real, abs_of_pos he]
  have hqFan : q ∈ capFan ω := interior_subset (hεball (by
    change dist q z < ε
    rw [hdist]
    dsimp [e]
    linarith [min_le_left ε δ]))
  have hqK : q ∉ (K.val : Set Point) := hδball (by
    change dist q z < δ
    rw [hdist]
    dsimp [e]
    linarith [min_le_right ε δ])
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    simpa [z, rotatingHallwayParts, hallwayParts] using
      inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hquad : q ∈ innerQuadrant (K.val : Set Point) t := by
    constructor
    · change inner ℝ q (normalVector (t : Real.Angle)) < _
      dsimp [q]
      rw [inner_sub_left, real_inner_smul_left, hzu]
      simp [normalVector, frame, PiLp.inner_apply]
      nlinarith
    · change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
        normalVector_add_pi_div_two]
      dsimp [q]
      rw [inner_sub_left, real_inner_smul_left, hzv]
      simp [normalVector, tangentVector, frame, PiLp.inner_apply]
      nlinarith
  exact ⟨q, ⟨hqFan, Set.mem_iUnion₂.mpr ⟨t, ht, hquad⟩⟩, hqK⟩

private theorem verticalLine_disjoint_cap_diff_niche_of_innerCorner {ω t : ℝ}
    (K : CapSpace ω) (ht : t ∈ Set.Ioo 0 ω)
    (hzFan : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      interior (capFan ω))
    (hzK : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
      (K.val : Set Point)) {q : Point}
    (hq : q ∈ (K.val : Set Point) \ capNiche K) :
    q 0 ≠ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner 0 := by
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  intro hx
  change q 0 = z 0 at hx
  by_cases hy : z 1 ≤ q 1
  · have hnot : ¬ ∀ u ∈ capUpperAngles ω,
        inner ℝ z (normalVector (u : Real.Angle)) ≤ supportValue K.val (u : Real.Angle) := by
      intro hall
      exact hzK (K.mem_of_mem_capFan_of_le_supportValue (interior_subset hzFan) hall)
    push Not at hnot
    obtain ⟨u, hu, hzu⟩ := hnot
    have huI : u ∈ Set.Icc 0 (ω + Real.pi / 2) := by
      rcases hu with hu | hu
      · exact ⟨hu.1, hu.2.trans (le_add_of_nonneg_right (by positivity))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hu.1, hu.2⟩
    have hsin : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi huI.1
      (huI.2.trans (by linarith [K.property.2.1, Real.pi_pos]))
    have hinner : inner ℝ z (normalVector (u : Real.Angle)) ≤
        inner ℝ q (normalVector (u : Real.Angle)) := by
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hx]
      nlinarith [mul_le_mul_of_nonneg_left hy hsin]
    have hqle := inner_le_supportValue K.val hq.1 (u : Real.Angle)
    linarith
  · have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
        supportValue K.val (t : Real.Angle) - 1 := by
      simpa [z, rotatingHallwayParts, hallwayParts] using
        inner_supportingPlacement_normalVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
    have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
      simpa [z, rotatingHallwayParts, hallwayParts] using
        inner_supportingPlacement_tangentVector (K.val : Set Point) (t : Real.Angle) (0 : Point)
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, K.property.2.1, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
    apply hq.2
    refine ⟨K.subset_capFan hq.1, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    constructor
    · change inner ℝ q (normalVector (t : Real.Angle)) < _
      simp [normalVector, frame, PiLp.inner_apply] at hzu ⊢
      nlinarith
    · change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
        normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply] at hzv ⊢
      nlinarith

private theorem exists_upperBoundary_segment_subset_diff {ω : ℝ} (K : CapSpace ω)
    {p : Point} (hp : p ∈ (K.val : Set Point) \ capNiche K) :
    ∃ q ∈ capUpperBoundary K, segment ℝ p q ⊆ (K.val : Set Point) \ capNiche K := by
  let F : Set Point := (K.val : Set Point) ∩ {q | q 0 = p 0}
  have hFc : IsCompact F := K.val.isCompact.inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hpF : p ∈ F := ⟨hp.1, rfl⟩
  obtain ⟨q, hqF, hqmax⟩ := hFc.exists_isMaxOn ⟨p, hpF⟩
    (by fun_prop : Continuous (fun q : Point ↦ q 1)).continuousOn
  have hqK : q ∈ (K.val : Set Point) := hqF.1
  have hqδ : q ∈ capUpperBoundary K := by
    rw [capUpperBoundary_relativeBoundary]
    let z : capFan ω := ⟨q, K.subset_capFan hqK⟩
    have hzK : z ∈ {w : capFan ω | (w : Point) ∈ (K.val : Set Point)} := hqK
    refine ⟨z, (mem_frontier_iff_notMem_interior hzK).2 ?_, rfl⟩
    intro hzint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzint
    let r : Point := q + (ε / 2) • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
    have hrFan : r ∈ capFan ω := by
      constructor
      · change 0 ≤ inner ℝ r (normalVector (ω : Real.Angle))
        dsimp [r]
        rw [inner_add_left, real_inner_smul_left, inner_normalVector_normalVector]
        have hsin : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi K.property.1.le
          (K.property.2.1.trans (by linarith [Real.pi_pos]))
        have := (K.subset_capFan hqK).1
        change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) at this
        rw [Real.cos_pi_div_two_sub]
        positivity
      · change 0 ≤ inner ℝ r (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        dsimp [r]
        rw [inner_add_left, real_inner_smul_left, inner_normalVector_self]
        have := (K.subset_capFan hqK).2
        change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
        linarith
    have hrball : (⟨r, hrFan⟩ : capFan ω) ∈ Metric.ball z ε := by
      change dist r q < ε
      simp [r, norm_smul, norm_normalVector_real, abs_of_pos hε]
      linarith
    have hrK := interior_subset (hball hrball)
    have hrF : r ∈ F := ⟨hrK, by simpa [r, normalVector, frame] using hqF.2⟩
    have := hqmax hrF
    simp [r, normalVector, frame] at this
    linarith
  refine ⟨q, hqδ, ?_⟩
  intro x hx
  have hxK := K.val.convex.segment_subset hp.1 hqK hx
  refine ⟨hxK, ?_⟩
  intro hxN
  have hxFan := hxN.1
  obtain ⟨u, hu, hxQuad⟩ := Set.mem_iUnion₂.mp hxN.2
  have hxp0 : x 0 = p 0 := by
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    simp only [Fin.isValue, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    rw [hqF.2]
    ring
  have hpx1 : p 1 ≤ x 1 := by
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hpq := hqmax hpF
    simp [AffineMap.lineMap_apply_module]
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hpq)]
  apply hp.2
  refine ⟨K.subset_capFan hp.1, Set.mem_iUnion₂.mpr ⟨u, hu, ?_⟩⟩
  rcases hxQuad with ⟨hxU, hxV⟩
  constructor
  · change inner ℝ p (normalVector (u : Real.Angle)) < _
    change inner ℝ x (normalVector (u : Real.Angle)) < _ at hxU
    have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1
      (by linarith [hu.2, K.property.2.1, Real.pi_pos])
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      gt_iff_lt] at hxU ⊢
    rw [hxp0] at hxU
    nlinarith [mul_le_mul_of_nonneg_left hpx1 hs.le]
  · change inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) < _
    change inner ℝ x (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) < _ at hxV
    have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hu.1], hu.2.trans_le K.property.2.1⟩
    rw [show ((u + Real.pi / 2 : ℝ) : Real.Angle) =
      (u : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hxV ⊢
    simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
      Fin.isValue, Matrix.cons_val_zero, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_add_lt_iff_lt_add, gt_iff_lt] at hxV ⊢
    rw [hxp0] at hxV
    nlinarith [mul_le_mul_of_nonneg_left hpx1 hc.le]

theorem cap_niche_connected_iff {ω : ℝ} (K : CapSpace ω) :
    (capNiche K ⊆ (K.val : Set Point) ↔
      capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K) ∧
    (capNiche K ⊆ (K.val : Set Point) \ capUpperBoundary K ↔
      ∀ t ∈ Set.Ioo 0 ω,
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
          interior (capFan ω) ∨
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
          (K.val : Set Point)) ∧
    ((∀ t ∈ Set.Ioo 0 ω,
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∉
          interior (capFan ω) ∨
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
          (K.val : Set Point)) ↔
      IsConnected ((K.val : Set Point) \ capNiche K)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hsub p hp
      refine ⟨hsub hp, ?_⟩
      exact fun hpδ ↦
        Set.disjoint_left.mp (capNiche_disjoint_upperBoundary_of_subset K hsub) hp hpδ
    · intro hsub p hp
      exact (hsub hp).1
  · constructor
    · intro hsub t ht
      by_cases hzFan : (rotatingHallwayParts (K.val : Set Point)
          (t : Real.Angle)).innerCorner ∈ interior (capFan ω)
      · right
        by_contra hzK
        obtain ⟨q, hqN, hqK⟩ :=
          exists_mem_capNiche_not_mem_of_innerCorner K ht hzFan hzK
        exact hqK (hsub hqN).1
      · exact Or.inl hzFan
    · intro hcorner p hp
      have hpFan := hp.1
      obtain ⟨t, ht, hpQuad⟩ := Set.mem_iUnion₂.mp hp.2
      have hpWedge : p ∈ capWedge K t := ⟨hpFan, by
        change p ∈ innerQuadrant (K.val : Set Point) t at hpQuad
        have hf := rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
        rw [hf.2.2.2.2.2.2.2.2]
        exact hpQuad⟩
      rcases hcorner t ht with hzout | hzK
      · exact False.elim (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K ht hpWedge))
      · have hpK := capWedge_subset_of_innerCorner_mem K t ht hzK hpWedge
        refine ⟨hpK, ?_⟩
        exact fun hpδ ↦ Set.disjoint_left.mp
          (capNiche_disjoint_upperBoundary_of_subset K fun q hq ↦ by
            have hqFan := hq.1
            obtain ⟨u, hu, hqQuad⟩ := Set.mem_iUnion₂.mp hq.2
            have hqWedge : q ∈ capWedge K u := ⟨hqFan, by
              have hf := rotatingHallwayParts_formulas (K.val : Set Point) (u : Real.Angle)
              rw [hf.2.2.2.2.2.2.2.2]
              exact hqQuad⟩
            rcases hcorner u hu with hzout | hzmem
            · exact False.elim
                (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K hu hqWedge))
            · exact capWedge_subset_of_innerCorner_mem K u hu hzmem hqWedge) hp hpδ
  · constructor
    · intro hcorner
      have hsub : capNiche K ⊆ (K.val : Set Point) := by
        intro p hp
        have hpFan := hp.1
        obtain ⟨t, ht, hpQuad⟩ := Set.mem_iUnion₂.mp hp.2
        have hpWedge : p ∈ capWedge K t := ⟨hpFan, by
          have hf := rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)
          rw [hf.2.2.2.2.2.2.2.2]
          exact hpQuad⟩
        rcases hcorner t ht with hzout | hzmem
        · exact False.elim
            (hzout (innerCorner_mem_interior_capFan_of_mem_capWedge K ht hpWedge))
        · exact capWedge_subset_of_innerCorner_mem K t ht hzmem hpWedge
      have hδS : capUpperBoundary K ⊆ (K.val : Set Point) \ capNiche K := by
        intro q hq
        have hqK : q ∈ (K.val : Set Point) := by
          obtain ⟨t, ht, hqedge⟩ := Set.mem_iUnion₂.mp hq
          exact hqedge.1
        exact ⟨hqK, fun hqN ↦
          Set.disjoint_left.mp (capNiche_disjoint_upperBoundary_of_subset K hsub) hqN hq⟩
      obtain ⟨l, r, hlK, -, hl, -⟩ := exists_horizontal_extrema K.val
      have hlS : l ∈ (K.val : Set Point) \ capNiche K := ⟨hlK, fun hlN ↦ by
        have := (capNiche_subset_rectangle K hlN).1
        linarith⟩
      obtain ⟨q₀, hq₀δ, hseg₀⟩ := exists_upperBoundary_segment_subset_diff K hlS
      let S : Set Point := (K.val : Set Point) \ capNiche K
      let f : S → Point := fun p ↦ Classical.choose
        (exists_upperBoundary_segment_subset_diff K p.property)
      have hfδ (p : S) : f p ∈ capUpperBoundary K :=
        (Classical.choose_spec (exists_upperBoundary_segment_subset_diff K p.property)).1
      have hfseg (p : S) : segment ℝ (p : Point) (f p) ⊆ S :=
        (Classical.choose_spec (exists_upperBoundary_segment_subset_diff K p.property)).2
      let A : S → Set Point := fun p ↦ capUpperBoundary K ∪ segment ℝ (p : Point) (f p)
      have hA (p : S) : IsPreconnected (A p) := by
        apply IsPreconnected.union' ⟨f p, hfδ p, right_mem_segment ℝ _ _⟩
        · exact (capUpperBoundary_connected K).isPreconnected
        · exact (convex_segment (𝕜 := ℝ) (p : Point) (f p)).isPreconnected
      have hcommon : (⋂ p, A p).Nonempty := by
        refine ⟨q₀, Set.mem_iInter.mpr fun p ↦ ?_⟩
        exact Or.inl hq₀δ
      have hunion : (⋃ p, A p) = S := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
          rcases hxp with hxδ | hxseg
          · exact hδS hxδ
          · exact hfseg p hxseg
        · intro x hx
          let p : S := ⟨x, hx⟩
          exact Set.mem_iUnion.mpr ⟨p, Or.inr (left_mem_segment ℝ _ _)⟩
      refine ⟨⟨l, hlS⟩, ?_⟩
      change IsPreconnected S
      rw [← hunion]
      exact isPreconnected_iUnion hcommon hA
    · intro hconn t ht
      by_cases hzFan : (rotatingHallwayParts (K.val : Set Point)
          (t : Real.Angle)).innerCorner ∈ interior (capFan ω)
      · right
        by_contra hzK
        let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
        obtain ⟨l, r, hlK, hrK, hl, hr⟩ := exists_horizontal_extrema K.val
        have hlS : l ∈ (K.val : Set Point) \ capNiche K := ⟨hlK, fun hlN ↦ by
          have := (capNiche_subset_rectangle K hlN).1
          linarith⟩
        have hrS : r ∈ (K.val : Set Point) \ capNiche K := ⟨hrK, fun hrN ↦ by
          have := (capNiche_subset_rectangle K hrN).2.1
          linarith⟩
        have hzy : 0 < z 1 := by
          by_contra hn
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzFan
          let q := z - (ε / 2) • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
          have hq := interior_subset (hball (by
            change dist q z < ε
            simp [q, norm_smul, norm_normalVector_real, abs_of_pos hε]
            linarith))
          have := hq.2
          change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
          simp [q, normalVector, frame, PiLp.inner_apply] at this
          linarith
        have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
            supportValue K.val (t : Real.Angle) - 1 := by
          simpa [z, rotatingHallwayParts, hallwayParts] using
            inner_supportingPlacement_normalVector (K.val : Set Point)
              (t : Real.Angle) (0 : Point)
        have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
            supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
          simpa [z, rotatingHallwayParts, hallwayParts] using
            inner_supportingPlacement_tangentVector (K.val : Set Point)
              (t : Real.Angle) (0 : Point)
        have hb := K.supportValue_horizontal_bounds ht
        have hb₁ := hb.1
        have hb₂ := hb.2
        change supportValue K.val ((t : Real.Angle) +
          ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
            -Real.sin t * horizontalMin K.val + Real.cos t at hb₂
        have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
          (by linarith [ht.2, K.property.2.1, Real.pi_pos])
        have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
        have hs1 : Real.sin t ≤ 1 := Real.sin_le_one t
        have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
        have hzlr : l 0 < z 0 ∧ z 0 < r 0 := by
          change inner ℝ z (tangentVector (t : Real.Angle)) =
            supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hzv
          simp [normalVector, tangentVector, frame, PiLp.inner_apply] at hzu hzv
          rw [hl, hr]
          constructor
          · nlinarith [hb₂, mul_pos hc hzy, sub_nonneg.mpr hc1]
          · nlinarith [hb₁, mul_pos hs hzy, sub_nonneg.mpr hs1]
        obtain ⟨q, hqS, hqx⟩ := hconn.isPreconnected.intermediate_value hlS hrS
          (by fun_prop : ContinuousOn (fun p : Point ↦ p 0) _)
          ⟨hzlr.1.le, hzlr.2.le⟩
        exact verticalLine_disjoint_cap_diff_niche_of_innerCorner K ht hzFan hzK hqS hqx
      · exact Or.inl hzFan

private theorem exists_line_meeting_of_support_bounds {s : Set Point} {ω : ℝ}
    (hs : IsCompact s) (hc : IsConnected s) (hω : ω ≤ Real.pi / 2) (p : Point)
    (hp0 : inner ℝ p (normalVector (0 : Real.Angle)) ≤ supportValue s 0)
    (hpω : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
      supportValue s ((ω + Real.pi / 2 : ℝ) : Real.Angle)) :
    ∃ q ∈ s, ∃ θ ∈ Set.Icc ω (Real.pi / 2),
      inner ℝ (q - p) (tangentVector (θ : Real.Angle)) = 0 := by
  obtain ⟨q₀, hq₀, he₀, _⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun q : Point ↦ inner ℝ q (normalVector (0 : Real.Angle))) hc.nonempty
    (continuous_id.inner continuous_const).continuousOn
  obtain ⟨qω, hqω, heω, _⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun q : Point ↦ inner ℝ q (tangentVector (ω : Real.Angle))) hc.nonempty
    (continuous_id.inner continuous_const).continuousOn
  have hn : normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (ω : Real.Angle) := by
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  have hzero : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector (0 : Real.Angle) := by
    simpa using tangentVector_add_pi_div_two 0
  have hpω' : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
      inner ℝ qω (tangentVector (ω : Real.Angle)) := by
    simpa only [supportValue, hn, heω] using hpω
  have hp0' : inner ℝ p (normalVector (0 : Real.Angle)) ≤
      inner ℝ q₀ (normalVector (0 : Real.Angle)) := by
    simpa only [supportValue, he₀] using hp0
  let f : Point × ℝ → ℝ := fun z ↦ inner ℝ (z.1 - p) (tangentVector (z.2 : Real.Angle))
  have hv : Continuous (fun θ : ℝ ↦ tangentVector (θ : Real.Angle)) := by
    have h := continuous_normalVector_real.comp (continuous_id.add continuous_const
      : Continuous (fun θ : ℝ ↦ θ + Real.pi / 2))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, Real.Angle.coe_add,
      normalVector_add_pi_div_two] using h
  have hf : Continuous f := (continuous_fst.sub continuous_const).inner
    (hv.comp continuous_snd)
  have hl : f (q₀, Real.pi / 2) ≤ 0 := by
    change inner ℝ (q₀ - p) (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
    rw [hzero, inner_neg_right, inner_sub_left]
    linarith
  have hr : 0 ≤ f (qω, ω) := by
    change 0 ≤ inner ℝ (qω - p) (tangentVector (ω : Real.Angle))
    rw [inner_sub_left]
    linarith
  obtain ⟨⟨q, θ⟩, hmem, he⟩ := (hc.isPreconnected.prod isPreconnected_Icc).intermediate_value
    (f := f) ⟨hq₀, hω, le_rfl⟩ ⟨hqω, le_rfl, hω⟩ hf.continuousOn ⟨hl, hr⟩
  exact ⟨q, hmem.1, θ, hmem.2, he⟩

private theorem mem_supportingHallway_iff_coordinates (s : Set Point) (t : Real.Angle)
    (p : Point) :
    p ∈ supportingHallway s t ↔
      inner ℝ p (normalVector t) ≤ supportValue s t ∧
      inner ℝ p (tangentVector t) ≤ supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ∧
      (supportValue s t - 1 ≤ inner ℝ p (normalVector t) ∨
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 ≤
          inner ℝ p (tangentVector t)) := by
  obtain ⟨h, _, _, _, _, _, _, ho, hi⟩ := rotatingHallwayParts_formulas s t
  rw [h, ho, hi]
  simp only [Set.mem_sdiff, Set.mem_inter_iff, normalHalfPlane, Set.mem_ofPred_eq,
    Bool.false_eq_true, ↓reduceIte, normalVector_add_pi_div_two]
  simp only [not_and_or, not_lt, and_assoc]

private theorem segment_subset_supportingHallway_of_projections_le {s : Set Point}
    {t : Real.Angle} {p q : Point} (hp : p ∈ supportingHallway s t)
    (hq : q ∈ supportingHallway s t)
    (hn : inner ℝ p (normalVector t) ≤ inner ℝ q (normalVector t))
    (hv : inner ℝ p (tangentVector t) ≤ inner ℝ q (tangentVector t)) :
    segment ℝ p q ⊆ supportingHallway s t := by
  rw [mem_supportingHallway_iff_coordinates] at hp hq
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  rw [mem_supportingHallway_iff_coordinates]
  simp only [inner_add_left, real_inner_smul_left]
  have weighted_le (x y m : ℝ) (hx : x ≤ m) (hy : y ≤ m) : a * x + b * y ≤ m := by
    calc
      a * x + b * y ≤ a * m + b * m :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = m := by rw [← add_mul, hab, one_mul]
  have le_weighted (x y m : ℝ) (hx : m ≤ x) (hy : m ≤ y) : m ≤ a * x + b * y := by
    calc
      m = a * m + b * m := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x + b * y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  refine ⟨weighted_le _ _ _ hp.1 hq.1, weighted_le _ _ _ hp.2.1 hq.2.1, ?_⟩
  rcases hp.2.2 with hn' | hv'
  · exact Or.inl (le_weighted _ _ _ hn' (hn'.trans hn))
  · exact Or.inr (le_weighted _ _ _ hv' (hv'.trans hv))

private theorem convex_stripParallelogram (ω : ℝ) : Convex ℝ (stripParallelogram ω).1 := by
  intro p hp q hq a b ha hb hab
  rw [mem_stripParallelogram_iff] at hp hq ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_add_left,
    real_inner_smul_left]
  exact ⟨convex_Icc (0 : ℝ) 1 hp.1 hq.1 ha hb hab, convex_Icc (0 : ℝ) 1 hp.2 hq.2 ha hb hab⟩

private theorem segment_subset_supportingHallway_of_tangent_eq_zero {s : Set Point}
    {t θ : ℝ} {p q : Point} (hp : p ∈ supportingHallway s (t : Real.Angle))
    (hq : q ∈ supportingHallway s (t : Real.Angle))
    (hθ : θ - t ∈ Set.Icc 0 (Real.pi / 2))
    (hline : inner ℝ (q - p) (tangentVector (θ : Real.Angle)) = 0) :
    segment ℝ p q ⊆ supportingHallway s (t : Real.Angle) := by
  let c := inner ℝ (q - p) (normalVector (θ : Real.Angle))
  have hdiff : q - p = c • normalVector (θ : Real.Angle) := by
    have h := inner_normalVector_smul_add_inner_tangentVector_smul (q - p) (θ : Real.Angle)
    simpa only [hline, zero_smul, add_zero] using h.symm
  have hcos : 0 ≤ Real.cos (θ - t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsin : 0 ≤ Real.sin (θ - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hn : inner ℝ q (normalVector (t : Real.Angle)) -
      inner ℝ p (normalVector (t : Real.Angle)) = c * Real.cos (θ - t) := by
    rw [← inner_sub_left, hdiff, real_inner_smul_left, inner_normalVector_normalVector]
  have hv : inner ℝ q (tangentVector (t : Real.Angle)) -
      inner ℝ p (tangentVector (t : Real.Angle)) = c * Real.sin (θ - t) := by
    rw [← inner_sub_left, hdiff, real_inner_smul_left]
    congr 1
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.sin_sub]
    ring
  by_cases hc : 0 ≤ c
  · apply segment_subset_supportingHallway_of_projections_le hp hq
    · linarith [mul_nonneg hc hcos]
    · linarith [mul_nonneg hc hsin]
  · rw [segment_symm]
    apply segment_subset_supportingHallway_of_projections_le hq hp
    · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hcos]
    · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hsin]

theorem standardPosition_monotonization_connected (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : IsConnected (monotonization s ω) := by
  have hc : IsConnected s := by
    obtain ⟨m, hm, _⟩ := hs.2.1
    exact hm.1
  have hsub := (standardPosition_subset_cap s ω hs).1
  obtain ⟨q₀, hq₀⟩ := hc.nonempty
  refine ⟨hc.nonempty.mono hsub, isPreconnected_of_forall q₀ ?_⟩
  intro p hp
  have hpH (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
      p ∈ supportingHallway s (t : Real.Angle) :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
  have hp0 := (mem_supportingHallway_iff_coordinates s 0 p).mp
    (hpH 0 ⟨le_rfl, hs.2.2.1.le⟩)
  have hpω := (mem_supportingHallway_iff_coordinates s (ω : Real.Angle) p).mp
    (hpH ω ⟨hs.2.2.1.le, le_rfl⟩)
  obtain ⟨q, hqs, θ, hθ, hline⟩ := exists_line_meeting_of_support_bounds hs.1 hc
    hs.2.2.2.1 p hp0.1 (by simpa only [Real.Angle.coe_add] using hpω.2.1)
  have hq := hsub hqs
  have hseg : segment ℝ p q ⊆ monotonization s ω := by
    intro z hz
    refine ⟨(convex_stripParallelogram ω).segment_subset hp.1 hq.1 hz,
      Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
    apply segment_subset_supportingHallway_of_tangent_eq_zero (hpH t ht)
      (Set.mem_iInter.1 (Set.mem_iInter.1 hq.2 t) ht) _ hline hz
    exact ⟨by linarith [hθ.1, ht.2], by linarith [hθ.2, ht.1]⟩
  refine ⟨s ∪ segment ℝ p q, Set.union_subset hsub hseg, Or.inl hq₀,
    Or.inr (left_mem_segment ℝ p q), ?_⟩
  exact IsPreconnected.union q hqs (right_mem_segment ℝ p q) hc.isPreconnected
    (convex_segment p q).isPreconnected

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
# Cap / Mirror Features
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem mirrorReflection_eq_capReflection_m6ef9701 (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    mirrorReflection ω = capReflection ω := by
  change stripTopReflection ω = capReflection ω
  exact stripTopReflection_eq_capReflection ω hω0 hωle

private theorem capReflection_rotationMap (ω s : ℝ) (p : Point) :
    capReflection ω (rotationMap (s : Real.Angle) p) =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) := by
  have hang : (ω : Real.Angle) - (s : Real.Angle) =
      ((ω - s : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (rotationMap (s : Real.Angle) p) 0 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 0
    rw [capReflection_apply_zero]
    rw [← hang]
    simp only [Fin.isValue, rotationMap, Orientation.rotation_apply, Real.Angle.cos_coe,
      Real.Angle.sin_coe, rightAngleRotation_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, mul_neg, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring
  · change capReflection ω (rotationMap (s : Real.Angle) p) 1 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 1
    rw [capReflection_apply_one]
    rw [← hang]
    simp only [Fin.isValue, rotationMap, Orientation.rotation_apply, Real.Angle.cos_coe,
      Real.Angle.sin_coe, rightAngleRotation_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
      Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring

private theorem capReflection_normal_at_complement (ω t : ℝ) :
    capReflection ω (normalVector ((ω - t : ℝ) : Real.Angle)) =
      tangentVector (t : Real.Angle) := by
  rw [capReflection_normalVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem capReflection_tangent_at_complement (ω t : ℝ) :
    capReflection ω (tangentVector ((ω - t : ℝ) : Real.Angle)) =
      normalVector (t : Real.Angle) := by
  rw [capReflection_tangentVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem supportValue_reflected_at (ω t : ℝ) (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) (t : Real.Angle) =
      supportValue K ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportValue_reflected_at_add_pi_div_two (ω t : ℝ)
    (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      supportValue K ((ω - t : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportingPlacement_reflection (ω t : ℝ)
    (K : ConvexBody Point) (q : Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) (coordinateSwap q) =
      capReflection ω (supportingPlacement K ((ω - t : ℝ) : Real.Angle) q) := by
  unfold supportingPlacement
  rw [map_add, map_add, map_smul, map_smul,
    capReflection_rotationMap]
  have hrot : ω - (ω - t) = t := by ring
  have htadd : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  have hsadd : ((ω - t : ℝ) : Real.Angle) +
      ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  rw [hrot, supportValue_reflected_at,
    htadd, supportValue_reflected_at_add_pi_div_two, hsadd,
    capReflection_normal_at_complement,
    capReflection_tangent_at_complement]
  module

private theorem coordinateSwap_involutive (p : Point) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  fin_cases i <;> simp [coordinateSwap]

private theorem coordinateSwap_image_hallway :
    coordinateSwap '' hallway = hallway := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
  · intro hp
    refine ⟨coordinateSwap p, ?_, coordinateSwap_involutive p⟩
    rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩

private theorem coordinateSwap_image_eq_preimage (s : Set Point) :
    coordinateSwap '' s = coordinateSwap ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change coordinateSwap (coordinateSwap q) ∈ s
    rwa [coordinateSwap_involutive]
  · intro hp
    exact ⟨coordinateSwap p, hp, coordinateSwap_involutive p⟩

private theorem coordinateSwap_image_outerQuadrant :
    coordinateSwap '' hallwayParts.outerQuadrant = hallwayParts.outerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_innerQuadrant :
    coordinateSwap '' hallwayParts.innerQuadrant = hallwayParts.innerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_a :
    coordinateSwap '' hallwayParts.a = hallwayParts.c := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_c :
    coordinateSwap '' hallwayParts.c = hallwayParts.a := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_b :
    coordinateSwap '' hallwayParts.b = hallwayParts.d := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_d :
    coordinateSwap '' hallwayParts.d = hallwayParts.b := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_bRay :
    coordinateSwap '' hallwayParts.bRay = hallwayParts.dRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_dRay :
    coordinateSwap '' hallwayParts.dRay = hallwayParts.bRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem supportingPlacement_image_reflection (ω t : ℝ)
    (K : ConvexBody Point) (s : Set Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) ''
        (coordinateSwap '' s) =
      capReflection ω ''
        (supportingPlacement K ((ω - t : ℝ) : Real.Angle) '' s) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact supportingPlacement_reflection ω t K q

private theorem supportingHallway_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    supportingHallway (reflectedBody ω K) (t : Real.Angle) =
      capReflection ω '' supportingHallway K ((ω - t : ℝ) : Real.Angle) := by
  unfold supportingHallway
  nth_rewrite 1 [← coordinateSwap_image_hallway]
  exact supportingPlacement_image_reflection ω t K hallway

private theorem rotatingHallwayParts_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).a =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).c ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).c =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).a ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).b =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).d ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).d =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).b ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).bRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).dRay ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).dRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).bRay := by
  have hzero : coordinateSwap (0 : Point) = 0 := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  have hone : coordinateSwap (!₂[1, 1] : Point) = !₂[1, 1] := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  unfold rotatingHallwayParts
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hallwayParts]
    rw [← hzero]
    exact supportingPlacement_reflection ω t K 0
  · simp only [hallwayParts]
    nth_rewrite 1 [← hone]
    exact supportingPlacement_reflection ω t K !₂[1, 1]
  · nth_rewrite 1 [← coordinateSwap_image_outerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.outerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_innerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.innerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_c]
    exact supportingPlacement_image_reflection ω t K hallwayParts.c
  · nth_rewrite 1 [← coordinateSwap_image_a]
    exact supportingPlacement_image_reflection ω t K hallwayParts.a
  · nth_rewrite 1 [← coordinateSwap_image_d]
    exact supportingPlacement_image_reflection ω t K hallwayParts.d
  · nth_rewrite 1 [← coordinateSwap_image_b]
    exact supportingPlacement_image_reflection ω t K hallwayParts.b
  · nth_rewrite 1 [← coordinateSwap_image_dRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.dRay
  · nth_rewrite 1 [← coordinateSwap_image_bRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.bRay

private theorem exposedEdge_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    exposedEdge (reflectedBody ω K) a =
      capReflection ω '' exposedEdge K (reflectedAngle ω a) := by
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a at hp
    change inner ℝ q (normalVector (reflectedAngle ω a)) =
      supportValue K (reflectedAngle ω a)
    rw [← inner_capReflection_normalVector ω q a,
      ← supportValue_reflectedBody ω K a]
    exact hp
  · rintro ⟨q, ⟨hq, hp⟩, rfl⟩
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a
    rw [inner_capReflection_normalVector, supportValue_reflectedBody]
    exact hp

private theorem exposedEdgeHeights_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    (fun p ↦ inner ℝ p (tangentVector a)) '' exposedEdge (reflectedBody ω K) a =
      -((fun p ↦ inner ℝ p (tangentVector (reflectedAngle ω a))) ''
        exposedEdge K (reflectedAngle ω a)) := by
  rw [exposedEdge_reflection]
  ext x
  simp only [Set.mem_image, Set.mem_neg]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨q, hq, ?_⟩
    rw [inner_capReflection_tangentVector, neg_neg]
  · rintro ⟨q, hq, hq_inner⟩
    refine ⟨capReflection ω q, ⟨q, hq, rfl⟩, ?_⟩
    rw [inner_capReflection_tangentVector, hq_inner, neg_neg]

private theorem edgeVertices_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    edgeVertices (reflectedBody ω K) a =
      (capReflection ω (edgeVertices K (reflectedAngle ω a)).2,
        capReflection ω (edgeVertices K (reflectedAngle ω a)).1) := by
  unfold edgeVertices
  dsimp only
  rw [supportValue_reflectedBody, exposedEdgeHeights_reflection,
    Real.sSup_neg, Real.sInf_neg]
  apply Prod.ext <;> dsimp only
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module

private theorem capVertices_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capVertices P t =
      ((capReflection ω (capVertices K (ω - t)).2.2,
        capReflection ω (capVertices K (ω - t)).2.1),
       (capReflection ω (capVertices K (ω - t)).1.2,
        capReflection ω (capVertices K (ω - t)).1.1)) := by
  dsimp only
  unfold capVertices
  rw [edgeVertices_reflection, edgeVertices_reflection]
  dsimp only
  rw [reflectedAngle_coe, reflectedAngle_coe]
  congr 1 <;> ring_nf

private theorem capReflection_normal_zero (ω : ℝ) :
    capReflection ω (normalVector 0) = tangentVector (ω : Real.Angle) := by
  simpa using capReflection_normal_at_complement ω ω

private theorem capReflection_tangent_omega (ω : ℝ) :
    capReflection ω (tangentVector (ω : Real.Angle)) = normalVector 0 := by
  simpa using capReflection_tangent_at_complement ω 0

private theorem wedgeEndpoints_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeEndpoints P t =
      (capReflection ω (wedgeEndpoints K (ω - t)).2,
        capReflection ω (wedgeEndpoints K (ω - t)).1) := by
  dsimp only
  unfold wedgeEndpoints
  rw [supportValue_reflected_at, supportValue_reflected_at_add_pi_div_two]
  apply Prod.ext <;> dsimp only
  · rw [map_smul, capReflection_tangent_omega]
    congr 2; ring_nf
  · rw [map_smul, capReflection_normal_zero]

private theorem wedgeGaps_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeGaps P t = ((wedgeGaps K (ω - t)).2, (wedgeGaps K (ω - t)).1) := by
  dsimp only
  unfold wedgeGaps
  rw [capVertices_reflection K 0, capVertices_reflection K ω,
    wedgeEndpoints_reflection K t]
  dsimp only
  apply Prod.ext <;> dsimp only
  · rw [← map_sub, ← capReflection_tangent_omega,
      (capReflection ω).inner_map_map]
    simp
  · rw [← map_sub, ← capReflection_normal_zero,
      (capReflection ω).inner_map_map]
    simp

private theorem capWedge_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capWedge P t = capReflection ω '' capWedge K (ω - t) := by
  dsimp only
  unfold capWedge
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan,
    (rotatingHallwayParts_reflection ω t K.val).2.2.2.1]

private theorem iUnion_innerQuadrant_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (reflectedBody ω K.val) t) =
      capReflection ω '' (⋃ s ∈ Set.Ioo 0 ω, innerQuadrant K.val s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω - t, ⟨by linarith, by linarith⟩, hq⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [innerQuadrant_reflection]
    exact ⟨q, by simpa, rfl⟩

private theorem capNiche_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capNiche P = capReflection ω '' capNiche K := by
  dsimp only
  unfold capNiche
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan, ← iUnion_innerQuadrant_reflection]

private theorem iUnion_exposedEdge_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
        exposedEdge (reflectedBody ω K.val) (t : Real.Angle)) =
      capReflection ω ''
        (⋃ s ∈ Set.Icc 0 (ω + Real.pi / 2),
          exposedEdge K.val (s : Real.Angle)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [exposedEdge_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω + Real.pi / 2 - t,
      ⟨by linarith, by linarith⟩, ?_⟩, rfl⟩
    simpa only [reflectedAngle_coe] using hq
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω + Real.pi / 2 - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [exposedEdge_reflection]
    refine ⟨q, ?_, rfl⟩
    rw [reflectedAngle_coe]
    convert hq using 1; ring_nf

private theorem capUpperBoundary_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capUpperBoundary P = capReflection ω '' capUpperBoundary K := by
  dsimp only
  unfold capUpperBoundary
  exact iUnion_exposedEdge_reflection K

private def reflectedAngleEquiv (ω : ℝ) : Real.Angle ≃ᵐ Real.Angle :=
  MeasurableEquiv.ofInvolutive (reflectedAngle ω)
    (reflectedAngle_involutive ω) (by unfold reflectedAngle; fun_prop)

private theorem reflectedAngle_add_pi (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (a + (Real.pi : Real.Angle)) =
      reflectedAngle ω a + (Real.pi : Real.Angle) := by
  have hpi : -(Real.pi : Real.Angle) = (Real.pi : Real.Angle) :=
    neg_eq_iff_add_eq_zero.mpr Real.Angle.coe_pi_add_coe_pi
  unfold reflectedAngle
  rw [sub_eq_add_neg, neg_add_rev, hpi]
  abel

private theorem isSegmentPresentation_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    IsSegmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2) := by
  refine ⟨fun h ↦ hd.1 ((capReflection ω).injective h), ?_, ?_⟩
  · change capReflection ω '' (K : Set Point) =
      segment ℝ (capReflection ω d.1) (capReflection ω d.2.1)
    rw [hd.2.1]
    exact image_segment ℝ
      (capReflection ω).toLinearEquiv.toLinearMap.toAffineMap d.1 d.2.1
  · rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact hd.2.2

private theorem reflectedBody_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    reflectedBody ω (reflectedBody ω K) = K := by
  apply ConvexBody.ext
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [capReflection_involutive] using hr
  · intro hp
    exact ⟨capReflection ω p, ⟨p, hp, rfl⟩, capReflection_involutive ω p⟩

private theorem subsingleton_reflectedBody_iff (ω : ℝ) (K : ConvexBody Point) :
    ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton ↔
      (K : Set Point).Subsingleton := by
  constructor
  · intro hP p hp q hq
    apply (capReflection ω).injective
    exact hP ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  · intro hK _
    rintro ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]

private theorem exists_segmentPresentation_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) :
    (∃ d, IsSegmentPresentation (reflectedBody ω K) d) ↔
      ∃ d, IsSegmentPresentation K d := by
  constructor
  · rintro ⟨d, hd⟩
    have h := isSegmentPresentation_reflectedBody ω (reflectedBody ω K) d hd
    rw [reflectedBody_reflectedBody] at h
    exact ⟨_, h⟩
  · rintro ⟨d, hd⟩
    exact ⟨_, isSegmentPresentation_reflectedBody ω K d hd⟩

private theorem surfaceAreaMeasure_reflectedBody_of_subsingleton (ω : ℝ)
    (K : ConvexBody Point) (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  have hP : ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton (reflectedBody ω K) hP,
    surfaceAreaMeasure_eq_zero_of_subsingleton K hK, Measure.map_zero]

private theorem surfaceAreaMeasure_reflectedBody_of_segmentPresentation (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2)
      (isSegmentPresentation_reflectedBody ω K d hd),
    surfaceAreaMeasure_eq_segmentPresentation K d hd,
    MeasureTheory.Measure.map_smul _ (reflectedAngleEquiv ω).measurable.aemeasurable,
    MeasureTheory.Measure.map_add _ _ (reflectedAngleEquiv ω).measurable,
    MeasureTheory.Measure.map_dirac, MeasureTheory.Measure.map_dirac,
    (capReflection ω).dist_map]
  change ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω d.2.2 + (Real.pi : Real.Angle))) =
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω (d.2.2 + (Real.pi : Real.Angle))))
  rw [reflectedAngle_add_pi]

private theorem isExteriorNormal_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (a : Real.Angle) :
    IsExteriorNormal (reflectedBody ω K) (capReflection ω p) (reflectedAngle ω a) ↔
      IsExteriorNormal K p a := by
  constructor
  · intro h q hq
    have h' := h (capReflection ω q) ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map] at h'
    exact h'
  · intro h _
    rintro ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact h q hq

private theorem mem_regularBoundary_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) :
    capReflection ω p ∈ regularBoundary (reflectedBody ω K) ↔
      p ∈ regularBoundary K := by
  have hfront : capReflection ω p ∈ frontier ((reflectedBody ω K : ConvexBody Point) : Set Point) ↔
      p ∈ frontier (K : Set Point) := by
    change capReflection ω p ∈ frontier (capReflection ω '' (K : Set Point)) ↔ _
    have himage : capReflection ω '' frontier (K : Set Point) =
        frontier (capReflection ω '' (K : Set Point)) :=
      (capReflection ω).toHomeomorph.image_frontier (K : Set Point)
    rw [← himage]
    constructor
    · rintro ⟨q, hq, hpq⟩
      have hqp : q = p := (capReflection ω).injective hpq
      simpa only [hqp] using hq
    · exact fun hp ↦ ⟨p, hp, rfl⟩
  have hunique :
      (∃! b, IsExteriorNormal (reflectedBody ω K) (capReflection ω p) b) ↔
        ∃! a, IsExteriorNormal K p a := by
    constructor
    · rintro ⟨b, hb, hub⟩
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      refine ⟨reflectedAngle ω b, hbK, ?_⟩
      intro c hc
      have hcL := (isExteriorNormal_reflectedBody_iff ω K p c).mpr hc
      have hcb : reflectedAngle ω c = b := hub _ hcL
      calc
        c = reflectedAngle ω (reflectedAngle ω c) :=
          (reflectedAngle_involutive ω c).symm
        _ = reflectedAngle ω b := congrArg (reflectedAngle ω) hcb
    · rintro ⟨a, ha, hua⟩
      refine ⟨reflectedAngle ω a,
        (isExteriorNormal_reflectedBody_iff ω K p a).mpr ha, ?_⟩
      intro b hb
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      have hba : reflectedAngle ω b = a := hua _ hbK
      calc
        b = reflectedAngle ω (reflectedAngle ω b) :=
          (reflectedAngle_involutive ω b).symm
        _ = reflectedAngle ω a := congrArg (reflectedAngle ω) hba
  simp only [regularBoundary, Set.mem_ofPred_eq]
  exact and_congr hfront hunique

private theorem exteriorNormalAngle_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (hp : p ∈ regularBoundary K) :
    exteriorNormalAngle (reflectedBody ω K) (capReflection ω p) =
      reflectedAngle ω (exteriorNormalAngle K p) := by
  have hP := (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp
  have huK : ∃! a, IsExteriorNormal K p a := hp.2
  have huP : ∃! a,
      IsExteriorNormal (reflectedBody ω K) (capReflection ω p) a := hP.2
  have hnK : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huK]
    generalize_proofs h
    exact h.choose_spec
  have hnP : IsExteriorNormal (reflectedBody ω K) (capReflection ω p)
      (exteriorNormalAngle (reflectedBody ω K) (capReflection ω p)) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huP]
    generalize_proofs _ h
    exact h.choose_spec
  exact huP.unique hnP ((isExteriorNormal_reflectedBody_iff ω K p _).mpr hnK)

private theorem regularBoundary_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    regularBoundary (reflectedBody ω K) =
      capReflection ω '' regularBoundary K := by
  ext q
  constructor
  · intro hq
    refine ⟨capReflection ω q, ?_, capReflection_involutive ω q⟩
    apply (mem_regularBoundary_reflectedBody_iff ω K (capReflection ω q)).mp
    simpa only [capReflection_involutive] using hq
  · rintro ⟨p, hp, rfl⟩
    exact (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp

private theorem map_hausdorffMeasure_restrict_regularBoundary (ω : ℝ)
    (K : ConvexBody Point) :
    Measure.map (capReflection ω)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) =
      (Measure.hausdorffMeasure 1).restrict
        (regularBoundary (reflectedBody ω K)) := by
  rw [regularBoundary_reflectedBody]
  let e := (capReflection ω).toHomeomorph.toMeasurableEquiv
  have hrestrict := e.restrict_map (Measure.hausdorffMeasure 1)
    (capReflection ω '' regularBoundary K)
  change (Measure.map (capReflection ω) (Measure.hausdorffMeasure 1)).restrict
      (capReflection ω '' regularBoundary K) =
    Measure.map (capReflection ω)
      ((Measure.hausdorffMeasure 1).restrict
        (capReflection ω ⁻¹' (capReflection ω '' regularBoundary K))) at hrestrict
  have hmap : Measure.map (capReflection ω) (Measure.hausdorffMeasure 1) =
      Measure.hausdorffMeasure 1 :=
    (capReflection ω).toIsometryEquiv.map_hausdorffMeasure 1
  rw [hmap] at hrestrict
  have hpre : capReflection ω ⁻¹' (capReflection ω '' regularBoundary K) =
      regularBoundary K := by
    exact Set.preimage_image_eq _ (capReflection ω).injective
  rw [hpre] at hrestrict
  exact hrestrict.symm

private theorem reflectedAngle_preimage_eq_image (ω : ℝ)
    (E : Set Real.Angle) :
    reflectedAngle ω ⁻¹' E = reflectedAngle ω '' E := by
  ext a
  constructor
  · intro ha
    exact ⟨reflectedAngle ω a, ha, reflectedAngle_involutive ω a⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [Set.mem_preimage, reflectedAngle_involutive] using hb

private theorem surfaceAreaMeasure_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · exact surfaceAreaMeasure_reflectedBody_of_subsingleton ω K hsub
  by_cases hseg : ∃ d, IsSegmentPresentation K d
  · obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_reflectedBody_of_segmentPresentation ω K d hd
  have hsubP : ¬ ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton :=
    fun h ↦ hsub ((subsingleton_reflectedBody_iff ω K).mp h)
  have hsegP : ¬ ∃ d, IsSegmentPresentation (reflectedBody ω K) d :=
    fun h ↦ hseg ((exists_segmentPresentation_reflectedBody_iff ω K).mp h)
  let μK := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  let μP := (Measure.hausdorffMeasure 1).restrict
    (regularBoundary (reflectedBody ω K))
  have hμ : Measure.map (capReflection ω) μK = μP :=
    map_hausdorffMeasure_restrict_regularBoundary ω K
  have haeK : AEMeasurable (exteriorNormalAngle K) μK :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _
  have haeP : AEMeasurable (exteriorNormalAngle (reflectedBody ω K)) μP :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary (reflectedBody ω K) _
  simp only [surfaceAreaMeasure, hsub, hseg, hsubP, hsegP, ↓reduceIte]
  change Measure.map (exteriorNormalAngle (reflectedBody ω K)) μP =
    Measure.map (reflectedAngleEquiv ω)
      (Measure.map (exteriorNormalAngle K) μK)
  rw [← hμ]
  have haeP' : AEMeasurable (exteriorNormalAngle (reflectedBody ω K))
      (Measure.map (capReflection ω) μK) := by
    rwa [hμ]
  rw [AEMeasurable.map_map_of_aemeasurable haeP'
      (capReflection ω).continuous.measurable.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable
      (reflectedAngleEquiv ω).measurable.aemeasurable haeK]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact exteriorNormalAngle_reflectedBody ω K p hp

theorem cap_mirror_features {ω : ℝ} (K : CapSpace ω) :
    ∃ P : CapSpace ω,
      (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) ∧
      (∀ t ∈ Set.Icc 0 ω,
        supportingHallway (P.val : Set Point) (t : Real.Angle) =
        mirrorReflection ω '' supportingHallway (K.val : Set Point) ((ω - t : ℝ) : Real.Angle) ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerCorner = mirrorReflection
          ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerCorner = mirrorReflection
          ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerQuadrant =
          mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) :
          Real.Angle)).outerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerQuadrant =
          mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) :
          Real.Angle)).innerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).a = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).c ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).c = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).a ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).b = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).d ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).d = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).b ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).bRay = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).dRay ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).dRay = mirrorReflection ω ''
          (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).bRay ∧
        (capVertices P t).1.1 = mirrorReflection ω (capVertices K (ω - t)).2.2 ∧
        (capVertices P t).1.2 = mirrorReflection ω (capVertices K (ω - t)).2.1 ∧
        (capVertices P t).2.1 = mirrorReflection ω (capVertices K (ω - t)).1.2 ∧
        (capVertices P t).2.2 = mirrorReflection ω (capVertices K (ω - t)).1.1) ∧
      (∀ t ∈ Set.Ioo 0 ω,
        (wedgeEndpoints P t).1 = mirrorReflection ω (wedgeEndpoints K (ω - t)).2 ∧
        (wedgeEndpoints P t).2 = mirrorReflection ω (wedgeEndpoints K (ω - t)).1 ∧
        (wedgeGaps P t).1 = (wedgeGaps K (ω - t)).2 ∧
        (wedgeGaps P t).2 = (wedgeGaps K (ω - t)).1 ∧
        capWedge P t = mirrorReflection ω '' capWedge K (ω - t)) ∧
      capUpperBoundary P = mirrorReflection ω '' capUpperBoundary K ∧
      capNiche P = mirrorReflection ω '' capNiche K ∧
      (∀ E : Set Real.Angle, MeasurableSet E →
        surfaceAreaMeasure P.val E = surfaceAreaMeasure K.val
          ((fun a : Real.Angle ↦ ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a) '' E)) := by
  let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
  have hM : mirrorReflection ω = capReflection ω :=
    mirrorReflection_eq_capReflection_m6ef9701 ω K.property.1 K.property.2.1
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change capReflection ω '' (K.val : Set Point) =
      mirrorReflection ω '' (K.val : Set Point)
    rw [hM]
  · intro t _
    rw [hM]
    have hh := supportingHallway_reflection ω t K.val
    have hp := rotatingHallwayParts_reflection ω t K.val
    have hv := capVertices_reflection K t
    rcases hp with ⟨hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay⟩
    refine ⟨hh, hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay,
      ?_, ?_, ?_, ?_⟩
    · simpa only [P] using congrArg (fun v ↦ v.1.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.1.2) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.2) hv
  · intro t _
    rw [hM]
    have he := wedgeEndpoints_reflection K t
    have hg := wedgeGaps_reflection K t
    refine ⟨?_, ?_, ?_, ?_, capWedge_reflection K t⟩
    · simpa only [P] using congrArg Prod.fst he
    · simpa only [P] using congrArg Prod.snd he
    · simpa only [P] using congrArg Prod.fst hg
    · simpa only [P] using congrArg Prod.snd hg
  · rw [hM]
    exact capUpperBoundary_reflection K
  · rw [hM]
    exact capNiche_reflection K
  · intro E hE
    change surfaceAreaMeasure (reflectedBody ω K.val) E = _
    rw [surfaceAreaMeasure_reflectedBody,
      (reflectedAngleEquiv ω).map_apply]
    change surfaceAreaMeasure K.val (reflectedAngle ω ⁻¹' E) = _
    rw [reflectedAngle_preimage_eq_image]
    rfl

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

* `Bounds.Arm.Geometry`.
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
# Bounds / Arm / Geometry
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

private theorem mirrorReflection_rightAngle_apply (p : Point) :
    mirrorReflection (Real.pi / 2) p = !₂[-p 0, p 1] := by
  have harg : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
  have hnorm : ‖(!₂[0, 1] : Point)‖ ^ 2 = 1 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.norm_sq_eq (!₂[0, 1] : Point)
  ext i
  fin_cases i <;>
    simp [mirrorReflection, stripParallelogram, harg, PiLp.inner_apply,
      Fin.sum_univ_two, hnorm]
  ring

private theorem inner_mirror_sub_tangent (p q : Point) (t : ℝ) :
    inner ℝ (mirrorReflection (Real.pi / 2) p - mirrorReflection (Real.pi / 2) q)
      (tangentVector (t : Real.Angle)) =
    inner ℝ (p - q) (normalVector ((Real.pi / 2 - t : ℝ) : Real.Angle)) := by
  rw [mirrorReflection_rightAngle_apply, mirrorReflection_rightAngle_apply]
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
  ring

private theorem inner_mirror_sub_normal (p q : Point) (t : ℝ) :
    inner ℝ (mirrorReflection (Real.pi / 2) p - mirrorReflection (Real.pi / 2) q)
      (normalVector (t : Real.Angle)) =
    inner ℝ (p - q) (tangentVector ((Real.pi / 2 - t : ℝ) : Real.Angle)) := by
  rw [mirrorReflection_rightAngle_apply, mirrorReflection_rightAngle_apply]
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, -Real.Angle.coe_sub]
  ring

theorem tangentArms_mirror (K P : RightAngleCapSpace)
    (hP : (P.val : Set Point) = mirrorReflection (Real.pi / 2) '' (K.val : Set Point))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths P t).1.1 = (tangentArmLengths K (Real.pi / 2 - t)).2.2 ∧
    (tangentArmLengths P t).1.2 = (tangentArmLengths K (Real.pi / 2 - t)).2.1 ∧
    (tangentArmLengths P t).2.1 = (tangentArmLengths K (Real.pi / 2 - t)).1.2 ∧
    (tangentArmLengths P t).2.2 = (tangentArmLengths K (Real.pi / 2 - t)).1.1 := by
  obtain ⟨Q, hQ, hfeatures, _⟩ := cap_mirror_features K
  have hPQ : P = Q := by
    apply Subtype.ext
    apply ConvexBody.ext
    exact hP.trans hQ.symm
  subst P
  obtain ⟨_, _, hy, _, _, _, _, _, _, _, _, hA₁, hA₂, hC₁, hC₂⟩ := hfeatures t ht
  dsimp only [tangentArmLengths]
  rw [hy, hA₁, hA₂, hC₁, hC₂]
  exact ⟨inner_mirror_sub_tangent _ _ _, inner_mirror_sub_tangent _ _ _,
    inner_mirror_sub_normal _ _ _, inner_mirror_sub_normal _ _ _⟩

private theorem tendsto_tan_sub_div (t : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.tan (s - t) / (s - t)) (𝓝[≠] t) (𝓝 1) := by
  have hd : HasDerivAt (fun s : ℝ ↦ Real.tan (s - t)) 1 t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_tan (x := t - t) (by simp)).comp (h := fun s : ℝ ↦ s - t) t
        ((hasDerivAt_id t).sub_const t)
  convert hd.tendsto_slope using 1
  funext s
  simp [slope_def_field]

private theorem tendsto_normal_slope {F : Filter ℝ} {t : ℝ}
    (hF : F ≤ 𝓝[≠] t) (a : ℝ) (y q : ℝ → Point) (p : Point)
    (hy : Tendsto y F (𝓝 (y t))) (hq : Tendsto q F (𝓝 p))
    (hfixed : ∀ᶠ s in F, inner ℝ (q s) (normalVector ((t + a : ℝ) : Real.Angle)) =
      inner ℝ (y t) (normalVector ((t + a : ℝ) : Real.Angle)))
    (hmoving : ∀ᶠ s in F, inner ℝ (q s) (normalVector ((s + a : ℝ) : Real.Angle)) =
      inner ℝ (y s) (normalVector ((s + a : ℝ) : Real.Angle))) :
    Tendsto (fun s : ℝ ↦ inner ℝ ((s - t)⁻¹ • (y s - y t))
      (normalVector ((t + a : ℝ) : Real.Angle))) F
      (𝓝 (inner ℝ (p - y t) (tangentVector ((t + a : ℝ) : Real.Angle)))) := by
  have htan := (tendsto_tan_sub_div t).mono_left hF
  have hpair := htan.mul ((hq.sub hy).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := tangentVector ((t + a : ℝ) : Real.Angle))))
  simp only [one_mul] at hpair
  apply hpair.congr'
  have hnear : ∀ᶠ s in F, s - t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hc : Tendsto (fun s : ℝ ↦ s - t) F (𝓝 0) := by
      simpa using (tendsto_id.mono_right (hF.trans nhdsWithin_le_nhds)).sub_const t
    exact hc.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  filter_upwards [hfixed, hmoving, hnear] with s hf hm hs
  have hn : normalVector ((s + a : ℝ) : Real.Angle) =
      Real.cos (s - t) • normalVector ((t + a : ℝ) : Real.Angle) +
      Real.sin (s - t) • tangentVector ((t + a : ℝ) : Real.Angle) := by
    convert normalVector_add_real (t + a) (s - t) using 1
    congr 2
    ring
  rw [hn] at hm
  simp only [inner_add_right, inner_smul_right] at hm
  rw [hf] at hm
  have hc : Real.cos (s - t) ≠ 0 := (Real.cos_pos_of_mem_Ioo hs).ne'
  simp only [real_inner_smul_left, inner_sub_left, Real.tan_eq_sin_div_cos]
  have heq : Real.sin (s - t) *
      (inner ℝ (q s) (tangentVector ((t + a : ℝ) : Real.Angle)) -
        inner ℝ (y s) (tangentVector ((t + a : ℝ) : Real.Angle))) =
      Real.cos (s - t) * (inner ℝ (y s) (normalVector ((t + a : ℝ) : Real.Angle)) -
        inner ℝ (y t) (normalVector ((t + a : ℝ) : Real.Angle))) := by linarith
  field_simp
  rw [heq]

private theorem outerCorner_inner_normal (K : ConvexBody Point) (t : ℝ) :
    inner ℝ (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  change inner ℝ (supportingPlacement (K : Set Point) (t : Real.Angle) (!₂[1, 1] : Point))
    (normalVector (t : Real.Angle)) = _
  rw [inner_supportingPlacement_normalVector]
  simp

private theorem outerCorner_inner_tangent (K : ConvexBody Point) (t : ℝ) :
    inner ℝ (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) = supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  change inner ℝ (supportingPlacement (K : Set Point) (t : Real.Angle) (!₂[1, 1] : Point))
    (tangentVector (t : Real.Angle)) = _
  rw [inner_supportingPlacement_tangentVector]
  simp

private theorem eventually_sin_sub_ne_zero {F : Filter ℝ} {t : ℝ}
    (hF : F ≤ 𝓝[≠] t) : ∀ᶠ s in F, Real.sin (s - t) ≠ 0 := by
  have hn : Tendsto (fun s : ℝ ↦ s - t) F (𝓝 0) := by
    simpa using (tendsto_id.mono_right (hF.trans nhdsWithin_le_nhds)).sub_const t
  have hnear := hn.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)
  have hne : ∀ᶠ s in F, s ≠ t := hF self_mem_nhdsWithin
  filter_upwards [hnear, hne] with s hs hst
  exact mt (Real.sin_eq_zero_iff_of_lt_of_lt hs.1 hs.2).mp (sub_ne_zero.mpr hst)

private theorem tendsto_outerCorner_slope {F : Filter ℝ} {t : ℝ}
    (K : ConvexBody Point) (hF : F ≤ 𝓝[≠] t) (p q : Point)
    (hp : Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      F (𝓝 p))
    (hq : Tendsto (fun s : ℝ ↦ supportingIntersection K
      ((t + Real.pi / 2 : ℝ) : Real.Angle) ((s + Real.pi / 2 : ℝ) : Real.Angle)) F (𝓝 q)) :
    Tendsto (fun s : ℝ ↦ (s - t)⁻¹ •
      ((rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner -
        (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)) F
      (𝓝 (inner ℝ (p - (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ (q - (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle))) := by
  let y (s : ℝ) := (rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner
  have hy : Tendsto y F (𝓝 (y t)) :=
    (continuous_outerCorner K).continuousAt.tendsto.mono_left (hF.trans nhdsWithin_le_nhds)
  have hA := tendsto_normal_slope hF 0 y
    (fun s ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle)) p hy hp
    (Eventually.of_forall fun s ↦ by
      simp only [add_zero, supportingIntersection_inner_left, y, outerCorner_inner_normal])
    (by
      filter_upwards [eventually_sin_sub_ne_zero hF] with s hs
      simp only [add_zero, y, outerCorner_inner_normal]
      exact supportingIntersection_inner_right K t s hs)
  simp only [add_zero] at hA
  have hC := tendsto_normal_slope hF (Real.pi / 2) y
    (fun s ↦ supportingIntersection K ((t + Real.pi / 2 : ℝ) : Real.Angle)
      ((s + Real.pi / 2 : ℝ) : Real.Angle)) q hy hq
    (Eventually.of_forall fun s ↦ by
      rw [supportingIntersection_inner_left]
      simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, y, outerCorner_inner_tangent])
    (by
      filter_upwards [eventually_sin_sub_ne_zero hF] with s hs
      rw [supportingIntersection_inner_right K (t + Real.pi / 2) (s + Real.pi / 2)
        (by simpa only [add_sub_add_right_eq_sub] using hs)]
      simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, y, outerCorner_inner_tangent])
  simp only [Real.Angle.coe_add, normalVector_add_pi_div_two] at hC
  have hCt : tangentVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
      -normalVector (t : Real.Angle) := tangentVector_add_pi_div_two t
  rw [hCt] at hC
  have hsum := (hA.smul (tendsto_const_nhds (x := normalVector (t : Real.Angle)))).add
    (hC.smul (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  simpa only [inner_normalVector_smul_add_inner_tangentVector_smul] using hsum

private theorem hasDerivWithinAt_outerCorner_right (K : RightAngleCapSpace) (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle)) (Set.Ici t) t := by
  have hshift : Tendsto (fun s : ℝ ↦ s + Real.pi / 2) (𝓝[>] t) (𝓝[>] (t + Real.pi / 2)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.add_const _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    change t + Real.pi / 2 < s + Real.pi / 2
    linarith [show t < s from hs]
  have h := tendsto_outerCorner_slope K.val (nhdsGT_le_nhdsNE t)
    (edgeVertices K.val (t : Real.Angle)).1
    (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
    (contact_oneSided_limits K.val t).2.2.1
    (((contact_oneSided_limits K.val (t + Real.pi / 2)).2.2.1).comp hshift)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left]
  have heq :
      inner ℝ ((edgeVertices K.val (t : Real.Angle)).1 -
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
          (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle) =
      -(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle) := by
    simp only [tangentArmLengths, capVertices, inner_sub_left, inner_neg_right]
    module
  rw [heq] at h
  convert h using 1
  funext s
  exact slope_def_module _ _ _

private theorem tendsto_supportingIntersection_left_ordered (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  apply (contact_oneSided_limits K t).2.2.2.2.2.congr'
  filter_upwards [eventually_sin_sub_ne_zero (nhdsLT_le_nhdsNE t)] with s hs
  exact (supportingIntersection_comm K t s hs).symm

private theorem hasDerivWithinAt_outerCorner_left (K : RightAngleCapSpace) (t : ℝ) :
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle)) (Set.Iic t) t := by
  have hshift : Tendsto (fun s : ℝ ↦ s + Real.pi / 2) (𝓝[<] t) (𝓝[<] (t + Real.pi / 2)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.add_const _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s + Real.pi / 2 < t + Real.pi / 2
    linarith [show s < t from hs]
  have h := tendsto_outerCorner_slope K.val (nhdsLT_le_nhdsNE t)
    (edgeVertices K.val (t : Real.Angle)).2
    (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2
    (tendsto_supportingIntersection_left_ordered K.val t)
    ((tendsto_supportingIntersection_left_ordered K.val (t + Real.pi / 2)).comp hshift)
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_sdiff_right]
  have heq :
      inner ℝ ((edgeVertices K.val (t : Real.Angle)).2 -
        (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (tangentVector (t : Real.Angle)) • normalVector (t : Real.Angle) +
        inner ℝ ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
          (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner)
          (-normalVector (t : Real.Angle)) • tangentVector (t : Real.Angle) =
      -(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
        (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle) := by
    simp only [tangentArmLengths, capVertices, inner_sub_left, inner_neg_right]
    module
  rw [heq] at h
  convert h using 1
  funext s
  exact slope_def_module _ _ _

theorem capCorners_oneSided_derivatives (K : RightAngleCapSpace) :
    (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(tangentArmLengths K t).1.1 • normalVector (t : Real.Angle) +
          (tangentArmLengths K t).2.1 • tangentVector (t : Real.Angle)) (Set.Ici t) t ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).innerCorner)
        (-((tangentArmLengths K t).1.1 - 1) • normalVector (t : Real.Angle) +
          ((tangentArmLengths K t).2.1 - 1) • tangentVector (t : Real.Angle)) (Set.Ici t) t) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(tangentArmLengths K t).1.2 • normalVector (t : Real.Angle) +
          (tangentArmLengths K t).2.2 • tangentVector (t : Real.Angle)) (Set.Iic t) t ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).innerCorner)
        (-((tangentArmLengths K t).1.2 - 1) • normalVector (t : Real.Angle) +
          ((tangentArmLengths K t).2.2 - 1) • tangentVector (t : Real.Angle)) (Set.Iic t) t) := by
  constructor
  · intro t _
    have hout := hasDerivWithinAt_outerCorner_right K t
    refine ⟨hout, ?_⟩
    convert hout.sub ((hasDerivAt_normalVector t).hasDerivWithinAt.add
      (hasDerivAt_tangentVector t).hasDerivWithinAt) using 1
    · funext s
      exact eq_sub_of_add_eq (outerCorner_eq_innerCorner_add K.val s).symm
    · module
  · intro t _
    have hout := hasDerivWithinAt_outerCorner_left K t
    refine ⟨hout, ?_⟩
    convert hout.sub ((hasDerivAt_normalVector t).hasDerivWithinAt.add
      (hasDerivAt_tangentVector t).hasDerivWithinAt) using 1
    · funext s
      exact eq_sub_of_add_eq (outerCorner_eq_innerCorner_add K.val s).symm
    · module

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

* `Cap.Regularity`.
* `Cap.Tail.Contacts`.
* `Cap.Tail.Bodies`.
* `Cap.Tail.Extension`.
* `Cap.Tail.Separation`.
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
# Cap / Regularity
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace MovingSofa

private theorem continuous_nondegenerateCapData_right (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 := by
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    (fun t : ℝ ↦ (capVertices K t).1.1) ((capVertices K (Real.pi / 2)).1.2)
    (fun t ht ↦ (contact_oneSided_limits K.1 t).1)
    (fun t ht ↦ ?_) (contact_oneSided_limits K.1 (Real.pi / 2)).2.2.2.1
  · apply (continuousOn_iff_continuous_domRestrict.mp h).congr
    intro t
    dsimp [Set.domRestrict, nondegenerateCapData]
    split_ifs with heq
    · rw [heq]
    · rfl
  · have heq := (capDensities_contact_eq K hD).1 t ⟨ht.1.le, ht.2⟩ |>.1
    change (edgeVertices K.1 (t : Real.Angle)).1 =
      (edgeVertices K.1 (t : Real.Angle)).2 at heq
    simpa only [← heq, capVertices] using (contact_oneSided_limits K.1 t).2.2.2.1

private theorem continuous_nondegenerateCapData_left (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.2 := by
  let f : ℝ → Point := fun t ↦ (capVertices K t).2.1
  have hr (t : ℝ) : Tendsto f (𝓝[>] t) (𝓝 (f t)) := by
    apply (contact_oneSided_limits K.1 (t + Real.pi / 2)).1.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change t + Real.pi / 2 < u + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Ioi.mp hu) (Real.pi / 2)
  have hl (t : ℝ) (ht : t ∈ Ioc 0 (Real.pi / 2)) :
      Tendsto f (𝓝[<] t) (𝓝 (f t)) := by
    have h := (contact_oneSided_limits K.1 (t + Real.pi / 2)).2.2.2.1
    have heq := (capDensities_contact_eq K hD).2 t ht |>.1
    change (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 =
      (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 at heq
    rw [← heq] at h
    apply h.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change u + Real.pi / 2 < t + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Iio.mp hu) (Real.pi / 2)
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    f (f (Real.pi / 2)) (fun t _ ↦ hr t) (fun t ht ↦ hl t ⟨ht.1, ht.2.le⟩)
    (hl (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hc : ContinuousOn f (Icc 0 (Real.pi / 2)) := h.congr fun t ht ↦ by
    by_cases heq : t = Real.pi / 2 <;> simp [heq]
  change Continuous ((Icc 0 (Real.pi / 2)).domRestrict f)
  exact continuousOn_iff_continuous_domRestrict.mp hc

private theorem continuous_nondegenerateCapData_arms (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 := by
  have hy := (continuous_outerCorner K.1).comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  constructor
  · apply ((hy.sub (continuous_nondegenerateCapData_right K hD)).inner hv).congr
    intro t
    dsimp [nondegenerateCapData, tangentArmLengths]
    split_ifs <;> rfl
  · exact (hy.sub (continuous_nondegenerateCapData_left K hD)).inner hn

private theorem nondegenerateCap_hasDerivWithinAt (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) (t : Icc (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (capInnerCorner K)
      (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
        ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) ∧
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
        (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hr (ht : (t : ℝ) < Real.pi / 2) :=
    (capCorners_oneSided_derivatives K).1 t ⟨t.property.1, ht⟩
  have hl (ht : 0 < (t : ℝ)) :=
    (capCorners_oneSided_derivatives K).2 t ⟨ht, t.property.2⟩
  have hfplus (ht : (t : ℝ) < Real.pi / 2) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.1 := by
    simp only [nondegenerateCapData, ite_eq_right ht.ne]
  have hfminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.2 := by
    dsimp [nondegenerateCapData]
    split_ifs with heq
    · rfl
    · exact ((capDensities_contact_eq K hD).1 t
        ⟨t.property.1, lt_of_le_of_ne t.property.2 heq⟩).2
  have hgminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.2 t = (tangentArmLengths K t).2.2 :=
    ((capDensities_contact_eq K hD).2 t ⟨ht, t.property.2⟩).2
  constructor
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).2
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).2
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).1
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).1

theorem nondegenerateCap_continuity (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 ∧
    Continuous (nondegenerateCapData K hD).1.2 ∧
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ContDiffOn ℝ 1
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K)
        (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
          ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
          (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hA := continuous_nondegenerateCapData_right K hD
  have hC := continuous_nondegenerateCapData_left K hD
  obtain ⟨hf, hg⟩ := continuous_nondegenerateCapData_arms K hD
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  refine ⟨hA, hC, hf, hg, ?_, ?_, nondegenerateCap_hasDerivWithinAt K hD⟩
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      (((hf.sub continuous_const).neg.smul hn).add ((hg.sub continuous_const).smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).1)
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      ((hf.neg.smul hn).add (hg.smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).2)

/-- The corner coordinates of a right-angle cap in its moving frame. -/
theorem inner_capInnerCorner (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  constructor
  · have h := inner_supportingPlacement_normalVector (K.1 : Set Point) (t : Real.Angle) 0
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h
  · have h := inner_supportingPlacement_tangentVector (K.1 : Set Point) (t : Real.Angle) 0
    rw [← Real.Angle.coe_add] at h
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h

/-- The injectivity condition supplies the support derivatives with their strict signs. -/
theorem capSupport_hasDerivAt (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) :
    ∃ dh dj : ℝ → ℝ,
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dh t) t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dj t)
          (t + Real.pi / 2)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        dh t - supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 < dj t + supportValue (K.1 : Set Point) (t : Real.Angle) - 1) := by
  obtain ⟨-, hC1, hsign⟩ := hinj
  have hxn : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) (t : Real.Angle) - 1 := fun t => (inner_capInnerCorner K t).1
  have hxt : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t => (inner_capInnerCorner K t).2
  have hdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (capInnerCorner K) (deriv (capInnerCorner K) t) t := by
    intro t ht
    have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    exact (((hC1.differentiableOn one_ne_zero) t (Set.Ioo_subset_Icc_self ht)).differentiableAt
      hmem).hasDerivAt
  have hderivEq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t = deriv (capInnerCorner K) t :=
    fun t ht => derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hfunn : (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (normalVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxn u]; ring
  have hfunt :
      (fun u : ℝ ↦ supportValue (K.1 : Set Point) ((u + Real.pi / 2 : ℝ) : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (tangentVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxt u]; ring
  refine ⟨fun t ↦ inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (normalVector (t : Real.Angle)),
    fun t ↦ -inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (tangentVector (t : Real.Angle)), ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hfunn]
    exact ((hdiff t ht).inner ℝ (hasDerivAt_normalVector t)).add_const 1
  · intro t ht
    refine (hasDerivAt_comp_add_const_iff (f := fun u : ℝ ↦
      supportValue (K.1 : Set Point) (u : Real.Angle)) t (Real.pi / 2)).mp ?_
    rw [hfunt]
    have hd := ((hdiff t ht).inner ℝ (hasDerivAt_tangentVector t)).add_const 1
    rw [inner_neg_right] at hd
    exact hd
  · intro t ht
    have h1 := (hsign t ht).1
    rw [hderivEq t ht] at h1
    dsimp only
    rw [hxt t]
    linarith only [h1]
  · intro t ht
    have h2 := (hsign t ht).2
    rw [hderivEq t ht] at h2
    dsimp only
    rw [hxn t]
    linarith only [h2]
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
# Endpoint contacts for the canonical cap tails

The right and left canonical tails of a special cap are cut out of the cap by the upper
half-planes of its inner supporting walls. This file supplies the contact points that make the
tail support values meet their endpoint bounds.

The mathematical content is the frame-free lemma
`exists_mem_inner_eq_sub_one_of_deriv_signs`: let `s` be a nonempty compact convex planar set
lying above the horizontal axis with `h_s(pi/2) = 1`, whose support function `h` is
differentiable on the two quarter-turn families with the strict corner velocity signs
`h'(t) - h(t + pi/2) + 1 < 0` and `h'(t + pi/2) + h(t) - 1 > 0` for `t` in `(0, pi/2)`. Then
every interior cut line `{q | inner q (normalVector t) = h(t) - 1}` meets `s` in a point that
stays above the whole cut family on `[t, pi/2]`.

The proof selects the transverse maximum `p` of the first cut section and studies the
deficiency `g(t) = h(t) - inner p (normalVector t)`. Wherever `g(t) = 1`, the chord joining the
two frame contacts has nonpositive signed area (`planeCrossProduct_nonpos_of_isMaxOn`), which
forces `g` to decrease strictly at the cut angle; at a first return of `g` to level one the
same determinant is strictly positive, a contradiction.

The left tail follows from the same lemma applied to `reflectedBody (pi/2) K`, whose support
derivatives are the negated right-hand ones read backwards; see `exists_left_tail_contact`.

This argument replaces the step in the paper's proof of `lem:right-left-body` which infers that the
upper boundary avoids the niche; that inference fails for the stated class of caps (P46 in
`NOTES.md`).
-/

public section

noncomputable section

namespace MovingSofa

/-- Lowering a right-angle cap point vertically to the base line keeps it inside the cap. -/
theorem basePoint_mem_of_rightAngleCap (K : RightAngleCapSpace) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) : (!₂[q 0, 0] : Point) ∈ (K.1 : Set Point) := by
  have hq0 : (!₂[q 0, 0] : Point) 0 = q 0 := rfl
  have hq1 : (!₂[q 0, 0] : Point) 1 = 0 := rfl
  have hqy : 0 ≤ q 1 := by
    have h := K.inner_normalVector_pi_div_two_nonneg hq
    rwa [inner_normalVector_pi_div_two] at h
  have hzero : inner ℝ (!₂[q 0, 0] : Point)
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_normalVector_pi_div_two, hq1]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  have hqt := inner_le_supportValue_of_isCompact K.1.isCompact hq (t : Real.Angle)
  rw [inner_normalVector_real] at hqt
  rw [inner_normalVector_real, hq0, hq1]
  nlinarith only [hqt, hsin, hqy]

/-- The two frame contacts at an interior angle, with their derivative coordinates. -/
theorem exists_frame_contacts {s : Set Point} (hcomp : IsCompact s) (hne : s.Nonempty)
    {t dh dj : ℝ}
    (hdh : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dh t)
    (hdj : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dj (t + Real.pi / 2)) :
    ∃ A ∈ s, ∃ C ∈ s,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = dh ∧
      inner ℝ C (normalVector (t : Real.Angle)) = -dj ∧
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  obtain ⟨A, hA, hA1, hA2⟩ := exists_contact_of_hasDerivAt hcomp hne hdh
  obtain ⟨C, hC, hC1, hC2⟩ := exists_contact_of_hasDerivAt hcomp hne hdj
  have hnv : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (t : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact normalVector_add_pi_div_two (t : Real.Angle)
  have htv : tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector (t : Real.Angle) := tangentVector_add_pi_div_two t
  rw [hnv] at hC1
  rw [htv, inner_neg_right] at hC2
  exact ⟨A, hA, C, hC, hA1, hA2, by linarith, hC1⟩

/-- A transverse chord through a maximizing section point has nonpositive signed area. -/
theorem planeCrossProduct_nonpos_of_isMaxOn {s : Set Point} (hconv : Convex ℝ s)
    {r c₀ : ℝ} {p : Point}
    (hpline : inner ℝ p (normalVector (r : Real.Angle)) = c₀)
    (hmax : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) = c₀ →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤ inner ℝ p (tangentVector (r : Real.Angle)))
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s)
    (hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)))
    (hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0) :
    planeCrossProduct (A - p) (C - p) ≤ 0 := by
  set u := normalVector (r : Real.Angle) with hu
  set v := tangentVector (r : Real.Angle) with hv
  set mu : ℝ := inner ℝ (A - p) u with hmu
  set la : ℝ := -inner ℝ (C - p) u with hla
  have hlapos : 0 < la := by simp only [hla]; linarith
  have hsum : 0 < la + mu := by linarith
  set w : ℝ := la / (la + mu) with hw
  have hw0 : 0 ≤ w := div_nonneg hlapos.le hsum.le
  have hw1 : 0 ≤ 1 - w := by
    rw [hw, sub_nonneg, div_le_one hsum]
    linarith
  set q : Point := w • A + (1 - w) • C with hq
  have hqs : q ∈ s := hconv hA hC hw0 hw1 (by ring)
  have hwmu : w * mu + (1 - w) * (-la) = 0 := by
    rw [hw]; field_simp; ring
  have hqu : inner ℝ q u = c₀ := by
    have h1 : inner ℝ q u - inner ℝ p u = w * mu + (1 - w) * (-la) := by
      simp only [hq, hmu, hla, inner_add_left, real_inner_smul_left, inner_sub_left]
      ring
    rw [hwmu] at h1
    rw [hpline] at h1
    linarith
  have hqv := hmax q hqs hqu
  have h2 : inner ℝ q v - inner ℝ p v =
      w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v := by
    simp only [hq, inner_add_left, real_inner_smul_left, inner_sub_left]
    ring
  have hnum : w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v ≤ 0 := by
    rw [← h2]; linarith
  have hcross : planeCrossProduct (A - p) (C - p) =
      mu * inner ℝ (C - p) v - inner ℝ (A - p) v * (-la) := by
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) r, ← hu, ← hv, ← hmu]
    simp only [hla]
    ring
  rw [hcross]
  have hwid : (1 - w) * (la + mu) = mu := by rw [hw]; field_simp; ring
  have hwid2 : w * (la + mu) = la := by rw [hw]; field_simp
  have hexp : (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu) =
      la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by
    calc (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu)
        = (w * (la + mu)) * inner ℝ (A - p) v +
          ((1 - w) * (la + mu)) * inner ℝ (C - p) v := by ring
      _ = la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by rw [hwid, hwid2]
  have hmul := mul_nonpos_of_nonpos_of_nonneg hnum hsum.le
  rw [hexp] at hmul
  linarith

/-- The three chord signs at a first return time, in the frame coordinates at that time. -/
private theorem chord_signs {r t d al be : ℝ} (hr : 0 < r) (hrt : r < t)
    (ht : t < Real.pi / 2) (hd : 0 ≤ d) (hal : al < 0) (hbe : 0 < be)
    (hstrip : Real.sin t + Real.cos t * d ≤ 1) :
    0 < Real.cos (t - r) - Real.sin (t - r) * d ∧
      Real.cos (t - r) * (-be) - Real.sin (t - r) * (1 - al + d) < 0 ∧
      0 < 1 - al + d + be * d := by
  have hpi := Real.pi_pos
  have hδpos : 0 < t - r := by linarith only [hrt]
  have hδlt : t - r < Real.pi / 2 := by linarith only [hr, ht]
  have hsinδ : 0 < Real.sin (t - r) :=
    Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith only [hpi, hδlt])
  have hcosδ : 0 < Real.cos (t - r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hδpos], hδlt⟩
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hr, hrt], ht⟩
  have hcosr : Real.cos (t - r) * Real.cos t + Real.sin (t - r) * Real.sin t = Real.cos r := by
    rw [← Real.cos_sub, show t - r - t = -r by ring, Real.cos_neg]
  have hcosrgt : Real.sin (t - r) < Real.cos r := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hpi, hδpos])
      (by linarith only [hr]) (by linarith only [ht])
  refine ⟨?_, ?_, by nlinarith only [hal, hbe, hd]⟩
  · have hmul := mul_le_mul_of_nonneg_left hstrip hsinδ.le
    have hstep : Real.cos r - Real.sin (t - r) ≤
        Real.cos t * (Real.cos (t - r) - Real.sin (t - r) * d) := by
      nlinarith only [hmul, hcosr]
    by_contra hc
    push Not at hc
    nlinarith only [hstep, hc, hcost, hcosrgt]
  · nlinarith only [hcosδ, hsinδ, hbe, hal, hd]

/-- Contradiction sign lemma at the cut angle: a nonpositive determinant forces a negative slope. -/
private theorem neg_of_det_nonpos {d al be : ℝ} (hal : al < 0) (hbe : 0 < be)
    (hdet : 1 - al + d + be * d ≤ 0) : d < 0 := by
  by_contra h
  push Not at h
  nlinarith only [hal, hbe, hdet, h]

/-- Endpoint contact for the upper cut family of a strip body with strict corner velocities. -/
theorem exists_mem_inner_eq_sub_one_of_deriv_signs
    {s : Set Point} (hcomp : IsCompact s) (hconv : Convex ℝ s) (hne : s.Nonempty)
    (dh dj : ℝ → ℝ)
    (hdh : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dh t) t)
    (hdj : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dj t) (t + Real.pi / 2))
    (halpha : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      dh t - supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0)
    (hbeta : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < dj t + supportValue s (t : Real.Angle) - 1)
    (htop : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hlow : ∀ q ∈ s, 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ s, inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue s (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue s (t : Real.Angle) - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  -- the cut line at `r` meets the body, between the two frame contacts
  obtain ⟨A₀, hA₀, C₀, hC₀, hA₀n, hA₀t, hC₀n, hC₀t⟩ :=
    exists_frame_contacts hcomp hne (hdh r hr) (hdj r hr)
  have hC₀le : inner ℝ C₀ (normalVector (r : Real.Angle)) ≤
      supportValue s (r : Real.Angle) - 1 := by
    rw [hC₀n]; linarith only [hbeta r hr]
  have hA₀ge : supportValue s (r : Real.Angle) - 1 ≤
      inner ℝ A₀ (normalVector (r : Real.Angle)) := by rw [hA₀n]; linarith only []
  obtain ⟨p₀, hp₀, hp₀line⟩ :=
    exists_mem_inner_eq_of_convex hconv hA₀ hC₀ hC₀le hA₀ge
  -- the transverse maximizer on that cut section
  have hcontinner : Continuous (fun q : Point ↦ inner ℝ q (normalVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hScomp : IsCompact (s ∩ {q : Point |
      inner ℝ q (normalVector (r : Real.Angle)) = supportValue s (r : Real.Angle) - 1}) :=
    hcomp.inter_right (isClosed_eq hcontinner continuous_const)
  have hconttang : Continuous (fun q : Point ↦ inner ℝ q (tangentVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  obtain ⟨p, hpS, hpmax⟩ :=
    hScomp.exists_isMaxOn ⟨p₀, hp₀, hp₀line⟩ hconttang.continuousOn
  have hps : p ∈ s := hpS.1
  have hpline : inner ℝ p (normalVector (r : Real.Angle)) =
    supportValue s (r : Real.Angle) - 1 := hpS.2
  have hmaxq : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) =
      supportValue s (r : Real.Angle) - 1 →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤
        inner ℝ p (tangentVector (r : Real.Angle)) := fun q hq hq2 => hpmax ⟨hq, hq2⟩
  -- the deficiency function
  set g : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ p (normalVector (u : Real.Angle)) with hgdef
  have hgval : ∀ u : ℝ, g u = supportValue s (u : Real.Angle) -
      inner ℝ p (normalVector (u : Real.Angle)) := fun _ => rfl
  have hgr : g r = 1 := by rw [hgval, hpline]; ring
  have hgderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt g (dh t - inner ℝ p (tangentVector (t : Real.Angle))) t :=
    fun t ht => (hdh t ht).sub (hasDerivAt_inner_normalVector p t)
  have hgT : g (Real.pi / 2) ≤ 1 := by
    rw [hgval, htop]
    linarith only [hlow p hps]
  -- coordinates of the two contact chords relative to the maximizer
  have hcoords : ∀ t : ℝ, g t = 1 → ∀ A C : Point,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) →
      inner ℝ A (tangentVector (t : Real.Angle)) = dh t →
      inner ℝ C (normalVector (t : Real.Angle)) = -dj t →
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) →
      inner ℝ (A - p) (normalVector (t : Real.Angle)) = 1 ∧
      inner ℝ (A - p) (tangentVector (t : Real.Angle)) =
        dh t - inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ (C - p) (normalVector (t : Real.Angle)) =
        -dj t - (supportValue s (t : Real.Angle) - 1) ∧
      inner ℝ (C - p) (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ p (tangentVector (t : Real.Angle)) := by
    intro t hgt A C e1 e2 e3 e4
    have hpu : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue s (t : Real.Angle) - 1 := by
      have h := hgval t
      rw [hgt] at h
      linarith only [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [inner_sub_left, e1, hpu]; ring
    · simp only [inner_sub_left, e2]
    · simp only [inner_sub_left, e3, hpu]
    · simp only [inner_sub_left, e4]
  -- the deficiency decreases strictly at the cut angle
  have hdgr : dh r - inner ℝ p (tangentVector (r : Real.Angle)) < 0 := by
    obtain ⟨k1, k2, k3, k4⟩ := hcoords r hgr A₀ C₀ hA₀n hA₀t hC₀n hC₀t
    have hApos : 0 < inner ℝ (A₀ - p) (normalVector (r : Real.Angle)) := by
      rw [k1]; norm_num
    have hCneg : inner ℝ (C₀ - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [k3]; linarith only [hbeta r hr]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA₀ hC₀ hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A₀ - p) (C₀ - p) r, k1, k2, k3, k4] at hcr
    exact neg_of_det_nonpos (halpha r hr) (hbeta r hr) (by linarith only [hcr])
  -- the deficiency never exceeds one on the cut range
  have hmain : ∀ t ∈ Set.Icc r (Real.pi / 2), g t ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁mem, ht₁gt⟩ := hcon
    have ht₁r : r < t₁ :=
      lt_of_le_of_ne ht₁mem.1 (by rintro rfl; rw [hgr] at ht₁gt; exact lt_irrefl 1 ht₁gt)
    have ht₁T : t₁ < Real.pi / 2 :=
      lt_of_le_of_ne ht₁mem.2 (by rintro rfl; exact absurd hgT (not_le.mpr ht₁gt))
    -- a time just to the right of the cut where the deficiency is below one
    have hev : ∀ᶠ y in nhdsWithin r (Set.Ioi r), slope g r y < 0 := by
      refine (((hasDerivAt_iff_tendsto_slope.mp (hgderiv r hr)).mono_left
        (nhdsWithin_mono r fun x hx => ne_of_gt hx)).eventually_lt_const hdgr)
    obtain ⟨r', hr'slope, hr'mem⟩ :=
      (hev.and (Filter.eventually_of_mem (Ioo_mem_nhdsGT ht₁r) fun y hy => hy)).exists
    have hrr' : r < r' := hr'mem.1
    have hr't₁ : r' < t₁ := hr'mem.2
    have hgr'lt : g r' < 1 := by
      rw [slope_def_field] at hr'slope
      have hnum : g r' - g r < 0 := by
        by_contra hcc
        push Not at hcc
        have h0 : 0 ≤ (g r' - g r) / (r' - r) := div_nonneg hcc (by linarith only [hrr'])
        linarith only [h0, hr'slope]
      linarith only [hnum, hgr]
    -- the first return to level one
    have hgcontOn : ContinuousOn g (Set.Icc r' t₁) := fun u hu =>
      ((hgderiv u ⟨by linarith only [hu.1, hrr', hr.1],
        by linarith only [hu.2, ht₁T]⟩).continuousAt).continuousWithinAt
    obtain ⟨t₂, ht₂mem', hgt₂, hleft⟩ :=
      exists_first_return hr't₁ hgcontOn hgr'lt ht₁gt.le
    have ht₂gt : r' < t₂ := ht₂mem'.1
    have ht₂mem : t₂ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [hr.1, hrr', ht₂gt], lt_of_le_of_lt ht₂mem'.2 ht₁T⟩
    have hdgt₂ : 0 ≤ dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle)) :=
      nonneg_of_first_return ht₂gt (hgderiv t₂ ht₂mem) hgt₂ hleft
    -- the transverse signs at the first return
    obtain ⟨A, hA, C, hC, e1, e2, e3, e4⟩ :=
      exists_frame_contacts hcomp hne (hdh t₂ ht₂mem) (hdj t₂ ht₂mem)
    obtain ⟨k1, k2, k3, k4⟩ := hcoords t₂ hgt₂ A C e1 e2 e3 e4
    have hframeR : normalVector (r : Real.Angle) =
        Real.cos (t₂ - r) • normalVector (t₂ : Real.Angle) -
          Real.sin (t₂ - r) • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((r : ℝ) : Real.Angle) = ((t₂ + -(t₂ - r) : ℝ) : Real.Angle) := by
        congr 1; ring
      rw [hrew, normalVector_add_real t₂ (-(t₂ - r)), Real.cos_neg, Real.sin_neg]
      module
    have hframeT : normalVector ((Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin t₂ • normalVector (t₂ : Real.Angle) +
          Real.cos t₂ • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((Real.pi / 2 : ℝ) : Real.Angle) =
          ((t₂ + (Real.pi / 2 - t₂) : ℝ) : Real.Angle) := by norm_num
      rw [hrew, normalVector_add_real t₂ (Real.pi / 2 - t₂), Real.cos_pi_div_two_sub,
        Real.sin_pi_div_two_sub]
    have hAT : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.sin t₂ * 1 + Real.cos t₂ *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeT, inner_add_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hstrip : Real.sin t₂ + Real.cos t₂ *
        (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) ≤ 1 := by
      have h1 := inner_le_supportValue_of_isCompact hcomp hA ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [htop] at h1
      have h2 : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
        rw [inner_sub_left]
        linarith only [h1, hlow p hps]
      rw [hAT] at h2
      linarith only [h2]
    obtain ⟨hs1, hs2, hs3⟩ := chord_signs hr.1 (by linarith only [hrr', ht₂gt])
      ht₂mem.2 hdgt₂ (halpha t₂ ht₂mem) (hbeta t₂ ht₂mem) hstrip
    have hAr : inner ℝ (A - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * 1 - Real.sin (t₂ - r) *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hCr : inner ℝ (C - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * (-dj t₂ - (supportValue s (t₂ : Real.Angle) - 1)) -
          Real.sin (t₂ - r) * (supportValue s ((t₂ + Real.pi / 2 : ℝ) : Real.Angle) -
            inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k3, k4]
    have hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)) := by
      rw [hAr]; linarith only [hs1]
    have hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [hCr]; linarith only [hs2]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA hC hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) t₂, k1, k2, k3, k4] at hcr
    linarith only [hcr, hs3]
  refine ⟨p, hps, hpline, fun t ht => ?_⟩
  have hle := hmain t ht
  rw [hgval] at hle
  linarith only [hle]

/-- The lowered horizontal extremes of a right-angle cap lie under all right and left cuts. -/
theorem exists_cap_base_points (K : RightAngleCapSpace) :
    ∃ pR ∈ (K.1 : Set Point), ∃ pL ∈ (K.1 : Set Point),
      inner ℝ pR (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      inner ℝ pL (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ pR (normalVector (t : Real.Angle))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ pL (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
  have hheight : ∀ q ∈ (K.1 : Set Point), 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q hq
    have hlo := K.inner_normalVector_pi_div_two_nonneg hq
    have hhi := inner_le_supportValue_of_isCompact K.1.isCompact hq
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hhi
    rw [inner_normalVector_pi_div_two] at hlo hhi
    exact ⟨hlo, hhi⟩
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.1 ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.1 ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hAmax : ∀ q ∈ (K.1 : Set Point), q 0 ≤ A 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((0 : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at h
    linarith only [h, hAeq]
  have hCmin : ∀ q ∈ (K.1 : Set Point), C 0 ≤ q 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at h
    linarith only [h, hCeq]
  refine ⟨!₂[A 0, 0], basePoint_mem_of_rightAngleCap K hA, !₂[C 0, 0],
    basePoint_mem_of_rightAngleCap K hC, ?_, ?_, ?_, ?_⟩
  · rw [inner_normalVector_pi_div_two]; rfl
  · rw [inner_normalVector_pi_div_two]; rfl
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
    have hbound : supportValue (K.1 : Set Point) (t : Real.Angle) ≤ A 0 * Real.cos t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real]
      nlinarith only [hAmax q hq, (hheight q hq).2, hcos, hsin, hsin1]
    rw [inner_normalVector_real]
    change supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤ A 0 * Real.cos t + 0 * Real.sin t
    linarith only [hbound]
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hbound : supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        -(C 0) * Real.sin t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
      nlinarith only [hCmin q hq, (hheight q hq).2, hcos, hcos1, hsin]
    rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    change supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      C 0 * -Real.sin t + 0 * Real.cos t
    linarith only [hbound]

/-- The right cut line meets the cap, below the whole right cut family. -/
theorem exists_right_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue (K.1 : Set Point) (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  exact exists_mem_inner_eq_sub_one_of_deriv_signs K.1.isCompact K.1.convex K.1.nonempty
    dh dj h1 h2 h3 h4 K.property.2.2.2.1
    (fun q hq => K.inner_normalVector_pi_div_two_nonneg hq) hr

/-- The left cut line meets the cap, below the whole left cut family. -/
theorem exists_left_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {l : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) l,
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have hsv : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi - u : ℝ) : Real.Angle) :=
    supportValue_reflectedBody_pi_div_two K.1
  have hfunS : (fun w : ℝ ↦ supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
      (w : Real.Angle)) =
      fun w : ℝ ↦ supportValue (K.1 : Set Point) ((Real.pi - w : ℝ) : Real.Angle) :=
    funext hsv
  have hrefl : ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Real.pi / 2 - u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have hsvL : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
          ((u + Real.pi / 2 : ℝ) : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u : ℝ) : Real.Angle) := by
    intro u
    rw [hsv (u + Real.pi / 2),
      hcast _ _ (show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring)]
  have hsvR : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u + Real.pi / 2 : ℝ) : Real.Angle) := by
    intro u
    rw [hsv u, hcast _ _ (show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring)]
  obtain ⟨q0, hq0s, hq0line, hq0bound⟩ :=
    exists_mem_inner_eq_sub_one_of_deriv_signs
      (reflectedBody (Real.pi / 2) K.1).isCompact (reflectedBody (Real.pi / 2) K.1).convex
      (reflectedBody (Real.pi / 2) K.1).nonempty
      (fun u ↦ -dj (Real.pi / 2 - u)) (fun u ↦ -dh (Real.pi / 2 - u))
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dj (Real.pi / 2 - u)) (Real.pi - u) := by
          rw [show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring]
          exact h2 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi u hF)
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dh (Real.pi / 2 - u)) (Real.pi - (u + Real.pi / 2)) := by
          rw [show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring]
          exact h1 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi (u + Real.pi / 2) hF)
      (by
        intro u hu
        rw [hsvL u]
        linarith only [h4 _ (hrefl u hu)])
      (by
        intro u hu
        rw [hsvR u]
        linarith only [h3 _ (hrefl u hu)])
      (by
        rw [hsv (Real.pi / 2), hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.property.2.2.2.1)
      (by
        rintro q ⟨v, hv, rfl⟩
        rw [inner_capReflection_pi_div_two,
          hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.inner_normalVector_pi_div_two_nonneg hv)
      (show Real.pi / 2 - l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from hrefl l hl)
  obtain ⟨p, hpK, rfl⟩ : ∃ p ∈ (K.1 : Set Point), capReflection (Real.pi / 2) p = q0 := hq0s
  refine ⟨p, hpK, ?_, ?_⟩
  · rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    rw [hsv (Real.pi / 2 - l),
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    exact hq0line
  · intro t ht
    have hw : Real.pi / 2 - t ∈ Set.Icc (Real.pi / 2 - l) (Real.pi / 2) :=
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
    have hb := hq0bound (Real.pi / 2 - t) hw
    rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    rw [hsv (Real.pi / 2 - t),
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    exact hb

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
# Cap / Tail / Bodies
-/

public section

noncomputable section

namespace MovingSofa

/-- The distinguished inner wall, upper half-plane, fan point and corner on one side. -/
structure DistinguishedCapSide where
  /-- The distinguished inner supporting wall. -/
  wall : Set Point
  /-- The upper half-plane selected at the distinguished wall. -/
  upperHalfPlane : Set Point
  /-- The corresponding endpoint of the cap fan. -/
  fanPoint : Point
  /-- The inner hallway corner at the distinguished angle. -/
  corner : Point

/-- The right and left cap geometry at the two distinguished Gerver angles. -/
@[expose]
def distinguishedCapSides (K : RightAngleCapSpace) : DistinguishedCapSide × DistinguishedCapSide :=
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  (⟨(rotatingHallwayParts (K.1 : Set Point) (r : Real.Angle)).b,
      (innerWallUpperHalfPlanes K r).1, (wedgeEndpoints K r).1, capInnerCorner K r⟩,
    ⟨(rotatingHallwayParts (K.1 : Set Point) (l : Real.Angle)).d,
      (innerWallUpperHalfPlanes K l).2, (wedgeEndpoints K l).2, capInnerCorner K l⟩)

/-- The right distinguished fan point is the right wedge endpoint at the right Gerver angle. -/
theorem distinguishedCapSides_fst_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.fanPoint = (wedgeEndpoints K paperGerverConstants.2.1).1 := rfl

/-- The right distinguished corner is the inner corner at the right Gerver angle. -/
theorem distinguishedCapSides_fst_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.corner = capInnerCorner K paperGerverConstants.2.1 := rfl

/-- The left distinguished fan point is the left wedge endpoint at the left Gerver angle. -/
theorem distinguishedCapSides_snd_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.fanPoint = (wedgeEndpoints K paperGerverConstants.2.2).2 := rfl

/-- The left distinguished corner is the inner corner at the left Gerver angle. -/
theorem distinguishedCapSides_snd_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.corner = capInnerCorner K paperGerverConstants.2.2 := rfl

/-- Canonical tails are convex bodies and satisfy all support and endpoint-line identities. -/
theorem canonicalTailSets_properties (K : SpecialCapSpace) :
    (canonicalTailSets K).1.Nonempty ∧ IsCompact (canonicalTailSets K).1 ∧ Convex ℝ
      (canonicalTailSets K).1 ∧ (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) ∧
    (canonicalTailSets K).2.Nonempty ∧ IsCompact (canonicalTailSets K).2 ∧ Convex ℝ
      (canonicalTailSets K).2 ∧ (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) ∧
    (∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((Real.pi + paperGerverConstants.2.1 : ℝ) :
      Real.Angle)).1 =
      (distinguishedCapSides K.1).1.wall ∧
    (∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 + paperGerverConstants.2.2
      : ℝ) : Real.Angle)).1 =
      (distinguishedCapSides K.1).2.wall := by
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  -- membership characterizations of the two tails
  have hBmem : ∀ p : Point, p ∈ (canonicalTailSets K).1 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        supportValue (K.1.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  have hDmem : ∀ p : Point, p ∈ (canonicalTailSets K).2 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        supportValue (K.1.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  -- domain properties
  obtain ⟨pR, hpRK, pL, hpLK, hpRy, hpLy, hpRcut, hpLcut⟩ := exists_cap_base_points K.1
  have hpRB : pR ∈ (canonicalTailSets K).1 :=
    (hBmem pR).mpr ⟨hpRK, fun t ht => hpRcut t ⟨le_trans hr.1.le ht.1, ht.2⟩⟩
  have hpLD : pL ∈ (canonicalTailSets K).2 :=
    (hDmem pL).mpr ⟨hpLK, fun t ht => hpLcut t ⟨ht.1, le_trans ht.2 hl.2.le⟩⟩
  have hBne : (canonicalTailSets K).1.Nonempty := ⟨pR, hpRB⟩
  have hDne : (canonicalTailSets K).2.Nonempty := ⟨pL, hpLD⟩
  have hBsub : (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) := fun p hp => ((hBmem p).mp hp).1
  have hDsub : (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) := fun p hp => ((hDmem p).mp hp).1
  have hBcomp : IsCompact (canonicalTailSets K).1 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hDcomp : IsCompact (canonicalTailSets K).2 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hBconv : Convex ℝ (canonicalTailSets K).1 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  have hDconv : Convex ℝ (canonicalTailSets K).2 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  -- the two support inequalities
  have hBbound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) (t : Real.Angle) := by
    intro t ht
    have h := supportValue_le_of_cut hBne (a := t) (b := Real.pi + t)
      (hcast _ _ (by ring)) (fun p hp => ((hBmem p).mp hp).2 t ht)
    linarith only [h]
  have hDbound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) := by
    intro t ht
    have hc : ∀ p ∈ (canonicalTailSets K).2,
        supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((Real.pi / 2 + t : ℝ) : Real.Angle)) := by
      intro p hp
      have h := ((hDmem p).mp hp).2 t ht
      rwa [hcast _ _ (show t + Real.pi / 2 = Real.pi / 2 + t by ring)] at h
    have h := supportValue_le_of_cut hDne (a := Real.pi / 2 + t) (b := 3 * Real.pi / 2 + t)
      (hcast _ _ (by ring)) hc
    linarith only [h]
  -- the four endpoint equalities
  have hBzero :
      supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hBbound (Real.pi / 2) ⟨hr.2.le, le_refl _⟩
      rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hBcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpRB hpRy
      linarith only [h]
  have hDzero :
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hDbound 0 ⟨le_refl _, hl.1.le⟩
      rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpLD hpLy
      linarith only [h]
  obtain ⟨pr, hprK, hprline, hprcut⟩ := exists_right_tail_contact K.1 K.property.1 hr
  obtain ⟨pl, hplK, hplline, hplcut⟩ := exists_left_tail_contact K.1 K.property.1 hl
  have hprB : pr ∈ (canonicalTailSets K).1 := (hBmem pr).mpr ⟨hprK, hprcut⟩
  have hplD : pl ∈ (canonicalTailSets K).2 := (hDmem pl).mpr ⟨hplK, hplcut⟩
  have hBeqR : supportValue (canonicalTailSets K).1
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    refine le_antisymm (hBbound _ ⟨le_refl _, hr.2.le⟩) ?_
    have h := le_supportValue_of_cut hBcomp (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)) hprB hprline
    linarith only [h]
  have hDeqL : supportValue (canonicalTailSets K).2
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    refine le_antisymm (hDbound _ ⟨hl.1.le, le_refl _⟩) ?_
    rw [hcast _ _ (show paperGerverConstants.2.2 + Real.pi / 2 =
      Real.pi / 2 + paperGerverConstants.2.2 by ring)] at hplline
    have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)) hplD hplline
    linarith only [h]
  -- the distinguished walls
  have hwallR : (distinguishedCapSides K.1).1.wall =
      normalLine ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
        (supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).2.2.2.2.1
  have hwallL : (distinguishedCapSides K.1).2.wall =
      normalLine
        (((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
        (supportValue (K.1.1 : Set Point)
          (((paperGerverConstants.2.2 : ℝ) : Real.Angle) +
            ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2.2.2.2.2.2.1
  have hangL :
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
    exact hcast _ _ (by ring)
  refine ⟨hBne, hBcomp, hBconv, hBsub, hDne, hDcomp, hDconv, hDsub,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    linarith only [hBbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · linarith only [hBeqR]
    · rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), hBzero, htop]
      ring
  · change normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hBzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · change normalLine ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)) = _
    rw [hBeqR, normalLine_eq_of_cut (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)), hwallR]
    congr 1
    ring
  · intro t ht
    linarith only [hDbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), hDzero, htop]
      ring
    · linarith only [hDeqL]
  · change normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hDzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · change normalLine ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = _
    rw [hDeqL, normalLine_eq_of_cut (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)), hwallL, hangL]
    congr 1
    ring

/-- The inner corner's normal support coordinate is the cap's support value less one. -/
theorem inner_capInnerCorner_normalVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  change inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (normalVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_self, inner_tangentVector_normalVector_real]
  simp

/-- The inner corner's tangent support coordinate is the quarter-turned support value less one. -/
theorem inner_capInnerCorner_tangentVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  change inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (tangentVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, inner_normalVector_tangentVector,
    ← Real.Angle.coe_add]
  simp

/-- A point whose displacement from the inner corner has negative coordinates in the rotating
frame at time `t` lies in the open inward quadrant at that time. -/
theorem mem_innerQuadrant_of_frame_coordinates_neg (K : RightAngleCapSpace) (t : ℝ) (q : Point)
    (h1 : (q 0 - capInnerCorner K t 0) * Real.cos t +
      (q 1 - capInnerCorner K t 1) * Real.sin t < 0)
    (h2 : -((q 0 - capInnerCorner K t 0) * Real.sin t) +
      (q 1 - capInnerCorner K t 1) * Real.cos t < 0) :
    q ∈ innerQuadrant (K.val : Set Point) t := by
  have e1 : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_normalVector K t, inner_normalVector_real,
      inner_normalVector_real]
    linarith only [h1]
  have e2 : inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_tangentVector K t, inner_tangentVector_real,
      inner_tangentVector_real]
    linarith only [h2]
  refine ⟨e1, ?_⟩
  change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  exact e2

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
# Cap / Tail / Extension
-/

public section

noncomputable section

namespace MovingSofa

/-- The canonical tail sets give an admissible cap-tail triple with exactly these carriers. -/
theorem exists_canonicalCapTail (K : SpecialCapSpace) :
    ∃ T : CapTailSpace, T.cap = K ∧
      (T.rightBody : Set Point) = (canonicalTailSets K).1 ∧
      (T.leftBody : Set Point) = (canonicalTailSets K).2 := by
  obtain ⟨hBne, hBcp, hBcv, hBsub, hDne, hDcp, hDcv, hDsub, hBbd, hBeq, -, -,
    hDbd, hDeq, -, -⟩ := canonicalTailSets_properties K
  exact ⟨{ cap := K
           rightBody := ⟨(canonicalTailSets K).1, hBcv, hBcp, hBne⟩
           leftBody := ⟨(canonicalTailSets K).2, hDcv, hDcp, hDne⟩
           right_subset := hBsub
           left_subset := hDsub
           right_bound := hBbd
           right_eq := hBeq
           left_bound := hDbd
           left_eq := hDeq }, rfl, rfl, rfl⟩

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
# Cap / Tail / Separation
-/

public section

noncomputable section

namespace MovingSofa

/-- A point above both distinguished inner walls of a special cap lies above mid-height. -/
private theorem lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes (K : SpecialCapSpace)
    {q : Point} (h₁ : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane)
    (h₂ : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane) :
    (horizontalMax K.val.val - horizontalMin K.val.val) / 2 < q 1 := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hsinle : Real.sin paperGerverConstants.2.1 ≤ paperGerverConstants.2.1 :=
    Real.sin_le hrIoo.1.le
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hleq : paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 := by linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [hleq, Real.sin_pi_div_two_sub]
  have hcosleq : Real.cos paperGerverConstants.2.2 = Real.sin paperGerverConstants.2.1 := by
    rw [hleq, Real.cos_pi_div_two_sub]
  -- the cap is wide, by rectangle area monotonicity and the special-cap area threshold
  have hwidth : (11 : ℝ) / 5 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) := by
    have h := K.property.2.trans K.val.area_le_horizontalWidth
    rwa [supportValue_zero_eq_horizontalMax, supportValue_pi_eq_neg_horizontalMin,
      ← sub_eq_add_neg]
  -- support lower bounds at the two distinguished angles
  have hlowR : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinr hcpos.le).1
    rwa [← supportValue_zero_eq_horizontalMax] at h
  have hlowL : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinl hcosl).2
    rw [supportValue_pi_eq_neg_horizontalMin, ← hsinleq, mul_neg, ← neg_mul]
    exact h
  -- the two defining support inequalities of the closed tail half-planes
  have h₁' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) := h₁
  have h₂' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q
        (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) := h₂
  rw [inner_normalVector_real] at h₁'
  rw [inner_normalVector_real, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, hsinleq, hcosleq] at h₂'
  -- the strict product bound of the informal proof
  rw [← supportValue_zero_eq_horizontalMax, sub_eq_add_neg,
    ← supportValue_pi_eq_neg_horizontalMin]
  by_contra hcon
  rw [not_lt] at hcon
  have hcs : (1199 : ℝ) / 1250 ≤
      Real.cos paperGerverConstants.2.1 - Real.sin paperGerverConstants.2.1 := by linarith
  have hprod : (2 : ℝ) < (Real.cos paperGerverConstants.2.1 -
      Real.sin paperGerverConstants.2.1) *
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) := by
    have h := mul_le_mul hcs hwidth (by norm_num) (by linarith)
    linarith
  have hmul : q 1 * Real.sin paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) / 2 *
        Real.sin paperGerverConstants.2.1 :=
    mul_le_mul_of_nonneg_right hcon hsinr
  nlinarith only [h₁', h₂', hlowR, hlowL, hmul, hprod]

theorem cap_and_niche_tail_separation (K : SpecialCapSpace) :
    ((K.val.val : Set Point) ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ ∧
    (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ := by
  have hwidth : (11 : ℝ) / 5 ≤ horizontalMax K.val.val - horizontalMin K.val.val :=
    K.property.2.trans K.val.area_le_horizontalWidth
  constructor
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqK, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (K.val.mem_horizontalStrip hqK).2
    linarith
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqN, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (capNiche_subset_rectangle K.val hqN).2.2.2
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

* `Area.NicheDecomposition`.
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
# Area / Niche Decomposition
-/

public section

noncomputable section

namespace MovingSofa

theorem niche_three_regions_area (K : SpecialCapSpace) :
    ∀ E₀ Eᵣ Eₗ : Set Point,
      E₀ = capNiche K.val \ ((distinguishedCapSides K.val).1.upperHalfPlane ∪
        (distinguishedCapSides K.val).2.upperHalfPlane) →
      Eᵣ = capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane →
      Eₗ = capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane →
      MeasurableSet E₀ ∧ MeasurableSet Eᵣ ∧ MeasurableSet Eₗ ∧
      MeasureTheory.volume E₀ < ⊤ ∧ MeasureTheory.volume Eᵣ < ⊤ ∧
      MeasureTheory.volume Eₗ < ⊤ ∧
      Disjoint E₀ Eᵣ ∧ Disjoint E₀ Eₗ ∧ Disjoint Eᵣ Eₗ ∧
      E₀ ∪ Eᵣ ∪ Eₗ = capNiche K.val ∧
      ClassicalResults.area (capNiche K.val) =
        ClassicalResults.area E₀ + ClassicalResults.area Eᵣ + ClassicalResults.area Eₗ := by
  intro E₀ Eᵣ Eₗ h₀ hᵣ hₗ
  set N := capNiche K.val with hN
  set HR := (distinguishedCapSides K.val).1.upperHalfPlane with hHR
  set HL := (distinguishedCapSides K.val).2.upperHalfPlane with hHL
  subst h₀ hᵣ hₗ
  -- Borel measurability: the niche is Borel and both tail half-planes are closed.
  have hNmeas : MeasurableSet N := measurableSet_capNiche K.val
  have hRmeas : MeasurableSet HR := (isClosed_normalHalfPlane _ _ true).measurableSet
  have hLmeas : MeasurableSet HL := (isClosed_normalHalfPlane _ _ true).measurableSet
  have hm₀ : MeasurableSet (N \ (HR ∪ HL)) := hNmeas.diff (hRmeas.union hLmeas)
  have hmᵣ : MeasurableSet (N ∩ HR) := hNmeas.inter hRmeas
  have hmₗ : MeasurableSet (N ∩ HL) := hNmeas.inter hLmeas
  -- Finite area: the uniform niche bounds confine the niche to a bounded rectangle.
  have hNfin : MeasureTheory.volume N < ⊤ := (niche_uniform_bounds.1 _ K.val).2.2.1
  have hf₀ : MeasureTheory.volume (N \ (HR ∪ HL)) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) hNfin
  have hfᵣ : MeasureTheory.volume (N ∩ HR) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hNfin
  have hfₗ : MeasureTheory.volume (N ∩ HL) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hNfin
  -- Disjointness: the outer region avoids both tails by definition, and the two tails
  -- meet the niche in disjoint sets by the strengthened separation theorem.
  have hd₀ᵣ : Disjoint (N \ (HR ∪ HL)) (N ∩ HR) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 (Or.inl hy.2)
  have hd₀ₗ : Disjoint (N \ (HR ∪ HL)) (N ∩ HL) :=
    Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 (Or.inr hy.2)
  have hdᵣₗ : Disjoint (N ∩ HR) (N ∩ HL) :=
    Set.disjoint_left.mpr fun x hx hy ↦
      Set.eq_empty_iff_forall_notMem.mp (cap_and_niche_tail_separation K).2 x ⟨hx, hy.2⟩
  -- The three regions exhaust the niche by cases on half-plane membership.
  have hunion : (N \ (HR ∪ HL)) ∪ (N ∩ HR) ∪ (N ∩ HL) = N := by
    rw [Set.union_assoc, ← Set.inter_union_distrib_left, Set.sdiff_union_inter]
  refine ⟨hm₀, hmᵣ, hmₗ, hf₀, hfᵣ, hfₗ, hd₀ᵣ, hd₀ₗ, hdᵣₗ, hunion, ?_⟩
  -- Additivity of the extended measures, transferred to real areas by finiteness.
  have hvol : MeasureTheory.volume N = MeasureTheory.volume (N \ (HR ∪ HL)) +
      MeasureTheory.volume (N ∩ HR) + MeasureTheory.volume (N ∩ HL) := by
    rw [← MeasureTheory.measure_union hd₀ᵣ hmᵣ,
      ← MeasureTheory.measure_union (hd₀ₗ.union_left hdᵣₗ) hmₗ, hunion]
  simp only [ClassicalResults.area]
  rw [hvol, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hf₀.ne, hfᵣ.ne⟩) hfₗ.ne,
    ENNReal.toReal_add hf₀.ne hfᵣ.ne]

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

* `Bounds.MonotonicityIntervals`.
* `Bounds.WedgeEndpoints`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-! # Monotonicity intervals for the distinguished cap sides

`cap_tail_monotonicity_intervals` records that on the right interval
`(φ, π/2]` the inner corner has left the distinguished right half-plane, and
that inside that half-plane the inner quadrant is cut out by the single inner
wall `b(t)`; symmetrically on `[0, π/2 - φ)` for the left side.  Intersecting
with the fan gives the two wedge forms.
-/

public section

noncomputable section

namespace MovingSofa

private theorem capInnerCorner_right_projection_neg (K : SpecialCapSpace) :
    ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
     inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
       (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- the injectivity condition: a continuously differentiable corner with strict interior signs
  obtain ⟨-, hcd, hsign⟩ := K.2.1
  set D : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) with hDdef
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (D s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs => (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hsub : Set.Icc GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Icc_subset_Icc hφ0 le_rfl
  have hanti : StrictAntiOn
      (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
        (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
      (Set.Icc GerversSofa.φ (Real.pi / 2)) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((hcont.mono hsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (D s) (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
      ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      have hsub' : Set.Ioo GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        fun z hz => ⟨hφ0.trans hz.1.le, hz.2.le⟩
      simpa using
        ((hdw s (hsub' hs)).mono hsub').inner ℝ
          (hasDerivWithinAt_const s _
            (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨hφ0.trans_lt hs1, hs2⟩
      rw [inner_normalVector_eq_frame_rotate (D s) s GerversSofa.φ]
      have hcos : 0 < Real.cos (s - GerversSofa.φ) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin : 0 < Real.sin (s - GerversSofa.φ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      nlinarith
  intro t ht
  have h := hanti ⟨le_rfl, le_trans hφ4 (by linarith)⟩ ⟨ht.1.le, ht.2⟩ ht.1
  rw [inner_sub_left]
  simpa using h

private theorem capInnerCorner_left_projection_neg (K : SpecialCapSpace) :
    ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
     inner ℝ (capInnerCorner K.val t -
         capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
       (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- the injectivity condition: a continuously differentiable corner with strict interior signs
  obtain ⟨-, hcd, hsign⟩ := K.2.1
  set D : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) with hDdef
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (D s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs => (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
      Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Icc_subset_Icc le_rfl (by linarith)
  have hmono : StrictMonoOn
      (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
        (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
      (Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      ((hcont.mono hsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (D s)
        (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
      ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      have hsub' : Set.Ioo (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
          Set.Icc (0 : ℝ) (Real.pi / 2) := fun z hz => ⟨hz.1.le, by linarith [hz.2]⟩
      simpa using
        ((hdw s (hsub' hs)).mono hsub').inner ℝ
          (hasDerivWithinAt_const s _
            (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨hs1, by linarith⟩
      rw [inner_tangentVector_eq_frame_rotate (D s) s (Real.pi / 2 - GerversSofa.φ)]
      have hcos : 0 < Real.cos (s - (Real.pi / 2 - GerversSofa.φ)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin : Real.sin (s - (Real.pi / 2 - GerversSofa.φ)) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      nlinarith
  intro t ht
  have h := hmono ⟨ht.1, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2
  rw [inner_sub_left]
  simpa using h

theorem cap_tail_monotonicity_intervals (K : SpecialCapSpace) :
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2) ∧
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).1.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).2.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).2) := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- frame coordinates of the inner corner path
  have hxu := inner_capInnerCorner_normalVector K.val
  have hxv := inner_capInnerCorner_tangentVector K.val
  -- membership descriptions relative to the moving corner
  have hHb : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).1 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxu]
    change (supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ≤
      inner ℝ p (normalVector (t : Real.Angle))) ↔ _
    constructor <;> intro hp <;> linarith
  have hHd : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).2 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxv]
    change (supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> intro hp <;> linarith
  have hQ : ∀ (t : ℝ) (p : Point), p ∈ innerQuadrant (K.val.val : Set Point) t ↔
      inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 ∧
        inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 := by
    intro t p
    rw [inner_sub_left, inner_sub_left, hxu, hxv]
    change (inner ℝ p (normalVector (t : Real.Angle)) <
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hfan : capFan (Real.pi / 2) = {p : Point | 0 ≤ p 1} := by
    ext p
    have hval : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
      simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    constructor
    · intro hp
      have := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
      rw [hval] at this
      exact this
    · intro hp
      have hp' : (0 : ℝ) ≤ p 1 := hp
      exact ⟨by change 0 ≤ inner ℝ p _; rw [hval]; exact hp',
        by change 0 ≤ inner ℝ p _; rw [hval]; exact hp'⟩
  have hwedge : ∀ t : ℝ, capWedge K.val t =
      {p : Point | 0 ≤ p 1} ∩ innerQuadrant (K.val.val : Set Point) t := by
    intro t
    have hiq : (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant =
        innerQuadrant (K.val.val : Set Point) t := by
      rw [(rotatingHallwayParts_formulas (K.val.val : Set Point)
        (t : Real.Angle)).2.2.2.2.2.2.2.2, innerQuadrant, ← Real.Angle.coe_add]
    change capFan (Real.pi / 2) ∩
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant = _
    rw [hfan, hiq]
  -- monotone comparison of the corner path against the two distinguished frames
  have hkeyR := capInnerCorner_right_projection_neg K
  have hkeyL := capInnerCorner_left_projection_neg K
  -- the right-hand quadrant identity, at all quadrant times
  have partR : ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1 := by
    intro t ht
    have hR := hkeyR t ht
    have hside : (distinguishedCapSides K.val).1.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val GerversSofa.φ).1 := rfl
    have hcos : 0 ≤ Real.cos (t - GerversSofa.φ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : 0 ≤ Real.sin (t - GerversSofa.φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHb _ _).mp hmem) (not_le.mpr hR)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHb t p]
      exact not_le.mpr ((hQ t p).mp hQp).1
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have ha : inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHb t p).mpr h)
      refine ⟨ha, ?_⟩
      by_contra hb
      rw [not_lt] at hb
      have hAmem : 0 ≤ inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := (hHb _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
            (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_normalVector_eq_frame_rotate (p - capInnerCorner K.val t) t GerversSofa.φ]
        linarith [mul_nonneg hb hsin, mul_nonneg (neg_nonneg.mpr ha.le) hcos]
      linarith
  -- the left-hand quadrant identity, at all quadrant times
  have partL : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2 := by
    intro t ht
    have hL := hkeyL t ht
    have hside : (distinguishedCapSides K.val).2.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val (Real.pi / 2 - GerversSofa.φ)).2 := rfl
    have hcos : 0 ≤ Real.cos (t - (Real.pi / 2 - GerversSofa.φ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : Real.sin (t - (Real.pi / 2 - GerversSofa.φ)) ≤ 0 := by
      have hpos : 0 ≤ Real.sin (Real.pi / 2 - GerversSofa.φ - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
      rw [show t - (Real.pi / 2 - GerversSofa.φ) =
        -(Real.pi / 2 - GerversSofa.φ - t) by ring, Real.sin_neg]
      linarith
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHd _ _).mp hmem) (not_le.mpr hL)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHd t p]
      exact not_le.mpr ((hQ t p).mp hQp).2
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have hb : inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHd t p).mpr h)
      refine ⟨?_, hb⟩
      by_contra ha
      rw [not_lt] at ha
      have hAmem : 0 ≤ inner ℝ
          (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := (hHd _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
            (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t -
                capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_tangentVector_eq_frame_rotate (p - capInnerCorner K.val t) t
          (Real.pi / 2 - GerversSofa.φ)]
        linarith [mul_nonneg ha (neg_nonneg.mpr hsin),
          mul_nonneg (neg_nonneg.mpr hb.le) hcos]
      linarith
  -- the wedge identities are the quadrant identities intersected with the fan
  refine ⟨partR, partL, ?_, ?_⟩
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partR t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partL t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto

/-- On any subinterval of `[0, π/2]` the inner corner of a special cap has strictly decreasing
horizontal coordinate: the injectivity condition makes its horizontal derivative negative. -/
theorem strictAntiOn_capInnerCorner_fst (K : SpecialCapSpace) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    StrictAntiOn (fun t ↦ capInnerCorner K.val t 0) (Set.Icc a b) := by
  obtain ⟨-, hcd, hsign⟩ := K.property.1
  set Dv : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2))
  have hIccsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hIoosub : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1.le, le_trans ht.2.le hb⟩
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (Dv s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs ↦ (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hinner0 : ∀ p : Point, inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
    intro p
    rw [inner_normalVector_real]
    simp
  have hmono0 : StrictAntiOn
      (fun t ↦ inner ℝ (capInnerCorner K.val t) (normalVector ((0 : ℝ) : Real.Angle)))
      (Set.Icc a b) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((hcont.mono hIccsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (Dv s) (normalVector ((0 : ℝ) : Real.Angle))) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      simpa using ((hdw s (hIoosub hs)).mono hIoosub).inner ℝ
        (hasDerivWithinAt_const s _ (normalVector ((0 : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨lt_of_le_of_lt ha hs.1, lt_of_lt_of_le hs.2 hb⟩
      rw [inner_normalVector_eq_frame_rotate (Dv s) s 0]
      have hcos : 0 < Real.cos (s - 0) := by
        rw [sub_zero]
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, hs.1, ha],
          by linarith only [hs.2, hb]⟩
      have hsin : 0 < Real.sin (s - 0) := by
        rw [sub_zero]
        exact Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_lt ha hs.1)
          (by linarith only [hs.2, hb, Real.pi_pos])
      have h1 : inner ℝ (Dv s) (normalVector (s : Real.Angle)) * Real.cos (s - 0) < 0 :=
        mul_neg_of_neg_of_pos hα hcos
      have h2 : 0 < inner ℝ (Dv s) (tangentVector (s : Real.Angle)) * Real.sin (s - 0) :=
        mul_pos hβ hsin
      linarith only [h1, h2]
  intro u hu w hw huw
  simpa only [hinner0] using hmono0 hu hw huw

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
# Bounds / Wedge Endpoints
-/

public section

noncomputable section

namespace MovingSofa

theorem wedgeGaps_positive_lower_bound {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) :
    (1 - Real.sin t) / Real.cos t ≤ (wedgeGaps K t).1 ∧
    0 < (1 - Real.sin t) / Real.cos t ∧
    (1 - Real.sin (ω - t)) / Real.cos (ω - t) ≤ (wedgeGaps K t).2 ∧
    0 < (1 - Real.sin (ω - t)) / Real.cos (ω - t) := by
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsint_lt : Real.sin t < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  have hsinδ_lt : Real.sin (ω - t) < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq (ω - t), sq_pos_of_pos hcosδ]
  have hbounds := K.supportValue_upper_bounds ht
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [normalVector, frame, Real.Angle.coe_add, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_coe, Real.Angle.sin_add_pi_div_two, Real.Angle.cos_coe] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  have hgap₁ := wedgeGaps_fst_eq_supportValue K t
  have hgap₂ : (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
    simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
      real_inner_smul_left, hC]
    rw [inner_tangentVector_self]
    ring
  rw [hgap₁, hgap₂]
  refine ⟨?_, div_pos (sub_pos.mpr hsint_lt) hcost, ?_,
    div_pos (sub_pos.mpr hsinδ_lt) hcosδ⟩
  · apply (div_le_iff₀ hcost).2
    rw [sub_mul, div_mul_cancel₀ _ hcost.ne']
    nlinarith [hbounds.1]
  · apply (div_le_iff₀ hcosδ).2
    rw [sub_mul, div_mul_cancel₀ _ hcosδ.ne']
    nlinarith [hbounds.2]

/-- Base points between the horizontal extrema of a right-angle cap lie in the cap. -/
private theorem smul_normalVector_zero_mem_of_rightAngleCap (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ x)
    (hhi : x ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.val ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.val ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hzero : inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_smul_normalVector_zero, Real.cos_pi_div_two, mul_zero]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  rw [inner_smul_normalVector_zero]
  rcases le_or_gt 0 (Real.cos t) with hcos | hcos
  · have h := inner_le_supportValue K.val hA (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hA).1
    nlinarith only [h, hAeq, hhi, hcos, mul_nonneg hsin hy]
  · have h := inner_le_supportValue K.val hC (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hC).1
    nlinarith only [h, hCeq, hlo, hcos, mul_nonneg hsin hy]

/-- The bottom right cap vertex is the horizontal maximum on the base line. -/
private theorem capVertices_zero_snd_eq (K : RightAngleCapSpace) :
    (capVertices K 0).1.2 =
      supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) •
        normalVector (0 : Real.Angle) := by
  set R := supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) with hRdef
  have hS : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ R := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hRdef]
    linarith
  have hmem : R • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K hS le_rfl
  have hedge : R • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((0 : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ (R • normalVector (0 : Real.Angle))
      (normalVector ((0 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_zero, mul_one]
  change (edgeVertices K.val ((0 : ℝ) : Real.Angle)).2 = _
  refine edgeVertices_snd_eq_of_tangent_isLeast K.val ((0 : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ (R • normalVector (0 : Real.Angle))
      (tangentVector ((0 : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) from rfl,
      inner_normalVector_tangentVector, mul_zero]
  rw [hp1, inner_tangentVector_zero]
  exact hq1

/-- The bottom left cap vertex is the horizontal minimum on the base line. -/
private theorem capVertices_pi_div_two_fst_eq (K : RightAngleCapSpace) :
    (capVertices K (Real.pi / 2)).2.1 =
      (-supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) •
        normalVector (0 : Real.Angle) := by
  set S := supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) with hSdef
  have hR : -S ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hSdef]
    linarith
  have hmem : (-S) • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K le_rfl hR
  have hang : ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hedge : (-S) • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_pi]
    ring
  change (edgeVertices K.val ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 = _
  rw [hang]
  refine edgeVertices_fst_eq_of_tangent_isGreatest K.val ((Real.pi : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (tangentVector ((Real.pi : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, inner_tangentVector_pi]
    simp [normalVector, frame]
  rw [hp1, inner_tangentVector_pi]
  linarith

/-- Horizontal coordinates strictly inside the cap width give interior bottom-edge points. -/
private theorem smul_normalVector_zero_mem_bottomEdge (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) < x)
    (hhi : x < supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K 0).1.2, (capVertices K (Real.pi / 2)).2.1} := by
  have hinj : ∀ a b : ℝ, a • normalVector (0 : Real.Angle) =
      b • normalVector (0 : Real.Angle) → a = b := by
    intro a b h
    have h' := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((0 : ℝ) : Real.Angle))) h
    simpa only [inner_smul_normalVector_zero, Real.cos_zero, mul_one] using h'
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  refine ⟨⟨smul_normalVector_zero_mem_of_rightAngleCap K hlo.le hhi.le, ?_⟩, ?_⟩
  · change inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, hcos, mul_zero, K.property.2.2.2.2.2.1]
  · rintro (h | h)
    · rw [capVertices_zero_snd_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_lt hhi)
    · rw [capVertices_pi_div_two_fst_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_gt hlo)

theorem specialCap_wedgeEndpoints_in_bottomEdge (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).1.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} ∧
    (distinguishedCapSides K.val).2.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  -- the certified parameter bound `0 < varphi ≤ 1/25` and its trigonometric consequences
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hcosdiff : Real.pi / 2 - paperGerverConstants.2.2 = paperGerverConstants.2.1 := by
    linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  have hinvc : (1 : ℝ) / Real.cos paperGerverConstants.2.1 ≤ 1250 / 1249 := by
    rw [div_le_div_iff₀ hcpos (by norm_num)]
    linarith
  -- the cap is wide, by rectangle area monotonicity and the special-cap area threshold
  have hwidth : (11 : ℝ) / 5 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) := by
    have h := K.property.2.trans K.val.area_le_horizontalWidth
    rwa [supportValue_zero_eq_horizontalMax, supportValue_pi_eq_neg_horizontalMin,
      ← sub_eq_add_neg]
  -- support lower bounds at the two distinguished angles
  have hlowR : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinr hcpos.le).1
    rwa [← supportValue_zero_eq_horizontalMax] at h
  have hlowL : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinl hcosl).2
    rw [supportValue_pi_eq_neg_horizontalMin, ← hsinleq, mul_neg, ← neg_mul]
    exact h
  -- the two positive wedge gaps
  have hgap₁ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.1 hrIoo
  have hgap₂ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.2 hlIoo
  rw [wedgeGaps_fst_eq_supportValue] at hgap₁
  rw [wedgeGaps_snd_eq_supportValue,
    show ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) by
      congr 1; ring, hcosdiff] at hgap₂
  have hgap₁' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.1
  have hgap₂' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.1
  -- the reciprocal-cosine lower bounds for the two inner-wall coordinates
  have hRc : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hSc : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hRc' : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  have hSc' : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  -- the two fan points as multiples of the horizontal normal
  have htv : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    have h := tangentVector_add_pi_div_two 0
    rwa [zero_add, Real.Angle.coe_zero] at h
  constructor
  · change ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1) • normalVector (0 : Real.Angle) ∈ _
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · linarith
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.2.1
      linarith
  · change ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos (Real.pi / 2 - paperGerverConstants.2.2)) •
        tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ _
    rw [hcosdiff, htv, smul_neg, ← neg_smul]
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.2
      linarith
    · linarith

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

* `Bounds.Upper.Q`.
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
# Bounds / Upper / Q
-/

public section

noncomputable section

namespace MovingSofa

/-- The cap-tail upper-bound functional Q assembled from cap area, tail arcs and endpoint
segments. -/
@[expose]
def upperBoundQ (T : CapTailSpace) : ℝ :=
  ClassicalResults.area (T.cap.val.val : Set Point) +
    convexArcArea T.leftBody (3 * Real.pi / 2)
      (3 * Real.pi / 2 + paperGerverConstants.2.2) +
    segmentArea (rightLeftTailArcs T.rightBody T.leftBody).2.endPoint
      (distinguishedCapSides T.cap.val).2.corner -
    curveAreaFunctional (capMiddleBV T.cap) +
    segmentArea (distinguishedCapSides T.cap.val).1.corner
      (rightLeftTailArcs T.rightBody T.leftBody).1.startPoint +
    convexArcArea T.rightBody (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)

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

* `Motion.Monotonization`.
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
# Motion / Monotonization
-/

public section

noncomputable section
open Set
open scoped unitInterval
namespace MovingSofa

private theorem isClosed_supportingHallway (s : Set Point) (t : Real.Angle) :
    IsClosed (supportingHallway s t) := by
  have hclosed : IsClosed hallway := by
    rw [hallway_eq_outerQuadrant_sdiff_innerQuadrant]
    apply IsClosed.sdiff
    · change IsClosed {p : Point | p 0 ≤ 1 ∧ p 1 ≤ 1}
      exact (isClosed_le (by fun_prop : Continuous (fun p : Point ↦ p 0)) continuous_const).inter
        (isClosed_le (by fun_prop : Continuous (fun p : Point ↦ p 1)) continuous_const)
    · change IsOpen {p : Point | p 0 < 0 ∧ p 1 < 0}
      exact (isOpen_lt (by fun_prop : Continuous (fun p : Point ↦ p 0)) continuous_const).inter
        (isOpen_lt (by fun_prop : Continuous (fun p : Point ↦ p 1)) continuous_const)
  have heq : supportingPlacement s t = supportingPlacementEquiv s t := by
    funext p
    exact (supportingPlacementEquiv_apply s t p).symm
  rw [supportingHallway, heq]
  exact (supportingPlacementEquiv s t).toHomeomorph.isClosedMap _ hclosed

private theorem isClosed_monotonization (s : Set Point) (ω : ℝ) :
    IsClosed (monotonization s ω) := by
  have hP : (stripParallelogram ω).1 =
      {p : Point | p 1 ∈ Icc (0 : ℝ) 1 ∧
        inner ℝ p (normalVector (ω : Real.Angle)) ∈ Icc (0 : ℝ) 1} := by
    ext p
    exact mem_stripParallelogram_iff ω p
  have hclosedP : IsClosed (stripParallelogram ω).1 := by
    rw [hP]
    exact (isClosed_Icc.preimage (by fun_prop : Continuous (fun p : Point ↦ p 1))).inter
      (isClosed_Icc.preimage (continuous_id.inner continuous_const))
  exact hclosedP.inter (isClosed_iInter fun t ↦
    isClosed_iInter fun _ ↦ isClosed_supportingHallway s (t : Real.Angle))

private theorem monotonization_subset_capOfSofa (s : Set Point) (ω : ℝ) :
    monotonization s ω ⊆ capOfSofa s ω := by
  intro p hp
  change p ∈ (stripParallelogram ω).1 ∩
    ⋂ t ∈ Icc 0 ω, supportingHallway s (t : Real.Angle) at hp
  refine ⟨hp.1, ?_⟩
  simp only [mem_inter_iff, mem_iInter] at hp ⊢
  intro t ht
  exact supportingHallway_subset_outerQuadrant s (t : Real.Angle) (hp.2 t ht)

private theorem isCompact_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : IsCompact (monotonization s ω) := by
  obtain ⟨K, hK⟩ := standardPosition_cap s ω hs
  have hc : IsCompact (capOfSofa s ω) := hK ▸ K.val.isCompact
  exact hc.of_isClosed_subset (isClosed_monotonization s ω)
    (monotonization_subset_capOfSofa s ω)

private theorem hasRotationAngle_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : HasRotationAngle (monotonization s ω) ω := by
  have hsne : s.Nonempty := by
    obtain ⟨m, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  exact hasRotationAngle_of_subset_supportingHallways s (monotonization s ω) ω
    hsne hs.1 hs.2.2.1.le hs.2.2.2.2.1 hs.2.2.2.2.2
    (standardPosition_monotonization_connected s ω hs)
    (isClosed_monotonization s ω) Set.Subset.rfl

theorem standardPosition_monotonization_standard (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    IsStandardPosition (monotonization s ω) ω ∧ s ⊆ monotonization s ω := by
  refine ⟨⟨isCompact_monotonization s ω hs, hasRotationAngle_monotonization s ω hs,
    hs.2.2.1, hs.2.2.2.1, ?_, ?_⟩, standardPosition_subset_monotonization s ω hs⟩
  · exact ((standardPosition_support_eq s ω hs).1 ω
      (Or.inl ⟨hs.2.2.1.le, le_rfl⟩)).1.trans hs.2.2.2.2.1
  · exact ((standardPosition_support_eq s ω hs).1 (Real.pi / 2)
      (Or.inr ⟨le_rfl, by linarith [hs.2.2.1]⟩)).1.trans hs.2.2.2.2.2

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

* `Sofa.Area`.
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
# Sofa / Area
-/

public section

noncomputable section

namespace MovingSofa

theorem monotoneSofa_structure (s : Set Point) (ω : ℝ)
    (hs : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω)
    (K : CapSpace ω) (hK : (K.val : Set Point) = capOfSofa s ω) :
    s = (K.val : Set Point) \ capNiche K := by
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  have heq : capOfSofa (monotonization s₀ ω) ω = capOfSofa s₀ ω := by
    have hparts (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
        (rotatingHallwayParts (monotonization s₀ ω) (t : Real.Angle)).outerQuadrant =
          (rotatingHallwayParts s₀ (t : Real.Angle)).outerQuadrant := by
      have h₀ := ((standardPosition_support_eq s₀ ω hs₀).1 t (Or.inl ht)).1
      have h₁ := ((standardPosition_support_eq s₀ ω hs₀).1 (t + Real.pi / 2)
        (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1
      simp only [Real.Angle.coe_add] at h₁
      change supportingPlacement (monotonization s₀ ω) (t : Real.Angle) ''
        hallwayParts.outerQuadrant = supportingPlacement s₀ (t : Real.Angle) ''
          hallwayParts.outerQuadrant
      have he : supportingPlacement (monotonization s₀ ω) (t : Real.Angle) =
          supportingPlacement s₀ (t : Real.Angle) := by
        funext p
        simp only [supportingPlacement, h₀, h₁]
      rw [he]
    unfold capOfSofa
    congr 1
    apply Set.iInter_congr
    intro t
    apply Set.iInter_congr
    exact hparts t
  exact standardPosition_monotonization s₀ ω hs₀ K (hK.trans heq)

theorem capAreaFunctional_eq_sofaArea (s : Set Point) (ω : ℝ)
    (hs : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω)
    (K : CapSpace ω) (hK : (K.val : Set Point) = capOfSofa s ω) :
    capAreaFunctional K = ClassicalResults.area s := by
  have heq := monotoneSofa_structure s ω hs K hK
  have hconn : IsConnected s := by
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact standardPosition_monotonization_connected s₀ ω hs₀
  have hsub : capNiche K ⊆ (K.val : Set Point) :=
    (cap_niche_connected_iff K).1.mpr
      ((cap_niche_connected_iff K).2.1.mpr
        ((cap_niche_connected_iff K).2.2.mpr (heq ▸ hconn)))
  rw [capAreaFunctional, heq]
  change MeasureTheory.volume.real (K.val : Set Point) -
    MeasureTheory.volume.real (capNiche K) =
      MeasureTheory.volume.real ((K.val : Set Point) \ capNiche K)
  have h := MeasureTheory.measureReal_inter_add_sdiff
    (μ := MeasureTheory.volume) (s := (K.val : Set Point))
    (measurableSet_capNiche K) K.val.isCompact.measure_lt_top.ne
  rw [Set.inter_eq_right.mpr hsub] at h
  linarith

end MovingSofa

end

end

end

end

end

end
