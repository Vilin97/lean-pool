/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development005
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development006
public import LeanPool.MovingSofa.Development.Geometry.Applications.Development001


public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development007









public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002





/-!
# Moving sofa: related mathematical developments

* `Bounds.Applications.Development001`.
* `Cap.Applications.Development002`.
* `Polygon.Applications.Development002`.
* `Cap.Applications.Development003`.
* `Bounds.Applications.Development002`.
* `Cap.Applications.Development004`.
* `Gerver.Applications.Development003`.
* `Cap.Applications.Development005`.
* `Cap.Applications.Development006`.
* `Area.Applications.Development004`.
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

* `Bounds.Arm.Estimates`.
* `Bounds.WedgeGap.Infimum`.
* `Bounds.WedgeGap.Limit`.
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
# Bounds / Arm / Estimates
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

private def positiveArmKernel (t : ℝ) (u : Real.Angle) : ℝ :=
  if 0 < (u - (t : Real.Angle)).sin ∧ 0 ≤ (u - (t : Real.Angle)).cos then
    (u - (t : Real.Angle)).sin
  else 0

private theorem measurable_positiveArmKernel :
    Measurable (Function.uncurry positiveArmKernel) := by
  have hs : Continuous (fun z : ℝ × Real.Angle ↦
      (z.2 - (z.1 : Real.Angle)).sin) :=
    Real.Angle.continuous_sin.comp
      (continuous_snd.sub (Real.Angle.continuous_coe.comp continuous_fst))
  have hc : Continuous (fun z : ℝ × Real.Angle ↦
      (z.2 - (z.1 : Real.Angle)).cos) :=
    Real.Angle.continuous_cos.comp
      (continuous_snd.sub (Real.Angle.continuous_coe.comp continuous_fst))
  exact hs.measurable.piecewise
    ((measurableSet_lt measurable_const hs.measurable).inter
      (measurableSet_le measurable_const hc.measurable)) measurable_const

private theorem mem_positiveArmArc_iff {t : ℝ} (u : Real.Angle) :
    u ∈ (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2) ↔
      0 < (u - (t : Real.Angle)).sin ∧ 0 ≤ (u - (t : Real.Angle)).cos := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [← Real.Angle.coe_sub, Real.Angle.sin_coe, Real.Angle.cos_coe]
    exact ⟨Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hx.1)
      (by linarith [hx.2, Real.pi_pos]),
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩⟩
  · intro hu
    let d := (u - (t : Real.Angle)).toReal
    have hdpos : 0 < d := by
      have hsign : (u - (t : Real.Angle)).sign = 1 := by
        simpa only [Real.Angle.sign, sign_eq_one_iff] using hu.1
      exact (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hsign).1
    have hdle : d ≤ Real.pi / 2 := by
      have habs := Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two.1 hu.2
      exact (le_abs_self d).trans habs
    refine ⟨t + d, ⟨by linarith, by linarith⟩, ?_⟩
    change (((t + d : ℝ) : Real.Angle)) = u
    calc
      (((t + d : ℝ) : Real.Angle)) = (t : Real.Angle) + (d : Real.Angle) :=
        Real.Angle.coe_add t d
      _ = (t : Real.Angle) + (u - (t : Real.Angle)) := by
        congr 1
        exact Real.Angle.coe_toReal (u - (t : Real.Angle))
      _ = u := by abel

private theorem positiveArmKernel_eq_indicator (t : ℝ) :
    positiveArmKernel t =
      ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)).indicator
        (fun u ↦ (u - (t : Real.Angle)).sin) := by
  classical
  funext u
  rw [Set.indicator_apply]
  simp only [positiveArmKernel, mem_positiveArmArc_iff]

private theorem stronglyMeasurable_integral_positiveArmKernel (μ : Measure Real.Angle)
    [SFinite μ] : StronglyMeasurable (fun t ↦ ∫ u, positiveArmKernel t u ∂μ) := by
  exact measurable_positiveArmKernel.stronglyMeasurable.integral_prod_right

/-- The positive tangent arm length is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_tangentArm_fst (C : RightAngleCapSpace) :
    AEStronglyMeasurable (fun t ↦ (tangentArmLengths C t).2.1)
      (volume.restrict (Ioc 0 (Real.pi / 2))) := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  apply (stronglyMeasurable_integral_positiveArmKernel
    (surfaceAreaMeasure C.val)).aestronglyMeasurable.congr
  filter_upwards [] with t
  rw [tangentArm_convolution C t, positiveArmKernel_eq_indicator]
  exact integral_indicator (μ := surfaceAreaMeasure C.val)
    (f := fun u : Real.Angle ↦ (u - (t : Real.Angle)).sin)
    (Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2))

/-- The positive tangent arm length is nonnegative: it is the integral of the sine of a
quarter-turn of normal directions against the surface area measure. -/
theorem tangentArm_fst_nonneg (C : RightAngleCapSpace) {t : ℝ} :
    0 ≤ (tangentArmLengths C t).2.1 := by
  rw [tangentArm_convolution C t]
  refine setIntegral_nonneg (Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2)) ?_
  rintro u ⟨v, hv, rfl⟩
  rw [← Real.Angle.coe_sub, Real.Angle.sin_coe]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hv.1])
    (by linarith [hv.2, Real.pi_pos])

/-- Both right tangent arm lengths of a right-angle cap are nonnegative: the outer corner
realizes the support value in the tangent direction, while the two contacts lie in the cap. -/
theorem tangentArmLengths_right_nonneg (K : RightAngleCapSpace) (t : ℝ) :
    0 ≤ (tangentArmLengths K t).1.1 ∧ 0 ≤ (tangentArmLengths K t).1.2 := by
  have hy : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    change inner ℝ (supportingPlacement (K.val : Set Point) (t : Real.Angle)
      hallwayParts.outerCorner) _ = _
    rw [inner_supportingPlacement_tangentVector]
    simp [hallwayParts]
  have hmem (p : Point) (hp : p ∈ (K.val : Set Point)) :
      inner ℝ p (tangentVector (t : Real.Angle)) ≤
        supportValue K.val ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← normalVector_add_pi_div_two (t : Real.Angle)]
    exact inner_le_supportValue K.val hp _
  simp only [tangentArmLengths, capVertices, inner_sub_left, hy]
  exact ⟨sub_nonneg.mpr (hmem _ (edgeVertices_fst_mem K.val _).1),
    sub_nonneg.mpr (hmem _ (edgeVertices_snd_mem K.val _).1)⟩

/-- The positive tangent arm length is bounded by the total mass of the surface area measure. -/
theorem abs_tangentArm_fst_le (C : RightAngleCapSpace) {t : ℝ} :
    |(tangentArmLengths C t).2.1| ≤ (surfaceAreaMeasure C.val).real Set.univ := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  rw [tangentArm_convolution C t]
  change ‖∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2),
    (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure C.val‖ ≤ _
  calc
    _ ≤ 1 * (surfaceAreaMeasure C.val).real
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)) := by
      apply norm_setIntegral_le_of_norm_le_const
      · finiteness
      · intro u hu
        simp only [Real.norm_eq_abs]
        rw [← Real.Angle.sin_toReal]
        exact Real.abs_sin_le_one _
    _ ≤ (surfaceAreaMeasure C.val).real Set.univ := by
      simpa only [one_mul] using
        measureReal_mono (μ := surfaceAreaMeasure C.val) (Set.subset_univ _)
          (measure_ne_top _ _)

/-- The positive tangent arm length is bounded by the total surface mass, hence integrable. -/
theorem intervalIntegrable_tangentArm_fst (C : RightAngleCapSpace) :
    IntervalIntegrable (fun t ↦ (tangentArmLengths C t).2.1)
      volume 0 (Real.pi / 2) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).2
  apply (integrableOn_const
    (μ := volume) (s := Ioc 0 (Real.pi / 2)) (measure_Ioc_lt_top.ne)
    (C := (surfaceAreaMeasure C.val).real Set.univ)).mono'
      (aestronglyMeasurable_tangentArm_fst C)
  filter_upwards [] with t
  exact abs_tangentArm_fst_le C

private theorem maximumPolygonCap_diam_le (n : ℕ) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) : Metric.diam (K.val : Set Point) ≤ 5 := by
  classical
  obtain ⟨hn, ⟨k, hk⟩, P, hPK, hmax⟩ := hK
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hinner : ∀ (p : Point) (s : ℝ),
      inner ℝ p (normalVector (s : Real.Angle)) = p 0 * Real.cos s + p 1 * Real.sin s := by
    intro p s
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.Angle.cos_coe,
      Real.Angle.sin_coe]
    ring
  have hc1 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hsn1 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hc2 : Real.cos (Real.pi / 4 + Real.pi / 2) = -(Real.sqrt 2 / 2) := by
    rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have hsn2 : Real.sin (Real.pi / 4 + Real.pi / 2) = Real.sqrt 2 / 2 := by
    rw [Real.sin_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  set h1 : ℝ := supportValue (K.val : Set Point) ((Real.pi / 4 : ℝ) : Real.Angle)
  set h2 : ℝ := supportValue (K.val : Set Point)
    ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)
  have htop : ∀ p ∈ (K.val : Set Point), p 1 ≤ 1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two, K.property.2.2.2.1] at hle
    linarith
  have hbot : ∀ p ∈ (K.val : Set Point), 0 ≤ p 1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hcc : Real.cos (3 * Real.pi / 2) = 0 := by
      rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add,
        Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hss : Real.sin (3 * Real.pi / 2) = -1 := by
      rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add,
        Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    rw [hinner, hcc, hss, K.property.2.2.2.2.2.1] at hle
    linarith
  have hsupp1 : ∀ p ∈ (K.val : Set Point),
      p 0 * (Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2) ≤ h1 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 4 : ℝ) : Real.Angle)
    rwa [hinner, hc1, hsn1] at hle
  have hsupp2 : ∀ p ∈ (K.val : Set Point),
      p 0 * -(Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2) ≤ h2 := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)
    rwa [hinner, hc2, hsn2] at hle
  -- the diagonal angle belongs to the dyadic grid
  have hdir : (rightAngleSet n hn).directions =
      (Finset.Ioo 0 n).image (fun i : ℕ ↦ (i : ℝ) / n * (Real.pi / 2)) := rfl
  have hquarter : Real.pi / 4 ∈ (rightAngleSet n hn).directions := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
      cases k with
      | zero => rw [pow_zero] at hk; omega
      | succ m => exact ⟨m, rfl⟩
    rw [hdir]
    refine Finset.mem_image.mpr ⟨2 ^ m, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · positivity
    · rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
    · rw [hk]
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      push_cast
      rw [pow_succ]
      field_simp
      ring
  -- the inner corner at the diagonal angle has height at most one
  have hsum : h1 + h2 ≤ 2 + Real.sqrt 2 := by
    by_contra hcon
    rw [not_le] at hcon
    set e : ℝ := (h1 + h2 - 2 - Real.sqrt 2) / 4 with he
    have hepos : 0 < e := by rw [he]; linarith
    set q : Point := !₂[Real.sqrt 2 / 2 * (h1 - h2),
      Real.sqrt 2 / 2 * (h1 + h2 - 2 - 2 * e)]
    have hq0 : q 0 = Real.sqrt 2 / 2 * (h1 - h2) := rfl
    have hq1 : q 1 = Real.sqrt 2 / 2 * (h1 + h2 - 2 - 2 * e) := rfl
    have hqheight : 1 < q 1 := by
      rw [hq1, he]
      nlinarith
    have hqu : inner ℝ q (normalVector ((Real.pi / 4 : ℝ) : Real.Angle)) = h1 - 1 - e := by
      rw [hinner, hq0, hq1, hc1, hsn1]
      linear_combination ((h1 - 1 - e) / 2) * hs2
    have hqv : inner ℝ q (normalVector ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle))
        = h2 - 1 - e := by
      rw [hinner, hq0, hq1, hc2, hsn2]
      linear_combination ((h2 - 1 - e) / 2) * hs2
    have hqe : inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = q 1 := by
      rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
    have hfan : q ∈ capFan (rightAngleSet n hn).angle := by
      rw [hangle]
      refine ⟨?_, ?_⟩ <;>
        · change (0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          rw [hqe]
          linarith
    have hquad : q ∈ innerQuadrant (P.val.val : Set Point) (Real.pi / 4) := by
      rw [hPK]
      refine ⟨?_, ?_⟩
      · change inner ℝ q (normalVector ((Real.pi / 4 : ℝ) : Real.Angle)) < h1 - 1
        rw [hqu]
        linarith
      · change inner ℝ q (normalVector ((Real.pi / 4 + Real.pi / 2 : ℝ) : Real.Angle)) < h2 - 1
        rw [hqv]
        linarith
    have hmemniche : q ∈ polygonNiche (rightAngleSet n hn) P.val :=
      ⟨hfan, Set.mem_biUnion hquarter hquad⟩
    have hsub := polygonNiche_subset_of_balanced P (maximumPolygonCap_balanced P hmax)
    have hqK : q ∈ (P.val.val : Set Point) := hsub hmemniche
    rw [hPK] at hqK
    exact absurd (htop q hqK) (not_le.mpr hqheight)
  -- the outer corner height and the trapezoid containing the cap
  set hgt : ℝ := Real.sqrt 2 / 2 * (h1 + h2) with hgtdef
  set ctr : ℝ := Real.sqrt 2 / 2 * (h1 - h2) with hctrdef
  have hgtle : hgt ≤ 1 + Real.sqrt 2 := by
    rw [hgtdef]
    nlinarith
  have hsum1 : hgt + ctr = Real.sqrt 2 * h1 := by rw [hgtdef, hctrdef]; ring
  have hsum2 : hgt - ctr = Real.sqrt 2 * h2 := by rw [hgtdef, hctrdef]; ring
  have htrap1 : ∀ p ∈ (K.val : Set Point), p 0 + p 1 ≤ hgt + ctr := by
    intro p hp
    have hm := mul_le_mul_of_nonneg_left (hsupp1 p hp) hs2pos.le
    have hkey : Real.sqrt 2 * (p 0 * (Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2))
        = p 0 + p 1 := by linear_combination (p 0 / 2 + p 1 / 2) * hs2
    rw [hkey] at hm
    linarith
  have htrap2 : ∀ p ∈ (K.val : Set Point), p 1 - p 0 ≤ hgt - ctr := by
    intro p hp
    have hm := mul_le_mul_of_nonneg_left (hsupp2 p hp) hs2pos.le
    have hkey : Real.sqrt 2 * (p 0 * -(Real.sqrt 2 / 2) + p 1 * (Real.sqrt 2 / 2))
        = p 1 - p 0 := by linear_combination (p 1 / 2 - p 0 / 2) * hs2
    rw [hkey] at hm
    linarith
  have hgtge : 1 ≤ hgt := by
    have hle : supportValue (K.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) ≤ hgt := by
      apply csSup_le (K.val.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ hgt
      rw [hinner, Real.cos_pi_div_two, Real.sin_pi_div_two]
      have h1p := htrap1 p hp
      have h2p := htrap2 p hp
      linarith
    rw [K.property.2.2.2.1] at hle
    exact hle
  -- every distance inside the trapezoid is at most the length of its bottom side
  have hdiam : Metric.diam (K.val : Set Point) ≤ 2 * hgt := by
    refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
    intro p hp q hq
    have hp1 := htrap1 p hp
    have hp2 := htrap2 p hp
    have hq1 := htrap1 q hq
    have hq2 := htrap2 q hq
    have hpt := htop p hp
    have hpb := hbot p hp
    have hqt := htop q hq
    have hqb := hbot q hq
    have hd : dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp [Real.dist_eq, sq_abs]
    rw [hd, show (2 : ℝ) * hgt = Real.sqrt ((2 * hgt) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    have kx : (p 0 - q 0) ^ 2 ≤ (2 * hgt - p 1 - q 1) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * hgt - p 1 - q 1 - (p 0 - q 0))
        (by linarith : (0 : ℝ) ≤ 2 * hgt - p 1 - q 1 + (p 0 - q 0))]
    nlinarith [kx, mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * hgt - 2)
      (by linarith : (0 : ℝ) ≤ p 1 + q 1),
      mul_nonneg hpb (by linarith : (0 : ℝ) ≤ 1 - p 1),
      mul_nonneg hqb (by linarith : (0 : ℝ) ≤ 1 - q 1)]
  have hdiam5 : Metric.diam (K.val : Set Point) ≤ 5 := by linarith
  exact hdiam5

private theorem tangentArmLengths_le_of_diam (K : RightAngleCapSpace)
    (hdiam5 : Metric.diam (K.val : Set Point) ≤ 5) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (tangentArmLengths K t).1.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).1.2 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.2 ∈ Set.Icc (0 : ℝ) 5 := by
  intro t ht
  obtain ⟨hAp, hAm, hCp, hCm⟩ := capTangentArm_identities K t
  have huu : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 :=
    inner_normalVector_self t
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have huv : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 :=
    inner_normalVector_tangentVector t
  have hvu : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, huv]
  have hnu : ‖normalVector (t : Real.Angle)‖ = 1 := norm_normalVector_real t
  have hvn : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (t : Real.Angle) := by
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  have hnv : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    rw [← hvn]
    exact norm_normalVector_real _
  have hyu : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (normalVector (t : Real.Angle)) = supportValue (K.val : Set Point) (t : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      huu, hvu]
    ring
  have hyv : inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner
      (tangentVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      huv, hvv]
    ring
  have hApmem : (capVertices K t).1.1 ∈ (K.val : Set Point) :=
    (edgeVertices_fst_mem K.val (t : Real.Angle)).1
  have hAmmem : (capVertices K t).1.2 ∈ (K.val : Set Point) :=
    (edgeVertices_snd_mem K.val (t : Real.Angle)).1
  have hCpmem : (capVertices K t).2.1 ∈ (K.val : Set Point) :=
    (edgeVertices_fst_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hCmmem : (capVertices K t).2.2 ∈ (K.val : Set Point) :=
    (edgeVertices_snd_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hsupv : ∀ p ∈ (K.val : Set Point),
      inner ℝ p (tangentVector (t : Real.Angle)) ≤
        supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    intro p hp
    have hle := inner_le_supportValue K.val hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
    rwa [hvn] at hle
  have hsupu : ∀ p ∈ (K.val : Set Point),
      inner ℝ p (normalVector (t : Real.Angle)) ≤
        supportValue (K.val : Set Point) (t : Real.Angle) :=
    fun p hp ↦ inner_le_supportValue K.val hp (t : Real.Angle)
  -- the arm identities in projected form
  have harm : ∀ (A C : Point) (f g : ℝ),
      (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
        A + f • tangentVector (t : Real.Angle) →
      (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
        C + g • normalVector (t : Real.Angle) →
      A ∈ (K.val : Set Point) → C ∈ (K.val : Set Point) →
      (f ∈ Set.Icc (0 : ℝ) 5 ∧ g ∈ Set.Icc (0 : ℝ) 5) := by
    intro A C f g hfA hgC hAmem hCmem
    have hfv : inner ℝ A (tangentVector (t : Real.Angle)) + f =
        supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← hyv, hfA, inner_add_left, real_inner_smul_left, hvv]
      ring
    have hgu : inner ℝ C (normalVector (t : Real.Angle)) + g =
        supportValue (K.val : Set Point) (t : Real.Angle) := by
      rw [← hyu, hgC, inner_add_left, real_inner_smul_left, huu]
      ring
    have hAC : A + f • tangentVector (t : Real.Angle) = C + g • normalVector (t : Real.Angle) :=
      hfA ▸ hgC
    have hprojv := congrArg (fun z : Point ↦ inner ℝ z (tangentVector (t : Real.Angle))) hAC
    have hproju := congrArg (fun z : Point ↦ inner ℝ z (normalVector (t : Real.Angle))) hAC
    simp only [inner_add_left, real_inner_smul_left, hvv, hvu, huu, huv, mul_one,
      mul_zero, add_zero] at hprojv hproju
    have hdist : dist A C ≤ Metric.diam (K.val : Set Point) :=
      Metric.dist_le_diam_of_mem K.val.isCompact.isBounded hAmem hCmem
    have hfeq : f = inner ℝ (C - A) (tangentVector (t : Real.Angle)) := by
      rw [inner_sub_left]
      linarith
    have hgeq : g = inner ℝ (A - C) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left]
      linarith
    constructor
    · refine ⟨by linarith [hsupv A hAmem], ?_⟩
      have hb : inner ℝ (C - A) (tangentVector (t : Real.Angle)) ≤
          ‖C - A‖ * ‖tangentVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      rw [hnv, mul_one, norm_sub_rev, ← dist_eq_norm] at hb
      rw [hfeq]
      linarith
    · refine ⟨by linarith [hsupu C hCmem], ?_⟩
      have hb : inner ℝ (A - C) (normalVector (t : Real.Angle)) ≤
          ‖A - C‖ * ‖normalVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      rw [hnu, mul_one, ← dist_eq_norm] at hb
      rw [hgeq]
      linarith
  obtain ⟨hf1, hg1⟩ := harm (capVertices K t).1.1 (capVertices K t).2.1
    (tangentArmLengths K t).1.1 (tangentArmLengths K t).2.1 hAp hCp hApmem hCpmem
  obtain ⟨hf2, hg2⟩ := harm (capVertices K t).1.2 (capVertices K t).2.2
    (tangentArmLengths K t).1.2 (tangentArmLengths K t).2.2 hAm hCm hAmmem hCmmem
  exact ⟨hf1, hf2, hg1, hg2⟩


theorem maximumPolygonCap_arm_bound (n : ℕ) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) :
    Metric.diam (K.val : Set Point) ≤ 5 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (tangentArmLengths K t).1.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).1.2 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.1 ∈ Set.Icc (0 : ℝ) 5 ∧
      (tangentArmLengths K t).2.2 ∈ Set.Icc (0 : ℝ) 5 := by
  have hdiam := maximumPolygonCap_diam_le n K hK
  exact ⟨hdiam, tangentArmLengths_le_of_diam K hdiam⟩

/-! ### Helpers for the discrete arm bound -/

/-- Two representatives of the same angle in one turn agree. -/
private theorem coe_angle_inj_Ioc {x y : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi))
    (hy : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)) (h : (x : Real.Angle) = (y : Real.Angle)) :
    x = y :=
  Real.Angle.injOn_coe_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) hx hy h

/-- Between consecutive grid normals a right-angle polygon cap has no exposed edge, both at
the direction itself and at the direction shifted by a right angle. -/
private theorem rightAnglePolygonCap_edgeVertices_eq (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hgrid : s ∉ (rightAngleSet n hn).directions) :
    (edgeVertices K.val.val (s : Real.Angle)).1 =
        (edgeVertices K.val.val (s : Real.Angle)).2 ∧
      (edgeVertices K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  have hdirI : ∀ r ∈ (rightAngleSet n hn).directions, r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun r hr ↦ (rightAngleSet n hn).interior r hr
  -- the possible normals of a nondegenerate exposed edge in the upper half turn
  have hkey : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) Real.pi →
      (edgeVertices K.val.val (x : Real.Angle)).1 ≠
        (edgeVertices K.val.val (x : Real.Angle)).2 →
      x ∈ (rightAngleSet n hn).directions ∨
        (∃ r ∈ (rightAngleSet n hn).directions, x = r + Real.pi / 2) ∨
        x = Real.pi / 2 := by
    intro x hx hne
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := ⟨hx.1, by linarith [hx.2]⟩
    have hlow : ∀ z : Real.Angle, z ∈ capLowerNormals (rightAngleSet n hn).angle →
        z = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      intro z hz
      rcases hz with hz | hz
      · rw [hz]
        congr 1
        show (rightAngleSet n hn).angle + Real.pi = 3 * Real.pi / 2
        change Real.pi / 2 + Real.pi = 3 * Real.pi / 2
        ring
      · exact hz
    rcases K.properEdgeNormal_mem_allowed_or_antipodal (x : Real.Angle) hne with
      (⟨r, hr, hrx⟩ | hlowx) | ⟨z, hz, hzx⟩
    · have hrI := angleDomain_subset_Ioo (rightAngleSet n hn) hr
      have hxr : x = r := coe_angle_inj_Ioc hxIoc ⟨hrI.1, by linarith [hrI.2]⟩ hrx.symm
      subst hxr
      rcases hr with (hr | ⟨r, hr, hrx⟩) | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inl ⟨r, hr, hrx.symm⟩)
      · rcases hr with hr | hr
        · exact Or.inr (Or.inr hr)
        · exact Or.inr (Or.inr hr)
    · exfalso
      have hx3 : x = 3 * Real.pi / 2 :=
        coe_angle_inj_Ioc hxIoc ⟨by linarith, by linarith⟩ (hlow _ hlowx)
      linarith [hx.2]
    · rcases hz with ⟨r, hr, rfl⟩ | hz
      · exfalso
        have hrI := angleDomain_subset_Ioo (rightAngleSet n hn) hr
        have hxr : x = r + Real.pi := by
          refine coe_angle_inj_Ioc hxIoc ⟨by linarith [hrI.1], by linarith [hrI.2]⟩ ?_
          rw [Real.Angle.coe_add]
          exact hzx.symm
        linarith [hx.2, hrI.1]
      · right; right
        refine coe_angle_inj_Ioc hxIoc ⟨by linarith, by linarith⟩ ?_
        have hxz : (x : Real.Angle) =
            ((3 * Real.pi / 2 : ℝ) : Real.Angle) + (Real.pi : Real.Angle) := by
          rw [← hzx, hlow _ hz]
        rw [hxz, ← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
        exact ⟨1, by push_cast; ring⟩
  constructor
  · by_contra hne
    rcases hkey s ⟨hs.1, by linarith [hs.2]⟩ hne with h | ⟨r, hr, hrs⟩ | h
    · exact hgrid h
    · linarith [(hdirI r hr).1, hs.2]
    · linarith [hs.2]
  · by_contra hne
    rcases hkey (s + Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ hne with
      h | ⟨r, hr, hrs⟩ | h
    · linarith [(hdirI _ h).2, hs.1]
    · exact hgrid (by rwa [show s = r by linarith])
    · linarith [hs.1]

/-- On a cell of degenerate exposed edges whose contacts lie in a finite set, the contact point
is constant and agrees with both endpoint conventions. -/
private theorem exists_edgeVertices_const_of_degenerate (K : ConvexBody Point)
    {S : Set Point} (hS : S.Finite) {a b : ℝ} (hab : a < b)
    (hdeg : ∀ s ∈ Set.Ioo a b,
      (edgeVertices K (s : Real.Angle)).1 = (edgeVertices K (s : Real.Angle)).2)
    (hmem : ∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 ∈ S) :
    ∃ A : Point, (∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 = A) ∧
      (edgeVertices K (a : Real.Angle)).1 = A ∧
      (edgeVertices K (b : Real.Angle)).2 = A := by
  classical
  have hloc : ∀ u ∈ Set.Ioo a b, ∀ᶠ r : ℝ in 𝓝 u,
      (edgeVertices K (r : Real.Angle)).1 = (edgeVertices K (u : Real.Angle)).1 := by
    intro u hu
    have hIoo : Set.Ioo a b ∈ 𝓝 u := isOpen_Ioo.mem_nhds hu
    have hnbhd : (S \ {(edgeVertices K (u : Real.Angle)).1})ᶜ ∈
        𝓝 (edgeVertices K (u : Real.Angle)).1 :=
      (hS.sdiff (t := {(edgeVertices K (u : Real.Angle)).1})).isClosed.isOpen_compl.mem_nhds
        (by simp)
    have hright := (contact_oneSided_limits K u).1 hnbhd
    have hleft := (contact_oneSided_limits K u).2.2.2.1
    rw [← hdeg u hu] at hleft
    have hleft' := hleft hnbhd
    have hfin : ∀ᶠ r : ℝ in 𝓝[≠] u,
        (edgeVertices K (r : Real.Angle)).1 = (edgeVertices K (u : Real.Angle)).1 := by
      rw [← nhdsLT_sup_nhdsGT]
      refine Filter.eventually_sup.mpr ⟨?_, ?_⟩
      · filter_upwards [hleft', nhdsWithin_le_nhds hIoo] with r hr hrI
        by_contra hcon
        exact hr ⟨hmem r hrI, hcon⟩
      · filter_upwards [hright, nhdsWithin_le_nhds hIoo] with r hr hrI
        by_contra hcon
        exact hr ⟨hmem r hrI, hcon⟩
    rw [← nhdsNE_sup_pure u]
    exact Filter.eventually_sup.mpr ⟨hfin, Filter.eventually_pure.mpr rfl⟩
  have hmI : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ s ∈ Set.Ioo a b, (edgeVertices K (s : Real.Angle)).1 =
      (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1 := by
    intro s hs
    by_contra hne
    have hUopen : IsOpen {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 =
        (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} :=
      isOpen_iff_mem_nhds.2 fun r hr ↦ eventually_eventually_nhds.2 hr
    have hVopen : IsOpen {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 ≠
        (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} :=
      isOpen_iff_mem_nhds.2 fun r hr ↦ eventually_eventually_nhds.2 hr
    have hcover : Set.Ioo a b ⊆
        {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 =
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} ∪
        {r : ℝ | ∀ᶠ x : ℝ in 𝓝 r, (edgeVertices K (x : Real.Angle)).1 ≠
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1} := by
      intro r hr
      by_cases hcase : (edgeVertices K (r : Real.Angle)).1 =
          (edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1
      · exact Or.inl (by filter_upwards [hloc r hr] with x hx; rw [hx, hcase])
      · exact Or.inr (by filter_upwards [hloc r hr] with x hx; rw [hx]; exact hcase)
    obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_Ioo _ _ hUopen hVopen hcover
      ⟨(a + b) / 2, hmI, hloc _ hmI⟩
      ⟨s, hs, by filter_upwards [hloc s hs] with x hx; rw [hx]; exact hne⟩
    obtain ⟨y, hy1, hy2⟩ := (hxU.and hxV).exists
    exact hy2 hy1
  refine ⟨(edgeVertices K (((a + b) / 2 : ℝ) : Real.Angle)).1, hconst, ?_, ?_⟩
  · refine tendsto_nhds_unique (contact_oneSided_limits K a).1
      (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsGT hab] with r hr
    exact (hconst r hr).symm
  · refine tendsto_nhds_unique (contact_oneSided_limits K b).2.2.2.1
      (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsLT hab] with r hr
    exact (hconst r hr).symm

private theorem normalVector_chord_norm_le (t δ : ℝ) (hδnonneg : 0 ≤ δ) :
    ‖(1 - Real.cos δ) • normalVector (t : Real.Angle) -
      Real.sin δ • tangentVector (t : Real.Angle)‖ ≤ δ := by
  have huu : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 :=
    inner_normalVector_self t
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have huv : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 :=
    inner_normalVector_tangentVector t
  have hvu : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm]
    exact huv
  have hsqn : ‖(1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)‖ ^ 2 =
      2 - 2 * Real.cos (δ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hvv, huv, hvu]
    nlinarith [Real.sin_sq_add_cos_sq (δ)]
  have hznorm : ‖(1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)‖ ≤
      δ := by
    have hcosb : 1 - δ ^ 2 / 2 ≤ Real.cos (δ) :=
      Real.one_sub_sq_div_two_le_cos
    nlinarith [norm_nonneg ((1 - Real.cos (δ)) • normalVector (t : Real.Angle) -
      Real.sin (δ) • tangentVector (t : Real.Angle)), hsqn, hδnonneg]
  exact hznorm

private theorem tangentArmLengths_snd_support (K : RightAngleCapSpace) :
    ∀ s : ℝ,
     (tangentArmLengths K s).2.1 = supportValue (K.val : Set Point) (s : Real.Angle) -
       inner ℝ (capVertices K s).2.1 (normalVector (s : Real.Angle)) ∧
     (tangentArmLengths K s).2.2 = supportValue (K.val : Set Point) (s : Real.Angle) -
       inner ℝ (capVertices K s).2.2 (normalVector (s : Real.Angle)) := by
  have hy : ∀ s : ℝ, inner ℝ
      (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner
      (normalVector (s : Real.Angle)) = supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s
    have hvu : inner ℝ (tangentVector (s : Real.Angle)) (normalVector (s : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector s
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self s, hvu]
    ring
  intro s
  constructor <;>
    · change inner ℝ (_ - _) (normalVector (s : Real.Angle)) = _
      rw [inner_sub_left, hy s]

theorem maximumPolygonCap_arm_cell (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions) :
    (∀ u ∈ Set.Ioo t (t + polygonStepSize n),
      (tangentArmLengths K u).2.1 ≤ (tangentArmLengths K t).2.1 ∧
      (tangentArmLengths K u).2.1 = (tangentArmLengths K u).2.2 ∧
      (tangentArmLengths K (t + polygonStepSize n)).2.2 ≤
        (tangentArmLengths K u).2.2) ∧
    (tangentArmLengths K t).2.1 -
      (tangentArmLengths K (t + polygonStepSize n)).2.2 ≤ 5 * polygonStepSize n := by
  classical
  obtain ⟨hdiam, harmbd⟩ := maximumPolygonCap_arm_bound n K hK
  obtain ⟨hn2, -, P, hPK, -⟩ := hK
  have hPKval : (P.val.val : ConvexBody Point) = K.val := congrArg Subtype.val hPK
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hδpos : 0 < polygonStepSize n := div_pos (by linarith) hnR
  have hδle : polygonStepSize n ≤ Real.pi / 4 := by
    change Real.pi / 2 / n ≤ Real.pi / 4
    rw [div_le_iff₀ hnR]
    nlinarith
  -- the cell lies in the parameter range and contains no grid direction
  have hcell0 : 0 ≤ t ∧ t + polygonStepSize n ≤ Real.pi / 2 := by
    rcases ht with rfl | ht'
    · exact ⟨le_rfl, by linarith⟩
    · obtain ⟨h1, h2⟩ := rightAngleSet_direction_bounds n hn ht'
      exact ⟨by linarith, by linarith⟩
  obtain ⟨ht0, htδ⟩ := hcell0
  have hnogrid : ∀ s ∈ Set.Ioo t (t + polygonStepSize n),
      s ∉ (rightAngleSet n hn).directions := by
    intro s hs hcon
    rcases ht with rfl | ht'
    · linarith [(rightAngleSet_direction_bounds n hn hcon).1, hs.2]
    · rcases rightAngleSet_direction_le_or_succ_le n hn hcon ht' with h | h
      · linarith [hs.1]
      · linarith [hs.2]
  -- no exposed edge has its normal inside the open cell, shifted or not
  have hdegen : ∀ s ∈ Set.Ioo t (t + polygonStepSize n),
      (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2 ∧
      (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2 := by
    intro s hs
    have hsI : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := rightAnglePolygonCap_edgeVertices_eq n hn2 P hsI (hnogrid s hs)
    rwa [hPKval] at h
  have hdegen2 : ∀ s ∈ Set.Ioo (t + Real.pi / 2) (t + polygonStepSize n + Real.pi / 2),
      (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2 := by
    intro s hs
    have hr : s - Real.pi / 2 ∈ Set.Ioo t (t + polygonStepSize n) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := (hdegen _ hr).2
    rwa [show s - Real.pi / 2 + Real.pi / 2 = s by ring] at h
  -- singleton contacts range over a finite set of constraint vertices
  have hdomain : (angleDomain (rightAngleSet n hn2)).Finite :=
    (((rightAngleSet n hn2).directions.finite_toSet.union
      ((rightAngleSet n hn2).directions.finite_toSet.image
        (fun r ↦ r + Real.pi / 2))).union
      ((Set.finite_singleton (Real.pi / 2)).insert (rightAngleSet n hn2).angle))
  have hNfin : (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain (rightAngleSet n hn2)) ∪
      capLowerNormals (rightAngleSet n hn2).angle).Finite :=
    (hdomain.image (fun r : ℝ ↦ (r : Real.Angle))).union
      ((Set.finite_singleton _).insert _)
  obtain ⟨Cs, hCsfin, -, hKCs⟩ := P.property.finite_constraints hNfin
  rw [hPKval] at hKCs
  have hSfin : (finiteConstraintVertices Cs).Finite :=
    finite_finiteConstraintVertices Cs hCsfin
  have hSmem : ∀ θ : Real.Angle, (edgeVertices K.val θ).1 = (edgeVertices K.val θ).2 →
      (edgeVertices K.val θ).1 ∈ finiteConstraintVertices Cs := by
    intro θ hθ
    refine singleton_exposedEdge_mem_finiteConstraintVertices Cs hCsfin K.val hKCs (t := θ) ?_
    rw [exposedEdge_eq_segment_edgeVertices, ← hθ, segment_same]
  -- the two contact points that are constant across the cell
  obtain ⟨A, hAcell, hAleft, hAright⟩ := exists_edgeVertices_const_of_degenerate K.val hSfin
    (a := t) (b := t + polygonStepSize n) (by linarith)
    (fun s hs ↦ (hdegen s hs).1) (fun s hs ↦ hSmem _ (hdegen s hs).1)
  obtain ⟨Cp, hCcell, hCleft, hCright⟩ := exists_edgeVertices_const_of_degenerate K.val hSfin
    (a := t + Real.pi / 2) (b := t + polygonStepSize n + Real.pi / 2) (by linarith)
    hdegen2 (fun s hs ↦ hSmem _ (hdegen2 s hs))
  -- the arm lengths in support-function coordinates
  have harm := tangentArmLengths_snd_support K
  have hAK : A ∈ (K.val : Set Point) := by
    rw [← hAleft]
    exact (edgeVertices_fst_mem K.val (t : Real.Angle)).1
  have hCK : Cp ∈ (K.val : Set Point) := by
    rw [← hCleft]
    exact (edgeVertices_fst_mem K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hAsup : ∀ s : ℝ, (edgeVertices K.val (s : Real.Angle)).1 = A →
      inner ℝ A (normalVector (s : Real.Angle)) =
        supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s hsA
    rw [← hsA]
    exact (edgeVertices_fst_mem K.val (s : Real.Angle)).2
  have hAsup' : ∀ s : ℝ, (edgeVertices K.val (s : Real.Angle)).2 = A →
      inner ℝ A (normalVector (s : Real.Angle)) =
        supportValue (K.val : Set Point) (s : Real.Angle) := by
    intro s hsA
    rw [← hsA]
    exact (edgeVertices_snd_mem K.val (s : Real.Angle)).2
  -- the smooth comparison function and its sign conditions
  have hadd : ∀ s ε : ℝ, inner ℝ (A - Cp) (normalVector ((s + ε : ℝ) : Real.Angle)) =
      Real.cos ε * inner ℝ (A - Cp) (normalVector (s : Real.Angle)) +
      Real.sin ε * inner ℝ (A - Cp) (tangentVector (s : Real.Angle)) := by
    intro s ε
    rw [normalVector_add_real, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hDsign : ∀ s : ℝ, (edgeVertices K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp →
      inner ℝ (A - Cp) (tangentVector (s : Real.Angle)) ≤ 0 := by
    intro s hsC
    rw [← normalVector_add_pi_div_two_real s, inner_sub_left]
    have hA' := inner_le_supportValue K.val hAK ((s + Real.pi / 2 : ℝ) : Real.Angle)
    have hC' : inner ℝ Cp (normalVector ((s + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K.val : Set Point) ((s + Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← hsC]
      exact (edgeVertices_fst_mem K.val ((s + Real.pi / 2 : ℝ) : Real.Angle)).2
    linarith
  have hgt : (tangentArmLengths K t).2.1 =
      inner ℝ (A - Cp) (normalVector (t : Real.Angle)) := by
    rw [(harm t).1, inner_sub_left, hAsup t hAleft,
      show (capVertices K t).2.1 = Cp from hCleft]
  have hgb : (tangentArmLengths K (t + polygonStepSize n)).2.2 =
      inner ℝ (A - Cp) (normalVector ((t + polygonStepSize n : ℝ) : Real.Angle)) := by
    rw [(harm (t + polygonStepSize n)).2, inner_sub_left,
      hAsup' (t + polygonStepSize n) hAright,
      show (capVertices K (t + polygonStepSize n)).2.2 = Cp from hCright]
  have hgu : ∀ u ∈ Set.Ioo t (t + polygonStepSize n),
      (tangentArmLengths K u).2.1 = inner ℝ (A - Cp) (normalVector (u : Real.Angle)) ∧
      (tangentArmLengths K u).2.2 = inner ℝ (A - Cp) (normalVector (u : Real.Angle)) := by
    intro u hu
    have hCu : (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp :=
      hCcell (u + Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hCu2 : (capVertices K u).2.2 = Cp := by
      rw [show (capVertices K u).2.2 =
        (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).2 from rfl, ← (hdegen u hu).2]
      exact hCu
    refine ⟨?_, ?_⟩
    · rw [(harm u).1, inner_sub_left, hAsup u (hAcell u hu),
        show (capVertices K u).2.1 = Cp from hCu]
    · rw [(harm u).2, inner_sub_left, hAsup u (hAcell u hu), hCu2]
  have hGt0 : 0 ≤ inner ℝ (A - Cp) (normalVector (t : Real.Angle)) := by
    rw [← hgt]
    exact ((harmbd t ⟨ht0, by linarith⟩).2.2.1).1
  have hGt5 : inner ℝ (A - Cp) (normalVector (t : Real.Angle)) ≤ 5 := by
    rw [← hgt]
    exact ((harmbd t ⟨ht0, by linarith⟩).2.2.1).2
  constructor
  · intro u hu
    have hCu : (edgeVertices K.val ((u + Real.pi / 2 : ℝ) : Real.Angle)).1 = Cp :=
      hCcell (u + Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hGu0 : 0 ≤ inner ℝ (A - Cp) (normalVector (u : Real.Angle)) := by
      rw [← (hgu u hu).2]
      exact ((harmbd u ⟨by linarith [hu.1], by linarith [hu.2]⟩).2.2.2).1
    have hkey : inner ℝ (A - Cp) (normalVector (u : Real.Angle)) =
        Real.cos (u - t) * inner ℝ (A - Cp) (normalVector (t : Real.Angle)) +
        Real.sin (u - t) * inner ℝ (A - Cp) (tangentVector (t : Real.Angle)) := by
      rw [show ((u : ℝ) : Real.Angle) = ((t + (u - t) : ℝ) : Real.Angle) by
        rw [show t + (u - t) = u by ring], hadd]
    have hkey2 : inner ℝ (A - Cp) (normalVector ((t + polygonStepSize n : ℝ) : Real.Angle)) =
        Real.cos (t + polygonStepSize n - u) *
            inner ℝ (A - Cp) (normalVector (u : Real.Angle)) +
          Real.sin (t + polygonStepSize n - u) *
            inner ℝ (A - Cp) (tangentVector (u : Real.Angle)) := by
      rw [show ((t + polygonStepSize n : ℝ) : Real.Angle) =
        ((u + (t + polygonStepSize n - u) : ℝ) : Real.Angle) by
          rw [show u + (t + polygonStepSize n - u) = t + polygonStepSize n by ring], hadd]
    have hD := hDsign t hCleft
    have hDu := hDsign u hCu
    have hc1 : Real.cos (u - t) ≤ 1 := Real.cos_le_one _
    have hs1 : 0 ≤ Real.sin (u - t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hu.1]) (by linarith [hu.2])
    have hc2 : Real.cos (t + polygonStepSize n - u) ≤ 1 := Real.cos_le_one _
    have hs2 : 0 ≤ Real.sin (t + polygonStepSize n - u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hu.2]) (by linarith [hu.1])
    refine ⟨?_, ?_, ?_⟩
    · rw [(hgu u hu).1, hgt, hkey]
      linarith [mul_nonneg (sub_nonneg.mpr hc1) hGt0,
        mul_nonneg hs1 (neg_nonneg.mpr hD)]
    · rw [(hgu u hu).1, (hgu u hu).2]
    · rw [hgb, (hgu u hu).2, hkey2]
      linarith [mul_nonneg (sub_nonneg.mpr hc2) hGu0,
        mul_nonneg hs2 (neg_nonneg.mpr hDu)]
  · have hD := hDsign t hCleft
    have hz : (tangentArmLengths K t).2.1 -
        (tangentArmLengths K (t + polygonStepSize n)).2.2 =
        inner ℝ (A - Cp)
          ((1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle)) := by
      rw [hgt, hgb, hadd t (polygonStepSize n), inner_sub_right, real_inner_smul_right,
        real_inner_smul_right]
      ring
    have hznorm := normalVector_chord_norm_le t (polygonStepSize n) hδpos.le
    have hwnorm : ‖A - Cp‖ ≤ 5 := by
      rw [← dist_eq_norm]
      exact le_trans (Metric.dist_le_diam_of_mem K.val.isCompact.isBounded hAK hCK) hdiam
    rw [hz]
    calc inner ℝ (A - Cp)
          ((1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle))
        ≤ ‖A - Cp‖ * ‖(1 - Real.cos (polygonStepSize n)) • normalVector (t : Real.Angle) -
            Real.sin (polygonStepSize n) • tangentVector (t : Real.Angle)‖ :=
          real_inner_le_norm _ _
      _ ≤ 5 * polygonStepSize n :=
          mul_le_mul hwnorm hznorm (norm_nonneg _) (by norm_num)

theorem polygonCap_arm_integral_limit (K : ℕ → RightAngleCapSpace)
    (L : RightAngleCapSpace)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
      |(tangentArmLengths (K i) t).2.1 - (tangentArmLengths L t).2.1|)
      atTop (𝓝 0) := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n).val, (surfaceAreaMeasure_face_union (K n).val).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L.val, (surfaceAreaMeasure_face_union L.val).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity (fun n ↦ (K n).val) L.val hlim f f.continuous
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := hμ.mass
  obtain ⟨M, hM⟩ := hmass.bddAbove_range
  have hmass_le (n : ℕ) : (μs n).mass ≤ M := hM ⟨n, rfl⟩
  have hcoe_inj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle))
      (Ioc 0 (Real.pi / 2)) :=
    Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos])
  have hshift_inj : Set.InjOn
      (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (Ioc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    apply hcoe_inj hx hy
    simp only [Real.Angle.coe_add] at hxy
    exact add_right_cancel hxy
  have hae_left : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      (μ : Measure Real.Angle) {(t : Real.Angle)} = 0 :=
    ae_measure_singleton_comp_eq_zero_of_injOn (μ : Measure Real.Angle)
      measurableSet_Ioc hcoe_inj
  have hae_right : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      (μ : Measure Real.Angle) {((t + Real.pi / 2 : ℝ) : Real.Angle)} = 0 :=
    ae_measure_singleton_comp_eq_zero_of_injOn (μ : Measure Real.Angle)
      measurableSet_Ioc hshift_inj
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      Tendsto (fun n ↦ (tangentArmLengths (K n) t).2.1) atTop
        (𝓝 (tangentArmLengths L t).2.1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_left, hae_right] with t ht hleft hright
    let A := (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc t (t + Real.pi / 2)
    have hfrontier : (μ : Measure Real.Angle) (frontier A) = 0 := by
      apply measure_mono_null (Real.Angle.frontier_image_Ioc_subset
        (by linarith [Real.pi_pos]))
      simp only [insert_eq, measure_union_null hleft hright]
    have hAmeas : MeasurableSet A :=
      Real.Angle.measurableSet_image_Ioc t (t + Real.pi / 2)
    have hfrontier' : μ (frontier A) = 0 := by
      rw [← ENNReal.coe_eq_zero, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact hfrontier
    have hres := FiniteMeasure.tendsto_restrict_of_null_frontier
      hAmeas hμ hfrontier'
    let f : Real.Angle →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun u ↦ (u - (t : Real.Angle)).sin,
        Real.Angle.continuous_sin.comp (continuous_id.sub continuous_const)⟩
    have hint := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hres f
    change Tendsto (fun n ↦ ∫ u in A,
      (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure (K n).val) atTop
      (𝓝 (∫ u in A, (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure L.val)) at hint
    have hKt (n : ℕ) := tangentArm_convolution (K n) t
    have hLt := tangentArm_convolution L t
    simpa only [A, hKt, hLt] using hint
  have hmeas_arm := aestronglyMeasurable_tangentArm_fst
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t ↦ |(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1|)
      (volume.restrict (Ioc 0 (Real.pi / 2))) := by
    intro n
    have hm := ((hmeas_arm (K n)).sub (hmeas_arm L)).norm
    convert hm using 1
  have hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      ‖|(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1|‖ ≤
        (M : ℝ) + (μ.mass : ℝ) := by
    intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |(tangentArmLengths (K n) t).2.1 - (tangentArmLengths L t).2.1| ≤
          |(tangentArmLengths (K n) t).2.1| + |(tangentArmLengths L t).2.1| :=
        abs_sub _ _
      _ ≤ (surfaceAreaMeasure (K n).val).real Set.univ +
          (surfaceAreaMeasure L.val).real Set.univ :=
        add_le_add (abs_tangentArm_fst_le (K n) (t := t))
          (abs_tangentArm_fst_le L (t := t))
      _ = ((μs n).mass : ℝ) + (μ.mass : ℝ) := by
        change (μs n : Measure Real.Angle).real univ +
          (μ : Measure Real.Angle).real univ = _
        simp [Measure.real, ← FiniteMeasure.ennreal_mass]
      _ ≤ (M : ℝ) + (μ.mass : ℝ) := by
        have hn : ((μs n).mass : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmass_le n
        exact add_le_add hn le_rfl
  have hlim_zero : ∀ᵐ t ∂volume.restrict (Ioc 0 (Real.pi / 2)),
      Tendsto (fun n ↦ |(tangentArmLengths (K n) t).2.1 -
        (tangentArmLengths L t).2.1|) atTop (𝓝 0) := by
    filter_upwards [hpoint] with t ht
    have hc : Tendsto (fun _ : ℕ ↦ (tangentArmLengths L t).2.1) atTop
        (𝓝 (tangentArmLengths L t).2.1) := tendsto_const_nhds
    simpa only [sub_self, abs_zero] using (ht.sub hc).abs
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 (Real.pi / 2)))
    (fun _ ↦ (M : ℝ) + (μ.mass : ℝ)) hmeas
    (integrableOn_const (μ := volume) (s := Ioc 0 (Real.pi / 2))
      (measure_Ioc_lt_top.ne)) hbound hlim_zero
  simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    integral_zero] using hdom

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
# Bounds / Wedge Gap / Infimum
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- The two infima of the wedge-gap components over interior rotation angles. -/
@[expose]
def wedgeGapInfimum {ω : ℝ} (K : CapSpace ω) : ℝ × ℝ :=
  (sInf ((fun t ↦ (wedgeGaps K t).1) '' Set.Ioo 0 ω),
    sInf ((fun t ↦ (wedgeGaps K t).2) '' Set.Ioo 0 ω))

private theorem bddBelow_wedgeGaps_fst {ω : ℝ} (K : CapSpace ω) :
    BddBelow ((fun t ↦ (wedgeGaps K t).1) '' Ioo 0 ω) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := wedgeGaps_positive_lower_bound K t ht
  exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_nonneg {ω : ℝ} (K : CapSpace ω) :
    0 ≤ (wedgeGapInfimum K).1 := by
  rw [wedgeGapInfimum]
  apply le_csInf
  · exact (nonempty_Ioo.mpr K.property.1).image _
  · rintro _ ⟨t, ht, rfl⟩
    have h := wedgeGaps_positive_lower_bound K t ht
    exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_le_supportValue_zero {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤ supportValue K.val (0 : Real.Angle) := by
  let f := fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
    (supportValue K.val (t : Real.Angle) - 1) / Real.cos t
  have hcos : Real.cos ω ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩).ne'
  have hf : ContinuousAt f ω := continuousAt_const.sub
    (((continuous_supportValue_real K.val).continuousAt.sub continuousAt_const).div
      Real.continuous_cos.continuousAt hcos)
  have hf' : Tendsto f (𝓝[<] ω) (𝓝 (f ω)) :=
    hf.tendsto.mono_left inf_le_left
  have hlim : Tendsto f (𝓝[<] ω)
      (𝓝 (supportValue K.val (0 : Real.Angle))) := by
    convert hf' using 1
    simp [f, K.property.2.2.1]
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT K.property.1] with t ht
  rw [wedgeGapInfimum]
  have hle := csInf_le (bddBelow_wedgeGaps_fst K) ⟨t, ht, rfl⟩
  simpa only [f, wedgeGaps_fst_eq_supportValue] using hle

private def bottomGapSegment {ω : ℝ} (K : CapSpace ω) : Set Point :=
  let a := supportValue K.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K).1
  segment ℝ ((a - w) • normalVector (0 : Real.Angle))
    (a • normalVector (0 : Real.Angle))

private theorem point_eq_fst_smul_normalVector_zero_of_mem_normalLine
    {p : Point} (hp : p ∈ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    p = p 0 • normalVector (0 : Real.Angle) := by
  have hpy : p 1 = 0 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hp
    simpa [normalVector, frame, PiLp.inner_apply] using hp
  ext i
  fin_cases i <;> simp [normalVector, frame, hpy]

private theorem bottomGapSegment_subset_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    bottomGapSegment K.val ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let A := a • normalVector (0 : Real.Angle)
  let B := (a - w) • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := by
    exact supportValue_zero_smul_normalVector_mem K.val
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hwa : w ≤ a := wedgeGapInfimum_fst_le_supportValue_zero K.val hω
  have hBK : B ∈ (K.val.val : Set Point) := by
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK
      (sub_nonneg.mpr hwa) (by linarith)
  have hbottom : supportValue K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := K.val.property.2.2.2.2.2.1
  have hAedge : A ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [A, normalVector, frame]
  have hBedge : B ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hBK, ?_⟩
    change inner ℝ B (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [B, normalVector, frame]
  exact (convex_exposedEdge K.val.val _).segment_subset hBedge hAedge

private theorem polygonNiche_fanLine_fst_lt_gapStart {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {q : Point}
    (hq : q ∈ polygonNiche Θ K.val ∩
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    q 0 < supportValue K.val.val (0 : Real.Angle) -
      (wedgeGapInfimum K.val).1 := by
  obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq.1.2
  have htt := Θ.interior t ht
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
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
  have hinf : (wedgeGapInfimum K.val).1 ≤ (wedgeGaps K.val t).1 := by
    rw [wedgeGapInfimum]
    exact csInf_le (bddBelow_wedgeGaps_fst K.val) ⟨t, htt, rfl⟩
  have hgap : (wedgeGaps K.val t).1 =
      supportValue K.val.val (0 : Real.Angle) - (wedgeEndpoints K.val t).1 0 := by
    rw [wedgeGaps_fst_eq_supportValue]
    simp [wedgeEndpoints, normalVector, frame]
  rw [hgap] at hinf
  linarith

private theorem polygonNiche_fanLine_subset_bottom_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  let a := supportValue K.val.val (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := supportValue_zero_smul_normalVector_mem K.val
  have hqx0 : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    have hqy : q 1 = 0 := by
      have hline := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
      simpa [normalVector, frame, PiLp.inner_apply] using hline
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hqy, mul_zero,
      add_zero] at hfan
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan)
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
  have hqxa : q 0 ≤ a := by
    have hlt := polygonNiche_fanLine_fst_lt_gapStart K hq
    have hw0 := wedgeGapInfimum_fst_nonneg K.val
    dsimp only [a]
    linarith
  have hqeq := point_eq_fst_smul_normalVector_zero_of_mem_normalLine hq.2
  have hqK : q ∈ (K.val.val : Set Point) := by
    rw [hqeq]
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK hqx0 hqxa
  refine ⟨hqK, ?_⟩
  change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.val.property.2.2.2.2.2.1]
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  rw [inner_normalVector_three_pi_div_two]
  simp [hqy]

private theorem bottomGapSegment_disjoint_polygonNiche_fanLine {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    Disjoint (bottomGapSegment K.val)
      (polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  rw [Set.disjoint_left]
  intro q hqS hqN
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let B := (a - w) • normalVector (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hqx : a - w ≤ q 0 := by
    change q ∈ segment ℝ B A at hqS
    rw [segment_eq_image'] at hqS
    obtain ⟨r, hr, rfl⟩ := hqS
    have heq : (B + r • (A - B)) 0 = a - w + r * w := by
      simp [B, A, normalVector, frame]
    rw [heq]
    nlinarith [hr.1]
  have hlt := polygonNiche_fanLine_fst_lt_gapStart K hqN
  exact (not_lt_of_ge hqx) (by simpa only [a, w] using hlt)

private theorem hausdorffMeasure_bottomGapSegment {ω : ℝ} (K : CapSpace ω) :
    (Measure.hausdorffMeasure 1 (bottomGapSegment K)).toReal =
      (wedgeGapInfimum K).1 := by
  have hw0 := wedgeGapInfimum_fst_nonneg K
  rw [show bottomGapSegment K =
      segment ℝ
        ((supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle))
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
    MeasureTheory.hausdorffMeasure_segment, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_eq_norm]
  have hdiff :
      (supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle) -
        supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) =
      (-(wedgeGapInfimum K).1) • normalVector (0 : Real.Angle) := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hw0,
    norm_normalVector, mul_one]

private theorem wedgeGapInfimum_fst_le_surface_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2)
    (hbal : IsBalancedPolygonCap K) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let S := bottomGapSegment K.val
  let M := polygonNiche Θ K.val ∩
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0
  let E := exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hSsub : S ⊆ E := bottomGapSegment_subset_exposedEdge K hω
  have hMsub : M ⊆ E := polygonNiche_fanLine_subset_bottom_exposedEdge K hω
  have hSMsub : S ∪ M ⊆ E := Set.union_subset hSsub hMsub
  have hdisj : Disjoint S M := bottomGapSegment_disjoint_polygonNiche_fanLine K
  have hMMeas : MeasurableSet M := by
    apply (measurableSet_polygonNiche Θ K.val).inter
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hSne : μ S ≠ ⊤ := by
    dsimp only [μ, S]
    rw [show bottomGapSegment K.val =
        segment ℝ
          ((supportValue K.val.val (0 : Real.Angle) - (wedgeGapInfimum K.val).1) •
            normalVector (0 : Real.Angle))
          (supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    exact ENNReal.ofReal_ne_top
  have hatom := surfaceAreaMeasure_atom_length K.val.val
    ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hEne : μ E ≠ ⊤ := by
    dsimp only [μ, E]
    rw [← hatom.1, hatom.2.1]
    exact ENNReal.ofReal_ne_top
  have hMne : μ M ≠ ⊤ := measure_ne_top_of_subset hMsub hEne
  have hunion := measureReal_union hdisj hMMeas hSne hMne
  have hmono : μ.real (S ∪ M) ≤ μ.real E :=
    ENNReal.toReal_mono hEne (measure_mono hSMsub)
  have hSreal : μ.real S = (wedgeGapInfimum K.val).1 := by
    exact hausdorffMeasure_bottomGapSegment K.val
  have hMreal : μ.real M =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal -
        polygonPolylineLengthAt K (Real.pi / 2) := by
    have h := (polygonCap_polyline_lengths K).2 (Real.pi / 2) (by simp)
    dsimp only [μ, M]
    change (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)).toReal = _
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    simpa only [hang] using h.2
  have hEreal : μ.real E =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    exact (congrArg ENNReal.toReal hatom.1).symm
  have htT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  let tT : angleDomain Θ := ⟨Real.pi / 2, htT⟩
  have hpoly0 : 0 ≤ polygonCapPolylineLength K tT := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
  have hbalReal :
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal =
        polygonCapPolylineLength K tT := by
    simpa only [tT, ENNReal.toReal_ofReal hpoly0] using
      congrArg ENNReal.toReal (hbal tT)
  have hlength : polygonPolylineLengthAt K (Real.pi / 2) =
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    simp only [polygonPolylineLengthAt, dite_eq_left htT]
    exact hbalReal.symm
  rw [hunion, hSreal, hMreal, hEreal, hlength] at hmono
  linarith

theorem maximumPolygonCap_gap_le_surface {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) (hω : Θ.angle < Real.pi / 2) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K.val).2 ≤
      (surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)}).toReal := by
  have hbal := maximumPolygonCap_balanced K hK
  refine ⟨wedgeGapInfimum_fst_le_surface_of_balanced K hω hbal, ?_⟩
  obtain ⟨Q, hQcarrier, hQmax⟩ := maximumPolygonCap_mirror Θ K hK
  obtain ⟨P, hPcarrier, _hHall, hgap, _hupper, _hniche, hsurface⟩ :=
    cap_mirror_features K.val
  have hPQ : P = Q.val := by
    apply Subtype.ext
    apply ConvexBody.ext
    exact hPcarrier.trans hQcarrier.symm
  have hQbal := maximumPolygonCap_balanced Q hQmax
  have hQright := wedgeGapInfimum_fst_le_surface_of_balanced Q hω hQbal
  have himage :
      (fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle =
        (fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      refine ⟨Θ.angle - t, ⟨by linarith, by linarith⟩, ?_⟩
      have hg := (hgap t ⟨ht0, htω⟩).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val t).1 = (wedgeGaps K.val (Θ.angle - t)).2 at hg
      exact hg.symm
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      have hcomp : Θ.angle - t ∈ Ioo 0 Θ.angle := ⟨by linarith, by linarith⟩
      refine ⟨Θ.angle - t, hcomp, ?_⟩
      have hg := (hgap (Θ.angle - t) hcomp).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val (Θ.angle - t)).1 =
        (wedgeGaps K.val (Θ.angle - (Θ.angle - t))).2 at hg
      simpa only [sub_sub_cancel] using hg
  have hinf : (wedgeGapInfimum Q.val).1 = (wedgeGapInfimum K.val).2 := by
    change sInf ((fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle) =
      sInf ((fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle)
    exact congrArg sInf himage
  have hsurface' :
      surfaceAreaMeasure Q.val.val {((Real.pi / 2 : ℝ) : Real.Angle)} =
        surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)} := by
    have hs := hsurface {((Real.pi / 2 : ℝ) : Real.Angle)}
      (measurableSet_singleton _)
    rw [hPQ] at hs
    rw [Set.image_singleton] at hs
    have hang :
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) -
            ((Real.pi / 2 : ℝ) : Real.Angle) =
          (Θ.angle : Real.Angle) := by
      rw [← Real.Angle.coe_sub]
      congr 1
      ring
    simpa only [hang] using hs
  rw [hinf, hsurface'] at hQright
  exact hQright

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
# Bounds / Wedge Gap / Limit
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem wedgeGapInfimum_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).1 - (wedgeGapInfimum L).1| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).1
  let g := fun t : ℝ ↦ (wedgeGaps L t).1
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcost {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_lt hω⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos t := hcost ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le
        (by linarith [Real.pi_pos, hω]) ht.2.le
    dsimp only [f, g]
    rw [wedgeGaps_fst_eq_supportValue, wedgeGaps_fst_eq_supportValue]
    calc
      |(supportValue K.val (0 : Real.Angle) -
          (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) -
        (supportValue L.val (0 : Real.Angle) -
          (supportValue L.val (t : Real.Angle) - 1) / Real.cos t)| =
          |(supportValue K.val (0 : Real.Angle) -
              supportValue L.val (0 : Real.Angle)) -
            (supportValue K.val (t : Real.Angle) -
              supportValue L.val (t : Real.Angle)) / Real.cos t| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |(supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)) / Real.cos t| := abs_sub _ _
      _ = |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)| / Real.cos t := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos t := add_le_add (hsupport' 0)
        (div_le_div_of_nonneg_right (hsupport' t) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val (t : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hf_eq : f = fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue K t
    rw [hf_eq]
    convert continuousOn_const.sub hquot using 1
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val (t : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hg_eq : g = fun t : ℝ ↦ supportValue L.val (0 : Real.Angle) -
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue L t
    rw [hg_eq]
    convert continuousOn_const.sub hquot using 1
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

/-- The left wedge-gap infimum obeys the same Hausdorff estimate as the right one. -/
theorem wedgeGapInfimum_snd_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).2 - (wedgeGapInfimum L).2| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).2
  let g := fun t : ℝ ↦ (wedgeGaps L t).2
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcosδ {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos (ω - t) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.2], by linarith [Real.pi_pos, ht.1, hω]⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos (ω - t) := hcosδ ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos (ω - t) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2.le)
        (by linarith [Real.pi_pos, hω]) (by linarith [ht.1])
    dsimp only [f, g]
    rw [wedgeGaps_snd_eq_supportValue, wedgeGaps_snd_eq_supportValue]
    calc
      |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t)) -
        (supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t))| =
          |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)) -
            (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
                Real.cos (ω - t)| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |(supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
              Real.cos (ω - t)| := abs_sub _ _
      _ = |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)| /
              Real.cos (ω - t) := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos (ω - t) := add_le_add (hsupport' (ω + Real.pi / 2))
        (div_le_div_of_nonneg_right (hsupport' (t + Real.pi / 2)) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hf_eq : f = fun t : ℝ ↦
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue K t
    rw [hf_eq]
    exact continuousOn_const.sub hquot
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hg_eq : g = fun t : ℝ ↦
        supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue L t
    rw [hg_eq]
    exact continuousOn_const.sub hquot
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

theorem balancedMaximumCap_gap_le_surface {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤
      (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K).2 ≤
      (surfaceAreaMeasure K.val {(ω : Real.Angle)}).toReal := by
  obtain ⟨n, hn, _hmono, _hdyadic, P, hmax, hlim⟩ := hK
  let Θ (i : ℕ) := uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)
  have hpolygon (i : ℕ) := maximumPolygonCap_gap_le_surface (P i) (hmax i) hω
  have hfst : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).1) atTop
      (𝓝 (wedgeGapInfimum K).1) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_hausdorff_bound (P i).val K hω
  have hsnd : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).2) atTop
      (𝓝 (wedgeGapInfimum K).2) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_snd_hausdorff_bound (P i).val K hω
  constructor
  · exact le_surfaceAreaMeasure_atom_of_tendsto hlim hfst (fun i ↦ (hpolygon i).1)
  · apply le_surfaceAreaMeasure_atom_of_tendsto hlim hsnd
    intro i
    simpa only [Θ, uniformAngleSet] using (hpolygon i).2

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

* `Cap.BalancedExistence`.
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
# Cap / Balanced Existence
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

private def polygonSeedSet (Θ : AngleSet) : Set Point :=
  capFan Θ.angle ∩ ⋂ t ∈ angleDomain Θ,
    normalHalfPlane (t : Real.Angle) 1 false false

private theorem mem_polygonSeedSet_iff (Θ : AngleSet) (p : Point) :
    p ∈ polygonSeedSet Θ ↔
      p ∈ capFan Θ.angle ∧
        ∀ t ∈ angleDomain Θ, inner ℝ p (normalVector (t : Real.Angle)) ≤ 1 := by
  simp [polygonSeedSet, normalHalfPlane]

private theorem normalVector_mem_polygonSeedSet (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) : normalVector (t : Real.Angle) ∈ polygonSeedSet Θ := by
  apply (mem_polygonSeedSet_iff Θ _).mpr
  have htupper : t ∈ capUpperAngles Θ.angle := by
    rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have ht0 : 0 ≤ t := by
    rcases htupper with ⟨h0, _⟩ | ⟨hT, _⟩
    · exact h0
    · linarith [Real.pi_pos]
  have htpi : t ≤ Real.pi := by
    rcases htupper with ⟨_, hω⟩ | ⟨_, hω⟩
    · linarith [Θ.angle_le, Real.pi_pos]
    · linarith [Θ.angle_le]
  have htω : -(Real.pi / 2) ≤ t - Θ.angle ∧ t - Θ.angle ≤ Real.pi / 2 := by
    rcases htupper with ⟨h0, hω⟩ | ⟨hT, hω⟩ <;>
      constructor <;> linarith [Θ.angle_le]
  constructor
  · constructor
    · change 0 ≤ inner ℝ (normalVector (t : Real.Angle))
        (normalVector (Θ.angle : Real.Angle))
      rw [inner_normalVector_normalVector]
      exact Real.cos_nonneg_of_mem_Icc htω
    · change 0 ≤ inner ℝ (normalVector (t : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two,
        Real.sin_pi_div_two, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, zero_add]
      exact Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  · intro s hs
    calc
      inner ℝ (normalVector (t : Real.Angle)) (normalVector (s : Real.Angle)) ≤
          ‖normalVector (t : Real.Angle)‖ * ‖normalVector (s : Real.Angle)‖ :=
        real_inner_le_norm _ _
      _ = 1 := by rw [norm_normalVector_real, norm_normalVector_real, mul_one]

private theorem zero_mem_polygonSeedSet (Θ : AngleSet) :
    (0 : Point) ∈ polygonSeedSet Θ := by
  rw [mem_polygonSeedSet_iff]
  simp [capFan, normalHalfPlane]

private theorem convex_polygonSeedSet (Θ : AngleSet) : Convex ℝ (polygonSeedSet Θ) := by
  rw [polygonSeedSet]
  apply Convex.inter
  · apply Convex.inter
    · exact convex_halfSpace_ge
        ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 0
    · exact convex_halfSpace_ge
        ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 0
  · apply convex_iInter
    intro t
    apply convex_iInter
    intro _
    exact convex_halfSpace_le
      ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩ 1

private theorem isClosed_polygonSeedSet (Θ : AngleSet) : IsClosed (polygonSeedSet Θ) := by
  rw [polygonSeedSet]
  apply IsClosed.inter
  · apply IsClosed.inter <;> exact isClosed_le continuous_const (by fun_prop)
  · apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _
    exact isClosed_le (by fun_prop) continuous_const

private theorem isBounded_polygonSeedSet (Θ : AngleSet) :
    Bornology.IsBounded (polygonSeedSet Θ) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  let l := -1 / Real.sin t
  let r := 1 / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + 1, ?_⟩
  intro p hp
  obtain ⟨hfan, hupp⟩ := (mem_polygonSeedSet_iff Θ p).mp hp
  have htmem : t ∈ angleDomain Θ := Or.inl (Or.inl ht)
  have htmem' : t + Real.pi / 2 ∈ angleDomain Θ :=
    Or.inl (Or.inr ⟨t, ht, rfl⟩)
  have ha := hupp t htmem
  have hb := hupp (t + Real.pi / 2) htmem'
  have hy0 : 0 ≤ p 1 := by
    have := hfan.2
    simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  have hy1 : p 1 ≤ 1 := by
    have htop := hupp (Real.pi / 2) (Or.inr (Or.inr rfl))
    simpa [normalVector, frame, PiLp.inner_apply] using htop
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    dsimp [l]
    nlinarith [mul_nonneg hc.le hy0]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    dsimp [r]
    nlinarith [mul_nonneg hs.le hy0]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

private def polygonSeedBody (Θ : AngleSet) : ConvexBody Point where
  carrier := polygonSeedSet Θ
  convex' := convex_polygonSeedSet Θ
  isCompact' := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_polygonSeedSet Θ, isBounded_polygonSeedSet Θ⟩
  nonempty' := ⟨0, zero_mem_polygonSeedSet Θ⟩

private theorem supportValue_polygonSeedBody_upper (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    supportValue (polygonSeedBody Θ) (t : Real.Angle) = 1 := by
  apply le_antisymm
  · apply supportValue_le_of_subset_normalHalfPlane
    intro p hp
    exact ((mem_polygonSeedSet_iff Θ p).mp hp).2 t ht
  · have hmem := normalVector_mem_polygonSeedSet Θ ht
    have hle := inner_le_supportValue (polygonSeedBody Θ) hmem (t : Real.Angle)
    rwa [inner_normalVector_self] at hle

private theorem supportValue_polygonSeedBody_lower_angle (Θ : AngleSet) :
    supportValue (polygonSeedBody Θ) ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 0 := by
  apply le_antisymm
  · apply csSup_le ((polygonSeedBody Θ).nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hfan := ((mem_polygonSeedSet_iff Θ p).mp hp).1.1
    change 0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle)) at hfan
    change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0
    rw [normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan
  · apply le_csSup ((polygonSeedBody Θ).isCompact.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
    exact ⟨0, zero_mem_polygonSeedSet Θ, by simp⟩

private theorem supportValue_polygonSeedBody_lower_vertical (Θ : AngleSet) :
    supportValue (polygonSeedBody Θ) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  apply le_antisymm
  · apply csSup_le ((polygonSeedBody Θ).nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hfan := ((mem_polygonSeedSet_iff Θ p).mp hp).1.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hfan
    change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring,
      normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan
  · apply le_csSup ((polygonSeedBody Θ).isCompact.image
      (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
    exact ⟨0, zero_mem_polygonSeedSet Θ, by simp⟩

private theorem polygonSeedBody_representation (Θ : AngleSet) :
    HasHalfPlaneRepresentation (polygonSeedBody Θ)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪
        capLowerNormals Θ.angle) := by
  let C : Set (Real.Angle × ℝ) :=
    (fun t : ℝ ↦ ((t : Real.Angle), 1)) '' angleDomain Θ ∪
      {(((Θ.angle + Real.pi : ℝ) : Real.Angle), 0),
        (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)}
  refine ⟨C, ?_, ?_⟩
  · rintro c (⟨t, ht, rfl⟩ | hc)
    · exact Or.inl ⟨t, ht, rfl⟩
    · rcases hc with rfl | hc
      · exact Or.inr (Or.inl rfl)
      · have hc' : c = ((((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)) := hc
        subst c
        exact Or.inr (Or.inr rfl)
  · ext p
    change p ∈ polygonSeedSet Θ ↔ _
    rw [mem_polygonSeedSet_iff]
    simp only [C, Set.mem_iInter, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, normalHalfPlane, Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro ⟨hfan, hupp⟩ c (⟨t, ht, rfl⟩ | hc)
      · exact hupp t ht
      · rcases hc with rfl | rfl
        · change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0
          rw [normalVector_add_pi, inner_neg_right]
          exact neg_nonpos.mpr hfan.1
        · change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
          rw [inner_normalVector_three_pi_div_two]
          have hy : 0 ≤ p 1 := by
            simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hfan.2
          exact neg_nonpos.mpr hy
    · intro hp
      constructor
      · constructor
        · change 0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle))
          have h := hp (((Θ.angle + Real.pi : ℝ) : Real.Angle), 0)
            (Or.inr (Or.inl rfl))
          change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ 0 at h
          rw [normalVector_add_pi, inner_neg_right] at h
          exact neg_nonpos.mp h
        · have h := hp (((3 * Real.pi / 2 : ℝ) : Real.Angle), 0)
            (Or.inr (Or.inr rfl))
          change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 at h
          rw [inner_normalVector_three_pi_div_two] at h
          change p ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false
          simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using h
      · intro t ht
        exact hp ((t : Real.Angle), 1) (Or.inl ⟨t, ht, rfl⟩)

private def polygonSeedCap (Θ : AngleSet) : PolygonCapSpace Θ := by
  let K := polygonSeedBody Θ
  have hrepr := polygonSeedBody_representation Θ
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have hcaprepr : HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
        capLowerNormals Θ.angle) := by
    obtain ⟨C, hC, hKC⟩ := hrepr
    refine ⟨C, ?_, hKC⟩
    intro c hc
    rcases hC c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hcap : IsCap Θ.angle K := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hcaprepr⟩
    · exact supportValue_polygonSeedBody_upper Θ (Or.inr (Or.inl rfl))
    · exact supportValue_polygonSeedBody_upper Θ (Or.inr (Or.inr rfl))
    · exact supportValue_polygonSeedBody_lower_angle Θ
    · exact supportValue_polygonSeedBody_lower_vertical Θ
  exact ⟨⟨K, hcap⟩, hrepr⟩

private theorem supportValue_polygonSeedCap_upper (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    supportValue (polygonSeedCap Θ).val.val (t : Real.Angle) = 1 := by
  change supportValue (polygonSeedBody Θ) (t : Real.Angle) = 1
  exact supportValue_polygonSeedBody_upper Θ ht

private theorem polygonNiche_polygonSeedCap (Θ : AngleSet) :
    polygonNiche Θ (polygonSeedCap Θ).val = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hfan, hq⟩ := hp
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  have hy : 0 ≤ p 1 := by
    have := hfan.2
    simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  have h₁ := hq.1
  have h₂ := hq.2
  change inner ℝ p (normalVector (t : Real.Angle)) <
    supportValue (polygonSeedCap Θ).val.val (t : Real.Angle) - 1 at h₁
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue (polygonSeedCap Θ).val.val
      ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h₂
  rw [supportValue_polygonSeedCap_upper Θ (Or.inl (Or.inl ht))] at h₁
  rw [supportValue_polygonSeedCap_upper Θ (Or.inl (Or.inr ⟨t, ht, rfl⟩))] at h₂
  simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_self,
    Real.cos_add, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two, mul_one,
    zero_sub, Real.sin_add, zero_add, neg_mul, neg_add_lt_iff_lt_add, add_zero] at h₁ h₂
  have h₁' := mul_lt_mul_of_pos_left h₁ hs
  have h₂' := mul_lt_mul_of_pos_left h₂ hc
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem polygonSeedCap_area_nonneg (Θ : AngleSet) :
    0 ≤ polygonAreaFunctional Θ (polygonSeedCap Θ).val := by
  rw [(polygonArea_upperBound Θ).1, polygonNiche_polygonSeedCap]
  simp [ClassicalResults.area]

private theorem angleDomain_distance_midpoint (Θ : AngleSet) {t : ℝ}
    (ht : t ∈ angleDomain Θ) :
    Real.pi / 4 - Θ.angle / 2 ≤
        |t - (Real.pi / 4 + Θ.angle / 2)| ∧
      |t - (Real.pi / 4 + Θ.angle / 2)| ≤ Real.pi / 2 := by
  have htupper : t ∈ capUpperAngles Θ.angle := by
    rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  rcases htupper with ⟨ht0, htω⟩ | ⟨htT, htωT⟩
  · rw [abs_of_nonpos (by linarith [Θ.angle_le])]
    constructor <;> linarith [Θ.angle_le, Real.pi_pos]
  · rw [abs_of_nonneg (by linarith [Θ.angle_le])]
    constructor <;> linarith [Θ.angle_le]

private theorem stripParallelogram_top_mem_polygonSeedCap (Θ : AngleSet) :
    (stripParallelogram Θ.angle).2.2 ∈ ((polygonSeedCap Θ).val.val : Set Point) := by
  change (stripParallelogram Θ.angle).2.2 ∈ polygonSeedSet Θ
  apply (mem_polygonSeedSet_iff Θ _).mpr
  let β := Real.pi / 4 - Θ.angle / 2
  let m := Real.pi / 4 + Θ.angle / 2
  have hβ0 : 0 ≤ β := by dsimp [β]; linarith [Θ.angle_le]
  have hβlt : β < Real.pi / 2 := by
    dsimp [β]
    linarith [Θ.angle_pos, Real.pi_pos]
  have hcosβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hβlt⟩
  have htanβ : 0 ≤ Real.tan β :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hβ0 hβlt.le
  have hcosω : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
  have hsinω : 0 ≤ Real.sin Θ.angle := Real.sin_nonneg_of_nonneg_of_le_pi
    Θ.angle_pos.le (by linarith [Θ.angle_le])
  constructor
  · constructor
    · change 0 ≤ inner ℝ (!₂[Real.tan β, 1] : Point)
        (normalVector (Θ.angle : Real.Angle))
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
      positivity
    · change 0 ≤ inner ℝ (!₂[Real.tan β, 1] : Point)
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
  · intro t ht
    have hd := angleDomain_distance_midpoint Θ ht
    have hdpi : |t - m| ≤ Real.pi := by dsimp [m]; linarith [hd.2, Real.pi_pos]
    have hcosabs : Real.cos |t - m| ≤ Real.cos β :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ0 hdpi (by simpa [β, m] using hd.1)
    have hcos : Real.cos (t - m) ≤ Real.cos β := by
      simpa only [Real.cos_abs] using hcosabs
    change inner ℝ (!₂[Real.tan β, 1] : Point) (normalVector (t : Real.Angle)) ≤ 1
    simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.inner_apply]
    have htrig : Real.sin β * Real.cos t + Real.cos β * Real.sin t =
        Real.cos (t - m) := by
      calc
        Real.sin β * Real.cos t + Real.cos β * Real.sin t =
            Real.sin (β + t) := by rw [Real.sin_add]
        _ = Real.cos (Real.pi / 2 - (β + t)) := by rw [Real.cos_pi_div_two_sub]
        _ = Real.cos (m - t) := by congr 1; dsimp [β, m]; ring
        _ = Real.cos (t - m) := by rw [← Real.cos_neg]; congr 1; ring
    apply le_of_mul_le_mul_left ?_ hcosβ
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcosβ.ne']
    change Real.sin β * Real.cos t + Real.cos β * Real.sin t ≤ Real.cos β
    rw [htrig]
    exact hcos

private def IsPolygonMaximizationCandidate (Θ : AngleSet) (K : PolygonCapSpace Θ) : Prop :=
  (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) ∧
    0 ≤ polygonAreaFunctional Θ K.val

private theorem exists_compact_polygonCap_bound (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) :
    ∃ A : Set Point, IsCompact A ∧ ∀ (Θ : AngleSet), Θ.angle = ω →
      t ∈ Θ.directions → ∀ K : PolygonCapSpace Θ,
        IsPolygonMaximizationCandidate Θ K → (K.val.val : Set Point) ⊆ A := by
  obtain ⟨c, hc, hwidth⟩ := polygonCap_width_bound ω t hω hω' ht
  let o := (stripParallelogram ω).2.2
  let R := c + |o 0| + 2
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  intro Θ hΘ hdir K hK p hp
  subst ω
  have hw := hwidth Θ rfl hdir K hK.2
  have hp0 := inner_le_supportValue K.val.val hp (0 : Real.Angle)
  have hpπ := inner_le_supportValue K.val.val hp (Real.pi : Real.Angle)
  have ho0 := inner_le_supportValue K.val.val hK.1 (0 : Real.Angle)
  have hoπ := inner_le_supportValue K.val.val hK.1 (Real.pi : Real.Angle)
  simp [directionalWidth, supportValue, normalVector, frame, PiLp.inner_apply]
    at hw hp0 hpπ ho0 hoπ
  have hpx : |p 0| ≤ c + |o 0| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (o 0)]
    · linarith [le_abs_self (o 0)]
  have hpy := K.val.mem_horizontalStrip hp
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  rw [Metric.mem_closedBall]
  have hpx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity : 0 ≤ c + |o 0|)).mpr hpx
  have hpy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hpy.1, hpy.2]
  have ha0 : 0 ≤ c + |o 0| := by positivity
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hpx2
  have hsquare : ‖p‖ ^ 2 ≤ R ^ 2 := by
    dsimp [R]
    nlinarith
  simpa [dist_eq_norm] using
    ((sq_le_sq₀ (norm_nonneg p) hR0).mp hsquare)

private theorem exists_compact_polygonCandidate_bound (Θ : AngleSet) :
    ∃ A : Set Point, IsCompact A ∧ ∀ K : PolygonCapSpace Θ,
      IsPolygonMaximizationCandidate Θ K → (K.val.val : Set Point) ⊆ A := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCap_bound Θ.angle
    Θ.angle_pos Θ.angle_le t (Θ.interior t ht)
  exact ⟨A, hA, fun K hK ↦ hbound Θ rfl ht K hK⟩

private theorem tendsto_supportValue_of_hausdorffBodies
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ supportValue (K i) (t : Real.Angle)) atTop
      (𝓝 (supportValue L (t : Real.Angle))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro i
  simpa only [Real.dist_eq, vectorSupport, supportValue] using
    (compactSet_support_continuity (K i) L (K i).nonempty
      (K i).isCompact L.nonempty L.isCompact).2.1
        (normalVector (t : Real.Angle)) (norm_normalVector_real t)

private theorem polygonCandidate_values_bddAbove (Θ : AngleSet) :
    BddAbove {r : ℝ | ∃ K : PolygonCapSpace Θ,
      IsPolygonMaximizationCandidate Θ K ∧ polygonAreaFunctional Θ K.val = r} := by
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCandidate_bound Θ
  refine ⟨ClassicalResults.area A, ?_⟩
  rintro r ⟨K, hK, rfl⟩
  rw [(polygonArea_upperBound Θ).1 K]
  calc
    ClassicalResults.area (K.val.val : Set Point) -
        ClassicalResults.area (polygonNiche Θ K.val) ≤
        ClassicalResults.area (K.val.val : Set Point) := by
      linarith [show 0 ≤ ClassicalResults.area (polygonNiche Θ K.val) from
        ENNReal.toReal_nonneg]
    _ ≤ ClassicalResults.area A := by
      exact ENNReal.toReal_mono hA.measure_ne_top (MeasureTheory.measure_mono (hbound K hK))

private theorem supportValue_limit_eq {K : ℕ → ConvexBody Point} {L : ConvexBody Point}
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (t c : ℝ)
    (hvalue : ∀ i, supportValue (K i) (t : Real.Angle) = c) :
    supportValue L (t : Real.Angle) = c := by
  apply tendsto_nhds_unique (tendsto_supportValue_of_hausdorffBodies K L hlim t)
  simpa only [hvalue] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))

private theorem mem_hausdorffLimit {K : ℕ → ConvexBody Point} {L : ConvexBody Point}
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i : Set Point)
    (L : Set Point)) atTop (𝓝 0)) {p : Point} (hp : ∀ i, p ∈ (K i : Set Point)) :
    p ∈ (L : Set Point) := by
  have hle : (fun _ : ℕ ↦ Metric.infDist p (L : Set Point)) ≤ᶠ[atTop]
      (fun i ↦ Metric.hausdorffDist (K i : Set Point) (L : Set Point)) := by
    filter_upwards [] with i
    exact Metric.infDist_le_hausdorffDist_of_mem (hp i)
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K i).nonempty L.nonempty (K i).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist p (L : Set Point) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (L.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)

private theorem exists_polygonCap_of_hausdorffLimit (Θ : AngleSet)
    (K : ℕ → PolygonCapSpace Θ) (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist (K i).val.val (L : Set Point))
      atTop (𝓝 0)) :
    ∃ P : PolygonCapSpace Θ, (P.val.val : Set Point) = (L : Set Point) := by
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  let U : Set Point := normalVector '' N
  have hU : ∀ u ∈ U, ‖u‖ = 1 := by
    rintro u ⟨a, ha, rfl⟩
    rcases ha with ⟨t, _, rfl⟩ | ha
    · exact norm_normalVector_real t
    · rcases ha with rfl | rfl
      · exact norm_normalVector_real (Θ.angle + Real.pi)
      · exact norm_normalVector_real (3 * Real.pi / 2)
  have hK (i : ℕ) : ((K i).val.val : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K i).val.val u} := by
    calc
      ((K i).val.val : Set Point) = ⋂ a ∈ N,
          normalHalfPlane a (supportValue (K i).val.val a) false false :=
        (K i).property.eq_iInter_supportValue
      _ = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K i).val.val u} := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]
  have hclosed := fixedNormalBody_closed U hU (fun i ↦ (K i).val.val) L hK hlim
  have hrepr : HasHalfPlaneRepresentation L N := by
    refine ⟨(fun t ↦ (t, supportValue L t)) '' N, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · calc
        (L : Set Point) = ⋂ u ∈ U,
            {x | inner ℝ x u ≤ vectorSupport L u} := hclosed
        _ = ⋂ t ∈ N, normalHalfPlane t (supportValue L t) false false := by
          ext p
          simp [U, normalHalfPlane, supportValue, vectorSupport]
        _ = ⋂ c ∈ (fun t ↦ (t, supportValue L t)) '' N,
            normalHalfPlane c.1 c.2 false false := by
          ext p
          simp
  have hω := supportValue_limit_eq hlim Θ.angle 1
    (fun i ↦ (K i).val.property.2.2.1)
  have hT := supportValue_limit_eq hlim (Real.pi / 2) 1
    (fun i ↦ (K i).val.property.2.2.2.1)
  have hωπ := supportValue_limit_eq hlim (Θ.angle + Real.pi) 0
    (fun i ↦ (K i).val.property.2.2.2.2.1)
  have h3T := supportValue_limit_eq hlim (3 * Real.pi / 2) 0
    (fun i ↦ (K i).val.property.2.2.2.2.2.1)
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
        by dsimp; linarith [(Θ.interior s hs).2]⟩
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
  have hcaprepr : HasHalfPlaneRepresentation L
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
        capLowerNormals Θ.angle) := by
    obtain ⟨C, hCN, hLC⟩ := hrepr
    refine ⟨C, ?_, hLC⟩
    intro c hc
    rcases hCN c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hcap : IsCap Θ.angle L :=
    ⟨Θ.angle_pos, Θ.angle_le, hω, hT, hωπ, h3T, hcaprepr⟩
  exact ⟨⟨⟨L, hcap⟩, hrepr⟩, rfl⟩

private theorem exists_maximum_polygonCandidate (Θ : AngleSet) :
    ∃ K : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ K ∧
      ∀ L : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ L →
        polygonAreaFunctional Θ L.val ≤ polygonAreaFunctional Θ K.val := by
  let S : Set ℝ := {r | ∃ K : PolygonCapSpace Θ,
    IsPolygonMaximizationCandidate Θ K ∧ polygonAreaFunctional Θ K.val = r}
  have hS : S.Nonempty := by
    refine ⟨polygonAreaFunctional Θ (polygonSeedCap Θ).val, polygonSeedCap Θ, ?_, rfl⟩
    exact ⟨stripParallelogram_top_mem_polygonSeedCap Θ, polygonSeedCap_area_nonneg Θ⟩
  have hSbdd : BddAbove S := polygonCandidate_values_bddAbove Θ
  obtain ⟨u, _, hu, huS⟩ := exists_seq_tendsto_sSup hS hSbdd
  choose K hK hKu using huS
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCandidate_bound Θ
  obtain ⟨φ, L, hφ, hlim⟩ := convexBody_selection A hA (fun i ↦ (K i).val.val)
    (fun i ↦ hbound (K i) (hK i))
  obtain ⟨P, hPL⟩ := exists_polygonCap_of_hausdorffLimit Θ (fun i ↦ K (φ i)) L hlim
  have hlimP : Tendsto (fun i ↦ Metric.hausdorffDist ((K (φ i)).val.val : Set Point)
      (P.val.val : Set Point)) atTop (𝓝 0) := by
    simpa only [hPL] using hlim
  have hcont := (polygonArea_continuity Θ (fun i ↦ (K (φ i)).val) P.val hlimP).2
  have huφ : Tendsto (fun i ↦ u (φ i)) atTop (𝓝 (sSup S)) :=
    hu.comp hφ.tendsto_atTop
  have hfuncSup : polygonAreaFunctional Θ P.val = sSup S := by
    apply tendsto_nhds_unique hcont
    simpa only [hKu] using huφ
  have hPtop : (stripParallelogram Θ.angle).2.2 ∈ (P.val.val : Set Point) := by
    rw [hPL]
    exact mem_hausdorffLimit hlim (fun i ↦ (hK (φ i)).1)
  have hPnonneg : 0 ≤ polygonAreaFunctional Θ P.val := by
    apply ge_of_tendsto hcont
    exact Eventually.of_forall fun i ↦ (hK (φ i)).2
  refine ⟨P, ⟨hPtop, hPnonneg⟩, ?_⟩
  intro Q hQ
  rw [hfuncSup]
  exact le_csSup hSbdd ⟨Q, hQ, rfl⟩

private theorem innerQuadrant_translate (K : ConvexBody Point) (v : Point) (t : ℝ) :
    innerQuadrant (ConvexBody.translate K v : Set Point) t =
      (fun p ↦ p + v) '' innerQuadrant (K : Set Point) t := by
  have hsupp (a : Real.Angle) : supportValue (ConvexBody.translate K v) a =
      supportValue K a + inner ℝ v (normalVector a) := supportValue_image_add K v a
  ext q
  simp only [innerQuadrant, normalHalfPlane, Set.mem_inter_iff, Bool.false_eq_true,
    ↓reduceIte, Set.mem_image]
  rw [hsupp, hsupp]
  constructor
  · intro h
    change inner ℝ q (normalVector (t : Real.Angle)) <
        supportValue K (t : Real.Angle) + inner ℝ v (normalVector (t : Real.Angle)) - 1 ∧
      inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) +
          inner ℝ v (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) - 1 at h
    refine ⟨q - v, ?_, by simp⟩
    constructor
    · change inner ℝ (q - v) (normalVector (t : Real.Angle)) < _
      rw [inner_sub_left]
      linarith [h.1]
    · change inner ℝ (q - v) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [inner_sub_left]
      linarith [h.2]
  · rintro ⟨p, hp, rfl⟩
    change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hp
    constructor
    · change inner ℝ (p + v) (normalVector (t : Real.Angle)) < _
      rw [inner_add_left]
      linarith [hp.1]
    · change inner ℝ (p + v) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
      rw [inner_add_left]
      linarith [hp.2]

private theorem exists_candidate_translate_rightAngle (Θ : AngleSet)
    (hΘ : Θ.angle = Real.pi / 2) (K : PolygonCapSpace Θ)
    (hK : 0 ≤ polygonAreaFunctional Θ K.val) :
    ∃ P : PolygonCapSpace Θ, IsPolygonMaximizationCandidate Θ P ∧
      polygonAreaFunctional Θ P.val = polygonAreaFunctional Θ K.val := by
  obtain ⟨p, hp, hpeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image
        (fun q ↦ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hp1 : p 1 = 1 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) at hpeq
    rw [K.val.property.2.2.2.1] at hpeq
    simpa [normalVector, frame, PiLp.inner_apply] using hpeq
  let v : Point := !₂[-p 0, 0]
  let L := ConvexBody.translate K.val.val v
  have hv (a : Real.Angle) (ha : a = ((Real.pi / 2 : ℝ) : Real.Angle) ∨
      a = ((3 * Real.pi / 2 : ℝ) : Real.Angle)) :
      inner ℝ v (normalVector a) = 0 := by
    rcases ha with rfl | rfl <;>
      simp [v, normalVector, frame, PiLp.inner_apply,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.cos_add, Real.sin_add, -Real.Angle.coe_add]
  have hsupp (a : Real.Angle) : supportValue L a = supportValue K.val.val a +
      inner ℝ v (normalVector a) := supportValue_image_add K.val.val v a
  have hrepr := K.property.translate v
  have hcaprepr := K.val.property.2.2.2.2.2.2.translate v
  have htopω : supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    simpa only [hΘ] using K.val.property.2.2.1
  have hbotω : supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have ha : (((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by rw [hΘ]; congr 1; ring
    simpa only [ha] using K.val.property.2.2.2.2.1
  have hcap : IsCap Θ.angle L := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hcaprepr⟩
    · rw [hΘ, hsupp, htopω, hv _ (Or.inl rfl), add_zero]
    · rw [hsupp, K.val.property.2.2.2.1, hv _ (Or.inl rfl), add_zero]
    · have ha : (((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by rw [hΘ]; congr 1; ring
      rw [ha, hsupp, hbotω, hv _ (Or.inr rfl), add_zero]
    · rw [hsupp, K.val.property.2.2.2.2.2.1, hv _ (Or.inr rfl), add_zero]
  let P : PolygonCapSpace Θ := ⟨⟨L, hcap⟩, hrepr⟩
  have htop : (stripParallelogram Θ.angle).2.2 ∈ (P.val.val : Set Point) := by
    refine ⟨p, hp, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, PiLp.add_apply, Matrix.cons_val_zero, add_neg_cancel,
      stripParallelogram, hΘ, v]
      rw [show Real.pi / 4 - Real.pi / 2 / 2 = 0 by ring, Real.tan_zero]
    · simp [v, hΘ, stripParallelogram, hp1]
  have hfan : capFan Θ.angle = (fun q ↦ q + v) '' capFan Θ.angle := by
    ext q
    rw [hΘ]
    simp only [capFan, normalHalfPlane, Set.mem_inter_iff, Bool.false_eq_true,
      ↓reduceIte, Set.mem_image]
    constructor
    · intro hq
      refine ⟨q - v, ?_, by simp⟩
      simpa [v, normalVector, frame, PiLp.inner_apply, inner_sub_left] using hq
    · rintro ⟨r, hr, rfl⟩
      simpa [v, normalVector, frame, PiLp.inner_apply, inner_add_left] using hr
  have hniche : polygonNiche Θ P.val =
      (fun q ↦ q + v) '' polygonNiche Θ K.val := by
    have hquad (t : ℝ) : innerQuadrant (P.val.val : Set Point) t =
        (fun q ↦ q + v) '' innerQuadrant (K.val.val : Set Point) t :=
      innerQuadrant_translate K.val.val v t
    have hunion : (⋃ t ∈ Θ.directions, innerQuadrant (P.val.val : Set Point) t) =
        (fun q ↦ q + v) '' ⋃ t ∈ Θ.directions,
          innerQuadrant (K.val.val : Set Point) t := by
      rw [Set.image_iUnion]
      congr 1
      funext t
      rw [Set.image_iUnion]
      congr 1
      funext ht
      exact hquad t
    unfold polygonNiche
    calc
      capFan Θ.angle ∩ ⋃ t ∈ Θ.directions, innerQuadrant (P.val.val : Set Point) t =
          (fun q ↦ q + v) '' capFan Θ.angle ∩
            (fun q ↦ q + v) '' ⋃ t ∈ Θ.directions,
              innerQuadrant (K.val.val : Set Point) t :=
        congrArg₂ (· ∩ ·) hfan hunion
      _ = (fun q ↦ q + v) '' (capFan Θ.angle ∩ ⋃ t ∈ Θ.directions,
          innerQuadrant (K.val.val : Set Point) t) :=
        (Set.image_inter (Equiv.addRight v).injective).symm
  have harea : polygonAreaFunctional Θ P.val = polygonAreaFunctional Θ K.val := by
    rw [(polygonArea_upperBound Θ).1 P, (polygonArea_upperBound Θ).1 K]
    change ClassicalResults.area ((fun q ↦ q + v) '' (K.val.val : Set Point)) -
        ClassicalResults.area (polygonNiche Θ P.val) = _
    rw [ClassicalResults.area_image_add, hniche, ClassicalResults.area_image_add]
  exact ⟨P, ⟨htop, harea.symm ▸ hK⟩, harea⟩

theorem exists_maximumPolygonCap (Θ : AngleSet) :
    ∃ K : PolygonCapSpace Θ, IsMaximumPolygonCap Θ K ∧ 0 ≤ polygonAreaFunctional Θ K.val := by
  obtain ⟨K, hK, hmax⟩ := exists_maximum_polygonCandidate Θ
  refine ⟨K, ⟨hK.1, ?_⟩, hK.2⟩
  intro L
  by_cases hL : 0 ≤ polygonAreaFunctional Θ L.val
  · rcases lt_or_eq_of_le Θ.angle_le with hΘ | hΘ
    · exact hmax L ⟨stripParallelogram_top_mem_of_angle_lt Θ hΘ L, hL⟩
    · obtain ⟨P, hP, heq⟩ := exists_candidate_translate_rightAngle Θ hΘ L hL
      rw [← heq]
      exact hmax P hP
  · exact (le_of_not_ge hL).trans hK.2

theorem maximumPolygonCap_niche_subset {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) : polygonNiche Θ K.val ⊆ (K.val.val : Set Point) := by
  exact polygonNiche_subset_of_balanced K (maximumPolygonCap_balanced K hK)

private theorem isCap_of_hausdorffLimit {ω : ℝ} (K : ℕ → CapSpace ω)
    (L : ConvexBody Point)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L : Set Point)) atTop (𝓝 0)) : IsCap ω L := by
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω
  let U : Set Point := normalVector '' N
  have hU : ∀ u ∈ U, ‖u‖ = 1 := by
    rintro u ⟨a, _, rfl⟩
    induction a using Real.Angle.induction_on with
    | _ a => exact norm_normalVector_real a
  have hrepr (i : ℕ) : ((K i).val : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K i).val u} := by
    calc
      ((K i).val : Set Point) = ⋂ a ∈ N,
          normalHalfPlane a (supportValue (K i).val a) false false :=
        (K i).property.2.2.2.2.2.2.eq_iInter_supportValue
      _ = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K i).val u} := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]
  have hclosed := fixedNormalBody_closed U hU (fun i ↦ (K i).val) L hrepr hlim
  refine ⟨(K 0).property.1, (K 0).property.2.1,
    supportValue_limit_eq hlim ω 1 (fun i ↦ (K i).property.2.2.1),
    supportValue_limit_eq hlim (Real.pi / 2) 1 (fun i ↦ (K i).property.2.2.2.1),
    supportValue_limit_eq hlim (ω + Real.pi) 0 (fun i ↦ (K i).property.2.2.2.2.1),
    supportValue_limit_eq hlim (3 * Real.pi / 2) 0
      (fun i ↦ (K i).property.2.2.2.2.2.1), ?_⟩
  refine ⟨(fun t ↦ (t, supportValue L t)) '' N, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · calc
      (L : Set Point) = ⋂ u ∈ U,
          {x | inner ℝ x u ≤ vectorSupport L u} := hclosed
      _ = ⋂ c ∈ (fun t ↦ (t, supportValue L t)) '' N,
          normalHalfPlane c.1 c.2 false false := by
        ext p
        simp [U, normalHalfPlane, supportValue, vectorSupport]

theorem exists_balancedMaximumCap (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2) :
    ∃ K : CapSpace ω, IsBalancedMaximumCap K := by
  let n : ℕ → ℕ := fun i ↦ 2 ^ (i + 1)
  have hn (i : ℕ) : 2 ≤ n i := by
    dsimp [n]
    have h : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    rw [pow_succ]
    omega
  let Θ (i : ℕ) := uniformAngleSet ω hω hω' (n i) (hn i)
  have hmid (i : ℕ) : ω / 2 ∈ (Θ i).directions := by
    apply Finset.mem_image.mpr
    refine ⟨2 ^ i, Finset.mem_Ioo.mpr ⟨by positivity, ?_⟩, ?_⟩
    · change 2 ^ i < 2 ^ (i + 1)
      exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self i)
    · simp only [n, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      push_cast
      ring
  choose Q hQmax hQnonneg using fun i ↦ exists_maximumPolygonCap (Θ i)
  obtain ⟨A, hA, hbound⟩ := exists_compact_polygonCap_bound ω hω hω' (ω / 2)
    ⟨by linarith, by linarith⟩
  obtain ⟨φ, L, hφ, hlim⟩ := convexBody_selection A hA (fun i ↦ (Q i).val.val)
    (fun i ↦ hbound (Θ i) rfl (hmid i) (Q i) ⟨(hQmax i).1, hQnonneg i⟩)
  let K : CapSpace ω := ⟨L, isCap_of_hausdorffLimit (fun i ↦ (Q (φ i)).val) L hlim⟩
  refine ⟨K, (fun i ↦ n (φ i)), (fun i ↦ hn (φ i)), ?_, ?_, ?_⟩
  · intro i j hij
    apply pow_lt_pow_right₀ (by norm_num)
    exact Nat.add_lt_add_right (hφ hij) 1
  · exact fun i ↦ ⟨φ i + 1, rfl⟩
  · exact ⟨(fun i ↦ Q (φ i)), (fun i ↦ hQmax (φ i)), hlim⟩

theorem balancedMaximumCap_niche_subset {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) : capNiche K ⊆ (K.val : Set Point) := by
  obtain ⟨n, hn, hmono, hdyadic, P, hmax, hlim⟩ := hK
  exact capNiche_subset_of_uniform_polygonNiche_subset K n hn hmono hdyadic P
    (fun i ↦ maximumPolygonCap_niche_subset (P i) (hmax i)) hlim

theorem balancedMaximumCap_maximizes_area {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) :
    ∀ L : CapSpace ω, capAreaFunctional L ≤ capAreaFunctional K := by
  obtain ⟨n, hn, hmono, hdyadic, P, hmax, hlim⟩ := hK
  let Θ (i : ℕ) := uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)
  have harealim := convexArea_hausdorff_continuity (fun i ↦ (P i).val.val) K.val hlim
  have hniche := maximizingPolygon_nicheArea_limit ω K.property.1 K.property.2.1
    n hn hmono hdyadic P hmax K hlim
  have hfunc : Tendsto (fun i ↦ polygonAreaFunctional (Θ i) (P i).val) atTop
      (𝓝 (capAreaFunctional K)) := by
    have hsub := harealim.sub hniche
    convert hsub using 1
    · funext i
      exact (polygonArea_upperBound (Θ i)).1 (P i)
    · rfl
  intro L
  apply ge_of_tendsto hfunc
  filter_upwards [] with i
  exact ((polygonArea_upperBound (Θ i)).2 L).trans
    (polygonAreaFunctional_le_maximum (Θ i) (P i) (hmax i) L)

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

* `Polygon.BalancedInequalities`.
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
# Polygon / Balanced Inequalities
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A real angle strictly inside one full turn is not the zero angle. -/
private theorem coe_ne_zero_of_pos_of_lt_two_pi {x : ℝ} (h0 : 0 < x)
    (h2 : x < 2 * Real.pi) : ((x : ℝ) : Real.Angle) ≠ (0 : Real.Angle) := by
  rw [← Real.Angle.coe_zero]
  refine Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith) ?_
  rw [abs_lt]
  constructor <;> linarith [Real.pi_pos]

/-- Adding half a turn keeps a small positive angle away from zero. -/
private theorem coe_add_pi_ne_zero_of_pos_of_lt_pi {x : ℝ} (h0 : 0 < x)
    (h1 : x < Real.pi) :
    ((x : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) ≠ (0 : Real.Angle) := by
  rw [← Real.Angle.coe_add]
  exact coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)

/-- A right-angle polygon cap has no face with horizontal outward normal. -/
private theorem rightAngle_edgeVertices_zero_eq (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    (edgeVertices K.val.val (0 : Real.Angle)).1 =
      (edgeVertices K.val.val (0 : Real.Angle)).2 := by
  by_contra hne
  have hpi := Real.pi_pos
  have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
  have hlow : ∀ u ∈ capLowerNormals (rightAngleSet n hn).angle,
      u = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    intro u hu
    simp only [capLowerNormals, hangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · congr 1
      ring
    · rfl
  have h3zero : ((3 * Real.pi / 2 : ℝ) : Real.Angle) ≠ (0 : Real.Angle) :=
    coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)
  have h3pi : ((3 * Real.pi / 2 : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) ≠
      (0 : Real.Angle) := by
    have hshift : ((3 * Real.pi / 2 : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨1, by push_cast; ring⟩
    rw [hshift]
    exact coe_ne_zero_of_pos_of_lt_two_pi (by linarith) (by linarith)
  have hmain := K.properEdgeNormal_mem_allowed_or_antipodal (0 : Real.Angle) hne
  rcases hmain with (⟨r, hr, hr0⟩ | hlowmem) | ⟨u, huN, hu0⟩
  · exact coe_ne_zero_of_pos_of_lt_two_pi
      (angleDomain_subset_Ioo _ hr).1
      (by linarith [(angleDomain_subset_Ioo _ hr).2]) hr0
  · exact h3zero (hlow _ hlowmem).symm
  · rcases huN with ⟨r, hr, rfl⟩ | hlowmem
    · exact coe_add_pi_ne_zero_of_pos_of_lt_pi
        (angleDomain_subset_Ioo _ hr).1 (angleDomain_subset_Ioo _ hr).2 hu0
    · rw [hlow _ hlowmem] at hu0
      exact h3pi hu0

/-- The surface measure of a right-angle polygon cap has no horizontal-normal atom. -/
private theorem rightAngle_surfaceAreaMeasure_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val {((0 : ℝ) : Real.Angle)} = 0 := by
  rw [Real.Angle.coe_zero, (surfaceAreaMeasure_atom_length K.val.val (0 : Real.Angle)).2.1,
    rightAngle_edgeVertices_zero_eq n hn K]
  simp

/-- The real-arithmetic core of the discrete balancing inequality. -/
private theorem magicBound_of_le {δ T c s gp gm : ℝ} (hδpos : 0 < δ) (hδ45 : δ ≤ 4 / 5)
    (hTub : T ≤ δ + 4 / 3 * δ ^ 3) (hTpos : 0 < T)
    (hcub : c ≤ δ / 2 + 4 / 3 * (δ / 2) ^ 3) (hcpos : 0 < c)
    (hgp5 : gp ≤ 5) (hgm0 : 0 ≤ gm) (hgle : gm ≤ gp)
    (hsum : s ≤ T * max 0 (gm - 1 + c) + T * max 0 (1 - gp + c) + max 0 (2 * c - s)) :
    s ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ + 8 * δ ^ 2 := by
  have hW0 : 0 ≤ max 0 (gm - 1) + max 0 (1 - gp) := by positivity
  have hMsum : max 0 (gm - 1) + max 0 (1 - gp) ≤ |gp - 1| := by
    rcases le_total gp 1 with hg | hg
    · rw [abs_of_nonpos (by linarith), max_eq_left (show gm - 1 ≤ 0 by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 - gp by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith), max_eq_left (show (1 : ℝ) - gp ≤ 0 by linarith)]
      rcases le_total gm 1 with h2 | h2
      · rw [max_eq_left (show gm - 1 ≤ 0 by linarith)]
        linarith
      · rw [max_eq_right (show (0 : ℝ) ≤ gm - 1 by linarith)]
        linarith
  have hMsum4 : max 0 (gm - 1) + max 0 (1 - gp) ≤ 4 := by
    rcases le_total gm 1 with h2 | h2
    · rw [max_eq_left (show gm - 1 ≤ 0 by linarith)]
      have h3 : max 0 (1 - gp) ≤ 1 := max_le (by norm_num) (by linarith)
      linarith
    · rw [max_eq_left (show (1 : ℝ) - gp ≤ 0 by linarith),
        max_eq_right (show (0 : ℝ) ≤ gm - 1 by linarith)]
      linarith
  have hstep1 : max 0 (gm - 1 + c) ≤ max 0 (gm - 1) + c := by
    rcases le_total (gm - 1 + c) 0 with h | h
    · rw [max_eq_left h]
      linarith [le_max_left (0 : ℝ) (gm - 1)]
    · rw [max_eq_right h]
      linarith [le_max_right (0 : ℝ) (gm - 1)]
  have hstep2 : max 0 (1 - gp + c) ≤ max 0 (1 - gp) + c := by
    rcases le_total (1 - gp + c) 0 with h | h
    · rw [max_eq_left h]
      linarith [le_max_left (0 : ℝ) (1 - gp)]
    · rw [max_eq_right h]
      linarith [le_max_right (0 : ℝ) (1 - gp)]
  have e1 : T * max 0 (gm - 1 + c) ≤ T * (max 0 (gm - 1) + c) :=
    mul_le_mul_of_nonneg_left hstep1 hTpos.le
  have e2 : T * max 0 (1 - gp + c) ≤ T * (max 0 (1 - gp) + c) :=
    mul_le_mul_of_nonneg_left hstep2 hTpos.le
  have hcombine : s ≤ T * (max 0 (gm - 1) + max 0 (1 - gp)) + 2 * (T * c) +
      max 0 (2 * c - s) := by nlinarith only [e1, e2, hsum]
  have p3 : δ ^ 3 ≤ 4 / 5 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ45)]
  have hδsq : δ ^ 2 ≤ 16 / 25 := by nlinarith only [hδpos, hδ45]
  have p4 : δ ^ 4 ≤ 16 / 25 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδsq)]
  have p6 : δ ^ 6 ≤ 1 / 2 * δ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg δ)
      (show (0 : ℝ) ≤ 1 / 2 - δ ^ 4 by nlinarith only [p4, hδsq])]
  have f1 : T * (max 0 (gm - 1) + max 0 (1 - gp)) ≤
      (δ + 4 / 3 * δ ^ 3) * (max 0 (gm - 1) + max 0 (1 - gp)) :=
    mul_le_mul_of_nonneg_right hTub hW0
  have f2 : δ * (max 0 (gm - 1) + max 0 (1 - gp)) ≤ δ * |gp - 1| :=
    mul_le_mul_of_nonneg_left hMsum hδpos.le
  have f3 : 4 / 3 * δ ^ 3 * (max 0 (gm - 1) + max 0 (1 - gp)) ≤ 4 / 3 * δ ^ 3 * 4 :=
    mul_le_mul_of_nonneg_left hMsum4 (by positivity)
  have f4 : T * c ≤ (δ + 4 / 3 * δ ^ 3) * (δ / 2 + 4 / 3 * (δ / 2) ^ 3) :=
    mul_le_mul hTub hcub hcpos.le (by positivity)
  have hE : T * (max 0 (gm - 1) + max 0 (1 - gp)) + 2 * (T * c) ≤
      |gp - 1| * δ + 7 * δ ^ 2 := by
    nlinarith only [f1, f2, f3, f4, p3, p4, p6]
  have hak1 : |gp - 1| * δ ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le
  have hak2 : (|gp - 1| + 1) / 2 * δ ≤ max |gp - 1| ((|gp - 1| + 1) / 2) * δ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hδpos.le
  have h2c : 2 * c ≤ δ + 1 / 3 * δ ^ 3 := by nlinarith only [hcub]
  rcases le_total (2 * c - s) 0 with hcase | hcase
  · rw [max_eq_left hcase] at hcombine
    nlinarith only [hcombine, hE, hak1, sq_nonneg δ]
  · rw [max_eq_right hcase] at hcombine
    nlinarith only [hcombine, hE, hak2, h2c, p3, sq_nonneg δ]

private theorem bRay_horizontal_boundary_measure_zero (K : ConvexBody Point)
    (t : ℝ) (htIoo : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Measure.hausdorffMeasure 1
       ((rotatingHallwayParts (K : Set Point) (t : Real.Angle)).bRay ∩
         {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) = 0 := by
  have hpi := Real.pi_pos
  have hns : NullSingletonClass (Measure.hausdorffMeasure 1 : Measure Point) :=
    Measure.nullSingletonClass_hausdorff Point one_pos
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  by_contra hxy
  have h1 : inner ℝ (x - y) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, ((mem_rotatingHallwayParts_bRay_iff _ _ x).mp hx.1).1,
      ((mem_rotatingHallwayParts_bRay_iff _ _ y).mp hy.1).1, sub_self]
  have hx2 : inner ℝ x (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := hx.2
  have hy2 : inner ℝ y (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := hy.2
  have h2 : inner ℝ (x - y) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_sub_left, hx2, hy2, sub_self]
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr hxy) h1 h2 with hA | hA
  · exact Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith [htIoo.2])
      (by rw [abs_lt]; constructor <;> linarith [htIoo.1, htIoo.2]) hA
  · rw [← Real.Angle.coe_add] at hA
    exact Real.Angle.coe_ne_coe_of_abs_sub_lt (by linarith [htIoo.2])
      (by rw [abs_lt]; constructor <;> linarith [htIoo.1, htIoo.2]) hA

/-- The magic function `k₀` read as a function on all reals through truncation. -/
def magicDensity (x : ℝ) : ℝ := magicFunctions.1 x.toNNReal

theorem maximumPolygonCap_surfaceAtom_bound (n : ℕ) (hn : 2 ≤ n)
    (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions) :
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
      ENNReal.ofReal (magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1) *
        polygonStepSize n + 8 * polygonStepSize n ^ 2) := by
  classical
  obtain ⟨hn2, hdy, P, hPK, hmax⟩ := hK
  subst hPK
  have hpi := Real.pi_pos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδpos : 0 < polygonStepSize n := by
    have hn0 : (0 : ℝ) < n := by linarith
    simp only [polygonStepSize]
    positivity
  have hδle : polygonStepSize n ≤ Real.pi / 4 := by
    have hn0 : (0 : ℝ) < n := by linarith
    rw [polygonStepSize, div_le_iff₀ hn0]
    nlinarith
  rcases ht with rfl | ht
  · rw [rightAngle_surfaceAreaMeasure_zero n hn2 P]
    exact zero_le
  · have htIoo : t ∈ Set.Ioo 0 (Real.pi / 2) := (rightAngleSet n hn2).interior t ht
    have hcap : supportValue (P.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
      P.val.property.2.2.2.1
    have htdom : t ∈ angleDomain (rightAngleSet n hn2) :=
      Set.mem_union_left _ (Set.mem_union_left _ (Finset.mem_coe.mpr ht))
    have hatom : surfaceAreaMeasure P.val.val {(t : Real.Angle)} =
        ENNReal.ofReal (polygonCapPolylineLength P ⟨t, htdom⟩) :=
      maximumPolygonCap_balanced P hmax ⟨t, htdom⟩
    have hlenat : polygonPolylineLengthAt P t = polygonCapPolylineLength P ⟨t, htdom⟩ := by
      simp only [polygonPolylineLengthAt, htdom, ↓reduceDIte]
    have hwall : (Measure.hausdorffMeasure 1
        (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay)).toReal =
        polygonPolylineLengthAt P t := (polygonNiche_wall_lengths P ht).2.1
    have hτnonneg : 0 ≤ polygonCapPolylineLength P ⟨t, htdom⟩ := by
      rw [← hlenat, ← hwall]
      exact ENNReal.toReal_nonneg
    -- the three pieces
    have hlegs := maximumPolygonCap_leg_lengths n hn2 P t ht
    have hsubset : frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ⊆
        (((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) ∪
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            (innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).2)) ∪
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
            (innerWallUpperHalfPlanes P.val (t + polygonStepSize n)).2) ∪
          ({p : Point | inner ℝ p (normalVector (t : Real.Angle)) =
              supportValue (P.val.val : Set Point) (t : Real.Angle) - 1} ∩
            ((innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).1 ∩
              (innerWallUpperHalfPlanes P.val (t + polygonStepSize n)).1)) := by
      rintro p ⟨hpfront, hpray⟩
      have hpline : inner ℝ p (normalVector (t : Real.Angle)) =
          supportValue (P.val.val : Set Point) (t : Real.Angle) - 1 :=
        ((mem_rotatingHallwayParts_bRay_iff _ _ p).mp hpray).1
      by_cases hzero : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
      · exact Or.inl (Or.inl (Or.inl ⟨hpray, hzero⟩))
      · have hclos : p ∈ capFan (rightAngleSet n hn2).angle := by
          have hsub : closure (polygonNiche (rightAngleSet n hn2) P.val) ⊆
              capFan (rightAngleSet n hn2).angle :=
            (isClosed_capFan _).closure_subset_iff.mpr (fun q hq ↦ hq.1)
          exact hsub hpfront.1
        have hppos : 0 < inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) :=
          lt_of_le_of_ne hclos.2 (Ne.symm hzero)
        have hnotN : p ∉ polygonNiche (rightAngleSet n hn2) P.val := by
          intro hpN
          refine hpfront.2 ?_
          have hUopen : IsOpen {q : Point |
              0 < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} :=
            isOpen_lt continuous_const (by fun_prop)
          have hVopen : IsOpen (⋃ u ∈ (rightAngleSet n hn2).directions,
              innerQuadrant (P.val.val : Set Point) u) :=
            isOpen_biUnion (fun u _ ↦ isOpen_innerQuadrant _ u)
          refine interior_maximal ?_ (hUopen.inter hVopen) ⟨hppos, hpN.2⟩
          rintro q ⟨hq1, hq2⟩
          have hq1' : (0 : ℝ) < inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hq1
          exact ⟨⟨hq1'.le, hq1'.le⟩, hq2⟩
        have hquad : ∀ u : ℝ,
            (u = 0 ∨ u = Real.pi / 2 ∨ u ∈ (rightAngleSet n hn2).directions) →
            p ∉ innerQuadrant (P.val.val : Set Point) u := by
          rintro u (rfl | rfl | hu)
          · intro hq
            have h2 : inner ℝ p (normalVector ((0 + Real.pi / 2 : ℝ) : Real.Angle)) <
                supportValue (P.val.val : Set Point)
                  ((0 + Real.pi / 2 : ℝ) : Real.Angle) - 1 := hq.2
            rw [show (0 + Real.pi / 2 : ℝ) = Real.pi / 2 by ring, hcap] at h2
            linarith
          · intro hq
            have h1 : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
                supportValue (P.val.val : Set Point)
                  ((Real.pi / 2 : ℝ) : Real.Angle) - 1 := hq.1
            rw [hcap] at h1
            linarith
          · intro hq
            exact hnotN ⟨hclos, Set.mem_biUnion hu hq⟩
        have hq1 : p ∉ innerQuadrant (P.val.val : Set Point) (t - polygonStepSize n) :=
          hquad _ ((rightAngleSet_sub_step n hn2 ht).imp id Or.inr)
        have hq2 : p ∉ innerQuadrant (P.val.val : Set Point) (t + polygonStepSize n) :=
          hquad _ (Or.inr ((rightAngleSet_add_step n hn2 ht).imp id id))
        rcases (notMem_innerQuadrant_iff _ _ _).mp hq1 with hb1 | hd1
        · rcases (notMem_innerQuadrant_iff _ _ _).mp hq2 with hb2 | hd2
          · exact Or.inr ⟨hpline, hb1, hb2⟩
          · exact Or.inl (Or.inr ⟨hpray, hd2⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hpray, hd1⟩))
    have hz := bRay_horizontal_boundary_measure_zero P.val.val t htIoo
    have hslice := hausdorffMeasure_faceLine_inter_innerWalls_le P.val.val t
      (polygonStepSize n) hδpos (by linarith)
    have hbound : Measure.hausdorffMeasure 1
        (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
          (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay) ≤
        ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 +
              Real.tan (polygonStepSize n / 2))) +
          ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 (1 - (tangentArmLengths P.val t).2.1 +
              Real.tan (polygonStepSize n / 2))) +
          ENNReal.ofReal (max 0 (2 * Real.tan (polygonStepSize n / 2) -
            (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal)) := by
      have hAB : Measure.hausdorffMeasure 1
          (((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
              {p : Point | inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0}) ∪
            ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay ∩
              (innerWallUpperHalfPlanes P.val (t - polygonStepSize n)).2)) ≤
          ENNReal.ofReal (Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 +
              Real.tan (polygonStepSize n / 2))) := by
        refine (measure_union_le _ _).trans ?_
        rw [hz, hlegs.1, zero_add]
      exact (measure_mono hsubset).trans ((measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans
          (add_le_add hAB (le_of_eq hlegs.2))) hslice))
    have harm := (maximumPolygonCap_arm_bound n P.val ⟨hn2, hdy, P, rfl, hmax⟩).2 t
      ⟨htIoo.1.le, htIoo.2.le⟩
    have hgp0 : 0 ≤ (tangentArmLengths P.val t).2.1 := harm.2.2.1.1
    have hgp5 : (tangentArmLengths P.val t).2.1 ≤ 5 := harm.2.2.1.2
    have hgm0 : 0 ≤ (tangentArmLengths P.val t).2.2 := harm.2.2.2.1
    have harm1 : (tangentArmLengths P.val t).2.1 =
        inner ℝ ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1)
          (normalVector (t : Real.Angle)) := rfl
    have harm2 : (tangentArmLengths P.val t).2.2 =
        inner ℝ ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2)
          (normalVector (t : Real.Angle)) := rfl
    have hgle : (tangentArmLengths P.val t).2.2 ≤ (tangentArmLengths P.val t).2.1 := by
      have hC : (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 =
          (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle) := by
        rw [(surfaceAreaMeasure_atom_length P.val.val
          ((t + Real.pi / 2 : ℝ) : Real.Angle)).2.2, tangentVector_add_pi_div_two]
        module
      rw [harm1, harm2, hC, show (rotatingHallwayParts (P.val.val : Set Point)
            (t : Real.Angle)).outerCorner -
          ((edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 -
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle)) =
          ((rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).outerCorner -
            (edgeVertices P.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).2) +
            (surfaceAreaMeasure P.val.val {((t + Real.pi / 2 : ℝ) : Real.Angle)}).toReal •
              normalVector (t : Real.Angle) from by module,
        inner_add_left, real_inner_smul_left, inner_normalVector_self, mul_one]
      have := ENNReal.toReal_nonneg (a := surfaceAreaMeasure P.val.val
        {((t + Real.pi / 2 : ℝ) : Real.Angle)})
      linarith
    have hstoReal : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal =
        polygonCapPolylineLength P ⟨t, htdom⟩ := by
      rw [hatom, ENNReal.toReal_ofReal hτnonneg]
    have hXeq : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal =
        (Measure.hausdorffMeasure 1
          (frontier (polygonNiche (rightAngleSet n hn2) P.val) ∩
            (rotatingHallwayParts (P.val.val : Set Point) (t : Real.Angle)).bRay)).toReal := by
      rw [hstoReal, ← hlenat]
      exact hwall.symm
    have hTpos : 0 < Real.tan (polygonStepSize n) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hδpos (by linarith)
    have hcpos : 0 < Real.tan (polygonStepSize n / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (le_max_left _ _)] at hbound
    have hsum : (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal ≤
        Real.tan (polygonStepSize n) *
            max 0 ((tangentArmLengths P.val t).2.2 - 1 + Real.tan (polygonStepSize n / 2)) +
          Real.tan (polygonStepSize n) *
            max 0 (1 - (tangentArmLengths P.val t).2.1 + Real.tan (polygonStepSize n / 2)) +
          max 0 (2 * Real.tan (polygonStepSize n / 2) -
            (surfaceAreaMeasure P.val.val {(t : Real.Angle)}).toReal) := by
      conv_lhs => rw [hXeq]
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq ?_
      exact ENNReal.toReal_ofReal (by positivity)
    have hmagic : magicFunctions.1 (Real.toNNReal (tangentArmLengths P.val t).2.1) =
        max |(tangentArmLengths P.val t).2.1 - 1|
          ((|(tangentArmLengths P.val t).2.1 - 1| + 1) / 2) := by
      simp only [magicFunctions, Real.coe_toNNReal _ hgp0]
    rw [hatom]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hstoReal, hmagic]
    refine magicBound_of_le hδpos ?_ ?_ hTpos ?_ hcpos hgp5 hgm0 hgle hsum
    · linarith [Real.pi_lt_d2]
    · exact Real.tan_le_self_add_cube hδpos.le (by linarith [Real.pi_le_four])
    · exact Real.tan_le_self_add_cube (by linarith) (by linarith [Real.pi_le_four])

section Domination

open Filter Set
open scoped Topology

/-! ### The magic density -/

private theorem magicDensity_eq (x : ℝ) :
    magicDensity x = max |max x 0 - 1| ((|max x 0 - 1| + 1) / 2) := by
  simp [magicDensity, magicFunctions]

/-- The magic function `k₀` is nonnegative. -/
theorem magicDensity_nonneg (x : ℝ) : 0 ≤ magicDensity x := by
  rw [magicDensity_eq]
  exact (abs_nonneg _).trans (le_max_left _ _)

private theorem continuous_magicDensity : Continuous magicDensity := by
  unfold magicDensity magicFunctions
  fun_prop

/-- The magic function `k₀` is `1`-Lipschitz. -/
private theorem abs_magicDensity_sub_le (x y : ℝ) :
    |magicDensity x - magicDensity y| ≤ |x - y| := by
  rw [magicDensity_eq, magicDensity_eq]
  have hxy : |max x 0 - max y 0| ≤ |x - y| := by
    calc
      |max x 0 - max y 0| ≤ max |x - y| |(0 : ℝ) - 0| :=
        abs_max_sub_max_le_max x 0 y 0
      _ = |x - y| := by simp
  have habs : abs (|max x 0 - 1| - |max y 0 - 1|) ≤ |x - y| := by
    calc
      abs (|max x 0 - 1| - |max y 0 - 1|) ≤
          |(max x 0 - 1) - (max y 0 - 1)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |max x 0 - max y 0| := by ring_nf
      _ ≤ |x - y| := hxy
  have hhalf :
      |((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2)| ≤ |x - y| := by
    rw [show ((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2) =
      (|max x 0 - 1| - |max y 0 - 1|) / 2 by ring, abs_div]
    norm_num
    linarith [abs_nonneg (|max x 0 - 1| - |max y 0 - 1|)]
  calc
    |max |max x 0 - 1| ((|max x 0 - 1| + 1) / 2) -
        max |max y 0 - 1| ((|max y 0 - 1| + 1) / 2)| ≤
        max (abs (|max x 0 - 1| - |max y 0 - 1|))
          |((|max x 0 - 1| + 1) / 2) - ((|max y 0 - 1| + 1) / 2)| :=
      abs_max_sub_max_le_max _ _ _ _
    _ ≤ |x - y| := max_le habs hhalf

/-- The magic function `k₀` grows at most linearly: `k₀ x ≤ |x| + 1`. -/
theorem magicDensity_le_abs_add_one (x : ℝ) : magicDensity x ≤ |x| + 1 := by
  have hzero : magicDensity 0 = 1 := by norm_num [magicDensity, magicFunctions]
  have h := abs_magicDensity_sub_le x 0
  rw [hzero, sub_zero] at h
  linarith [le_abs_self (magicDensity x - 1)]

/-! ### Integrability of the magic density -/

/-- The magic density of the positive tangent arm length is almost everywhere strongly
measurable on the rotation interval. -/
theorem aestronglyMeasurable_magicDensity_tangentArm_fst (C : RightAngleCapSpace) :
    AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (volume.restrict (Ioc 0 (Real.pi / 2))) :=
  continuous_magicDensity.comp_aestronglyMeasurable (aestronglyMeasurable_tangentArm_fst C)

/-- The magic density of the positive tangent arm length is integrable on the rotation
interval. -/
private theorem intervalIntegrable_magicDensity_tangentArm_fst (C : RightAngleCapSpace) :
    IntervalIntegrable (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      volume 0 (Real.pi / 2) := by
  have hdensity' : AEStronglyMeasurable
      (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (volume.restrict (uIoc 0 (Real.pi / 2))) := by
    simpa only [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using
      aestronglyMeasurable_magicDensity_tangentArm_fst C
  have harmInt := intervalIntegrable_tangentArm_fst C
  apply (harmInt.norm.add (intervalIntegrable_const (c := (1 : ℝ)))).mono_fun hdensity'
  filter_upwards [] with t
  change |magicDensity (tangentArmLengths C t).2.1| ≤
    abs (|(tangentArmLengths C t).2.1| + 1)
  rw [abs_of_nonneg (magicDensity_nonneg _),
    abs_of_nonneg (add_nonneg (abs_nonneg (tangentArmLengths C t).2.1) zero_le_one)]
  exact magicDensity_le_abs_add_one _

private theorem integrableOn_magicDensity_tangentArm_fst (C : RightAngleCapSpace)
    {S : Set ℝ} (hS : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    IntegrableOn (fun t ↦ magicDensity (tangentArmLengths C t).2.1) S volume := by
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)).1
      (intervalIntegrable_magicDensity_tangentArm_fst C)
  have hIcc : IntegrableOn (fun t ↦ magicDensity (tangentArmLengths C t).2.1)
      (Icc (0 : ℝ) (Real.pi / 2)) volume := by
    rwa [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] at hIoc
  exact hIcc.mono_set hS

/-! ### The density measure of a cap -/

/-- The measure `k₀(g⁺_K(t)) dt` on the rotation interval. -/
private def armDensityMeasure (C : RightAngleCapSpace) : Measure ℝ :=
  (volume.restrict (Ioc 0 (Real.pi / 2))).withDensity
    (fun t ↦ ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1))

private theorem armDensityMeasure_apply (C : RightAngleCapSpace) {S : Set ℝ}
    (hS : MeasurableSet S) :
    armDensityMeasure C S = ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
      ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) := by
  rw [armDensityMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]

private theorem lintegral_magicDensity_eq_ofReal (C : RightAngleCapSpace) {S : Set ℝ}
    (hS : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    ∫⁻ t in S, ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) =
      ENNReal.ofReal (∫ t in S, magicDensity (tangentArmLengths C t).2.1) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_magicDensity_tangentArm_fst C hS)
    (Filter.Eventually.of_forall fun t ↦ magicDensity_nonneg _)]

private theorem armDensityMeasure_ne_top (C : RightAngleCapSpace) :
    armDensityMeasure C Set.univ ≠ ⊤ := by
  rw [armDensityMeasure_apply C MeasurableSet.univ, Set.univ_inter,
    lintegral_magicDensity_eq_ofReal C Ioc_subset_Icc_self]
  exact ENNReal.ofReal_ne_top

private theorem armDensityMeasure_eq_ofReal_integral (C : RightAngleCapSpace) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : S ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    armDensityMeasure C S =
      ENNReal.ofReal (∫ t in S, magicDensity (tangentArmLengths C t).2.1) := by
  have hnull : S ∩ Ioc 0 (Real.pi / 2) =ᵐ[volume] S := by
    have hsub : S \ (S ∩ Ioc 0 (Real.pi / 2)) ⊆ {0} := by
      intro x hx
      have hxS := hx.1
      have hx2 : x ∉ Ioc 0 (Real.pi / 2) := fun h ↦ hx.2 ⟨hxS, h⟩
      have hxIco := hS hxS
      have : x = 0 := by
        by_contra hne
        exact hx2 ⟨lt_of_le_of_ne hxIco.1 (Ne.symm hne), hxIco.2.le⟩
      simp [this]
    refine (Filter.EventuallyEq.symm ?_)
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null hsub (measure_singleton 0)
    · simp [Set.sdiff_eq_empty.2 Set.inter_subset_left]
  rw [armDensityMeasure_apply C hSm, setLIntegral_congr hnull,
    lintegral_magicDensity_eq_ofReal C (hS.trans Ico_subset_Icc_self)]

/-- Comparing two cap densities costs at most the `L¹` distance of their arm lengths. -/
private theorem armDensityMeasure_le_add_l1 (C D : RightAngleCapSpace) {S : Set ℝ}
    (hS : MeasurableSet S) :
    armDensityMeasure C S ≤ armDensityMeasure D S +
      ENNReal.ofReal (∫ t in (0 : ℝ)..(Real.pi / 2),
        |magicDensity (tangentArmLengths C t).2.1 -
          magicDensity (tangentArmLengths D t).2.1|) := by
  have hT : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hdiff : IntervalIntegrable (fun t ↦ |magicDensity (tangentArmLengths C t).2.1 -
      magicDensity (tangentArmLengths D t).2.1|) volume 0 (Real.pi / 2) := by
    simpa only [Real.norm_eq_abs] using
      ((intervalIntegrable_magicDensity_tangentArm_fst C).sub
        (intervalIntegrable_magicDensity_tangentArm_fst D)).norm
  have hdiffIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hdiff
  have hmeasD : AEMeasurable
      (fun t ↦ ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1))
      (volume.restrict (S ∩ Ioc 0 (Real.pi / 2))) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    exact ((continuous_magicDensity.comp_aestronglyMeasurable
      (aestronglyMeasurable_tangentArm_fst D)).aemeasurable).mono_measure
        (Measure.restrict_mono Set.inter_subset_right le_rfl)
  rw [armDensityMeasure_apply C hS, armDensityMeasure_apply D hS]
  calc
    ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
        ENNReal.ofReal (magicDensity (tangentArmLengths C t).2.1) ≤
        ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          (ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1) +
            ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
              magicDensity (tangentArmLengths D t).2.1|) := by
      refine lintegral_mono fun t ↦ ?_
      rw [← ENNReal.ofReal_add (magicDensity_nonneg _) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [le_abs_self (magicDensity (tangentArmLengths C t).2.1 -
        magicDensity (tangentArmLengths D t).2.1)]
    _ = (∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1)) +
        ∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
            magicDensity (tangentArmLengths D t).2.1| := lintegral_add_left' hmeasD _
    _ ≤ (∫⁻ t in S ∩ Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (magicDensity (tangentArmLengths D t).2.1)) +
        ∫⁻ t in Ioc 0 (Real.pi / 2),
          ENNReal.ofReal |magicDensity (tangentArmLengths C t).2.1 -
            magicDensity (tangentArmLengths D t).2.1| := by
      gcongr
      exact Set.inter_subset_right
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hdiffIoc
        (Filter.Eventually.of_forall fun t ↦ abs_nonneg _),
        intervalIntegral.integral_of_le hT]

/-! ### Surface measure support of a right-angle polygon cap -/

/-- Angular images of Borel subsets of the half-open rotation interval are Borel. -/
private theorem measurableSet_coe_image_of_subset_Ico {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' E) :=
  Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
    (by linarith [Real.pi_pos]) hE fun t ht ↦
      ⟨by linarith [Real.pi_pos, (hET ht).1],
        (hET ht).2.le.trans (half_le_self Real.pi_pos.le)⟩

private theorem rightAngle_properEdgeNormal_real (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ} (hs : s ∈ Ioc (-Real.pi) Real.pi)
    (hedge : (edgeVertices K.val.val (s : Real.Angle)).1 ≠
      (edgeVertices K.val.val (s : Real.Angle)).2) :
    s ∈ angleDomain (rightAngleSet n hn) ∨ s = -(Real.pi / 2) := by
  have hpi := Real.pi_pos
  have h := K.properEdgeNormal_mem_allowed (s : Real.Angle) hedge
  rw [rightAngle_polygon_normals_eq n hn] at h
  obtain ⟨r, hr, hrs⟩ := h
  rcases hr with hr | rfl
  · left
    have hrb := angleDomain_subset_Ioo (rightAngleSet n hn) hr
    have hsr : s = r := Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith) hs ⟨by linarith [hrb.1], hrb.2.le⟩ hrs.symm
    exact hsr ▸ hr
  · right
    have hrs' : ((3 * Real.pi / 2 : ℝ) : Real.Angle) = ((s : ℝ) : Real.Angle) := hrs
    refine Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi) (by linarith) hs
      ⟨by linarith, by linarith⟩ ?_
    change ((s : ℝ) : Real.Angle) = ((-(Real.pi / 2) : ℝ) : Real.Angle)
    rw [← hrs', Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨1, by push_cast; ring⟩

private theorem rightAngle_properEdgeNormal_mem_directions (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) (Real.pi / 2))
    (hedge : (edgeVertices K.val.val (s : Real.Angle)).1 ≠
      (edgeVertices K.val.val (s : Real.Angle)).2) :
    s ∈ (rightAngleSet n hn).directions := by
  have hpi := Real.pi_pos
  have hsIoc : s ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases rightAngle_properEdgeNormal_real n hn K hsIoc hedge with hdom | hneg
  · rcases hdom with (hd | ⟨r, hr, hrs⟩) | hd
    · exact hd
    · exact absurd hs.2 (by
        have hr0 := ((rightAngleSet n hn).interior r hr).1
        rw [← hrs]
        push Not
        linarith)
    · exfalso
      have hangle : (rightAngleSet n hn).angle = Real.pi / 2 := rfl
      simp only [hangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with hd | hd <;> (rw [hd] at hs; linarith [hs.2])
  · exfalso
    rw [hneg] at hs
    linarith [hs.1]

private theorem rightAngle_edgeVertices_eq_of_mem_Ioo_neg (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {s : ℝ}
    (hs : s ∈ Ioo (-(Real.pi / 2)) 0) :
    (edgeVertices K.val.val (s : Real.Angle)).1 =
      (edgeVertices K.val.val (s : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  by_contra hne
  have hsIoc : s ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases rightAngle_properEdgeNormal_real n hn K hsIoc hne with hdom | hneg
  · have hrb := angleDomain_subset_Ioo (rightAngleSet n hn) hdom
    linarith [hrb.1, hs.2]
  · rw [hneg] at hs
    linarith [hs.1]

private theorem surfaceAreaMeasure_rightAngle_compl_grid_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val
      (((fun s : ℝ ↦ (s : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)) \
        ((fun s : ℝ ↦ (s : Real.Angle)) ''
          ({0} ∪ ((rightAngleSet n hn).directions : Set ℝ)))) = 0 := by
  apply measure_mono_null _ K.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
  rintro u ⟨⟨s, hs, rfl⟩, hnot⟩
  by_contra hne
  exact hnot ⟨s, Or.inr (rightAngle_properEdgeNormal_mem_directions n hn K hs hne), rfl⟩

private theorem surfaceAreaMeasure_rightAngle_Ioo_neg_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) :
    surfaceAreaMeasure K.val.val
      ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) = 0 := by
  apply measure_mono_null _ K.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
  rintro u ⟨s, hs, rfl⟩
  exact rightAngle_edgeVertices_eq_of_mem_Ioo_neg n hn K hs

/-! ### Discrete cell bounds -/

private theorem maximumPolygonCap_arm_cell_abs_le (n : ℕ) (hn : 2 ≤ n)
    (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K) (t u : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hu : u ∈ Ioo t (t + polygonStepSize n)) :
    |(tangentArmLengths K u).2.1 - (tangentArmLengths K t).2.1| ≤
      5 * polygonStepSize n := by
  obtain ⟨hcell, hdrop⟩ := maximumPolygonCap_arm_cell n hn K hK t ht
  have hu' := hcell u hu
  have hlower :
      (tangentArmLengths K t).2.1 - 5 * polygonStepSize n ≤
        (tangentArmLengths K u).2.1 := by
    rw [hu'.2.1]
    linarith [hu'.2.2]
  rw [abs_le]
  constructor <;> linarith [hu'.1]

private theorem magicDensity_mul_le_integral_add_of_cell_bound
    (f : ℝ → ℝ) (t δ c : ℝ) (hδ : 0 ≤ δ)
    (hint : IntervalIntegrable (fun u ↦ magicDensity (f u)) volume t (t + δ))
    (hvar : ∀ᵐ u ∂volume.restrict (Icc t (t + δ)), |f u - f t| ≤ c) :
    magicDensity (f t) * δ ≤
      (∫ u in t..(t + δ), magicDensity (f u)) + c * δ := by
  have hp : ∀ᵐ u ∂volume.restrict (Icc t (t + δ)),
      magicDensity (f t) ≤ magicDensity (f u) + c := by
    filter_upwards [hvar] with u hu
    have hle : magicDensity (f t) - magicDensity (f u) ≤ c := by
      calc
        magicDensity (f t) - magicDensity (f u) ≤
            |magicDensity (f t) - magicDensity (f u)| := le_abs_self _
        _ ≤ |f t - f u| := abs_magicDensity_sub_le _ _
        _ = |f u - f t| := abs_sub_comm _ _
        _ ≤ c := hu
    linarith
  have hc : IntervalIntegrable (fun _ : ℝ ↦ c) volume t (t + δ) :=
    intervalIntegrable_const
  have hi := intervalIntegral.integral_mono_ae_restrict
    (show t ≤ t + δ by linarith)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ ↦ magicDensity (f t)) volume t (t + δ))
    (hint.add hc) hp
  rw [intervalIntegral.integral_add hint hc, intervalIntegral.integral_const,
    intervalIntegral.integral_const] at hi
  simpa only [add_sub_cancel_left, smul_eq_mul, mul_comm] using hi

private theorem maximumPolygonCap_magicDensity_cell_bound
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hint : IntervalIntegrable
      (fun u ↦ magicDensity (tangentArmLengths K u).2.1)
      volume t (t + polygonStepSize n)) :
    magicDensity (tangentArmLengths K t).2.1 * polygonStepSize n ≤
      (∫ u in t..(t + polygonStepSize n),
        magicDensity (tangentArmLengths K u).2.1) +
        5 * polygonStepSize n ^ 2 := by
  have haeIoo : ∀ᵐ u ∂volume.restrict
      (Icc t (t + polygonStepSize n)), u ∈ Ioo t (t + polygonStepSize n) := by
    rw [ae_iff]
    change (volume.restrict (Icc t (t + polygonStepSize n)))
      (Ioo t (t + polygonStepSize n))ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Ioo.compl]
    have hsub : (Ioo t (t + polygonStepSize n))ᶜ ∩
        Icc t (t + polygonStepSize n) ⊆ {t, t + polygonStepSize n} := by
      intro x hx
      simp only [mem_inter_iff, mem_Icc, mem_compl_iff, mem_Ioo, not_and_or,
        not_lt, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with ⟨hxt | hux, htx, hxu⟩
      · exact Or.inl (le_antisymm hxt htx)
      · exact Or.inr (le_antisymm hxu hux)
    exact measure_mono_null hsub
      ((Set.finite_singleton (t + polygonStepSize n)).insert t |>.measure_zero volume)
  have hvar : ∀ᵐ u ∂volume.restrict (Icc t (t + polygonStepSize n)),
      |(tangentArmLengths K u).2.1 - (tangentArmLengths K t).2.1| ≤
        5 * polygonStepSize n := by
    filter_upwards [haeIoo] with u hu
    exact maximumPolygonCap_arm_cell_abs_le n hn K hK t u ht hu
  have hδ : 0 ≤ polygonStepSize n := by
    simp only [polygonStepSize]
    positivity
  have h := magicDensity_mul_le_integral_add_of_cell_bound
    (fun u ↦ (tangentArmLengths K u).2.1) t (polygonStepSize n)
      (5 * polygonStepSize n) hδ hint hvar
  nlinarith [sq_nonneg (polygonStepSize n)]

private theorem maximumPolygonCap_surfaceAtom_le_lintegral_cell
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace)
    (hK : IsMaximumPolygonCapSteps n K) (t : ℝ)
    (ht : t = 0 ∨ t ∈ (rightAngleSet n hn).directions)
    (hmem : Icc t (t + polygonStepSize n) ⊆ Icc (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
      (∫⁻ u in Ioc t (t + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) +
      ENNReal.ofReal (13 * polygonStepSize n ^ 2) := by
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le zero_lt_two hn
    exact_mod_cast this
  have hδ : 0 < polygonStepSize n :=
    div_pos (by linarith [Real.pi_pos]) hnR
  have hle : t ≤ t + polygonStepSize n := by linarith
  have hint : IntervalIntegrable
      (fun u ↦ magicDensity (tangentArmLengths K u).2.1) volume t (t + polygonStepSize n) := by
    apply (intervalIntegrable_magicDensity_tangentArm_fst K).mono_set
    rw [uIcc_of_le hle, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hmem
  have hcell := maximumPolygonCap_magicDensity_cell_bound n hn K hK t ht hint
  have hnonneg : 0 ≤ ∫ u in t..(t + polygonStepSize n),
      magicDensity (tangentArmLengths K u).2.1 :=
    intervalIntegral.integral_nonneg hle fun u _ ↦ magicDensity_nonneg _
  have hlint : ENNReal.ofReal (∫ u in t..(t + polygonStepSize n),
        magicDensity (tangentArmLengths K u).2.1) =
      ∫⁻ u in Ioc t (t + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1) := by
    rw [intervalIntegral.integral_of_le hle]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hint)
      (Filter.Eventually.of_forall fun u ↦ magicDensity_nonneg _)
  calc
    surfaceAreaMeasure K.val {(t : Real.Angle)} ≤
        ENNReal.ofReal (magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1) *
          polygonStepSize n + 8 * polygonStepSize n ^ 2) :=
      maximumPolygonCap_surfaceAtom_bound n hn K hK t ht
    _ ≤ ENNReal.ofReal ((∫ u in t..(t + polygonStepSize n),
          magicDensity (tangentArmLengths K u).2.1) + 13 * polygonStepSize n ^ 2) := by
      refine ENNReal.ofReal_le_ofReal ?_
      change magicDensity (tangentArmLengths K t).2.1 * polygonStepSize n +
        8 * polygonStepSize n ^ 2 ≤ _
      linarith
    _ = _ := by rw [ENNReal.ofReal_add hnonneg (by positivity), hlint]

/-! ### The per-level grid bound -/

private theorem maximumPolygonCap_surface_image_le_thickening
    (n : ℕ) (hn : 2 ≤ n) (K : RightAngleCapSpace) (hK : IsMaximumPolygonCapSteps n K)
    (S : Set ℝ) (hSm : MeasurableSet S) (hST : S ⊆ Ico (0 : ℝ) (Real.pi / 2))
    {ε : ℝ} (hε : polygonStepSize n < ε) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' S) ≤
      armDensityMeasure K (Metric.thickening ε S) +
        ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
  classical
  have hpi := Real.pi_pos
  have hK0 := hK
  obtain ⟨hn', hdy, P, hPK, hmax⟩ := hK
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le zero_lt_two hn
    exact_mod_cast this
  have hδpos : 0 < polygonStepSize n := div_pos (by linarith) hnR
  have hnδ : (n : ℝ) * polygonStepSize n = Real.pi / 2 := by
    rw [polygonStepSize]
    field_simp
  have hinj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Ico (0 : ℝ) (Real.pi / 2)) := by
    apply (Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi) (by linarith)).mono
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgridmem : ∀ i : ℕ, i < n →
      (i : ℝ) * polygonStepSize n ∈ Ico (0 : ℝ) (Real.pi / 2) := by
    intro i hi
    have hin : (i : ℝ) < n := by exact_mod_cast hi
    refine ⟨mul_nonneg (Nat.cast_nonneg i) hδpos.le, ?_⟩
    calc (i : ℝ) * polygonStepSize n < (n : ℝ) * polygonStepSize n := by
          exact mul_lt_mul_of_pos_right hin hδpos
      _ = Real.pi / 2 := hnδ
  have hcellIcc : ∀ i : ℕ, i < n →
      Icc ((i : ℝ) * polygonStepSize n) ((i : ℝ) * polygonStepSize n + polygonStepSize n) ⊆
        Icc (0 : ℝ) (Real.pi / 2) := by
    intro i hi x hx
    have hsucc : ((i : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    refine ⟨le_trans (mul_nonneg (Nat.cast_nonneg i) hδpos.le) hx.1, hx.2.trans ?_⟩
    calc (i : ℝ) * polygonStepSize n + polygonStepSize n =
          ((i : ℝ) + 1) * polygonStepSize n := by ring
      _ ≤ (n : ℝ) * polygonStepSize n := mul_le_mul_of_nonneg_right hsucc hδpos.le
      _ = Real.pi / 2 := hnδ
  have hgriddir : ∀ i : ℕ, i < n →
      (i : ℝ) * polygonStepSize n = 0 ∨
        (i : ℝ) * polygonStepSize n ∈ (rightAngleSet n hn').directions := by
    intro i hi
    by_cases hi0 : i = 0
    · exact Or.inl (by simp [hi0])
    · exact Or.inr ((mem_rightAngleSet_directions_iff n hn' _).2
        ⟨i, Finset.mem_Ioo.2 ⟨Nat.pos_of_ne_zero hi0, hi⟩, rfl⟩)
  -- the surface measure restricted to the arc of interest
  have hSimage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' S) :=
    measurableSet_coe_image_of_subset_Ico hSm hST
  have hμS : ((surfaceAreaMeasure K.val).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)))
        ((fun t : ℝ ↦ (t : Real.Angle)) '' S) =
      surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' S) := by
    rw [Measure.restrict_apply hSimage,
      Set.inter_eq_left.2 (Set.image_mono hST)]
  -- the atom decomposition over the grid
  have hbound := measure_le_sum_of_measure_compl_image_eq_zero
    ((surfaceAreaMeasure K.val).restrict
      ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico (0 : ℝ) (Real.pi / 2)))
    (Finset.range n)
    ((Finset.range n).filter (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S))
    (fun i : ℕ ↦ (((i : ℝ) * polygonStepSize n : ℝ) : Real.Angle))
    (fun i : ℕ ↦ (∫⁻ u in Ioc ((i : ℝ) * polygonStepSize n)
        ((i : ℝ) * polygonStepSize n + polygonStepSize n),
        ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) +
      ENNReal.ofReal (13 * polygonStepSize n ^ 2))
    ?_ ?_ ?_ ((fun t : ℝ ↦ (t : Real.Angle)) '' S) hSimage ?_
  · rw [hμS] at hbound
    refine hbound.trans ?_
    rw [Finset.sum_add_distrib]
    have hdisj : ((Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S) : Set ℕ).PairwiseDisjoint
        (fun i : ℕ ↦ Ioc ((i : ℝ) * polygonStepSize n)
          ((i : ℝ) * polygonStepSize n + polygonStepSize n)) := by
      intro i _ j _ hij
      simp only [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rcases lt_or_gt_of_ne hij with h | h
      · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        have : (i : ℝ) * polygonStepSize n + polygonStepSize n ≤
            (j : ℝ) * polygonStepSize n := by
          nlinarith [hδpos]
        linarith [hx.2, hx'.1]
      · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
        have : (j : ℝ) * polygonStepSize n + polygonStepSize n ≤
            (i : ℝ) * polygonStepSize n := by
          nlinarith [hδpos]
        linarith [hx.1, hx'.2]
    have hsumlint : ∑ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
          (∫⁻ u in Ioc ((i : ℝ) * polygonStepSize n)
            ((i : ℝ) * polygonStepSize n + polygonStepSize n),
            ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1)) =
        ∫⁻ u in ⋃ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
            Ioc ((i : ℝ) * polygonStepSize n)
              ((i : ℝ) * polygonStepSize n + polygonStepSize n),
          ENNReal.ofReal (magicDensity (tangentArmLengths K u).2.1) :=
      (lintegral_biUnion_finset hdisj (fun i _ ↦ measurableSet_Ioc) _).symm
    have hsubset : (⋃ i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
            Ioc ((i : ℝ) * polygonStepSize n)
              ((i : ℝ) * polygonStepSize n + polygonStepSize n)) ⊆
        Metric.thickening ε S ∩ Ioc 0 (Real.pi / 2) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hiR, hiS⟩ := Finset.mem_filter.1 hi
      have hi' : i < n := Finset.mem_range.1 hiR
      refine ⟨?_, ?_⟩
      · refine Metric.mem_thickening_iff.2 ⟨(i : ℝ) * polygonStepSize n, hiS, ?_⟩
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hxi.1])]
        linarith [hxi.2]
      · exact ⟨lt_of_le_of_lt (hgridmem i hi').1 hxi.1,
          (hcellIcc i hi' ⟨hxi.1.le, hxi.2⟩).2⟩
    have hcard : (((Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)).card : ENNReal) ≤
        (n : ENNReal) := by
      have := Finset.card_filter_le (Finset.range n)
        (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hconst : ∑ _i ∈ (Finset.range n).filter
          (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S),
          ENNReal.ofReal (13 * polygonStepSize n ^ 2) ≤
        ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (((Finset.range n).filter
            (fun i : ℕ ↦ ((i : ℝ) * polygonStepSize n) ∈ S)).card : ENNReal) *
              ENNReal.ofReal (13 * polygonStepSize n ^ 2) ≤
            (n : ENNReal) * ENNReal.ofReal (13 * polygonStepSize n ^ 2) := by
          gcongr
        _ = ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize n) := by
          rw [show ((n : ENNReal)) = ENNReal.ofReal ((n : ℝ)) by
            simp [ENNReal.ofReal_natCast],
            ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          congr 1
          nlinarith [hnδ]
    refine add_le_add ?_ hconst
    rw [hsumlint, armDensityMeasure_apply K Metric.isOpen_thickening.measurableSet]
    exact lintegral_mono_set hsubset
  · -- injectivity of the grid map
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < n := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have heq : (i : ℝ) * polygonStepSize n = (j : ℝ) * polygonStepSize n :=
      hinj (hgridmem i hi') (hgridmem j hj') hij
    have hij' : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hδpos.ne' heq
    exact_mod_cast hij'
  · -- the surface measure is carried by the grid
    have himagegrid :
        (fun i : ℕ ↦ (((i : ℝ) * polygonStepSize n : ℝ) : Real.Angle)) ''
            (Finset.range n : Set ℕ) =
          (fun s : ℝ ↦ (s : Real.Angle)) ''
            ({0} ∪ ((rightAngleSet n hn').directions : Set ℝ)) := by
      ext u
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi' : i < n := Finset.mem_range.1 (Finset.mem_coe.1 hi)
        rcases hgriddir i hi' with h0 | hdir
        · exact ⟨(i : ℝ) * polygonStepSize n, Or.inl h0, rfl⟩
        · exact ⟨(i : ℝ) * polygonStepSize n, Or.inr hdir, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        rcases hs with hs | hs
        · refine ⟨0, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)), ?_⟩
          simp only [Set.mem_singleton_iff] at hs
          simp [hs]
        · obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn' s).1 hs
          exact ⟨i, Finset.mem_coe.2 (Finset.mem_range.2 (Finset.mem_Ioo.1 hi).2), rfl⟩
    rw [himagegrid, Measure.restrict_apply
      (((Set.finite_singleton (0 : ℝ)).union
        (rightAngleSet n hn').directions.finite_toSet).image
          (fun s : ℝ ↦ (s : Real.Angle))).measurableSet.compl,
      Set.inter_comm]
    have hsupp := surfaceAreaMeasure_rightAngle_compl_grid_eq_zero n hn' P
    rw [hPK] at hsupp
    exact hsupp
  · -- the atom bound at each grid point
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    refine le_trans (Measure.restrict_apply_le _ _) ?_
    exact maximumPolygonCap_surfaceAtom_le_lintegral_cell n hn' K hK0
      ((i : ℝ) * polygonStepSize n) (hgriddir i hi') (hcellIcc i hi')
  · -- only grid points inside `S` contribute
    intro i hi hmem
    have hi' : i < n := Finset.mem_range.1 hi
    obtain ⟨s, hsS, hseq⟩ := hmem
    have hs : s = (i : ℝ) * polygonStepSize n :=
      hinj (hST hsS) (hgridmem i hi') hseq
    exact Finset.mem_filter.2 ⟨hi, hs ▸ hsS⟩

/-! ### Passing to the limit -/

private theorem tendsto_integral_abs_magicDensity_sub_of_dominated
    (f g : ℕ → ℝ → ℝ) (hfi : ∀ i, IntervalIntegrable (f i) volume 0 (Real.pi / 2))
    (hgi : ∀ i, IntervalIntegrable (g i) volume 0 (Real.pi / 2))
    (hlim : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2), |f i t - g i t|)
      atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
      |magicDensity (f i t) - magicDensity (g i t)|) atTop (𝓝 0) := by
  have hsource (i : ℕ) :
      IntervalIntegrable (fun t ↦ |f i t - g i t|) volume 0 (Real.pi / 2) :=
    ((hfi i).sub (hgi i)).norm
  have htarget (i : ℕ) : IntervalIntegrable
      (fun t ↦ |magicDensity (f i t) - magicDensity (g i t)|)
      volume 0 (Real.pi / 2) := by
    apply (hsource i).mono_fun
    · rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      convert ((continuous_magicDensity.comp_aestronglyMeasurable
        (hfi i).aestronglyMeasurable).sub
        (continuous_magicDensity.comp_aestronglyMeasurable
          (hgi i).aestronglyMeasurable)).norm using 1
    · filter_upwards [] with t
      simpa only [Real.norm_eq_abs, abs_abs] using abs_magicDensity_sub_le (f i t) (g i t)
  apply squeeze_zero
  · intro i
    exact intervalIntegral.integral_nonneg (by positivity) (fun _ _ ↦ abs_nonneg _)
  · intro i
    apply intervalIntegral.integral_mono_on (by positivity) (htarget i) (hsource i)
    intro t _
    exact abs_magicDensity_sub_le (f i t) (g i t)
  · exact hlim

private theorem IsBalancedMaximumCap.approximatingPolygonCaps
    (K : RightAngleCapSpace) (hK : IsBalancedMaximumCap K) :
    ∃ (n : ℕ → ℕ) (P : ℕ → RightAngleCapSpace), StrictMono n ∧
      (∀ i, IsMaximumPolygonCapSteps (n i) (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val : Set Point) (K.val : Set Point))
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
        |magicDensity (tangentArmLengths (P i) t).2.1 -
          magicDensity (tangentArmLengths K t).2.1|) atTop (𝓝 0) := by
  obtain ⟨n, hn, hmono, hdyadic, Q, hQmax, hQlim⟩ := hK
  refine ⟨n, fun i ↦ (Q i).val, hmono, fun i ↦ ⟨hn i, hdyadic i, Q i, rfl, hQmax i⟩,
    hQlim, ?_⟩
  apply tendsto_integral_abs_magicDensity_sub_of_dominated
    (fun i t ↦ (tangentArmLengths ((Q i).val) t).2.1)
    (fun _ t ↦ (tangentArmLengths K t).2.1)
    (fun i ↦ intervalIntegrable_tangentArm_fst _)
    (fun i ↦ intervalIntegrable_tangentArm_fst K)
  exact polygonCap_arm_integral_limit (fun i ↦ (Q i).val) K hQlim

/-- The limit of the discrete inequalities on a compact subset of the rotation interval. -/
private theorem balancedMaximumCap_surface_isCompact_le (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) {C : Set ℝ} (hC : IsCompact C)
    (hCT : C ⊆ Ico (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
      armDensityMeasure K C := by
  have hpi := Real.pi_pos
  obtain ⟨n, P, hmono, hPmax, hPlim, hL1⟩ :=
    IsBalancedMaximumCap.approximatingPolygonCaps K hK
  set err : ℕ → ℝ := fun i ↦ ∫ t in (0 : ℝ)..(Real.pi / 2),
    |magicDensity (tangentArmLengths (P i) t).2.1 -
      magicDensity (tangentArmLengths K t).2.1| with herrdef
  have herr0 : ∀ i, 0 ≤ err i := fun i ↦
    intervalIntegral.integral_nonneg (by positivity) fun t _ ↦ abs_nonneg _
  have hδpos : ∀ i, 0 < polygonStepSize (n i) := by
    intro i
    obtain ⟨hn', _⟩ := hPmax i
    have hnR : (0 : ℝ) < n i := by
      have : 0 < n i := lt_of_lt_of_le zero_lt_two hn'
      exact_mod_cast this
    exact div_pos (by linarith) hnR
  have hδtend : Tendsto (fun i ↦ polygonStepSize (n i)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2)).comp
      hmono.tendsto_atTop
    simpa only [polygonStepSize, Function.comp_def] using h
  -- weak convergence of the surface measures
  let μs : ℕ → FiniteMeasure Real.Angle := fun i ↦
    ⟨surfaceAreaMeasure (P i).val, (surfaceAreaMeasure_face_union (P i).val).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure K.val, (surfaceAreaMeasure_face_union K.val).1⟩
  have hweak : Tendsto μs atTop (𝓝 μ) := by
    apply MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity (fun i ↦ (P i).val) K.val hPlim f f.continuous
  -- the estimate at every positive thickening radius
  have hkey : ∀ η : ℝ, 0 < η →
      surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
        armDensityMeasure K (Metric.thickening (2 * η) C) := by
    intro η hη
    set V := (Metric.thickening η C ∩ Ioo (-(Real.pi / 2)) (Real.pi / 2)) ∪
      Ioo (-(Real.pi / 2)) 0 with hVdef
    have hVopen : IsOpen V :=
      (Metric.isOpen_thickening.inter isOpen_Ioo).union isOpen_Ioo
    have hCV : C ⊆ V := by
      intro x hx
      exact Or.inl ⟨Metric.self_subset_thickening hη C hx,
        ⟨by linarith [(hCT hx).1], (hCT hx).2⟩⟩
    have hVsubIoo : V ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro x (hx | hx)
      · exact hx.2
      · exact ⟨hx.1, by linarith [hx.2]⟩
    have hVsubThick : V ∩ Ico (0 : ℝ) (Real.pi / 2) ⊆ Metric.thickening η C := by
      rintro x ⟨hxV, hxI⟩
      rcases hxV with hx | hx
      · exact hx.1
      · exact absurd hxI.1 (by simpa using hx.2)
    have hVmeas : MeasurableSet (V ∩ Ico (0 : ℝ) (Real.pi / 2)) :=
      hVopen.measurableSet.inter measurableSet_Ico
    have hφVopen : IsOpen ((fun t : ℝ ↦ (t : Real.Angle)) '' V) :=
      QuotientAddGroup.isOpenMap_coe _ hVopen
    have hstep1 : surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' C) ≤
        Filter.liminf (fun i ↦ surfaceAreaMeasure (P i).val
          ((fun t : ℝ ↦ (t : Real.Angle)) '' V)) atTop := by
      refine le_trans (measure_mono (Set.image_mono hCV)) ?_
      exact FiniteMeasure.le_liminf_measure_open_of_tendsto (μ := μ) (μs := μs)
        hweak hφVopen
    have hev : ∀ᶠ i in atTop, surfaceAreaMeasure (P i).val
        ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ≤
        armDensityMeasure K (Metric.thickening (2 * η) C) +
          ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i)) := by
      filter_upwards [hδtend.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity))]
        with i hi
      obtain ⟨hn', hdy, Q, hQK, hQmax⟩ := hPmax i
      have hQval : Q.val.val = (P i).val := by rw [hQK]
      have hneg : surfaceAreaMeasure (P i).val
          ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) = 0 := by
        rw [← hQval]
        exact surfaceAreaMeasure_rightAngle_Ioo_neg_eq_zero (n i) hn' Q
      have hsplit : ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ⊆
          ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) ∪
            ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) := by
        rintro u ⟨x, hxV, rfl⟩
        rcases lt_or_ge x 0 with hx | hx
        · exact Or.inr ⟨x, ⟨(hVsubIoo hxV).1, hx⟩, rfl⟩
        · exact Or.inl ⟨x, ⟨hxV, ⟨hx, (hVsubIoo hxV).2⟩⟩, rfl⟩
      have hthick : Metric.thickening (2 * polygonStepSize (n i))
          (V ∩ Ico (0 : ℝ) (Real.pi / 2)) ⊆ Metric.thickening (2 * η) C := by
        calc
          Metric.thickening (2 * polygonStepSize (n i))
              (V ∩ Ico (0 : ℝ) (Real.pi / 2)) ⊆
              Metric.thickening (2 * polygonStepSize (n i))
                (Metric.thickening η C) :=
            Metric.thickening_subset_of_subset _ hVsubThick
          _ ⊆ Metric.thickening (2 * polygonStepSize (n i) + η) C :=
            Metric.thickening_thickening_subset _ _ _
          _ ⊆ Metric.thickening (2 * η) C :=
            Metric.thickening_mono (by linarith) C
      calc
        surfaceAreaMeasure (P i).val ((fun t : ℝ ↦ (t : Real.Angle)) '' V) ≤
            surfaceAreaMeasure (P i).val
                ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) +
              surfaceAreaMeasure (P i).val
                ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioo (-(Real.pi / 2)) 0) :=
          (measure_mono hsplit).trans (measure_union_le _ _)
        _ = surfaceAreaMeasure (P i).val
            ((fun t : ℝ ↦ (t : Real.Angle)) '' (V ∩ Ico (0 : ℝ) (Real.pi / 2))) := by
          rw [hneg, add_zero]
        _ ≤ armDensityMeasure (P i) (Metric.thickening (2 * polygonStepSize (n i))
              (V ∩ Ico (0 : ℝ) (Real.pi / 2))) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) :=
          maximumPolygonCap_surface_image_le_thickening (n i) hn' (P i) (hPmax i)
            (V ∩ Ico (0 : ℝ) (Real.pi / 2)) hVmeas Set.inter_subset_right
            (by linarith [hδpos i])
        _ ≤ armDensityMeasure (P i) (Metric.thickening (2 * η) C) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          gcongr
        _ ≤ (armDensityMeasure K (Metric.thickening (2 * η) C) +
              ENNReal.ofReal (err i)) +
            ENNReal.ofReal (13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          gcongr
          exact armDensityMeasure_le_add_l1 (P i) K Metric.isOpen_thickening.measurableSet
        _ = armDensityMeasure K (Metric.thickening (2 * η) C) +
            ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i)) := by
          rw [ENNReal.ofReal_add (herr0 i)
            (mul_nonneg (by positivity) (hδpos i).le), add_assoc]
    have htend : Tendsto (fun i ↦ armDensityMeasure K (Metric.thickening (2 * η) C) +
        ENNReal.ofReal (err i + 13 * (Real.pi / 2) * polygonStepSize (n i))) atTop
        (𝓝 (armDensityMeasure K (Metric.thickening (2 * η) C))) := by
      have hsum : Tendsto (fun i ↦ err i + 13 * (Real.pi / 2) * polygonStepSize (n i))
          atTop (𝓝 0) := by
        have h13 : Tendsto (fun i ↦ 13 * (Real.pi / 2) * polygonStepSize (n i))
            atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds (x := 13 * (Real.pi / 2))
            (f := atTop (α := ℕ))).mul hδtend
        simpa using hL1.add h13
      have h0 : Tendsto (fun i ↦ ENNReal.ofReal
          (err i + 13 * (Real.pi / 2) * polygonStepSize (n i))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hsum
      simpa using (tendsto_const_nhds
        (x := armDensityMeasure K (Metric.thickening (2 * η) C))
        (f := atTop (α := ℕ))).add h0
    exact hstep1.trans ((Filter.liminf_le_liminf hev).trans (le_of_eq htend.liminf_eq))
  -- shrink the radius to zero
  have hinter : (⋂ m : ℕ, Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) = C := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hclos : x ∈ closure C := by
        rw [Metric.mem_closure_iff]
        intro r hr
        obtain ⟨m, hm⟩ := exists_nat_gt (2 / r)
        obtain ⟨y, hyC, hy⟩ := Metric.mem_thickening_iff.1 (Set.mem_iInter.1 hx m)
        refine ⟨y, hyC, lt_of_lt_of_le hy ?_⟩
        have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        rw [mul_one_div, div_le_iff₀ hmpos]
        have h2r : 2 / r < (m : ℝ) := hm
        have : 2 < r * (m : ℝ) := by
          rw [div_lt_iff₀ hr] at h2r
          linarith
        nlinarith
      rwa [hC.isClosed.closure_eq] at hclos
    · exact Set.subset_iInter fun m ↦
        Metric.self_subset_thickening (by positivity) C
  have hanti : Antitone (fun m : ℕ ↦ Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) := by
    intro a b hab
    refine Metric.thickening_mono ?_ C
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [mul_one_div, mul_one_div]
    gcongr
  have hfin : ∃ m : ℕ, armDensityMeasure K
      (Metric.thickening (2 * (1 / (m + 1) : ℝ)) C) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    exact ne_top_of_le_ne_top (armDensityMeasure_ne_top K)
      (measure_mono (Set.subset_univ _))
  have hseq := tendsto_measure_iInter_atTop
    (μ := armDensityMeasure K)
    (s := fun m : ℕ ↦ Metric.thickening (2 * (1 / (m + 1) : ℝ)) C)
    (fun m ↦ Metric.isOpen_thickening.measurableSet.nullMeasurableSet) hanti hfin
  rw [hinter] at hseq
  refine ge_of_tendsto hseq (Filter.Eventually.of_forall fun m ↦ ?_)
  exact hkey _ (by positivity)

private theorem exists_isCompact_preimage {E : Set ℝ}
    (hET : E ⊆ Ico (0 : ℝ) (Real.pi / 2)) {F : Set Real.Angle} (hF : IsCompact F)
    (hFE : F ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' E) :
    ∃ C : Set ℝ, IsCompact C ∧ C ⊆ E ∧ F ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' C := by
  have hpi := Real.pi_pos
  have hinj : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Icc (0 : ℝ) (Real.pi / 2)) := by
    apply (Real.Angle.injOn_coe_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith)).mono
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hclosed : IsClosed ((fun t : ℝ ↦ (t : Real.Angle)) ⁻¹' F) :=
    hF.isClosed.preimage Real.Angle.continuous_coe
  refine ⟨(fun t : ℝ ↦ (t : Real.Angle)) ⁻¹' F ∩ Icc 0 (Real.pi / 2),
    isCompact_Icc.inter_left hclosed, ?_, ?_⟩
  · rintro t ⟨htF, htI⟩
    obtain ⟨e, heE, het⟩ := hFE htF
    have : e = t := hinj (Ico_subset_Icc_self (hET heE)) htI het
    exact this ▸ heE
  · intro u hu
    obtain ⟨e, heE, rfl⟩ := hFE hu
    exact ⟨e, ⟨hu, Ico_subset_Icc_self (hET heE)⟩, rfl⟩

end Domination

theorem balancedMaximumCap_surface_domination (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) (E : Set ℝ) (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ico (0 : ℝ) (Real.pi / 2)) :
    surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E) ≤
      ENNReal.ofReal (∫ t in E,
        magicFunctions.1 (Real.toNNReal (tangentArmLengths K t).2.1)) := by
  classical
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hEimage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' E) :=
    measurableSet_coe_image_of_subset_Ico hE hET
  rw [show ENNReal.ofReal (∫ t in E, magicFunctions.1
      (Real.toNNReal (tangentArmLengths K t).2.1)) = armDensityMeasure K E from
    (armDensityMeasure_eq_ofReal_integral K hE hET).symm,
    MeasurableSet.measure_eq_iSup_isCompact hEimage (surfaceAreaMeasure K.val)]
  refine iSup_le fun F ↦ iSup_le fun hFE ↦ iSup_le fun hFcomp ↦ ?_
  obtain ⟨C, hCcomp, hCE, hFC⟩ := exists_isCompact_preimage hET hFcomp hFE
  exact (measure_mono hFC).trans
    ((balancedMaximumCap_surface_isCompact_le K hK hCcomp (hCE.trans hET)).trans
      (measure_mono hCE))

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

* `Cap.DensityExistence`.
* `Cap.Interpolation`.
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
# Existence and uniqueness of the surface densities of a balanced maximum cap

A balanced maximum cap of rotation angle `π / 2` satisfies the density clause of the
injectivity condition: its surface area measure has nonnegative measurable densities on the
quarter arcs `[0, π / 2)` and `(π / 2, π]`, unique up to Lebesgue-null sets.

On the first arc the density comes from the limiting inequality
`balancedMaximumCap_surface_domination` together with the Radon–Nikodym construction
`exists_nnreal_density_of_domination`. On the second arc the mirror image of the cap is again a
balanced maximum cap, and the surface-measure identity of `cap_mirror_features` transports its
first-arc density back along the reflection `a ↦ π - a` of normal angles.

On the first arc the domination inequality also bounds the density: the real density produced by
`exists_capDensity_right_le_magicDensity` is at most `k₀` of the positive tangent arm length.
-/

/-! ### A continuous section of the angular projection -/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MovingSofa

/-- A continuous left inverse of the angle coercion on `[-(π / 2), π / 2]`. -/
private def angleSection (a : Real.Angle) : ℝ := Real.arcsin a.sin

private theorem continuous_angleSection : Continuous angleSection :=
  Real.continuous_arcsin.comp Real.Angle.continuous_sin

private theorem angleSection_coe {t : ℝ} (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    angleSection (t : Real.Angle) = t := by
  rw [angleSection, Real.Angle.sin_coe, Real.arcsin_sin ht.1 ht.2]

/-- After a quarter-turn shift, `angleSection` inverts the angle coercion on `[0, π]`. -/
private theorem angleSection_sub_coe {t : ℝ} (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    angleSection (((t + Real.pi / 2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle)) = t := by
  rw [← Real.Angle.coe_sub, add_sub_cancel_right, angleSection_coe ht]

/-- The second quarter arc, parametrized from `0` by a quarter-turn shift. -/
private theorem image_coe_add_pi_div_two_Ioc :
    (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' Ioc 0 (Real.pi / 2) =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi := by
  rw [show (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
      (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) from rfl,
    Set.image_comp, Set.image_add_const_Ioc, zero_add, add_halves]

/-- If `ψ` inverts `φ` on `S`, then cutting a `ψ`-preimage down to the `φ`-image of `S` is the
same as taking the `φ`-image of the corresponding part of `S`. -/
private theorem preimage_inter_image_eq_image_inter {α β : Type*} {φ : α → β} {ψ : β → α}
    {S : Set α} (hsec : ∀ t ∈ S, ψ (φ t) = t) (E : Set α) :
    ψ ⁻¹' E ∩ φ '' S = φ '' (E ∩ S) := by
  ext a
  constructor
  · rintro ⟨haE, t, ht, rfl⟩
    rw [mem_preimage, hsec t ht] at haE
    exact ⟨t, ⟨haE, ht⟩, rfl⟩
  · rintro ⟨t, ⟨htE, ht⟩, rfl⟩
    exact ⟨by rw [mem_preimage, hsec t ht]; exact htE, t, ht, rfl⟩

/-! ### Densities on an arc from a domination inequality -/

/-- Transport of the bounded-density construction to an arc of normal angles. If the angular
parametrization `φ` has a measurable left inverse on a measurable set `S` that fills
`[0, π / 2]` up to a null set, and the mass that `μ₀` gives to `φ '' E` is dominated by the
integral of a bounded nonnegative function `f` over `E ⊆ S`, then `μ₀` restricted to the arc
`φ '' S` is the pushforward along `φ` of a weighted Lebesgue measure on `S`. -/
private theorem exists_arcDensity_of_domination (μ₀ : Measure Real.Angle) [IsFiniteMeasure μ₀]
    {φ : ℝ → Real.Angle} (hφ : Measurable φ) {ψ : Real.Angle → ℝ} (hψ : Measurable ψ)
    {S : Set ℝ} (hS : MeasurableSet S) (hSae : S =ᵐ[volume] Icc (0 : ℝ) (Real.pi / 2))
    (hSsub : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) (hA : MeasurableSet (φ '' S))
    (hsec : ∀ t ∈ S, ψ (φ t) = t)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))))
    (hf_nonneg : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ S →
      μ₀ (φ '' E) ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      μ₀.restrict (φ '' S) =
        Measure.map φ ((volume.restrict S).withDensity fun t ↦ (r t : ℝ≥0∞)) := by
  classical
  set μ : Measure ℝ := Measure.map ψ (μ₀.restrict (φ '' S)) with hμ
  have hμ_apply : ∀ E : Set ℝ, MeasurableSet E → μ E = μ₀ (φ '' (E ∩ S)) := fun E hE ↦ by
    rw [hμ, Measure.map_apply hψ hE, Measure.restrict_apply (hψ hE),
      preimage_inter_image_eq_image_inter hsec E]
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_apply univ MeasurableSet.univ]
    exact measure_lt_top _ _
  have hμ_compl : μ (Icc (0 : ℝ) (Real.pi / 2))ᶜ = 0 := by
    rw [hμ_apply _ measurableSet_Icc.compl,
      show (Icc (0 : ℝ) (Real.pi / 2))ᶜ ∩ S = ∅ from
        eq_empty_of_subset_empty fun x hx ↦ hx.1 (hSsub hx.2),
      Set.image_empty, measure_empty]
  have hdom' : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Icc (0 : ℝ) (Real.pi / 2) →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t) := by
    intro E hE hEsub
    have hES : E ∩ S =ᵐ[volume] E := by
      have h := Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ E) hSae
      rwa [inter_eq_left.mpr hEsub] at h
    rw [hμ_apply E hE]
    exact (hdom _ (hE.inter hS) inter_subset_right).trans
      (le_of_eq (congrArg ENNReal.ofReal (setIntegral_congr_set hES)))
  obtain ⟨r, hr, hreq⟩ :=
    exists_nnreal_density_of_domination μ hμ_compl f hf hf_nonneg hf_bound hdom'
  refine ⟨r, hr, ?_⟩
  have hmap : Measure.map φ μ = μ₀.restrict (φ '' S) := by
    rw [hμ]
    refine Measure.map_map_of_ae_leftInverse hψ hφ ?_
    filter_upwards [ae_restrict_mem hA] with a ha
    obtain ⟨t, ht, rfl⟩ := ha
    rw [hsec t ht]
  rw [← hmap, hreq, ← Measure.restrict_congr_set hSae]

/-! ### The density on the first arc -/

private theorem exists_capDensity_right (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      (surfaceAreaMeasure K.1).restrict
          ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico 0 (Real.pi / 2)) =
        Measure.map (fun t : ℝ ↦ (t : Real.Angle))
          ((volume.restrict (Ico 0 (Real.pi / 2))).withDensity
            (fun t ↦ (r t : ℝ≥0∞))) := by
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hmeas : AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths K t).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst K
  refine exists_arcDensity_of_domination (surfaceAreaMeasure K.val)
    Real.Angle.continuous_coe.measurable continuous_angleSection.measurable
    measurableSet_Ico Ico_ae_eq_Icc Ico_subset_Icc_self ?_
    (fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩)
    (fun t ↦ magicDensity (tangentArmLengths K t).2.1) hmeas
    (fun t _ ↦ magicDensity_nonneg _)
    (M := (surfaceAreaMeasure K.val).real univ + 1)
    (fun t _ ↦ (magicDensity_le_abs_add_one _).trans
      (by linarith [abs_tangentArm_fst_le K (t := t)]))
    fun E hE hEsub ↦ balancedMaximumCap_surface_domination K hK E hE hEsub
  exact Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
    (by linarith) measurableSet_Ico fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- On the first quarter arc the surface area measure of a balanced maximum cap is the integral
of a real density on the rotation interval which is bounded by the magic density of the positive
tangent arm length. This refines `exists_capDensity_right`, which only records the existence of a
density, by the pointwise bound carried by the limiting inequality
`balancedMaximumCap_surface_domination`. -/
theorem exists_capDensity_right_le_magicDensity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ ρ : ℝ → ℝ, IntegrableOn ρ (Icc 0 (Real.pi / 2)) volume ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)),
        0 ≤ ρ t ∧ ρ t ≤ magicDensity (tangentArmLengths K t).2.1) ∧
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ico 0 (Real.pi / 2) →
        (surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E)).toReal =
          ∫ t in E, ρ t := by
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hsec : ∀ t ∈ Ico (0 : ℝ) (Real.pi / 2), angleSection (t : Real.Angle) = t :=
    fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩
  set μ : Measure ℝ := Measure.map angleSection ((surfaceAreaMeasure K.val).restrict
    ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico 0 (Real.pi / 2))) with hμdef
  have hμ_apply : ∀ E : Set ℝ, MeasurableSet E →
      μ E = surfaceAreaMeasure K.val
        ((fun t : ℝ ↦ (t : Real.Angle)) '' (E ∩ Ico 0 (Real.pi / 2))) := fun E hE ↦ by
    rw [hμdef, Measure.map_apply continuous_angleSection.measurable hE,
      Measure.restrict_apply (continuous_angleSection.measurable hE),
      preimage_inter_image_eq_image_inter hsec E]
  have _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_apply univ MeasurableSet.univ]
    exact measure_lt_top _ _
  have hμ_compl : μ (Icc (0 : ℝ) (Real.pi / 2))ᶜ = 0 := by
    rw [hμ_apply _ measurableSet_Icc.compl,
      show (Icc (0 : ℝ) (Real.pi / 2))ᶜ ∩ Ico 0 (Real.pi / 2) = ∅ from
        eq_empty_of_subset_empty fun x hx ↦ hx.1 (Ico_subset_Icc_self hx.2),
      Set.image_empty, measure_empty]
  have hmeas : AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths K t).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst K
  have hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Icc 0 (Real.pi / 2) →
      μ E ≤ ENNReal.ofReal (∫ t in E, magicDensity (tangentArmLengths K t).2.1) := by
    intro E hE hEsub
    have hES : E ∩ Ico (0 : ℝ) (Real.pi / 2) =ᵐ[volume] E := by
      have h := Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ E)
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))
      rwa [inter_eq_left.mpr hEsub] at h
    rw [hμ_apply E hE]
    exact (balancedMaximumCap_surface_domination K hK _ (hE.inter measurableSet_Ico)
      inter_subset_right).trans
      (le_of_eq (congrArg ENNReal.ofReal (setIntegral_congr_set hES)))
  obtain ⟨ρ, -, hρint, hρle, hρeq⟩ := exists_density_le_of_domination μ hμ_compl
    (fun t ↦ magicDensity (tangentArmLengths K t).2.1) hmeas (fun t _ ↦ magicDensity_nonneg _)
    (M := (surfaceAreaMeasure K.val).real univ + 1)
    (fun t _ ↦ (magicDensity_le_abs_add_one _).trans
      (by linarith [abs_tangentArm_fst_le K (t := t)])) hdom
  refine ⟨ρ, hρint, hρle, fun E hE hEsub ↦ ?_⟩
  have hEIcc : E ⊆ Icc (0 : ℝ) (Real.pi / 2) := hEsub.trans Ico_subset_Icc_self
  have hEint : Integrable ρ (volume.restrict E) := hρint.mono_set hEIcc
  have hEnn : 0 ≤ᵐ[volume.restrict E] ρ :=
    (ae_restrict_of_ae_restrict_of_subset hEIcc hρle).mono fun t h ↦ h.1
  have hEμ : μ E = surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E) := by
    rw [hμ_apply E hE, inter_eq_left.mpr hEsub]
  rw [← hEμ, hρeq, withDensity_apply _ hE, Measure.restrict_restrict_of_subset hEIcc,
    ← ofReal_integral_eq_lintegral_ofReal hEint hEnn]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hEnn)

/-! ### The mirrored cap and the density on the second arc -/

/-- The mirror image of a balanced maximum right-angle cap is again a balanced maximum cap, and
the surface area measure of the cap is obtained from that of its mirror image by reflecting
normal angles through `a ↦ π - a`. -/
private theorem exists_mirror_balancedMaximumCap (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ P : RightAngleCapSpace, IsBalancedMaximumCap P ∧
      ∀ E : Set Real.Angle, MeasurableSet E →
        surfaceAreaMeasure K.val E =
          surfaceAreaMeasure P.val
            ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) := by
  obtain ⟨P, hPset, hPbal⟩ := balancedMaximumCap_mirror K hK
  obtain ⟨Q, hQset, -, -, -, -, hQmeas⟩ := cap_mirror_features K
  have hQP : Q = P := Subtype.ext (ConvexBody.ext (by rw [hQset, hPset]))
  have hF : Function.Involutive (fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) :=
    fun a ↦ sub_sub_cancel _ _
  refine ⟨P, hPbal, fun E hE ↦ ?_⟩
  have hFEmeas : MeasurableSet
      ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) := by
    rw [Set.image_eq_preimage_of_inverse hF hF]
    exact (continuous_const.sub continuous_id).measurable hE
  have himg : (fun a : Real.Angle ↦ ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) - a) ''
      ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) = E := by
    rw [show ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) from
      by rw [add_halves], Set.image_image, show (fun a : Real.Angle ↦
        ((Real.pi : ℝ) : Real.Angle) - (((Real.pi : ℝ) : Real.Angle) - a)) = fun a ↦ a from
      funext hF, Set.image_id']
  have hkey := hQmeas _ hFEmeas
  rw [hQP, himg] at hkey
  exact hkey.symm

private theorem exists_capDensity_left (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ s : ℝ → ℝ≥0, Measurable s ∧
      (surfaceAreaMeasure K.1).restrict
          ((fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi) =
        Measure.map (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
          ((volume.restrict (Ioc 0 (Real.pi / 2))).withDensity
            (fun t ↦ (s t : ℝ≥0∞))) := by
  obtain ⟨P, hPbal, hPmeas⟩ := exists_mirror_balancedMaximumCap K hK
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hrefl : Function.Involutive (fun t : ℝ ↦ Real.pi / 2 - t) := fun t ↦ sub_sub_cancel _ _
  have hmp : MeasurePreserving (fun t : ℝ ↦ Real.pi / 2 - t)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2)))
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    have h := (Measure.measurePreserving_sub_left volume (Real.pi / 2)).restrict_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := Real.pi / 2))
    have hpre : (fun t : ℝ ↦ Real.pi / 2 - t) ⁻¹' Icc (0 : ℝ) (Real.pi / 2) =
        Icc (0 : ℝ) (Real.pi / 2) := by
      ext x
      simp only [mem_preimage, mem_Icc]
      constructor <;> intro hx <;> exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rwa [hpre] at h
  have hmeas : AEStronglyMeasurable (fun u ↦ magicDensity (tangentArmLengths P u).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst P
  have hbound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1 ≤
        (surfaceAreaMeasure P.val).real univ + 1 := by
    intro t _
    refine (magicDensity_le_abs_add_one _).trans ?_
    have harm := abs_tangentArm_fst_le P (t := Real.pi / 2 - t)
    linarith
  rw [← image_coe_add_pi_div_two_Ioc]
  refine exists_arcDensity_of_domination (surfaceAreaMeasure K.val)
    (φ := fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
    (ψ := fun a : Real.Angle ↦ angleSection (a - ((Real.pi / 2 : ℝ) : Real.Angle)))
    (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
    (continuous_angleSection.comp (continuous_id.sub continuous_const)).measurable
    measurableSet_Ioc Ioc_ae_eq_Icc Ioc_subset_Icc_self ?_
    (fun t ht ↦ angleSection_sub_coe ⟨by linarith [ht.1], ht.2⟩)
    (fun t ↦ magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1)
    (hmeas.comp_measurePreserving hmp) (fun t _ ↦ magicDensity_nonneg _) hbound ?_
  · rw [image_coe_add_pi_div_two_Ioc]
    exact Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith) measurableSet_Ioc fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
  · intro E hE hEsub
    have hgmeas : MeasurableSet ((fun t : ℝ ↦ Real.pi / 2 - t) '' E) := by
      rw [Set.image_eq_preimage_of_inverse hrefl hrefl]
      exact (measurable_const.sub measurable_id) hE
    have hgsub : (fun t : ℝ ↦ Real.pi / 2 - t) '' E ⊆ Ico 0 (Real.pi / 2) := by
      rintro u ⟨t, ht, rfl⟩
      exact ⟨by linarith [(hEsub ht).2], by linarith [(hEsub ht).1]⟩
    have hEarc : MeasurableSet
        ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E) := by
      rw [show (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) from rfl,
        Set.image_comp]
      refine Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
        (by linarith) ?_ ?_
      · rw [Set.image_add_right]
        exact (measurable_id.add_const _) hE
      · rintro u ⟨t, ht, rfl⟩
        exact ⟨by linarith [(hEsub ht).1], by linarith [(hEsub ht).2]⟩
    have hmirror : (fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) ''
        ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E) =
        (fun u : ℝ ↦ (u : Real.Angle)) '' ((fun t : ℝ ↦ Real.pi / 2 - t) '' E) := by
      rw [Set.image_image, Set.image_image]
      refine Set.image_congr' fun t ↦ ?_
      show ((Real.pi : ℝ) : Real.Angle) - ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 - t : ℝ) : Real.Angle)
      rw [← Real.Angle.coe_sub]
      congr 1
      ring
    calc surfaceAreaMeasure K.val
          ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E)
        = surfaceAreaMeasure P.val ((fun u : ℝ ↦ (u : Real.Angle)) ''
            ((fun t : ℝ ↦ Real.pi / 2 - t) '' E)) := by rw [hPmeas _ hEarc, hmirror]
      _ ≤ ENNReal.ofReal (∫ t in (fun t : ℝ ↦ Real.pi / 2 - t) '' E,
            magicDensity (tangentArmLengths P t).2.1) :=
          balancedMaximumCap_surface_domination P hPbal _ hgmeas hgsub
      _ = ENNReal.ofReal
            (∫ t in E, magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1) :=
          congrArg ENNReal.ofReal
            ((Measure.measurePreserving_sub_left volume (Real.pi / 2)).setIntegral_image_emb
              (measurableEmbedding_subLeft _) _ E)

/-! ### Uniqueness of the densities -/

/-- Two measurable weights on `S` whose pushforwards along `φ` agree are almost everywhere
equal, provided `φ` has a measurable left inverse on `S`. -/
private theorem ae_eq_of_map_withDensity_eq {S : Set ℝ} (hS : MeasurableSet S)
    {φ : ℝ → Real.Angle} (hφ : Measurable φ) {ψ : Real.Angle → ℝ} (hψ : Measurable ψ)
    (hsec : ∀ t ∈ S, ψ (φ t) = t) {w₁ w₂ : ℝ → ℝ≥0}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂)
    (h : Measure.map φ ((volume.restrict S).withDensity (fun t ↦ (w₁ t : ℝ≥0∞))) =
      Measure.map φ ((volume.restrict S).withDensity (fun t ↦ (w₂ t : ℝ≥0∞)))) :
    w₁ =ᵐ[volume.restrict S] w₂ := by
  have key : ∀ w : ℝ → ℝ≥0,
      Measure.map ψ (Measure.map φ ((volume.restrict S).withDensity
        (fun t ↦ (w t : ℝ≥0∞)))) =
      (volume.restrict S).withDensity (fun t ↦ (w t : ℝ≥0∞)) := by
    intro w
    refine Measure.map_map_of_ae_leftInverse hφ hψ ?_
    filter_upwards [(withDensity_absolutelyContinuous (volume.restrict S)
      (fun t ↦ (w t : ℝ≥0∞))).ae_le (ae_restrict_mem hS)] with t ht
    exact hsec t ht
  have hν : (volume.restrict S).withDensity (fun t ↦ (w₁ t : ℝ≥0∞)) =
      (volume.restrict S).withDensity (fun t ↦ (w₂ t : ℝ≥0∞)) := by
    rw [← key w₁, ← key w₂, h]
  filter_upwards [(withDensity_eq_iff_of_sigmaFinite
    h₁.coe_nnreal_ennreal.aemeasurable h₂.coe_nnreal_ennreal.aemeasurable).mp hν] with t ht
  exact ENNReal.coe_inj.mp ht

/-- A right-angle cap determines its two surface densities up to Lebesgue-null sets: any two
pairs of densities of the same cap agree almost everywhere on `[0, π / 2]`. -/
theorem HasCapDensities.ae_eq {K : RightAngleCapSpace} {r s r' s' : ℝ → ℝ≥0}
    (h : HasCapDensities K r s) (h' : HasCapDensities K r' s') :
    (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
    (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s') := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · rw [← Measure.restrict_congr_set (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))]
    exact ae_eq_of_map_withDensity_eq measurableSet_Ico
      Real.Angle.continuous_coe.measurable continuous_angleSection.measurable
      (fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩)
      h.1 h'.1 (h.2.2.1.symm.trans h'.2.2.1)
  · rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))]
    exact ae_eq_of_map_withDensity_eq measurableSet_Ioc
      (φ := fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (ψ := fun a : Real.Angle ↦ angleSection (a - ((Real.pi / 2 : ℝ) : Real.Angle)))
      (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
      (continuous_angleSection.comp (continuous_id.sub continuous_const)).measurable
      (fun t ht ↦ angleSection_sub_coe ⟨by linarith [ht.1], ht.2⟩)
      h.2.1 h'.2.1 (h.2.2.2.symm.trans h'.2.2.2)

theorem balancedMaximumCap_hasDensities (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ r s : ℝ → NNReal, HasCapDensities K r s ∧
      ∀ r' s', HasCapDensities K r' s' →
        (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
        (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s') := by
  obtain ⟨r, hrmeas, hr⟩ := exists_capDensity_right K hK
  obtain ⟨s, hsmeas, hs⟩ := exists_capDensity_left K hK
  have h : HasCapDensities K r s := ⟨hrmeas, hsmeas, hr, hs⟩
  exact ⟨r, s, h, fun _ _ h' ↦ h.ae_eq h'⟩

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
# Minkowski interpolation of right-angle caps

The cap conditions of `IsCap (π / 2)` and the injectivity condition of
`SatisfiesInjectivityCondition` are preserved by the Minkowski interpolation
`convexBodyCombination t K L = (1 - t) • K + t • L` of two right-angle caps.  Each statement
about the interpolation is phrased for an arbitrary cap whose underlying convex body is that
interpolation, so that it applies both to the cap produced by `isCap_convexBodyCombination`
and to an interpolated cap obtained by choice.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Pointwise unitInterval

namespace MovingSofa

/-- Lowering a point of an interpolated right-angle cap onto the base line keeps it inside,
because the same projection can be applied to both summands. -/
theorem base_projection_mem_convexBodyCombination (t : I) (K L : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (convexBodyCombination t K.val L.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      (convexBodyCombination t K.val L.val : Set Point) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_convexBodyCombination_iff t K.val L.val q).1 hq
  refine (mem_convexBodyCombination_iff t K.val L.val _).2
    ⟨_, K.base_projection_mem ha, _, L.base_projection_mem hb, ?_⟩
  have hcoord : ((1 - (t : ℝ)) • a + (t : ℝ) • b) 1 =
      (1 - (t : ℝ)) * a 1 + (t : ℝ) * b 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hcoord]
  module

/-- Right-angle caps are closed under Minkowski interpolation. -/
theorem isCap_convexBodyCombination (t : I) (K L : RightAngleCapSpace) :
    IsCap (Real.pi / 2) (convexBodyCombination t K.val L.val) := by
  have hsup := supportValue_convexBodyCombination t K.val L.val
  have hbase : supportValue (convexBodyCombination t K.val L.val)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    rw [hsup, K.property.2.2.2.2.2.1, L.property.2.2.2.2.2.1]; ring
  refine ⟨by positivity, le_rfl, ?_, ?_, ?_, hbase,
    hasHalfPlaneRepresentation_of_base_projection _ hbase
      (fun q hq ↦ base_projection_mem_convexBodyCombination t K L hq)⟩
  · rw [hsup, K.property.2.2.1, L.property.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.1, L.property.2.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.2.1, L.property.2.2.2.2.1]; ring

/-- An interpolated right-angle cap carries the interpolated surface densities: its surface
measure is the interpolation of the two surface measures, and pushing a weighted measure
forward is linear in the weight. -/
theorem hasCapDensities_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    {r₁ s₁ r₂ s₂ : ℝ → ℝ≥0} (hK : HasCapDensities K r₁ s₁) (hL : HasCapDensities L r₂ s₂) :
    HasCapDensities M (fun x ↦ (1 - (t : ℝ)).toNNReal * r₁ x + (t : ℝ).toNNReal * r₂ x)
      (fun x ↦ (1 - (t : ℝ)).toNNReal * s₁ x + (t : ℝ).toNNReal * s₂ x) := by
  have hmeasure : surfaceAreaMeasure M.val =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K.val +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L.val := by
    rw [hM]; exact surfaceAreaMeasure_convexBodyCombination t K.val L.val
  refine ⟨(measurable_const.mul hK.1).add (measurable_const.mul hL.1),
    (measurable_const.mul hK.2.1).add (measurable_const.mul hL.2.1), ?_, ?_⟩
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.1, hL.2.2.1]
    exact (Measure.map_withDensity_eq_smul_add_smul _ Real.Angle.continuous_coe.measurable _ _
      hK.1.coe_nnreal_ennreal hL.1.coe_nnreal_ennreal (fun x ↦ by simp [ENNReal.ofReal])).symm
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.2, hL.2.2.2]
    exact (Measure.map_withDensity_eq_smul_add_smul _
      (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable _ _
      hK.2.1.coe_nnreal_ennreal hL.2.1.coe_nnreal_ennreal
      (fun x ↦ by simp [ENNReal.ofReal])).symm

/-- The inner corner of an interpolated cap is the interpolation of the two inner corners. -/
theorem capInnerCorner_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val) (x : ℝ) :
    capInnerCorner M x =
      (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x := by
  simp only [capInnerCorner, (rotatingHallwayParts_formulas _ _).2.1, hM,
    supportValue_convexBodyCombination]
  module

/-- The injectivity condition is inherited by Minkowski interpolations of right-angle caps: the
inner corner interpolates, so its two frame velocity components are the same combinations of
the original ones, and a combination with nonnegative weights summing to one preserves their
strict signs even at the two degenerate weights. -/
theorem satisfiesInjectivityCondition_of_eq_convexBodyCombination {t : I}
    {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    (hK : SatisfiesInjectivityCondition K) (hL : SatisfiesInjectivityCondition L) :
    SatisfiesInjectivityCondition M := by
  obtain ⟨⟨r₁, s₁, hd₁, -⟩, hC₁, hsign₁⟩ := hK
  obtain ⟨⟨r₂, s₂, hd₂, -⟩, hC₂, hsign₂⟩ := hL
  have hcornerfun : capInnerCorner M =
      fun x ↦ (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x :=
    funext (capInnerCorner_of_eq_convexBodyCombination hM)
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  -- A combination of two negative quantities with weights summing to one is negative.
  have hneg : ∀ a b : ℝ, a < 0 → b < 0 → (1 - (t : ℝ)) * a + (t : ℝ) * b < 0 := by
    intro a b ha hb
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]; simpa using ha
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht1 ha.le, mul_neg_of_pos_of_neg h hb]
  have hpos : ∀ a b : ℝ, 0 < a → 0 < b → 0 < (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    intro a b ha hb
    have := hneg (-a) (-b) (by linarith) (by linarith)
    linarith
  -- Density uniqueness needs no proof here: it holds for every right-angle cap.
  have hdens := hasCapDensities_of_eq_convexBodyCombination hM hd₁ hd₂
  refine ⟨⟨_, _, hdens, fun _ _ h' ↦ hdens.ae_eq h'⟩, ?_, ?_⟩
  · rw [hcornerfun]
    exact (hC₁.const_smul _).add (hC₂.const_smul _)
  · intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, hx.2.le⟩
    have hdK := ((hC₁.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdL := ((hC₂.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdM : HasDerivWithinAt (capInnerCorner M)
        ((1 - (t : ℝ)) • derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) x +
          (t : ℝ) • derivWithin (capInnerCorner L) (Set.Icc 0 (Real.pi / 2)) x)
        (Set.Icc 0 (Real.pi / 2)) x := by
      rw [hcornerfun]
      exact (hdK.const_smul (1 - (t : ℝ))).add (hdL.const_smul (t : ℝ))
    rw [hdM.derivWithin (uniqueDiffOn_Icc hpi x hxmem), inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    exact ⟨hneg _ _ (hsign₁ x hx).1 (hsign₂ x hx).1,
      hpos _ _ (hsign₁ x hx).2 (hsign₂ x hx).2⟩

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

* `Bounds.Arm.Regularity`.
* `Bounds.Lower.Sequence`.
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
# Regularity of the arm length function of a balanced maximum cap

For a balanced maximum cap `K` of rotation angle `π / 2` the arm length function `f_K` is
absolutely continuous on `[0, π / 2]` and satisfies `f_K' ≥ m₀ ∘ g_K` almost everywhere on
`(0, π / 2)`.

The argument combines three inputs. The differentiation identity
`positiveArm_stieltjes_surface` for the positive arm length, read on an interval `(0, t]` with
`t < π / 2`, expresses `f_K(t) - f_K(0)` as the integral of `g_K` minus the surface measure of the
arc traversed. The surface measure on that arc has a real density bounded by `k₀ ∘ g_K`, by
`exists_capDensity_right_le_magicDensity`. Together they present `f_K` on `[0, π / 2)` as the
primitive of `w = g_K - ρ`; continuity of `f_K` on the closed interval
(`nondegenerateCap_continuity`) upgrades the representation to `[0, π / 2]`, whence absolute
continuity and `f_K' = w ≥ g_K - k₀ ∘ g_K = m₀ ∘ g_K` almost everywhere.

The module also records the pointwise data accompanying that differential inequality: both arm
length functions of a nondegenerate cap are nonnegative, and the right one has initial value
`f_K(0) = 1`.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A function on the interval subtype `Set.Icc a b`, extended to `ℝ` by zero. -/
def extendIntervalScalar {a b : ℝ} (f : Set.Icc a b → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : t ∈ Set.Icc a b then f ⟨t, h⟩ else 0

/-- Inside its interval the zero extension agrees with the original subtype function. -/
theorem extendIntervalScalar_of_mem {a b : ℝ} (f : Set.Icc a b → ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc a b) : extendIntervalScalar f t = f ⟨t, ht⟩ := by
  classical
  simp only [extendIntervalScalar, dite_eq_left ht]

/-- The right arm length of a nondegenerate right-angle cap at the horizontal normal equals one.
Lowering the contact there onto the base line stays inside the cap and meets the same supporting
line, so the infimum of the tangent heights of that edge is at most zero; the contacts coincide,
so the contact itself has height zero, and the outer corner at that angle has height
`h_K(π / 2) = 1`. -/
theorem tangentArmLengths_right_zero_eq_one (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) : (tangentArmLengths K 0).1.1 = 1 := by
  have hAmem : (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 ∈
      exposedEdge K.val ((0 : ℝ) : Real.Angle) := edgeVertices_fst_mem _ _
  set A : Point := (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 with hAdef
  set B : Point := A - A 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) with hBdef
  -- the lowered contact lies on the same supporting line and on the base line
  have hBline : B ∈ exposedEdge K.val ((0 : ℝ) : Real.Angle) := by
    refine ⟨K.base_projection_mem hAmem.1, ?_⟩
    change inner ℝ B (normalVector ((0 : ℝ) : Real.Angle)) = supportValue K.val _
    rw [hBdef, inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector]
    simp only [sub_zero, Real.cos_pi_div_two, mul_zero, sub_zero]
    exact hAmem.2
  have hBtan : inner ℝ B (tangentVector ((0 : ℝ) : Real.Angle)) = 0 := by
    rw [hBdef, inner_sub_left, real_inner_smul_left, inner_tangentVector_zero,
      ← normalVector_add_pi_div_two_real 0, inner_normalVector_normalVector]
    norm_num
  -- the two contacts coincide, so the edge is a single point of height zero
  have hcontact := (capDensities_contact_eq K hD).1 0 ⟨le_rfl, by positivity⟩
  have hAeq : A = (edgeVertices K.val ((0 : ℝ) : Real.Angle)).2 := hcontact.1
  have hA1le : A 1 ≤ 0 := by
    have h1 : A 1 = sInf ((fun p ↦ inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle))) ''
        exposedEdge K.val ((0 : ℝ) : Real.Angle)) := by
      rw [← inner_tangentVector_zero A, hAeq, inner_edgeVertices_snd_tangent]
    rw [h1]
    refine csInf_le ?_ ⟨B, hBline, hBtan⟩
    exact ((isCompact_exposedEdge K.val _).image
      (continuous_id.inner continuous_const)).bddBelow
  have hA1ge : 0 ≤ A 1 := by
    simpa only [inner_normalVector_pi_div_two] using
      K.inner_normalVector_pi_div_two_nonneg hAmem.1
  have hA1 : A 1 = 0 := le_antisymm hA1le hA1ge
  -- the outer corner at the horizontal normal has unit height
  have hy : inner ℝ
      (rotatingHallwayParts (K.val : Set Point) ((0 : ℝ) : Real.Angle)).outerCorner
      (tangentVector ((0 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ (supportingPlacement (K.val : Set Point) ((0 : ℝ) : Real.Angle)
      hallwayParts.outerCorner) _ = 1
    rw [inner_supportingPlacement_tangentVector, Real.Angle.coe_zero, zero_add,
      K.property.2.2.2.1]
    simp [hallwayParts]
  simp only [tangentArmLengths, capVertices, inner_sub_left, hy, ← hAdef,
    inner_tangentVector_zero, hA1, sub_zero]

/-- Both arm length functions of a nondegenerate right-angle cap are nonnegative. -/
theorem nondegenerateCapData_arm_nonneg (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) (t : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (nondegenerateCapData K hD).2.1 t ∧ 0 ≤ (nondegenerateCapData K hD).2.2 t := by
  refine ⟨?_, tangentArm_fst_nonneg K⟩
  simp only [nondegenerateCapData]
  split_ifs
  · exact (tangentArmLengths_right_nonneg K t).2
  · exact (tangentArmLengths_right_nonneg K t).1

/-- Absolute continuity and the almost everywhere derivative of a function `G` that agrees on
`[a, b]` with a function `F` which is a primitive of `w` on the half-open interval `[a, b)`. Only
continuity of `F` at `b` is needed there, so no limit of the primitive has to be computed. -/
private theorem absolutelyContinuousOnInterval_and_ae_hasDerivAt_of_eqOn_Ico
    {a b : ℝ} (hab : a < b) {F G w : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hFw : ∀ t ∈ Set.Ico a b, F t = F a + ∫ y in a..t, w y)
    (hGF : Set.EqOn G F (Set.Icc a b)) :
    AbsolutelyContinuousOnInterval G a b ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b), HasDerivAt G (w t) t := by
  set Φ : ℝ → ℝ := fun x ↦ F a + ∫ y in a..x, w y
  have hΦAC : AbsolutelyContinuousOnInterval Φ a b :=
    ((LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hw.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [hab.le]))
  have hΦcont : ContinuousOn Φ (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab.le] using hΦAC.continuousOn
  have heq : Set.EqOn G Φ (Set.Icc a b) := by
    refine hGF.trans (Set.EqOn.of_subset_closure (fun x hx ↦ hFw x hx) hF hΦcont
      Set.Ico_subset_Icc_self ?_)
    rw [closure_Ico hab.ne]
  refine ⟨hΦAC.congr fun x hx ↦
    (heq (by simpa only [Set.uIcc_of_le hab.le] using hx)).symm, ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hw.ae_hasDerivAt_integral] with x hx hxo
  have hxu : x ∈ Set.uIcc a b := by
    simpa only [Set.uIcc_of_le hab.le] using ⟨hxo.1.le, hxo.2.le⟩
  refine ((hx hxu a (by simp [hab.le])).const_add (F a)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hyo
  exact heq ⟨hyo.1.le, hyo.2.le⟩

/-- The differentiation identity for the positive arm length, restricted to an interval `(0, t]`
with `t < π / 2`: the positive arm length increases by the integral of the positive tangent arm
length minus the surface measure of the arc of normal directions traversed. Restricting to
`t < π / 2` keeps the possibly nonzero top-face atom of the surface measure out of the
identity. -/
private theorem positiveArm_sub_eq_integral_sub_surface (K : RightAngleCapSpace) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths K t).1.1 - (tangentArmLengths K 0).1.1 =
      (∫ u in Set.Ioc (0 : ℝ) t, (tangentArmLengths K u).2.1) -
        (surfaceAreaMeasure K.val
          ((fun u : ℝ ↦ (u : Real.Angle)) '' Set.Ioc (0 : ℝ) t)).toReal := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hle⟩
  have htmem : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, ht.2.le⟩
  obtain ⟨F, hF, hinc⟩ := positiveArm_stieltjes_surface K
  have hzx : (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ≤ ⟨t, htmem⟩ :=
    Subtype.mk_le_mk.mpr ht.1
  have himg : (fun u : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ (u : ℝ)) ''
      Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩ =
      Set.Ioc (0 : ℝ) t := by
    apply Set.eq_of_subset_of_subset
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨hu.1, hu.2⟩
    · intro y hy
      exact ⟨⟨y, ⟨hy.1.le, hy.2.trans ht.2.le⟩⟩, ⟨hy.1, hy.2⟩, rfl⟩
  have himg2 : (fun u : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ ((u : ℝ) : Real.Angle)) ''
      Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩ =
      (fun y : ℝ ↦ (y : Real.Angle)) '' Set.Ioc (0 : ℝ) t := by
    rw [← himg, Set.image_image]
  have hEpos : ∀ y ∈ Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩,
      0 < (y : ℝ) := fun y hy ↦ hy.1
  have h := hinc _ measurableSet_Ioc hEpos
  rw [intervalStieltjesMeasure_Ioc F _ _ hzx, himg, himg2, hF, hF] at h
  push_cast at h ⊢
  linarith [h]

theorem balancedMaximumCap_arm_regularity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      AbsolutelyContinuousOnInterval
        (extendIntervalScalar (nondegenerateCapData K hD).2.1) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
        magicFunctions.2
          (Real.toNNReal (extendIntervalScalar (nondegenerateCapData K hD).2.2 t)) ≤
        deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) t := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hTpos.le
  obtain ⟨rd, sd, hrs, -⟩ := balancedMaximumCap_hasDensities K hK
  have hD : ∃ r s, HasCapDensities K r s := ⟨rd, sd, hrs⟩
  refine ⟨hD, ?_⟩
  obtain ⟨-, -, hFcont, hGcont, -, -, -⟩ := nondegenerateCap_continuity K hD
  -- the continuous representatives of `f_K` and `g_K`, obtained by clamping the parameter
  set fc : ℝ → ℝ :=
    fun t ↦ (nondegenerateCapData K hD).2.1 (Set.projIcc 0 (Real.pi / 2) hle t) with hfcdef
  set gc : ℝ → ℝ :=
    fun t ↦ (nondegenerateCapData K hD).2.2 (Set.projIcc 0 (Real.pi / 2) hle t) with hgcdef
  have hfccont : Continuous fc := hFcont.comp continuous_projIcc
  have hgccont : Continuous gc := hGcont.comp continuous_projIcc
  have hext_f : Set.EqOn (extendIntervalScalar (nondegenerateCapData K hD).2.1) fc
      (Set.Icc 0 (Real.pi / 2)) := by
    intro x hx
    rw [extendIntervalScalar_of_mem _ hx, hfcdef]
    simp only [Set.projIcc_of_mem hle hx]
  have hext_g : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      extendIntervalScalar (nondegenerateCapData K hD).2.2 x = gc x := by
    intro x hx
    rw [extendIntervalScalar_of_mem _ hx, hgcdef]
    simp only [Set.projIcc_of_mem hle hx]
  -- on `[0, π / 2)` the arm length function is the positive arm length `f⁺_K`
  have hfcval : ∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 2), fc x = (tangentArmLengths K x).1.1 := by
    intro x hx
    rw [hfcdef]
    simp only [Set.projIcc_of_mem hle (Set.Ico_subset_Icc_self hx), nondegenerateCapData,
      ite_eq_right (ne_of_lt hx.2)]
  have hgcval : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), gc x = (tangentArmLengths K x).2.1 := by
    intro x hx
    rw [hgcdef]
    simp only [Set.projIcc_of_mem hle hx]
    rfl
  have hgcnonneg : ∀ x, 0 ≤ gc x := fun x ↦ by
    rw [hgcdef]
    exact tangentArm_fst_nonneg K
  -- the density of the surface measure on the first arc, bounded by `k₀ ∘ g_K`
  obtain ⟨ρ, hρint, hρle, hρeq⟩ := exists_capDensity_right_le_magicDensity K hK
  set w : ℝ → ℝ := fun t ↦ gc t - ρ t
  have hwint : IntervalIntegrable w volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).2
      ((hgccont.continuousOn.integrableOn_Icc).sub hρint)
  -- the integral representation of the arm length function on `[0, π / 2)`
  have hrepr : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      fc t = fc 0 + ∫ y in (0 : ℝ)..t, w y := by
    intro t ht
    have hIocsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ico 0 (Real.pi / 2) :=
      fun y hy ↦ ⟨hy.1.le, lt_of_le_of_lt hy.2 ht.2⟩
    have hIccsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc 0 (Real.pi / 2) :=
      hIocsub.trans Set.Ico_subset_Icc_self
    have hsplit : (∫ y in Set.Ioc (0 : ℝ) t, w y) =
        (∫ u in Set.Ioc (0 : ℝ) t, gc u) - ∫ y in Set.Ioc (0 : ℝ) t, ρ y :=
      integral_sub (hgccont.continuousOn.integrableOn_Icc.mono_set hIccsub)
        (hρint.mono_set hIccsub)
    have harm : (∫ u in Set.Ioc (0 : ℝ) t, gc u) =
        ∫ u in Set.Ioc (0 : ℝ) t, (tangentArmLengths K u).2.1 :=
      setIntegral_congr_fun measurableSet_Ioc fun u hu ↦ hgcval u (hIccsub hu)
    rw [intervalIntegral.integral_of_le ht.1, hsplit, harm,
      ← hρeq _ measurableSet_Ioc hIocsub, hfcval t ht, hfcval 0 ⟨le_rfl, hTpos⟩]
    linarith [positiveArm_sub_eq_integral_sub_surface K ht]
  -- absolute continuity on `[0, π / 2]` and the almost everywhere derivative on `(0, π / 2)`
  obtain ⟨hAC, hderiv⟩ := absolutelyContinuousOnInterval_and_ae_hasDerivAt_of_eqOn_Ico
    hTpos hfccont.continuousOn hwint hrepr hext_f
  refine ⟨hAC, ?_⟩
  have hρIoo : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 ≤ ρ t ∧ ρ t ≤ magicDensity (tangentArmLengths K t).2.1 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self hρle
  filter_upwards [hderiv, hρIoo, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
  have h3' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self h3
  rw [h1.deriv, hext_g t h3']
  have hval : magicFunctions.2 (Real.toNNReal (gc t)) = gc t - magicDensity (gc t) := by
    simp only [magicDensity, magicFunctions, Real.coe_toNNReal _ (hgcnonneg t)]
  have hw : w t = gc t - ρ t := rfl
  rw [hval, hw, hgcval t h3']
  linarith [h2.2]

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
# Bounds / Lower / Sequence
-/

public section

noncomputable section

namespace MovingSofa

/-- The nonnegative-real version of the continuous lower-bound profile. -/
def nonnegativeLowerBoundProfile (c : Set.Icc (0 : ℝ) 1) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal) where
  toFun x := Real.toNNReal (lowerBoundProfile c x)
  continuous_toFun := continuous_real_toNNReal.comp (lowerBoundProfile c).continuous

theorem armIntegralOperator_monotone
    (f g : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal))
    (hfg : ∀ x, f x ≤ g x) :
    ∀ x, armIntegralOperator f x ≤ armIntegralOperator g x := by
  have hc (k : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)) :
      Continuous (fun u : ℝ ↦ magicFunctions.2
        (k (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))) := by
    unfold magicFunctions
    fun_prop
  intro x
  change (1 : ℝ) + _ ≤ 1 + _
  apply add_le_add le_rfl
  exact intervalIntegral.integral_mono x.property.1
    ((hc f).intervalIntegrable _ _) ((hc g).intervalIntegrable _ _)
    (fun u ↦ magicFunctions_snd_monotone (hfg _))

private theorem magicFunction_eq_affine_of_mem_Icc (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    magicFunctions.2 (Real.toNNReal y) = 3 / 2 * y - 1 := by
  simp only [magicFunctions, Real.toNNReal_of_nonneg hy0, NNReal.coe_mk, abs_of_nonpos (by
    linarith : y - 1 ≤ 0), neg_sub]
  rw [max_eq_right (by linarith)]
  ring

private theorem armIntegralOperator_nonnegativeLowerBoundProfile_eq
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 2 / 3)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
  armIntegralOperator (nonnegativeLowerBoundProfile ⟨c, ⟨hc, by linarith⟩⟩) x =
    1 - (x : ℝ) + (3 / 2) *
      (∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c) := by
  have hintegrand (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) (x : ℝ)) :
      magicFunctions.2
          ((nonnegativeLowerBoundProfile ⟨c, hc, by linarith⟩)
            (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u))) =
        3 / 2 * max (1 - (Real.pi / 2 - u)) c - 1 := by
    rw [Set.uIcc_of_le x.property.1] at hu
    have hu0 : 0 ≤ u := hu.1
    have huT : Real.pi / 2 - u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hu.2, x.property.2, Real.pi_pos]
    rw [Set.projIcc_of_mem (by positivity) huT]
    apply magicFunction_eq_affine_of_mem_Icc
    · exact le_max_of_le_right hc
    · apply max_le
      · linarith [huT.1]
      · linarith
  change
    (1 + ∫ u in (0 : ℝ)..(x : ℝ),
        magicFunctions.2
          ((nonnegativeLowerBoundProfile ⟨c, ⟨hc, by linarith⟩⟩)
            (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))) = _
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  rw [intervalIntegral.integral_congr (fun u hu ↦ hintegrand u hu)]
  have hsplit :
      (∫ u in (0 : ℝ)..(x : ℝ), 3 / 2 * max (1 - (Real.pi / 2 - u)) c - 1) =
        (3 / 2) * (∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c) - (x : ℝ) := by
    calc
      _ = (∫ u in (0 : ℝ)..(x : ℝ), 3 / 2 * max (1 - (Real.pi / 2 - u)) c) -
            ∫ u in (0 : ℝ)..(x : ℝ), (1 : ℝ) := by
        rw [intervalIntegral.integral_sub ((hcont.const_mul (3 / 2)).intervalIntegrable _ _)
          intervalIntegrable_const]
      _ = _ := by
        nth_rewrite 1 [intervalIntegral.integral_const_mul]
        nth_rewrite 1 [intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        ring
  rw [hsplit]
  ring

private theorem split_le_integral_lowerBoundProfile (c : ℝ) (hc : 0 ≤ c)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) (hsx : Real.pi / 2 - 1 + c ≤ (x : ℝ)) :
    c * (Real.pi / 2 - 1 + c) + (((x : ℝ) + 1 - Real.pi / 2) ^ 2 - c ^ 2) / 2 ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  have hlin (s t : ℝ) :
      (∫ u in s..t, 1 - Real.pi / 2 + u) =
        ((t + 1 - Real.pi / 2) ^ 2 - (s + 1 - Real.pi / 2) ^ 2) / 2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ ↦ 1 - Real.pi / 2)
      (g := fun u : ℝ ↦ u)
      (a := s) (b := t) (intervalIntegrable_const)
      (continuous_id.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, integral_id]
    ring
  let s : ℝ := Real.pi / 2 - 1 + c
  have hq : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := hcont
  have hfirst := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
    (f := fun _ : ℝ ↦ c) (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c)
    (a := (0 : ℝ)) (b := s) (by dsimp [s]; linarith [Real.pi_gt_three])
    (intervalIntegrable_const (μ := MeasureTheory.volume)) (hq.intervalIntegrable _ _)
    (fun u ↦ (le_max_right _ _ : c ≤ max (1 - (Real.pi / 2 - u)) c))
  have hcontlin : Continuous (fun u : ℝ ↦ 1 - Real.pi / 2 + u) := by fun_prop
  have hsecond := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
    (f := fun u : ℝ ↦ 1 - Real.pi / 2 + u)
    (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) (a := s) (b := (x : ℝ)) hsx
    (hcontlin.intervalIntegrable _ _) (hq.intervalIntegrable _ _)
    (fun u ↦ by
      change 1 - Real.pi / 2 + u ≤ max (1 - (Real.pi / 2 - u)) c
      have hu : 1 - Real.pi / 2 + u = 1 - (Real.pi / 2 - u) := by ring
      exact hu.le.trans (le_max_left _ _))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hq.intervalIntegrable (0 : ℝ) s) (hq.intervalIntegrable s (x : ℝ))
  rw [hlin s (x : ℝ)] at hsecond
  have hfirst' : c * s ≤ ∫ u in (0 : ℝ)..s,
      max (1 - (Real.pi / 2 - u)) c := by
    convert hfirst using 1
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have hsum : c * s + ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
    calc
      _ ≤ (∫ u in (0 : ℝ)..s, max (1 - (Real.pi / 2 - u)) c) +
          ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hfirst' (∫ u in s..(x : ℝ),
              max (1 - (Real.pi / 2 - u)) c)
      _ = _ := hadd
  calc
    c * s + (((x : ℝ) + 1 - Real.pi / 2) ^ 2 - c ^ 2) / 2 ≤
        c * s + ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
      dsimp [s] at *
      nlinarith [hsecond]
    _ ≤ _ := hsum

theorem armIntegralOperator_profile_step (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 2 / 3) :
    ∀ x, lowerBoundProfile ⟨c + 1 / 12, by constructor <;> linarith⟩ x ≤
      armIntegralOperator
        (nonnegativeLowerBoundProfile ⟨c, hc, by linarith⟩) x := by
  intro x
  rw [armIntegralOperator_nonnegativeLowerBoundProfile_eq c hc hc' x]
  simp only [lowerBoundProfile, ContinuousMap.coe_mk]
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  have hI : c * (x : ℝ) ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
    have h := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
      (f := fun _ : ℝ ↦ c) (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) x.property.1
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (hcont.intervalIntegrable _ _)
      (fun u ↦ (le_max_right _ _ : c ≤ max (1 - (Real.pi / 2 - u)) c))
    convert h using 1
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  let s : ℝ := Real.pi / 2 - 1 + c
  apply max_le
  · have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
      exact intervalIntegral.integral_nonneg x.property.1
        (fun _ _ ↦ le_max_of_le_right hc)
    linarith
  · have hpi : Real.pi ≤ 22 / 7 := by linarith [Real.pi_lt_d20]
    have hmul : 0 ≤ (22 / 7 - Real.pi) * (2 / 3 - c) :=
      mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hc')
    by_cases hsx : s ≤ (x : ℝ)
    · have hs := split_le_integral_lowerBoundProfile c hc x hsx
      nlinarith [sq_nonneg ((x : ℝ) - (Real.pi / 2 - 1 / 3)),
        sq_nonneg (c - 2 / 21), hmul]
    · have hxs : (x : ℝ) ≤ s := le_of_not_ge hsx
      have hprod : 0 ≤ (s - (x : ℝ)) * (1 - 3 / 2 * c) :=
        mul_nonneg (sub_nonneg.mpr hxs) (by linarith)
      dsimp [s] at hxs hprod ⊢
      nlinarith [hI, sq_nonneg (c - 7 / 6 + Real.pi / 4), hprod, hmul]

private theorem armIntegralOperator_le_sequence_succ (n : ℕ)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    armIntegralOperator (armLowerBoundSequence n) x ≤
      (armLowerBoundSequence (n + 1) x : ℝ) := by
  exact (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (le_max_right _ _))

private theorem lowerBoundProfile_zero_le_one
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    lowerBoundProfile ⟨0, by constructor <;> norm_num⟩ x ≤
      (armLowerBoundSequence 1 x : ℝ) := by
  change max (1 - (x : ℝ)) 0 ≤ _
  simp only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_max,
    NNReal.coe_zero]
  simp only [armIntegralOperator, magicFunctions, ContinuousMap.coe_mk, NNReal.coe_zero, zero_sub,
    abs_neg, abs_one, add_self_div_two, max_self, intervalIntegral.integral_neg,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
    Real.coe_toNNReal', le_max_iff, le_add_neg_iff_add_le, zero_add, Std.le_refl, or_true,
    sup_of_le_right, sup_le_iff, tsub_le_iff_right, and_true]
  by_cases hx : 1 ≤ (x : ℝ)
  · exact Or.inr hx
  · left
    rw [max_eq_left (by linarith)]
    linarith

private theorem lowerBoundProfile_le_sequence_succ (n : ℕ) (hn : n ≤ 9)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    lowerBoundProfile ⟨(n : ℝ) / 12, by
      have hnR : (n : ℝ) ≤ 9 := by exact_mod_cast hn
      constructor
      · positivity
      · linarith⟩ x ≤
      (armLowerBoundSequence (n + 1) x : ℝ) := by
  induction n generalizing x with
  | zero => simpa [lowerBoundProfile] using lowerBoundProfile_zero_le_one x
  | succ n ih =>
      have hn' : n ≤ 9 := by omega
      have hn8 : n ≤ 8 := by omega
      have hn8r : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
      have hprof := armIntegralOperator_profile_step ((n : ℝ) / 12) (by positivity)
        (by nlinarith)
      have hmon := armIntegralOperator_monotone
        (nonnegativeLowerBoundProfile ⟨(n : ℝ) / 12, by
          have hnR : (n : ℝ) ≤ 9 := by exact_mod_cast hn'
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩)
        (armLowerBoundSequence (n + 1)) (by
          intro y
          exact Real.toNNReal_le_iff_le_coe.mpr (ih hn' y))
      have hop : lowerBoundProfile ⟨(n + 1) / 12, by
          have hnR : ((n + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast hn
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩ x ≤
          armIntegralOperator (armLowerBoundSequence (n + 1)) x := by
        have heq : (n : ℝ) / 12 + 1 / 12 = (n + 1) / 12 := by ring
        simpa only [heq] using (hprof x).trans (hmon x)
      simpa only [Nat.cast_add, Nat.cast_one] using
        hop.trans (armIntegralOperator_le_sequence_succ (n + 1) x)

theorem armLowerBoundSequence_threshold :
    ∀ x : Set.Icc (0 : ℝ) (Real.pi / 2), 0 < (x : ℝ) →
      1 < (armLowerBoundSequence 11 x : ℝ) := by
  intro x hx
  let f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal) := ⟨fun _ ↦ 3 / 4, continuous_const⟩
  have hbound (y : Set.Icc (0 : ℝ) (Real.pi / 2)) : f y ≤ armLowerBoundSequence 10 y := by
    have h := lowerBoundProfile_le_sequence_succ 9 (by omega) y
    have hreal : (3 / 4 : ℝ) ≤ (armLowerBoundSequence 10 y : ℝ) := by
      norm_num [lowerBoundProfile] at h
      exact h.2
    exact_mod_cast hreal
  have hmon := armIntegralOperator_monotone f (armLowerBoundSequence 10) hbound x
  have hconst : armIntegralOperator f x = 1 + (x : ℝ) / 8 := by
    norm_num [armIntegralOperator, f, magicFunctions, intervalIntegral.integral_const]
  rw [hconst] at hmon
  have hstep := armIntegralOperator_le_sequence_succ 10 x
  linarith

/-- The mirror reflection turns the right arm length function of a nondegenerate right-angle cap
into the reflected left arm length function of the original cap. At the two endpoints the
prescribed one-sided conventions match: `f⁺` of the mirror at `π / 2 - t = 0` is the terminal
`g⁻`, and `f⁻` of the mirror at `π / 2` is the prescribed `g⁺` at `0`. -/
private theorem nondegenerateCapData_arm_mirror (K P : RightAngleCapSpace)
    (hP : (P.val : Set Point) = mirrorReflection (Real.pi / 2) '' (K.val : Set Point))
    (hDK : ∃ r s, HasCapDensities K r s) (hDP : ∃ r s, HasCapDensities P r s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (nondegenerateCapData P hDP).2.1
        ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩ =
      (nondegenerateCapData K hDK).2.2 ⟨t, ht⟩ := by
  have hT : Real.pi / 2 - t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨h1, h2, -, -⟩ := tangentArms_mirror K P hP (Real.pi / 2 - t) hT
  rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring] at h1 h2
  simp only [nondegenerateCapData]
  split_ifs with hcase
  · exact h2
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 fun h ↦ hcase (by rw [← h]; ring)
    rw [h1]
    exact ((capDensities_contact_eq K hDK).2 t ⟨htpos, ht.2⟩).2.symm

/-- The integral operator is a lower bound for the right arm length function of a balanced
maximum cap, for every continuous profile `f` with `f(π / 2 - u) ≤ g_K(u)`. Absolute continuity
of `f_K` on `[0, t]` turns it into the integral of its derivative, the differential inequality
`f_K' ≥ m₀ ∘ g_K` bounds that derivative from below almost everywhere, and `m₀` is nondecreasing;
the initial value `f_K(0) = 1` supplies the constant term of the operator. -/
private theorem armIntegralOperator_le_nondegenerateCapData_right (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) (hD : ∃ r s, HasCapDensities K r s)
    (f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal))
    (hf : ∀ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      (f ⟨Real.pi / 2 - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩ : ℝ) ≤
        (nondegenerateCapData K hD).2.2 ⟨u, hu⟩)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    armIntegralOperator f ⟨t, ht⟩ ≤ (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := by
  have hTle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  obtain ⟨hD', hAC, hderiv⟩ := balancedMaximumCap_arm_regularity K hK
  -- proof irrelevance retypes the regularity statement for the witness `hD`
  have hACf : AbsolutelyContinuousOnInterval
      (extendIntervalScalar (nondegenerateCapData K hD).2.1) 0 (Real.pi / 2) := hAC
  have hderivf : ∀ᵐ u ∂MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      magicFunctions.2
          (Real.toNNReal (extendIntervalScalar (nondegenerateCapData K hD).2.2 u)) ≤
        deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) u := hderiv
  have hACt := hACf.mono (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hTle]
    exact Set.Icc_subset_Icc le_rfl ht.2)
  have hFTC := hACt.integral_deriv_eq_sub
  have hF0 : extendIntervalScalar (nondegenerateCapData K hD).2.1 0 = 1 := by
    rw [extendIntervalScalar_of_mem _ ⟨le_rfl, hTle⟩]
    simp only [nondegenerateCapData,
      ite_eq_right (ne_of_lt (show (0 : ℝ) < Real.pi / 2 by positivity))]
    exact tangentArmLengths_right_zero_eq_one K hD
  have hFt : extendIntervalScalar (nondegenerateCapData K hD).2.1 t =
      (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := extendIntervalScalar_of_mem _ ht
  have hcont : Continuous (fun u : ℝ ↦ magicFunctions.2
      (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u)))) := by
    unfold magicFunctions
    fun_prop
  -- the integrand of the operator is dominated by the derivative almost everywhere
  have hae : (fun u : ℝ ↦ magicFunctions.2
        (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u)))) ≤ᵐ[
      MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)]
      deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (Set.Ioo_subset_Ioo le_rfl ht.2) hderivf,
      MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u h1 h2
    refine le_trans ?_ h1
    have humem : u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨h2.1.le, h2.2.le.trans ht.2⟩
    have hTu : Real.pi / 2 - u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [humem.2], by linarith [humem.1]⟩
    apply magicFunctions_snd_monotone
    rw [Set.projIcc_of_mem hTle hTu, extendIntervalScalar_of_mem _ humem,
      Real.le_toNNReal_iff_coe_le (nondegenerateCapData_arm_nonneg K hD ⟨u, humem⟩).2]
    exact hf u humem
  have hmono := intervalIntegral.integral_mono_ae_restrict ht.1
    (hcont.intervalIntegrable _ _) hACt.intervalIntegrable_deriv hae
  have hval : armIntegralOperator f ⟨t, ht⟩ =
      1 + ∫ u in (0 : ℝ)..t, magicFunctions.2
        (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u))) := rfl
  rw [hval, ← hFt]
  linarith [hFTC, hmono, hF0]

/-- The simultaneous lower bound for the two arm length functions of a balanced maximum
right-angle cap. The induction on `n` quantifies over every balanced maximum cap, because the
bound for the left arm is obtained by applying the bound for the right arm to the mirror cap. -/
private theorem armLowerBoundSequence_le_nondegenerateCapData (n : ℕ) :
    ∀ (K : RightAngleCapSpace), IsBalancedMaximumCap K →
      ∀ (hD : ∃ r s, HasCapDensities K r s) (t : ℝ)
        (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
        (armLowerBoundSequence n ⟨t, ht⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ ∧
        (armLowerBoundSequence n
            ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.2 ⟨t, ht⟩ := by
  induction n with
  | zero =>
      intro K hK hD t ht
      simpa only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_zero] using
        nondegenerateCapData_arm_nonneg K hD ⟨t, ht⟩
  | succ n ih =>
      -- the bound for the right arm, proved for every balanced maximum cap at once
      have hfirst : ∀ (K : RightAngleCapSpace), IsBalancedMaximumCap K →
          ∀ (hD : ∃ r s, HasCapDensities K r s) (t : ℝ)
            (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
            (armLowerBoundSequence (n + 1) ⟨t, ht⟩ : ℝ) ≤
              (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := by
        intro K hK hD t ht
        have hop := armIntegralOperator_le_nondegenerateCapData_right K hK hD
          (armLowerBoundSequence n) (fun u hu ↦ (ih K hK hD u hu).2) t ht
        simp only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_max,
          Real.coe_toNNReal']
        exact max_le (ih K hK hD t ht).1
          (max_le hop (nondegenerateCapData_arm_nonneg K hD ⟨t, ht⟩).1)
      intro K hK hD t ht
      refine ⟨hfirst K hK hD t ht, ?_⟩
      obtain ⟨P, hP, hPbal⟩ := balancedMaximumCap_mirror K hK
      obtain ⟨r, s, hrs, -⟩ := balancedMaximumCap_hasDensities P hPbal
      have hT : Real.pi / 2 - t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [← nondegenerateCapData_arm_mirror K P hP hD ⟨r, s, hrs⟩ t ht]
      exact hfirst P hPbal ⟨r, s, hrs⟩ (Real.pi / 2 - t) hT

theorem balancedMaximumCap_sequence_bound (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      ∀ (n : ℕ) (t : Set.Icc (0 : ℝ) (Real.pi / 2)),
        (armLowerBoundSequence n t : ℝ) ≤ (nondegenerateCapData K hD).2.1 t ∧
        (armLowerBoundSequence n
          ⟨Real.pi / 2 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.2 t := by
  obtain ⟨r, s, hrs, -⟩ := balancedMaximumCap_hasDensities K hK
  refine ⟨⟨r, s, hrs⟩, fun n t ↦ ?_⟩
  exact armLowerBoundSequence_le_nondegenerateCapData n K hK ⟨r, s, hrs⟩ t t.property

theorem balancedMaximumCap_arm_gt_one (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2), 0 < (t : ℝ) →
        1 < (nondegenerateCapData K hD).2.1 t) ∧
      (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2), (t : ℝ) < Real.pi / 2 →
        1 < (nondegenerateCapData K hD).2.2 t) := by
  obtain ⟨hD, hbound⟩ := balancedMaximumCap_sequence_bound K hK
  refine ⟨hD, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · exact (armLowerBoundSequence_threshold t ht).trans_le (hbound 11 t).1
  · have hT : Real.pi / 2 - (t : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [t.property.1, t.property.2]
    exact (armLowerBoundSequence_threshold ⟨Real.pi / 2 - (t : ℝ), hT⟩
      (by linarith)).trans_le (hbound 11 t).2

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

* `Cap.Injectivity`.
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
# The injectivity condition for balanced maximum caps

Every balanced maximum cap of rotation angle `π / 2` satisfies the injectivity condition: its
surface measure has densities that are unique up to null sets, its inner corner is continuously
differentiable, and the two frame components of the corner velocity have strict signs on the open
rotation interval.

The theorem lives downstream of `MovingSofa/Cap/Regularity.lean` because its inputs
`balancedMaximumCap_hasDensities` and `balancedMaximumCap_arm_gt_one` depend on that module.
-/

public section

noncomputable section

namespace MovingSofa

theorem balancedMaximumCap_injectivity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) : SatisfiesInjectivityCondition K := by
  obtain ⟨hD, hf, hg⟩ := balancedMaximumCap_arm_gt_one K hK
  obtain ⟨-, -, -, -, hC1, -, hderiv⟩ := nondegenerateCap_continuity K hD
  refine ⟨balancedMaximumCap_hasDensities K hK, hC1, fun t ht ↦ ?_⟩
  have hmem : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1.le, ht.2.le⟩
  have hvn : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm]; exact inner_normalVector_tangentVector t
  rw [(hderiv ⟨t, hmem⟩).1.derivWithin (uniqueDiffOn_Icc (by positivity) t hmem)]
  refine ⟨?_, ?_⟩
  · have h := hf ⟨t, hmem⟩ ht.1
    simp only [inner_add_left, real_inner_smul_left, inner_normalVector_self, hvn, mul_one,
      mul_zero, add_zero]
    linarith
  · have h := hg ⟨t, hmem⟩ ht.2
    simp only [inner_add_left, real_inner_smul_left, inner_normalVector_tangentVector,
      inner_tangentVector_self, mul_one, mul_zero, zero_add]
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

* `Gerver.Injectivity`.
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
# Gerver / Injectivity
-/

public section

noncomputable section

namespace MovingSofa

/-- On the rotation interval the inner corner of the cap of Gerver's sofa is the certified
direct Gerver path.  The rotating-hallway coordinates of the inner corner are the cap's two
support values at `t` and `t + π / 2`, and `gerver_capSupport_identification` evaluates those
at the frame coordinates of the paper path. -/
theorem capInnerCorner_eq_paperGerverPath (K : RightAngleCapSpace)
    (hK : (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    capInnerCorner K t = paperGerverPath t := by
  obtain ⟨-, hGeq, -, -, hcapeq, -, hsup⟩ := gerver_capSupport_identification
  -- The certified cap is the outer half-plane cap, so its support values are the paper ones.
  have hKmem : (K.val : Set Point) ∈
      ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)) := by
    refine Or.inl ?_
    rw [hK, hGeq, hcapeq]
  have hangsum : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, add_comm]
  rw [capInnerCorner,
    (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1, hangsum,
    (hsup _ hKmem t ht).1, (hsup _ hKmem t ht).2, add_sub_cancel_right,
    add_sub_cancel_right, inner_normalVector_smul_add_inner_tangentVector_smul]

/-- On the open rotation interval the inner-corner velocity of the cap of Gerver's sofa is the
velocity of the certified direct Gerver path. -/
theorem derivWithin_capInnerCorner_eq_deriv_paperGerverPath (K : RightAngleCapSpace)
    (hK : (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t = deriv paperGerverPath t := by
  have hcorner : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K s = paperGerverPath s :=
    fun _ hs ↦ capInnerCorner_eq_paperGerverPath K hK hs
  rw [derivWithin_congr hcorner (hcorner t ⟨ht.1.le, ht.2.le⟩),
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem paperGerverCap_injectivity :
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      SatisfiesInjectivityCondition K := by
  obtain ⟨K, hKset, r, s, hdens, -, -⟩ := gerver_surface_densities
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K t = paperGerverPath t :=
    fun _ ht ↦ capInnerCorner_eq_paperGerverPath K hKset ht
  refine ⟨K, hKset, ⟨r, s, hdens, fun r' s' h' ↦ hdens.ae_eq h'⟩,
    contDiff_paperGerverPath.contDiffOn.congr hcorner, fun t ht ↦ ?_⟩
  rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K hKset ht]
  exact ⟨(gerver_strict_velocity t ht).2.2.1, (gerver_strict_velocity t ht).2.2.2⟩

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

* `Cap.Special.Domain`.
* `Cap.Special.AreaVariation`.
* `Cap.Tail.Interpolation`.
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
# Cap / Special / Domain
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- Choose the special cap representing a convex body combination, with a fallback to the
first cap. -/
def specialCapCombination (t : I) (K L : SpecialCapSpace) : SpecialCapSpace := by
  classical
  exact if h : ∃ M : SpecialCapSpace,
    M.val.val = convexBodyCombination t K.val.val L.val.val then h.choose else K

theorem specialCap_isConvexDomain :
    (∀ t K L, (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val) ∧
    IsConvexDomain.{0, 0} specialCapCombination ∧
    (∀ K : RightAngleCapSpace, IsBalancedMaximumCap K →
      ∃ L : SpecialCapSpace, L.val = K) ∧
    (∃ K : SpecialCapSpace,
      (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) := by
  -- ### The special class is closed under Minkowski interpolation
  have hclosed : ∀ (t : I) (K L : SpecialCapSpace), ∃ M : SpecialCapSpace,
      M.val.val = convexBodyCombination t K.val.val L.val.val := fun t K L ↦
    ⟨⟨⟨convexBodyCombination t K.val.val L.val.val,
        isCap_convexBodyCombination t K.val L.val⟩,
      satisfiesInjectivityCondition_of_eq_convexBodyCombination rfl K.property.1 L.property.1,
      convexBody_area_superlevel _ _ K.property.2 L.property.2 t⟩, rfl⟩
  have h1 : ∀ (t : I) (K L : SpecialCapSpace), (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val := by
    intro t K L
    have h := hclosed t K L
    rw [specialCapCombination, dite_eq_left h]
    exact h.choose_spec
  -- ### The sofa area functional is bounded by the cap area
  have hfunc : ∀ C : RightAngleCapSpace,
      capAreaFunctional C ≤ ClassicalResults.area (C.val : Set Point) := by
    intro C
    have h : (0 : ℝ) ≤ ClassicalResults.area (capNiche C) := ENNReal.toReal_nonneg
    simp only [capAreaFunctional]
    linarith
  -- ### Gerver's cap is a special cap
  obtain ⟨KG, hKGset, hKGinj⟩ := paperGerverCap_injectivity
  have hstd : IsStandardPosition paperGerverSofa (Real.pi / 2) :=
    gerver_capSupport_identification.2.1 ▸ gerver_capSupport_identification.2.2.1
  have hGfunc : capAreaFunctional KG = ClassicalResults.area paperGerverSofa :=
    capAreaFunctional_eq_sofaArea paperGerverSofa (Real.pi / 2)
      ⟨paperGerverSofa, hstd, gerver_paperNiche_identification.2.2.1.symm⟩ KG hKGset
  have hGbound : (11 : ℝ) / 5 ≤ capAreaFunctional KG := by
    rw [hGfunc, ← gerver_canonical_paper_literal.1]
    exact gerver_area_lower_bound.2
  have hGarea : (11 : ℝ) / 5 ≤ ClassicalResults.area (KG.val : Set Point) :=
    hGbound.trans (hfunc KG)
  refine ⟨h1, ?_, ?_, ⟨⟨KG, hKGinj, hGarea⟩, hKGset⟩⟩
  -- ### The convex-domain structure restricts from the ambient body domain
  · obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
    refine ⟨V, fun K ↦ e K.val.val, ?_, ?_, fun t K L ↦
      (congrArg e (h1 t K L)).trans (hcomb t K.val.val L.val.val)⟩
    · intro K L h
      exact Subtype.ext (Subtype.ext (hinj h))
    · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
      have hb1 : b ≤ 1 := by linarith
      refine ⟨specialCapCombination ⟨b, hb, hb1⟩ K L, ?_⟩
      have hba : 1 - b = a := by linarith
      simpa only [hba] using (congrArg e (h1 ⟨b, hb, hb1⟩ K L)).trans
        (hcomb ⟨b, hb, hb1⟩ K.val.val L.val.val)
  -- ### Every balanced maximum cap is special
  · intro K hK
    refine ⟨⟨K, balancedMaximumCap_injectivity K hK, ?_⟩, rfl⟩
    exact hGbound.trans ((balancedMaximumCap_maximizes_area K hK KG).trans (hfunc K))

/-- The extreme face vertices and the intersections of supporting lines of a special cap are
convex-linear along `specialCapCombination`: the underlying bodies interpolate, and both quantities
are convex-linear in the body. -/
theorem specialCap_maps_linear (t : I) (K L : SpecialCapSpace) :
    (∀ a : Real.Angle,
      (edgeVertices (specialCapCombination t K L).val.val a).1 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).1 +
            (t : ℝ) • (edgeVertices L.val.val a).1 ∧
        (edgeVertices (specialCapCombination t K L).val.val a).2 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).2 +
            (t : ℝ) • (edgeVertices L.val.val a).2) ∧
    ∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (specialCapCombination t K L).val.val (a : Real.Angle)
          (b : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) +
          (t : ℝ) • supportingIntersection L.val.val (a : Real.Angle) (b : Real.Angle) := by
  obtain ⟨-, hev, hsi, -⟩ := convexBody_maps_linear t K.val.val L.val.val
  rw [specialCap_isConvexDomain.1 t K L]
  exact ⟨hev, hsi⟩

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
# Cap / Special / Area Variation
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem specialCapArea_variation :
    IsQuadraticFunctional specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue L.val.val t - supportValue K.val.val t) ∂surfaceAreaMeasure K.val.val := by
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcomb := specialCap_isConvexDomain.1
  -- ### Quadraticity is the ambient bilinear form restricted to the special caps
  refine ⟨⟨fun K L ↦ (1 / 2 : ℝ) * ∫ a : Real.Angle,
      supportValue K.val.val a ∂surfaceAreaMeasure L.val.val, ⟨?_, ?_⟩,
    fun K ↦ harea K.val.val⟩, ?_⟩
  · intro K t L M
    change (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K.val.val a
        ∂surfaceAreaMeasure (specialCapCombination t L M).val.val = _
    rw [hcomb t L M]
    exact hbil.1 K.val.val t L.val.val M.val.val
  · intro M t K L
    change (1 / 2 : ℝ) * ∫ a : Real.Angle,
        supportValue (specialCapCombination t K L).val.val a
        ∂surfaceAreaMeasure M.val.val = _
    rw [hcomb t K L]
    exact hbil.2 M.val.val t K.val.val L.val.val
  intro K L
  -- ### The support difference is integrable against the finite surface area measure
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hint : ∀ M : ConvexBody Point,
      Integrable (supportValue M) (surfaceAreaMeasure K.val.val) := by
    intro M
    have hcont : Continuous (supportValue M) :=
      (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
    exact hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hdiff : Integrable (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
      (surfaceAreaMeasure K.val.val) := (hint L.val.val).sub (hint K.val.val)
  -- ### Interpolating special caps is interpolating convex bodies, so the two segment
  -- functionals are equal as functions and the mixed-area derivative transports
  have hseg : segmentFunctional specialCapCombination
        (fun M : SpecialCapSpace ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point))
        K.val.val L.val.val := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · simp only [segmentFunctional, ht, ↓reduceDIte]
      exact congrArg (fun s : Set Point ↦ ClassicalResults.area s)
        (congrArg (fun M : ConvexBody Point ↦ (M : Set Point)) (hcomb ⟨t, ht⟩ K L))
    · simp only [segmentFunctional, ht, ↓reduceDIte]
  -- ### Both caps have vanishing base support value, so the lower normals contribute nothing
  have hzero := K.val.setIntegral_compl_image_Icc_zero_pi_eq_zero
    (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
    (by rw [K.val.property.2.2.2.2.2.1, L.val.property.2.2.2.2.2.1, sub_zero])
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  rw [convexDirectionalDerivative, hseg,
    ((supportMeasure_mixedArea_symmetry K.val.val L.val.val).2).derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num)),
    ← integral_add_compl hS hdiff, hzero, add_zero]

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
# Cap / Tail / Interpolation
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The cap and both tail bodies are the corresponding convex body combinations. -/
@[expose]
def IsCapTailCombination (t : I) (X Y Z : CapTailSpace) : Prop :=
  Z.cap.val.val = convexBodyCombination t X.cap.val.val Y.cap.val.val ∧
    Z.rightBody = convexBodyCombination t X.rightBody Y.rightBody ∧
    Z.leftBody = convexBodyCombination t X.leftBody Y.leftBody

/-- Choose a cap-tail triple representing componentwise convex combination, with a fallback to
`X`. -/
def capTailCombination (t : I) (X Y : CapTailSpace) : CapTailSpace := by
  classical
  exact if h : ∃ Z, IsCapTailCombination t X Y Z then h.choose else X

theorem capTail_isConvexDomain :
    (∀ t X Y, IsCapTailCombination t X Y (capTailCombination t X Y)) ∧
    IsConvexDomain.{0, 0} capTailCombination := by
  -- A cap-tail triple is determined by its three convex bodies.
  have hext : ∀ X Y : CapTailSpace, X.cap = Y.cap → X.rightBody = Y.rightBody →
      X.leftBody = Y.leftBody → X = Y := by
    intro X Y hcap hright hleft
    revert hcap hright hleft
    obtain ⟨c₁, r₁, l₁, -, -, -, -, -, -⟩ := X
    obtain ⟨c₂, r₂, l₂, -, -, -, -, -, -⟩ := Y
    intro hcap hright hleft
    subst hcap; subst hright; subst hleft
    rfl
  -- Minkowski interpolation is monotone in both of its convex-body arguments.
  have hmono : ∀ (t : I) (A B C D : ConvexBody Point), (A : Set Point) ⊆ (C : Set Point) →
      (B : Set Point) ⊆ (D : Set Point) →
      (convexBodyCombination t A B : Set Point) ⊆
        (convexBodyCombination t C D : Set Point) := by
    intro t A B C D hAC hBD z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_convexBodyCombination_iff t A B z).1 hz
    exact (mem_convexBodyCombination_iff t C D _).2 ⟨x, hAC hx, y, hBD hy, rfl⟩
  -- ### The cap-tail conditions are closed under componentwise Minkowski interpolation
  have hclosed : ∀ (t : I) (X Y : CapTailSpace), ∃ Z, IsCapTailCombination t X Y Z := by
    intro t X Y
    have hKval : (specialCapCombination t X.cap Y.cap).val.val =
        convexBodyCombination t X.cap.val.val Y.cap.val.val :=
      specialCap_isConvexDomain.1 t X.cap Y.cap
    have hlin : ∀ (K L : ConvexBody Point) (a : Real.Angle),
        supportValue (convexBodyCombination t K L) a =
          (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a :=
      fun K L ↦ (convexBody_maps_linear t K L).1
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
    have hb : ∀ a b c d : ℝ, a + b ≤ 1 → c + d ≤ 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) ≤ 1 := by
      intro a b c d h₁ h₂
      nlinarith [mul_le_mul_of_nonneg_left h₁ ht1, mul_le_mul_of_nonneg_left h₂ ht0]
    have he : ∀ a b c d : ℝ, a + b = 1 → c + d = 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) = 1 := by
      intro a b c d h₁ h₂
      linear_combination (1 - (t : ℝ)) * h₁ + (t : ℝ) * h₂
    refine ⟨⟨specialCapCombination t X.cap Y.cap,
      convexBodyCombination t X.rightBody Y.rightBody,
      convexBodyCombination t X.leftBody Y.leftBody,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, hKval, rfl, rfl⟩
    · rw [hKval]
      exact hmono t _ _ _ _ X.right_subset Y.right_subset
    · rw [hKval]
      exact hmono t _ _ _ _ X.left_subset Y.left_subset
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.right_bound s hs) (Y.right_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.right_eq s hs) (Y.right_eq s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.left_bound s hs) (Y.left_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.left_eq s hs) (Y.left_eq s hs)
  -- ### The totalized selection therefore always matches
  have h1 : ∀ (t : I) (X Y : CapTailSpace),
      IsCapTailCombination t X Y (capTailCombination t X Y) := by
    intro t X Y
    have h := hclosed t X Y
    rw [capTailCombination, dite_eq_left h]
    exact h.choose_spec
  refine ⟨h1, ?_⟩
  -- ### The convex-domain structure is inherited from three copies of the body domain
  obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
  refine ⟨ModuleCat.of ℝ (V × V × V),
    fun X ↦ (e X.cap.val.val, e X.rightBody, e X.leftBody), ?_, ?_, ?_⟩
  · intro X Y h
    simp only [Prod.mk.injEq] at h
    exact hext X Y (Subtype.ext (Subtype.ext (hinj h.1))) (hinj h.2.1) (hinj h.2.2)
  · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩ a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have hba : 1 - b = a := by linarith
    obtain ⟨hc, hr, hl⟩ := h1 ⟨b, hb, hb1⟩ X Y
    refine ⟨capTailCombination ⟨b, hb, hb1⟩ X Y, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hba] using (congrArg e hc).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hr).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hl).trans (hcomb ⟨b, hb, hb1⟩ _ _)
  · intro t X Y
    obtain ⟨hc, hr, hl⟩ := h1 t X Y
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨(congrArg e hc).trans (hcomb t _ _), (congrArg e hr).trans (hcomb t _ _),
      (congrArg e hl).trans (hcomb t _ _)⟩

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

* `Cap.InnerCornerVariation`.
* `Cap.CornerModuloLinear`.
* `Cap.Tail.AreaBounds`.
* `Cap.UpperBoundaryTracing`.
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
# The inner-corner variation on the middle window

On the middle window `I = [φᴿ, φᴸ]` the inner corner of a special cap is
`(h_K(t) - 1) • u_t + (h_K(t + π/2) - 1) • v_t`, an affine expression in two support values, so it
depends convex-linearly on the cap. `capInnerCorner_variation` pulls the quadratic curve-area
functional back along that convex-linear map, which gives quadraticity of
`K ↦ 𝒥(x_K|_I)` and reduces its directional derivative to the curve-variation formula.

The remaining work is to recognize the two mixed Stieltjes integrals of that formula as the
pairing of the support increment against the corner measure. The inner corner is `C¹` on the cap
domain by the injectivity condition, so its Stieltjes measure is its classical velocity times
Lebesgue measure; the frame identity `planeCrossProduct_eq_inner_frame` then turns the pointwise
cross product into the corner density against the support increment, on `I` and on `I + π/2`
separately.
-/

/-! ### The middle window -/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The two distinguished Gerver angles are positive, ordered, and below `π / 2`, so the middle
window `[φᴿ, φᴸ]` and its quarter turn are disjoint subsets of `[0, π]`. -/
private theorem middleWindow_bounds :
    0 < paperGerverConstants.2.1 ∧ paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 ∧
      paperGerverConstants.2.2 < Real.pi / 2 := by
  obtain ⟨hr, hl, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hle : paperGerverConstants.2.1 ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  exact ⟨hr.1, by linarith only [hle, hsum], hl.2⟩

/-- The middle window lies inside the cap's angular domain. -/
private theorem middleWindow_subset :
    Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ⊆ Set.Icc 0 (Real.pi / 2) := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  exact Set.Icc_subset_Icc hrpos.le hlpi.le

/-! ### Regularity of the inner corner of a special cap -/

/-- The inner corner of a special cap is continuously differentiable on the cap domain. -/
private theorem specialCap_contDiffOn (K : SpecialCapSpace) :
    ContDiffOn ℝ 1 (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1

/-- At an interior time the inner corner of a special cap has an honest derivative. -/
private theorem specialCap_hasDerivAt (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (capInnerCorner K.val)
      (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t :=
  ((specialCap_contDiffOn K).differentiableOn one_ne_zero t
    (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-! ### The corner density on the two middle windows -/

/-- On the right middle window the corner density is the tangent velocity component. -/
private theorem capCornerDensity_eq_right (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    capCornerDensity K s = (capVelocityCoefficients K s).2 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  rw [capCornerDensity, ite_eq_left ⟨lt_of_lt_of_le hrpos hs.1, hs.2.trans hlpi.le⟩]

/-- On the left middle window the corner density is the shifted normal velocity component. -/
private theorem capCornerDensity_eq_left (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2)) :
    capCornerDensity K s = -(capVelocityCoefficients K (s - Real.pi / 2)).1 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have h1 : Real.pi / 2 < s := by linarith [hs.1]
  have h2 : s ≤ Real.pi := by linarith [hs.2]
  rw [capCornerDensity, ite_eq_right (by rintro ⟨-, h⟩; linarith), ite_eq_left ⟨h1, h2⟩]

/-- The corner density is nonnegative on the middle windows, by the injectivity signs. -/
private theorem capCornerDensity_nonneg_middle (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :
    0 ≤ capCornerDensity K s := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have hsign := K.property.1.2.2
  rcases hs with hs | hs
  · rw [capCornerDensity_eq_right K hs]
    exact (hsign s ⟨lt_of_lt_of_le hrpos hs.1, lt_of_le_of_lt hs.2 hlpi⟩).2.le
  · rw [capCornerDensity_eq_left K hs]
    have hmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact neg_nonneg.mpr (hsign _ hmem).1.le

/-- The corner density is continuous on each of the two middle windows. -/
private theorem continuousOn_capCornerDensity_middle (K : SpecialCapSpace) :
    ContinuousOn (capCornerDensity K)
        (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) ∧
      ContinuousOn (capCornerDensity K)
        (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)) := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  refine ⟨(hβ.mono middleWindow_subset).congr fun s hs ↦ capCornerDensity_eq_right K hs, ?_⟩
  have hmaps : Set.MapsTo (fun s : ℝ ↦ s - Real.pi / 2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ContinuousOn.congr ?_ fun s hs ↦ capCornerDensity_eq_left K hs
  exact (((hα.mono middleWindow_subset).comp
    (continuous_id.sub continuous_const).continuousOn hmaps)).neg

/-! ### Integrating against the corner angle measure -/

/-- On a parameter window inside `[0, π]` the corner angle measure integrates a continuous
function against the real corner density. -/
private theorem setIntegral_capCornerAngleMeasure (K : SpecialCapSpace) {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hS : S ⊆ Set.Icc 0 Real.pi)
    (hd : AEMeasurable (capCornerDensity K) (volume.restrict S))
    (hdpos : ∀ s ∈ S, 0 ≤ capCornerDensity K s) {f : Real.Angle → ℝ} (hf : Continuous f) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in S, capCornerDensity K s * f (s : Real.Angle) := by
  have hcoe : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hSIoc : S ⊆ Set.Ioc (-1) Real.pi := fun s hs ↦ ⟨by linarith [(hS hs).1], (hS hs).2⟩
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSmeas hSIoc
  have hApre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) := himg.preimage hcoe
  have hAS : ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) ∩ Set.Icc 0 Real.pi = S := by
    refine Set.Subset.antisymm ?_ fun s hs ↦ ⟨⟨s, hs, rfl⟩, hS hs⟩
    rintro x ⟨⟨s, hs, hxs⟩, hx⟩
    have hxIoc : x ∈ Set.Ioc (-1) Real.pi := ⟨by linarith [hx.1], hx.2⟩
    exact (Real.Angle.injOn_coe_Ioc hturn (hSIoc hs) hxIoc hxs) ▸ hs
  have h1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K := by
    rw [capCornerAngleMeasure]
    exact setIntegral_map himg hf.aestronglyMeasurable hcoe.aemeasurable
  have hrestrict : (volume.restrict (Set.Icc 0 Real.pi)).restrict
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) =
      volume.restrict S := by
    rw [Measure.restrict_restrict hApre, hAS]
  have haem : AEMeasurable (fun s ↦ ENNReal.ofReal (capCornerDensity K s))
      ((volume.restrict (Set.Icc 0 Real.pi)).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S))) := by
    rw [hrestrict]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hd
  have h2 : ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        (ENNReal.ofReal (capCornerDensity K s)).toReal • f (s : Real.Angle)
          ∂volume.restrict (Set.Icc 0 Real.pi) := by
    rw [capCornerMeasure]
    exact setIntegral_withDensity_eq_setIntegral_toReal_smul₀ haem
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _ hApre
  rw [h1, h2]
  change ∫ s, _ ∂((volume.restrict (Set.Icc 0 Real.pi)).restrict _) = _
  rw [hrestrict]
  refine setIntegral_congr_fun hSmeas fun s hs ↦ ?_
  rw [ENNReal.toReal_ofReal (hdpos s hs), smul_eq_mul]

/-! ### The middle Stieltjes integrals as weighted Lebesgue integrals -/

/-- The middle corner path's Stieltjes measure has the inner-corner velocity as density. -/
private theorem capMiddle_stieltjesDensity (K : SpecialCapSpace) (i : Fin 2) :
    HasIntervalStieltjesDensity (continuousBVCoordinate (capMiddleBV K) i)
      (fun t ↦ derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  have hproj : ContDiff ℝ 1 fun p : Point ↦ p i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  refine hasIntervalStieltjesDensity_of_hasDerivAt hrl _
    (fun s ↦ capInnerCorner K.val s i) _ (fun _ ↦ rfl) ?_ ?_ ?_
  · refine ContDiffOn.absolutelyContinuousOnInterval ?_
    rw [Set.uIcc_of_le hrl]
    exact hproj.comp_contDiffOn ((specialCap_contDiffOn K).mono middleWindow_subset)
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hrpos.trans ht.1, ht.2.trans hlpi⟩
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (specialCap_hasDerivAt K ht')
  · exact (((PiLp.continuous_apply 2 _ i).comp_continuousOn
      ((continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset))).integrableOn_compact
        isCompact_Icc

/-- A mixed Stieltjes integral over the middle window is the corresponding weighted Lebesgue
integral of the inner-corner velocity. -/
private theorem capMiddle_stieltjesIntegral_eq (K L : SpecialCapSpace) (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate (capMiddleBV K) i)
        (fun t ↦ (capMiddleBV L).val t j - (capMiddleBV K).val t j) Set.univ =
      ∫ t in Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        (capInnerCorner L.val t j - capInnerCorner K.val t j) *
          derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i := by
  have hq : Continuous fun t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ↦
      (capMiddleBV L).val t j - (capMiddleBV K).val t j :=
    ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV L).property.1).sub
      ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV K).property.1)
  have hval : ∀ (M : SpecialCapSpace)
      (t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (capMiddleBV M).val t = capInnerCorner M.val t.val := fun _ _ ↦ rfl
  rw [intervalStieltjesIntegral_eq_integral_mul_of_density _ (capMiddle_stieltjesDensity K i)
    hq Set.univ MeasurableSet.univ, Measure.restrict_univ]
  simp only [hval]
  have key := MeasureTheory.integral_subtype_preimage (μ := volume)
    (s := Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) measurableSet_Icc
    (MeasurableSet.univ (α := ℝ))
    (fun t : ℝ ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
      derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ] at key
  exact key

/-! ### The variation of the inner corner -/

theorem capInnerCorner_variation :
    IsConvexLinear specialCapCombination bvPathCombination capMiddleBV ∧
    IsQuadraticFunctional specialCapCombination (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ curveAreaFunctional (capMiddleBV M)) K L =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue L.val.val t - supportValue K.val.val t) ∂capCornerAngleMeasure K) +
        (segmentArea (distinguishedCapSides K.val).2.corner
            (distinguishedCapSides L.val).2.corner -
          segmentArea (distinguishedCapSides K.val).1.corner
            (distinguishedCapSides L.val).1.corner) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  -- ### The middle corner path is convex-linear
  have hlinear : IsConvexLinear specialCapCombination bvPathCombination capMiddleBV := by
    intro t K L
    refine Subtype.ext (funext fun s ↦ ?_)
    change capInnerCorner (specialCapCombination t K L).val s.val = _
    rw [capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)]
    rfl
  refine ⟨hlinear, (curveArea_variation _ _ hrl).1.comp_isConvexLinear hlinear, ?_⟩
  intro K L
  rw [convexDirectionalDerivative_comp_isConvexLinear hlinear _ K L,
    (curveArea_variation _ _ hrl).2]
  refine congrArg₂ (· + ·) ?_ rfl
  -- ### The middle window and the corner density on it
  have hSmeas : MeasurableSet (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) := measurableSet_Icc.union measurableSet_Icc
  have hSsub : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2) ⊆ Set.Icc 0 Real.pi := by
    have hpi := Real.pi_pos
    rintro s (hs | hs)
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨hdc1, hdc2⟩ := continuousOn_capCornerDensity_middle K
  have hd : AEMeasurable (capCornerDensity K)
      (volume.restrict (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2))) :=
    (hdc1.union_of_isClosed hdc2 isClosed_Icc isClosed_Icc).aemeasurable hSmeas
  have hcont (M : ConvexBody Point) : Continuous fun u : Real.Angle ↦ supportValue M u :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hfcont : Continuous fun u : Real.Angle ↦ supportValue (L.val.val : Set Point) u -
      supportValue (K.val.val : Set Point) u := (hcont L.val.val).sub (hcont K.val.val)
  have hfreal : Continuous fun s : ℝ ↦ supportValue (L.val.val : Set Point) (s : Real.Angle) -
      supportValue (K.val.val : Set Point) (s : Real.Angle) :=
    hfcont.comp Real.Angle.continuous_coe
  -- ### Continuity of the four Lebesgue integrands on the middle window
  have hXc : ContinuousOn (capInnerCorner K.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn K).mono middleWindow_subset).continuousOn
  have hYc : ContinuousOn (capInnerCorner L.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn L).mono middleWindow_subset).continuousOn
  have hDc : ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset
  have hmixed (i j : Fin 2) : IntegrableOn
      (fun t ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
        derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((((PiLp.continuous_apply 2 _ j).comp_continuousOn hYc).sub
      ((PiLp.continuous_apply 2 _ j).comp_continuousOn hXc)).mul
      ((PiLp.continuous_apply 2 _ i).comp_continuousOn hDc)).integrableOn_compact isCompact_Icc
  have hG1 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (hdc1.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hG2 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    (hdc2.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hmaps : Set.MapsTo (fun t : ℝ ↦ t + Real.pi / 2)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hG2' : IntegrableOn (fun t ↦ capCornerDensity K (t + Real.pi / 2) *
      (supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (((hdc2.mul hfreal.continuousOn).comp
      (continuous_id.add continuous_const).continuousOn hmaps)).integrableOn_compact isCompact_Icc
  -- ### Both sides are Lebesgue integrals over the middle window
  rw [capMiddle_stieltjesIntegral_eq K L 1 0, capMiddle_stieltjesIntegral_eq K L 0 1,
    setIntegral_capCornerAngleMeasure K hSmeas hSsub hd
      (fun s hs ↦ capCornerDensity_nonneg_middle K hs) hfcont,
    setIntegral_union (Set.disjoint_left.mpr fun s hs hs' ↦ by linarith [hs.2, hs'.1])
      measurableSet_Icc hG1 hG2,
    integral_Icc_const_add_eq (Real.pi / 2),
    ← integral_sub (hmixed 1 0) (hmixed 0 1), ← integral_add hG1 hG2']
  -- ### The pointwise cross-product identity
  refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
  have hts : t + Real.pi / 2 ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2) := hmaps ht
  have hdens1 : capCornerDensity K t =
      inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle)) := capCornerDensity_eq_right K ht
  have hdens2 : capCornerDensity K (t + Real.pi / 2) =
      -inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) := by
    rw [capCornerDensity_eq_left K hts]
    simp only [add_sub_cancel_right, capVelocityCoefficients]
  have hu : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (normalVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) (t : Real.Angle) -
        supportValue (K.val.val : Set Point) (t : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_normalVector, inner_capInnerCorner_normalVector]
    ring
  have hv : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (tangentVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_tangentVector, inner_capInnerCorner_tangentVector]
    ring
  have hframe := planeCrossProduct_eq_inner_frame
    (capInnerCorner L.val t - capInnerCorner K.val t)
    (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t
  have hs0 : (capInnerCorner L.val t - capInnerCorner K.val t) 0 =
      capInnerCorner L.val t 0 - capInnerCorner K.val t 0 := by simp
  have hs1 : (capInnerCorner L.val t - capInnerCorner K.val t) 1 =
      capInnerCorner L.val t 1 - capInnerCorner K.val t 1 := by simp
  rw [planeCrossProduct, hs0, hs1] at hframe
  rw [hdens1, hdens2, ← hu, ← hv]
  linear_combination hframe

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
# The outer corner and the two wedge segments, modulo convex-linear functionals

On the middle window `I = [φᴿ, φᴸ]` the outer corner of a cap is its inner corner translated by the
`K`-independent frame sum `c t = u_t + v_t`, so the two curve-area functionals differ by the two
mixed Stieltjes cross integrals, each convex-linear in `K`, plus the constant area of `c`.

The same happens at the two ends of the window: the tangent-line intersection point and the wedge
endpoint differ by a fixed vector, as do the outer and the inner corner, so each of the two
segment-area comparisons differs by a determinant that is affine in the support values and in the
inner corner, hence convex-linear in `K` as well.
-/

/-! ### The outer corner path on the middle window -/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The frame sum `t ↦ u_t + v_t`, as a continuous path of bounded variation. -/
def frameSumBV (a b : ℝ) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn
    (fun t ↦ normalVector (t : Real.Angle) + tangentVector (t : Real.Angle))
    ((contDiff_normalVector.add contDiff_tangentVector).of_le
      (by exact_mod_cast le_top)).contDiffOn

/-- The outer corner of a special cap on the middle window, as a continuous path of bounded
variation: the inner-corner path translated by the frame sum. -/
def capOuterMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capMiddleBV K + frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2

/-- The outer middle path of a special cap traces the outer corner of its body. -/
theorem capOuterMiddleBV_val (K : SpecialCapSpace)
    (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    (capOuterMiddleBV K).val s =
      (rotatingHallwayParts (K.val.val : Set Point) ((s : ℝ) : Real.Angle)).outerCorner :=
  (outerCorner_eq_innerCorner_add K.val.val (s : ℝ)).symm

/-! ### The two end segments -/

/-- At the right Gerver angle the tangent-line intersection point is the right wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_fst (K : RightAngleCapSpace)
    (hcos : Real.cos paperGerverConstants.2.1 ≠ 0) :
    supportingIntersection K.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.1).1 +
        !₂[(1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1, 1] := by
  have hangle : ((Real.pi / 2 : ℝ) : Real.Angle) - (paperGerverConstants.2.1 : Real.Angle) =
      ((Real.pi / 2 - paperGerverConstants.2.1 : ℝ) : Real.Angle) := by rw [Real.Angle.coe_sub]
  have hpyth := Real.sin_sq_add_cos_sq paperGerverConstants.2.1
  obtain ⟨hW0, hW1⟩ := wedgeEndpoints_fst_coords K paperGerverConstants.2.1
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, hW0, hW1]
  · field_simp
    linear_combination (supportValue (K.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)) * hpyth
  · field_simp
    ring

/-- At the left Gerver angle the tangent-line intersection point is the left wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_snd (K : RightAngleCapSpace)
    (hsin : Real.sin paperGerverConstants.2.2 ≠ 0) :
    supportingIntersection K.val ((Real.pi / 2 : ℝ) : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.2).2 +
        !₂[(Real.cos paperGerverConstants.2.2 - 1) /
          Real.sin paperGerverConstants.2.2, 1] := by
  have hangle : ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle) = (paperGerverConstants.2.2 : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show Real.pi / 2 + paperGerverConstants.2.2 - Real.pi / 2 =
      paperGerverConstants.2.2 from by ring]
  obtain ⟨hZ0, hZ1⟩ := wedgeEndpoints_snd_coords K paperGerverConstants.2.2
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hZ0, hZ1] <;>
    field_simp <;> ring_nf

/-- A pair of segment areas whose endpoints are fixed translates of a second pair differs from it
by a determinant, which is convex-linear as soon as the two base points are. -/
private theorem segmentArea_equivalent_of_translations {α : Type*} (cα : I → α → α → α)
    {W X P Q : α → Point} {v w : Point} (hP : ∀ K, P K = W K + w) (hQ : ∀ K, Q K = X K + v)
    (hW : ∀ (t : I) (K L : α), W (cα t K L) = (1 - (t : ℝ)) • W K + (t : ℝ) • W L)
    (hX : ∀ (t : I) (K L : α), X (cα t K L) = (1 - (t : ℝ)) • X K + (t : ℝ) • X L) :
    EquivalentModuloConvexLinear cα (fun K ↦ segmentArea (P K) (Q K))
      (fun K ↦ segmentArea (W K) (X K)) := by
  intro t K L
  simp only [hP, hQ, hW, hX, realCombination, segmentArea, planeCrossProduct, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### The main equivalence -/

theorem cornerArea_equivalent_modulo_linear :
    ∃ F : SpecialCapSpace →
        ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2,
      (∀ K, (F K).val = fun t ↦
        (rotatingHallwayParts (K.val.val : Set Point) (t.val : Real.Angle)).outerCorner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ curveAreaFunctional (F K))
        (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.1 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).1.fanPoint
          (distinguishedCapSides K.val).1.corner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).2.fanPoint
          (distinguishedCapSides K.val).2.corner) := by
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl : paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 :=
    paperGerverConstants_snd_fst_lt_snd_snd.le
  refine ⟨capOuterMiddleBV, fun K ↦ funext (capOuterMiddleBV_val K), ?_, ?_, ?_⟩
  -- ### The middle window: translation by the frame-sum path
  · intro t K L
    change curveAreaFunctional (capMiddleBV (specialCapCombination t K L) +
        frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2) -
      curveAreaFunctional (capMiddleBV (specialCapCombination t K L)) = _
    rw [capInnerCorner_variation.1 t K L]
    exact curveArea_translation_convexLinear _ t (capMiddleBV K) (capMiddleBV L)
  -- ### The right end: both endpoints move by fixed vectors
  · have hcos : 0 < Real.cos paperGerverConstants.2.1 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hr.1], hr.2⟩
    simp only [distinguishedCapSides_fst_fanPoint, distinguishedCapSides_fst_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1, 1])
      (v := normalVector (paperGerverConstants.2.1 : Real.Angle) +
        tangentVector (paperGerverConstants.2.1 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_fst K.val hcos.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.1)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.1).1 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.1
  -- ### The left end: the same, with the complementary trigonometric normalisation
  · have hsin : 0 < Real.sin paperGerverConstants.2.2 :=
      Real.sin_pos_of_pos_of_lt_pi hl.1 (by linarith [Real.pi_pos, hl.2])
    simp only [distinguishedCapSides_snd_fanPoint, distinguishedCapSides_snd_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(Real.cos paperGerverConstants.2.2 - 1) / Real.sin paperGerverConstants.2.2, 1])
      (v := normalVector (paperGerverConstants.2.2 : Real.Angle) +
        tangentVector (paperGerverConstants.2.2 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_snd K.val hsin.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.2)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.2).2 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.2

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
# Cap / Tail / Area Bounds
-/

public section

noncomputable section

namespace MovingSofa

/-- A point of a special cap above both the right inner wall at `φᴿ` and the bottom axis that
misses the right canonical tail lies in the niche, on the right side. -/
private theorem mem_capNiche_inter_right_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.1).1)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).1) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane := by
  obtain ⟨hrIoo, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨hmonR, -, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqR : (innerWallUpperHalfPlanes K.val (Real.pi / 2)).1 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    change normalHalfPlane _ (supportValue (K.1.1 : Set Point) _ - 1) true false = _
    rw [K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      q ∉ (innerWallUpperHalfPlanes K.val t).1 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : paperGerverConstants.2.1 < t :=
    ht.1.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hthigh : t < Real.pi / 2 :=
    ht.2.lt_of_ne fun h ↦ hqt (by rw [h, hUpEqR]; exact hup)
  have hmem : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonR t ⟨htlow, ht.2⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨hrIoo.1.trans htlow, hthigh⟩, hmem.2⟩⟩, hwall⟩

/-- A point of a special cap above both the left inner wall at `φᴸ` and the bottom axis that
misses the left canonical tail lies in the niche, on the left side. -/
private theorem mem_capNiche_inter_left_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.2).2)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).2) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane := by
  obtain ⟨-, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨-, hmonL, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqL : (innerWallUpperHalfPlanes K.val 0).2 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    have hzero : ((((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)) =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by rw [zero_add]
    change normalHalfPlane (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (K.1.1 : Set Point) (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle) - 1)
        true false = _
    rw [hzero, K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      q ∉ (innerWallUpperHalfPlanes K.val t).2 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : 0 < t := ht.1.lt_of_ne fun h ↦ hqt (by rw [← h, hUpEqL]; exact hup)
  have hthigh : t < paperGerverConstants.2.2 := ht.2.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hmem : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonL t ⟨ht.1, hthigh⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨htlow, hthigh.trans hlIoo.2⟩, hmem.2⟩⟩, hwall⟩

theorem canonicalTail_niche_area_lower_bounds (K : SpecialCapSpace)
    (B D : ConvexBody Point)
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    segmentArea (rightLeftTailArcs B D).1.startPoint
        (distinguishedCapSides K.val).1.fanPoint -
      convexArcArea B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∧
    segmentArea (distinguishedCapSides K.val).2.fanPoint
        (rightLeftTailArcs B D).2.endPoint -
      convexArcArea D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane) := by
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  obtain ⟨-, -, -, hBsub, -, -, -, hDsub, -, hBeq, -, -, -, hDeq, -, -⟩ :=
    canonicalTailSets_properties K
  -- endpoint support values of the two tails
  have hB1 : supportValue (B : Set Point)
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := hBeq paperGerverConstants.2.1 (by simp)
    rw [hB]
    linarith
  have hB2 : supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hBeq (Real.pi / 2) (by simp)
    rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
    rw [hB]
    linarith
  have hD1 : supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hDeq 0 (by simp)
    rw [hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring),
      hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring), htop] at h
    rw [hD]
    linarith
  have hD2 : supportValue (D : Set Point)
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    have h := hDeq paperGerverConstants.2.2 (by simp)
    rw [hD]
    linarith
  obtain ⟨hOB, hOD, hsegB, hsegD, -, -⟩ :=
    tailFanPoint_identities K.val B D hrIoo hlIoo hB1 hB2 hD1 hD2
  obtain ⟨hWmem, hZmem⟩ := specialCap_wedgeEndpoints_in_bottomEdge K
  have hnichefin : MeasureTheory.volume (capNiche K.val) ≠ ⊤ :=
    ne_of_lt (niche_uniform_bounds.1 _ K.val).2.2.1
  have hRfin : ∀ S : Set Point,
      MeasureTheory.volume (capNiche K.val ∩ S) ≠ ⊤ := fun S ↦
    ne_top_of_le_ne_top hnichefin (MeasureTheory.measure_mono Set.inter_subset_left)
  have hKconv : Convex ℝ (K.1.1 : Set Point) := K.1.1.convex
  have hKclosed : IsClosed (K.1.1 : Set Point) := K.1.1.isCompact.isClosed
  constructor
  · -- right tail
    have hHa : (supportingLineHalfPlane (B : Set Point)
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).1.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show Real.pi + paperGerverConstants.2.1 =
          paperGerverConstants.2.1 + Real.pi by ring), normalVector_add_pi]
      · rw [hB1]; ring
    have hHb : (supportingLineHalfPlane (B : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hB2]; ring
    have hmain := convexArc_tangentRegion_area_le B
      (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)
      (by linarith [hrIoo.2]) (by linarith [hrIoo.1])
      hKconv hKclosed (by rw [hB]; exact hBsub) (by rw [hOB]; exact hWmem.1.1)
      (hRfin _) (fun q hq hqK hqB ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_right_of_notMem_canonicalTail K hq'.1 hq'.2 hqK
          (by rwa [hB] at hqB))
    rw [hOB] at hmain
    rw [show (rightLeftTailArcs B D).1.startPoint =
        (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 from rfl,
      show (distinguishedCapSides K.val).1.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.1).1 from rfl]
    linarith [hmain, hsegB]
  · -- left tail
    have hHa : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hD1]; ring
    have hHb : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).2.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 + paperGerverConstants.2.2 =
          (paperGerverConstants.2.2 + Real.pi / 2) + Real.pi by ring), normalVector_add_pi]
      · rw [hD2, hcast _ _ (show Real.pi / 2 + paperGerverConstants.2.2 =
          paperGerverConstants.2.2 + Real.pi / 2 by ring)]
        ring
    have hmain := convexArc_tangentRegion_area_le D
      (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)
      (by linarith [hlIoo.1]) (by linarith [hlIoo.2])
      hKconv hKclosed (by rw [hD]; exact hDsub) (by rw [hOD]; exact hZmem.1.1)
      (hRfin _) (fun q hq hqK hqD ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_left_of_notMem_canonicalTail K hq'.2 hq'.1 hqK
          (by rwa [hD] at hqD))
    rw [hOD] at hmain
    rw [show (rightLeftTailArcs B D).2.endPoint =
        (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
        from rfl,
      show (distinguishedCapSides K.val).2.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.2).2 from rfl]
    linarith [hmain, hsegD]

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
# Tracing the area of a special cap along its upper boundary

The area of a convex body is half the integral of its support function against its surface area
measure.  For a special cap that measure is carried by the closed upper semicircle of normals,
because the two open quarter arcs of lower normals carry degenerate faces
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`) and the bottom normal carries
support value zero.  The injectivity condition provides angular densities on the two upper quarter
circles, so the four distinguished angles `0`, `φᴿ`, `φᴸ` and `π` are not atoms, and the semicircle
splits — up to a null set — into the four open arcs `(0, φᴿ)`, `(φᴿ, φᴸ)`, `(φᴸ, π / 2)`,
`(π / 2, π)` and the top normal `π / 2`.  Each open arc is shorter than `π`, so the convex arc area
formula applies to it, and the top normal contributes half the mass of a single atom
(`MovingSofa.HasCapDensities.area_eq_upper_arcs_add_top_atom`).  Evaluating the surface area
measure at that fixed angle is convex-linear on the convex domain of special caps, whence the cap
area agrees with the sum of the four arc areas modulo convex-linear functionals
(`MovingSofa.specialCapArea_equivalent_upper_arcs`).
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MovingSofa

/-- On an open arc shorter than `π` the support-area integral is twice the convex arc area. -/
private theorem setIntegral_image_Ioo_eq_two_mul_convexArcArea (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue (K : Set Point) t ∂surfaceAreaMeasure K =
      2 * convexArcArea K a b := by
  rw [(convexArc_area a b hab hba).2.1 K]
  ring

/-- Up to half the mass of the atom at its top normal, the area of a right-angle cap carrying
angular densities is the sum of the areas of the four upper boundary arcs cut out by the two
distinguished Gerver angles. -/
theorem HasCapDensities.area_eq_upper_arcs_add_top_atom {C : RightAngleCapSpace}
    {dr dl : ℝ → ℝ≥0} (hdens : HasCapDensities C dr dl) :
    ClassicalResults.area (C.val : Set Point) =
      (convexArcArea C.val 0 paperGerverConstants.2.1 +
          convexArcArea C.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea C.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea C.val (Real.pi / 2) Real.pi) +
        (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨⟨hrpos, -⟩, ⟨-, hlT⟩, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  set r := paperGerverConstants.2.1
  set l := paperGerverConstants.2.2
  -- ### The surface measure is finite, so the continuous support function is integrable
  have hfinite : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  have hint : Integrable (fun a : Real.Angle ↦ supportValue (C.val : Set Point) a)
      (surfaceAreaMeasure C.val) :=
    ((compactSet_support_continuity (C.val : Set Point) (C.val : Set Point) C.val.nonempty'
      C.val.isCompact' C.val.nonempty' C.val.isCompact').2.2.1).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  -- ### The five pieces of the closed upper semicircle that carry the surface measure
  set U : Set ℝ := Set.Ioo 0 r ∪ Set.Ioo r l ∪ Set.Ioo l (Real.pi / 2) ∪
    Set.Ioo (Real.pi / 2) Real.pi ∪ {Real.pi / 2} with hUdef
  have hs1 : Set.Ioo (0 : ℝ) r ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨hx.1, by linarith [hx.2]⟩
  have hs2 : Set.Ioo r l ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs3 : Set.Ioo l (Real.pi / 2) ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs4 : Set.Ioo (Real.pi / 2) Real.pi ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs5 : ({Real.pi / 2} : Set ℝ) ⊆ Set.Ioc 0 (2 * Real.pi) := by
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUsub : U ⊆ Set.Ioc 0 (2 * Real.pi) :=
    Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
  have hUIcc : U ⊆ Set.Icc 0 Real.pi := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (fun x hx ↦ ⟨hx.1.le, by linarith [hx.2]⟩)
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩)) ?_
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUmeas : MeasurableSet U :=
    (((measurableSet_Ioo.union measurableSet_Ioo).union measurableSet_Ioo).union
      measurableSet_Ioo).union (measurableSet_singleton _)
  -- ### Angular images of disjoint pieces of one turn are disjoint, and Borel pieces stay Borel
  have hdisj : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y →
      Disjoint ((fun t : ℝ ↦ (t : Real.Angle)) '' X)
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := by
    intro X Y hX hY hXY
    rw [Set.disjoint_left]
    rintro a ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' : y = x :=
      Real.Angle.injOn_coe_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) (hY hy) (hX hx) hyx
    exact Set.disjoint_left.mp hXY hx (hyx' ▸ hy)
  have hmimg : ∀ {Y : Set ℝ}, MeasurableSet Y → Y ⊆ Set.Ioc 0 (2 * Real.pi) →
      MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := fun hY hYs ↦
    Real.Angle.measurableSet_image_of_subset_Ioc (by linarith) hY hYs
  -- ### Splitting the last piece off an angular union
  have hstep : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y → MeasurableSet Y →
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' (X ∪ Y),
          supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
        (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' X,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val) +
          ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Y,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val := by
    intro X Y hX hY hXY hmY
    rw [Set.image_union, setIntegral_union (hdisj hX hY hXY) (hmimg hmY hY)
      hint.integrableOn hint.integrableOn]
  -- ### The four distinguished angles of the upper semicircle are not atoms
  have hatom0 : surfaceAreaMeasure C.val {((0 : ℝ) : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨le_rfl, by positivity⟩
  have hatomr : surfaceAreaMeasure C.val {(r : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨hrpos.le, by linarith⟩
  have hatoml : surfaceAreaMeasure C.val {(l : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨by linarith, hlT⟩
  have hatompi : surfaceAreaMeasure C.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    have h := hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
      (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
    rwa [show (Real.pi / 2 + Real.pi / 2 : ℝ) = Real.pi by ring] at h
  -- ### The five pieces cover the upper semicircle up to those four angles
  have hcover : Set.Icc (0 : ℝ) Real.pi ⊆ U ∪ {0, r, l, Real.pi} := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · exact Or.inr (by simp [← h0])
    rcases lt_trichotomy x r with h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h0, h⟩))))
    · exact Or.inr (by simp [h])
    rcases lt_trichotomy x l with h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, h'⟩))))
    · exact Or.inr (by simp [h'])
    rcases lt_trichotomy x (Real.pi / 2) with h'' | h'' | h''
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h', h''⟩)))
    · exact Or.inl (Or.inr h'')
    rcases eq_or_lt_of_le hx.2 with h₃ | h₃
    · exact Or.inr (by simp [h₃])
    · exact Or.inl (Or.inl (Or.inr ⟨h'', h₃⟩))
  have hnull : surfaceAreaMeasure C.val
      ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi \
        (fun t : ℝ ↦ (t : Real.Angle)) '' U) = 0 := by
    refine measure_mono_null (t := {((0 : ℝ) : Real.Angle), (r : Real.Angle), (l : Real.Angle),
      ((Real.pi : ℝ) : Real.Angle)}) ?_ ?_
    · rw [Set.sdiff_subset_iff]
      refine (Set.image_mono hcover).trans ?_
      rw [Set.image_union]
      exact Set.union_subset_union_right _ (by simp [Set.image_insert_eq])
    · simp only [Set.insert_eq]
      exact measure_union_null hatom0
        (measure_union_null hatomr (measure_union_null hatoml hatompi))
  -- ### The support-area integral is carried by the angular image of the five pieces
  have hSmeas : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have htotal : ∫ a, supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val =
      ∫ a in (fun t : ℝ ↦ (t : Real.Angle)) '' U,
        supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val := by
    rw [← integral_add_compl hSmeas hint,
      C.setIntegral_compl_image_Icc_zero_pi_eq_zero _ C.property.2.2.2.2.2.1, add_zero,
      ← Set.union_sdiff_cancel (Set.image_mono hUIcc),
      setIntegral_union Set.disjoint_sdiff_right (hSmeas.diff (hmimg hUmeas hUsub))
        hint.integrableOn hint.integrableOn,
      setIntegral_measure_zero _ hnull, add_zero]
  -- ### The four short arcs contribute their arc areas and the top normal its atom
  have hI1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (0 : ℝ) r,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val 0 r :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrpos (by linarith)
  have hI2 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo r l,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val r l :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrl (by linarith)
  have hI3 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo l (Real.pi / 2),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val l (Real.pi / 2) :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hlT (by linarith)
  have hI4 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (Real.pi / 2) Real.pi,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val (Real.pi / 2) Real.pi :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val (by linarith) (by linarith)
  have hIT : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' ({Real.pi / 2} : Set ℝ),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    rw [Set.image_singleton, integral_singleton, C.property.2.2.2.1, smul_eq_mul, mul_one,
      measureReal_def]
  -- ### Assembling the support-area identity
  rw [convexBody_area_support_integral.1 C.val, htotal, hUdef,
    hstep (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
      (by rw [Set.disjoint_singleton_right]
          rintro (((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) | ⟨h, -⟩) <;> linarith)
      (measurableSet_singleton _),
    hstep (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4
      (by rw [Set.disjoint_left]
          rintro x ((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep (Set.union_subset hs1 hs2) hs3
      (by rw [Set.disjoint_left]
          rintro x (⟨-, h⟩ | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep hs1 hs2
      (by rw [Set.disjoint_left]
          rintro x ⟨-, h⟩ ⟨h', -⟩
          linarith)
      measurableSet_Ioo,
    hI1, hI2, hI3, hI4, hIT]
  ring

theorem specialCapArea_equivalent_upper_arcs :
    EquivalentModuloConvexLinear specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point))
      (fun K ↦ convexArcArea K.val.val 0 paperGerverConstants.2.1 +
        convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
        convexArcArea K.val.val paperGerverConstants.2.2 (Real.pi / 2) +
        convexArcArea K.val.val (Real.pi / 2) Real.pi) := by
  -- ### The discrepancy is half the mass of the surface measure at the fixed top normal
  have key : ∀ M : SpecialCapSpace,
      ClassicalResults.area (M.val.val : Set Point) -
        (convexArcArea M.val.val 0 paperGerverConstants.2.1 +
          convexArcArea M.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea M.val.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea M.val.val (Real.pi / 2) Real.pi) =
        (surfaceAreaMeasure M.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 :=
    fun M ↦ by
      obtain ⟨dr, dl, hdens, -⟩ := M.property.1.1
      rw [hdens.area_eq_upper_arcs_add_top_atom]
      ring
  intro t K L
  have hKfin : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hLfin : IsFiniteMeasure (surfaceAreaMeasure L.val.val) :=
    (surfaceAreaMeasure_face_union L.val.val).1
  simp only [realCombination, key]
  rw [specialCap_isConvexDomain.1 t K L, surfaceAreaMeasure_convexBodyCombination,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ)),
    ENNReal.toReal_ofReal t.2.1]
  ring

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

* `Area.Mamikon.Middle`.
* `Area.Mamikon.TangentValues`.
* `Area.Mamikon.SofaConvex`.
* `Area.QVariation`.
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
# The middle Mamikon functional of a special cap

`middleMamikon` is the evaluated four-term Mamikon decomposition of the part of a special cap's
niche cut out by the two straight tangent paths on `[0, φᴿ]` and `[φᴸ, π / 2]`, the outer-corner arc
on the middle window `[φᴿ, φᴸ]` and the terminal tangent path on `[π / 2, π]`.  This module proves
that it agrees with `-upperBoundMiddle` modulo convex-linear functionals of the cap.

The four summands already express their straight paths as endpoint segment areas, so the whole
functional is a sum of eleven signed segment areas, one curve area and four convex arc areas.  The
four arc areas add up to the cap area modulo a convex-linear functional
(`specialCapArea_equivalent_upper_arcs`), which supplies the `-|K|` of the upper bound.  Of the
eleven segments, five are convex-linear and therefore discarded
(`middleMamikon_segments_isConvexLinear`): all their endpoints move convex-linearly with the cap and
stay on the two fixed horizontal lines `y = 0` and `y = 1`, the latter being the top supporting
line, so no determinant of two moving coordinates ever appears.  Two more pairs collapse at the two
Gerver angles, where the extreme faces are singletons: at `φᴿ` the tangent-line intersection, the
face and the outer corner are collinear, so the two segments merge
(`middleMamikon_segments_merge_right`), and at `φᴸ` the tangent-line intersection *is* the outer
corner, so the two segments cancel (`middleMamikon_segments_cancel_left`).  What remains are exactly
the three comparisons of `cornerArea_equivalent_modulo_linear`, the last of them reversed.
-/

public section

noncomputable section

namespace MovingSofa

/-- The signed area between a convex boundary arc and the specified broken straight path. -/
def straightMamikonValue (K : ConvexBody Point) (a b : ℝ) (p q : Point) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1 p + segmentArea p q +
    segmentArea q (edgeVertices K (b : Real.Angle)).2 - convexArcArea K a b

/-- The middle Mamikon functional constructed from the special cap’s hallway-corner geometry. -/
def middleMamikon (K : SpecialCapSpace) : ℝ :=
  let B := K.val.val
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  let T := Real.pi / 2
  let y := fun t : ℝ ↦ (rotatingHallwayParts (B : Set Point) (t : Real.Angle)).outerCorner
  straightMamikonValue B 0 r
      (supportingIntersection B 0 (T : Real.Angle))
      (supportingIntersection B (r : Real.Angle) (T : Real.Angle)) +
    (segmentArea (edgeVertices B (r : Real.Angle)).1 (y r) +
      curveAreaFunctional (capOuterMiddleBV K) +
      segmentArea (y l) (edgeVertices B (l : Real.Angle)).2 - convexArcArea B r l) +
    straightMamikonValue B l T
      (supportingIntersection B (l : Real.Angle) ((T + l : ℝ) : Real.Angle))
      (supportingIntersection B (T : Real.Angle) ((T + l : ℝ) : Real.Angle)) +
    tangentMamikonValue B T Real.pi

/-! ### The singleton faces of a special cap and their positions -/

/-- The extreme faces of a special cap at the upper normals other than the vertical one are
singletons, because its injectivity condition supplies angular densities. -/
private theorem specialCap_edgeVertices_eq (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Icc 0 Real.pi) (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val.val (t : Real.Angle)).1 =
      (edgeVertices K.val.val (t : Real.Angle)).2 := by
  obtain ⟨r, s, hdens, -⟩ := K.property.1.1
  exact capDensities_edgeVertices_eq K.val ⟨r, s, hdens⟩ ht htop

/-- Both horizontal extreme faces of a special cap lie on the base line: they are singletons, and a
singleton horizontal face of a right-angle cap cannot have positive height. -/
private theorem specialCap_horizontal_edgeVertices_apply_one (K : SpecialCapSpace) :
    (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1 1 = 0 ∧
      (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 1 = 0 := by
  have hpi := Real.pi_pos
  have h0 := specialCap_edgeVertices_eq K (t := 0) ⟨le_rfl, hpi.le⟩
    (by positivity : (0 : ℝ) < Real.pi / 2).ne
  have hp := specialCap_edgeVertices_eq K (t := Real.pi) ⟨hpi.le, le_rfl⟩
    (by linarith : Real.pi / 2 < Real.pi).ne'
  refine ⟨K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_zero h0, ?_⟩
  rw [← hp]
  exact K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_pi hp

/-- At the left Gerver angle the two supporting lines of the middle Mamikon loop are at angular
difference `π / 2`, so they meet at the outer corner of the supporting hallway. -/
private theorem specialCap_supportingIntersection_left_eq_outerCorner (K : SpecialCapSpace) :
    supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.2 : Real.Angle)).outerCorner := by
  rw [show (Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
    paperGerverConstants.2.2 + Real.pi / 2 from by ring]
  exact supportingIntersection_add_pi_div_two_eq_outerCorner _ _

/-! ### The convex-linear segments -/

/-- The signed area of the segment between two convex-linear point functionals of a special cap
that both keep a constant height is convex-linear. -/
private theorem segmentArea_isConvexLinear_of_apply_one_eq (P Q : SpecialCapSpace → Point)
    {a b : ℝ}
    (hP : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      P (specialCapCombination t K L) = (1 - (t : ℝ)) • P K + (t : ℝ) • P L)
    (hQ : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      Q (specialCapCombination t K L) = (1 - (t : ℝ)) • Q K + (t : ℝ) • Q L)
    (hPa : ∀ K, P K 1 = a) (hQb : ∀ K, Q K 1 = b) :
    IsConvexLinear specialCapCombination realCombination fun K ↦ segmentArea (P K) (Q K) :=
  fun t K L ↦ by
    change segmentArea (P (specialCapCombination t K L)) (Q (specialCapCombination t K L)) =
      realCombination t (segmentArea (P K) (Q K)) (segmentArea (P L) (Q L))
    rw [hP, hQ, realCombination]
    exact segmentArea_combination_of_apply_one_eq _ ((hPa K).trans (hPa L).symm)
      ((hQb K).trans (hQb L).symm)

/-- The five straight segments that the reductions leave in place have convex-linear total signed
area.  In the order of the four-term definition they are the bottom segment at the horizontal normal
`0`, the chord of the top supporting line from `l_K^T(0)` to `l_K^T(φᴿ)`, the chord from
`l_K^{T + φᴸ}(T)` to the negative top vertex `v_K^-(T)`, the chord from the positive top vertex
`v_K^+(T)` to `l_K^π(T)`, and the bottom segment at the normal `π`.  All ten endpoints are
convex-linear in the cap, and each lies on one of the two fixed horizontal lines `y = 0` — the two
singleton horizontal contacts — and `y = 1` — the top supporting line. -/
private theorem middleMamikon_segments_isConvexLinear :
    IsConvexLinear specialCapCombination realCombination fun K ↦
      segmentArea (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 +
        segmentArea (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  -- ### The endpoints move convex-linearly
  have hev := fun (a : Real.Angle) (t : unitInterval) (M N : SpecialCapSpace) ↦
    (specialCap_maps_linear t M N).1 a
  have hsi := fun (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) (t : unitInterval)
    (M N : SpecialCapSpace) ↦ (specialCap_maps_linear t M N).2 a b hab hba
  have hsi0 : ∀ (t : unitInterval) (M N : SpecialCapSpace),
      supportingIntersection (specialCapCombination t M N).val.val 0
          ((Real.pi / 2 : ℝ) : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) +
          (t : ℝ) • supportingIntersection N.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) :=
    fun t M N ↦ by
      simpa only [Real.Angle.coe_zero] using
        hsi 0 (Real.pi / 2) (by positivity) (by linarith) t M N
  -- ### The endpoints keep their heights
  have htop : ∀ (M : SpecialCapSpace) (p : Point),
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (M.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) → p 1 = 1 :=
    fun M _ hp ↦ M.val.apply_one_eq_one hp
  have hsiL : ∀ (M : SpecialCapSpace) (s : ℝ),
      supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle) (s : Real.Angle) 1 = 1 :=
    fun M s ↦ htop M _ (supportingIntersection_inner_left _ _ s)
  have hsiR : ∀ (M : SpecialCapSpace) (s : ℝ), Real.sin (Real.pi / 2 - s) ≠ 0 →
      supportingIntersection M.val.val (s : Real.Angle) ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 :=
    fun M s hs ↦ htop M _ (supportingIntersection_inner_right _ s _ hs)
  have hsi0h : ∀ M : SpecialCapSpace,
      supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 := fun M ↦ by
    simpa only [Real.Angle.coe_zero] using
      hsiR M 0 (by rw [sub_zero, Real.sin_pi_div_two]; norm_num)
  have hvtop : ∀ M : SpecialCapSpace,
      (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 1 ∧
        (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 1 :=
    fun M ↦ ⟨htop M _ (edgeVertices_fst_mem _ _).2, htop M _ (edgeVertices_snd_mem _ _).2⟩
  have hsinr : Real.sin (Real.pi / 2 - paperGerverConstants.2.1) ≠ 0 := by
    rw [Real.sin_pi_div_two_sub]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1], hr.2⟩).ne'
  -- ### The five segments
  have h1 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((0 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) hsi0
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).1) hsi0h
  have h2 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun M ↦ supportingIntersection M.val.val (paperGerverConstants.2.1 : Real.Angle)
      ((Real.pi / 2 : ℝ) : Real.Angle))
    hsi0 (hsi paperGerverConstants.2.1 (Real.pi / 2) hr.2 (by linarith [hr.1]))
    hsi0h (fun M ↦ hsiR M paperGerverConstants.2.1 hsinr)
  have h3 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2) (by linarith [hl.1])
      (by linarith [hl.2]))
    (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M (Real.pi / 2 + paperGerverConstants.2.2)) (fun M ↦ (hvtop M).2)
  have h4 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith))
    (fun M ↦ (hvtop M).1) (fun M ↦ hsiL M Real.pi)
  have h5 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith)) (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M Real.pi)
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).2)
  intro t M N
  have e1 := h1 t M N
  have e2 := h2 t M N
  have e3 := h3 t M N
  have e4 := h4 t M N
  have e5 := h5 t M N
  simp only [realCombination] at e1 e2 e3 e4 e5 ⊢
  linear_combination e1 + e2 + e3 + e4 + e5

/-! ### The two collapsing pairs at the Gerver angles -/

/-- At the right Gerver angle the tangent-line intersection, the singleton extreme face and the
outer corner all lie on the same supporting line, so the two segments through the face merge into a
single chord. -/
private theorem middleMamikon_segments_merge_right (K : SpecialCapSpace) :
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle))
        (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).1
        (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.1 : Real.Angle)).outerCorner =
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle))
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.1 : Real.Angle)).outerCorner := by
  have hpi := Real.pi_pos
  obtain ⟨hr, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  have h1 := supportingIntersection_inner_left K.val.val paperGerverConstants.2.1 (Real.pi / 2)
  have h2 : inner ℝ (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) :=
    (edgeVertices_snd_mem _ _).2
  have h3 : inner ℝ (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
    ring
  have h := segmentArea_sub_segmentArea_of_inner_normalVector_eq h1 h3 h2
  rw [specialCap_edgeVertices_eq K ⟨hr.1.le, by linarith [hr.2]⟩ hr.2.ne]
  linarith [segmentArea_swap (edgeVertices K.val.val
    (paperGerverConstants.2.1 : Real.Angle)).2
    (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner]

/-- At the left Gerver angle the extreme face is a single point and the tangent-line intersection is
the outer corner, so the two segments through the face cancel by antisymmetry. -/
private theorem middleMamikon_segments_cancel_left (K : SpecialCapSpace) :
    segmentArea (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.2 : Real.Angle)).outerCorner
        (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).1
        (supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨-, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  rw [specialCap_supportingIntersection_left_eq_outerCorner,
    specialCap_edgeVertices_eq K ⟨hl.1.le, by linarith [hl.2]⟩ hl.2.ne]
  linarith [segmentArea_swap (rotatingHallwayParts (K.val.val : Set Point)
    (paperGerverConstants.2.2 : Real.Angle)).outerCorner
    (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2]

/-! ### The equivalence -/

theorem middleMamikon_equivalent_neg_upperBoundMiddle :
    EquivalentModuloConvexLinear specialCapCombination middleMamikon
      (fun K ↦ -upperBoundMiddle K) := by
  obtain ⟨F, hFval, hmid, hright, hleft⟩ := cornerArea_equivalent_modulo_linear
  have hF : ∀ M : SpecialCapSpace, F M = capOuterMiddleBV M := fun M ↦
    Subtype.ext ((hFval M).trans (funext (capOuterMiddleBV_val M)).symm)
  -- The chord closing the third straight path reverses the left comparison chord.
  have hrev : ∀ M : SpecialCapSpace,
      segmentArea (supportingIntersection M.val.val (paperGerverConstants.2.2 : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) =
        -segmentArea (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (M.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner := fun M ↦ by
    rw [specialCap_supportingIntersection_left_eq_outerCorner]
    exact segmentArea_swap _ _
  -- The right wedge segment of the upper bound runs in the opposite orientation.
  have hswap : ∀ M : SpecialCapSpace,
      segmentArea (distinguishedCapSides M.val).1.corner
          (distinguishedCapSides M.val).1.fanPoint =
        -segmentArea (distinguishedCapSides M.val).1.fanPoint
          (distinguishedCapSides M.val).1.corner := fun M ↦ segmentArea_swap _ _
  intro t K L
  have e1 := specialCapArea_equivalent_upper_arcs t K L
  have e2 := hmid t K L
  have e3 := hright t K L
  have e4 := hleft t K L
  have f := middleMamikon_segments_isConvexLinear t K L
  simp only [hF, realCombination] at e1 e2 e3 e4 f
  simp only [middleMamikon, straightMamikonValue, tangentMamikonValue, upperBoundMiddle,
    realCombination, hrev, hswap]
  linear_combination f + e1 + e2 + e3 - e4 +
    middleMamikon_segments_merge_right (specialCapCombination t K L) +
    middleMamikon_segments_cancel_left (specialCapCombination t K L) -
    (1 - (t : ℝ)) * (middleMamikon_segments_merge_right K +
      middleMamikon_segments_cancel_left K) -
    (t : ℝ) * (middleMamikon_segments_merge_right L +
      middleMamikon_segments_cancel_left L)

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
# Mamikon values of tangent-line chords

For a fixed tangent normal `q`, the tangent-line parametrization of a convex body is a
continuous bounded-variation path, convex-linear in the body, each of whose values lies on the
supporting line at its own path parameter.  Mamikon convexity therefore makes the enclosed area
`straightMamikonValue` a convex quadratic functional of the body, and the terminal case `q = b`
does the same for `tangentMamikonValue`.
-/

public section

noncomputable section

namespace MovingSofa

/-- The Mamikon value of a straight tangent-line chord is a convex quadratic functional of the
body. -/
theorem straightMamikon_quadratic_convex (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) ∧
      IsConvexFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) false := by
  obtain ⟨F, hFval, hFlin⟩ := tangentLinePath_convexLinear t a b ha hb hab.le
  have hF : ∀ (K : ConvexBody Point) (s : Set.Icc a b),
      (F K).val s ∈ (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro K s
    rw [hFval K]
    exact tangentLinePath_mem_supportingLine K t
      ⟨(s : ℝ), lt_of_lt_of_le ha.1 s.property.1, le_trans s.property.2 hb.2⟩
  have hval : ∀ K : ConvexBody Point,
      mamikonFunctional K a b hab hba (F K) (hF K) =
        straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩) := by
    intro K
    have hchoose : F K = (tangentLinePath_segment_area K t a b ha hb hab.le).choose :=
      Subtype.ext ((hFval K).trans
        (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.1.symm)
    have hstart : (F K).val ⟨a, le_rfl, hab.le⟩ = tangentLinePath K t ⟨a, ha⟩ := by
      rw [hFval K]; rfl
    have hend : (F K).val ⟨b, hab.le, le_rfl⟩ = tangentLinePath K t ⟨b, hb⟩ := by
      rw [hFval K]; rfl
    have harea : curveAreaFunctional (F K) =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
      rw [hchoose]
      exact (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.2.2.2
    unfold mamikonFunctional straightMamikonValue
    rw [hstart, hend, harea]
  have hmain := mamikon_quadratic_convex a b hab hba F hF hFlin
  rw [funext hval] at hmain
  exact hmain

/-- The Mamikon value of a terminal tangent normal is a convex quadratic functional of the body. -/
theorem tangentMamikon_quadratic_convex (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) ∧
      IsConvexFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) false := by
  have ha : a ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith, hab.le⟩
  have hb : b ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hmain := straightMamikon_quadratic_convex b a b ha hb hab hba
  have hval : ∀ K : ConvexBody Point,
      straightMamikonValue K a b (tangentLinePath K b ⟨a, ha⟩) (tangentLinePath K b ⟨b, hb⟩) =
        tangentMamikonValue K a b := by
    intro K
    have hstart : tangentLinePath K b ⟨a, ha⟩ =
        supportingIntersection K (a : Real.Angle) (b : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hab]
    have hend : tangentLinePath K b ⟨b, hb⟩ = (edgeVertices K (b : Real.Angle)).2 := by
      unfold tangentLinePath
      rw [ite_eq_right (lt_irrefl b)]
    have hdeg : segmentArea (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2 = 0 := by
      have h := segmentArea_swap (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2
      linarith
    unfold straightMamikonValue tangentMamikonValue
    rw [hstart, hend, hdeg]
    ring
  rw [funext hval] at hmain
  exact hmain

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
# Area / Mamikon / Sofa Convex
-/

public section

noncomputable section

namespace MovingSofa

theorem sofaMamikon_quadratic_convex :
    IsConvexFunctional specialCapCombination middleMamikon false ∧
    IsQuadraticFunctional specialCapCombination middleMamikon ∧
    IsConvexFunctional convexBodyCombination rightTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination rightTailMamikon ∧
    IsConvexFunctional convexBodyCombination leftTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination leftTailMamikon := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  have hr0 := hrIoo.1
  have hr2 := hrIoo.2
  have hl0 := hlIoo.1
  have hl2 := hlIoo.2
  -- ### The two tail functionals are terminal tangent Mamikon values
  have htailR := tangentMamikon_quadratic_convex (Real.pi + paperGerverConstants.2.1)
    (3 * Real.pi / 2) (by linarith) (by linarith)
  have htailL := tangentMamikon_quadratic_convex (3 * Real.pi / 2)
    (3 * Real.pi / 2 + paperGerverConstants.2.2) (by linarith) (by linarith)
  -- ### The first middle summand
  have ha1 : (0 : ℝ) ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hb1 : paperGerverConstants.2.1 ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hmid1 := straightMamikon_quadratic_convex (Real.pi / 2) 0 paperGerverConstants.2.1
    ha1 hb1 (by linarith) (by linarith)
  -- ### The third middle summand
  have ha3 : paperGerverConstants.2.2 ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hb3 : (Real.pi / 2 : ℝ) ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hmid3 := straightMamikon_quadratic_convex (Real.pi / 2 + paperGerverConstants.2.2)
    paperGerverConstants.2.2 (Real.pi / 2) ha3 hb3 (by linarith) (by linarith)
  -- ### The fourth middle summand
  have hmid4 := tangentMamikon_quadratic_convex (Real.pi / 2) Real.pi (by linarith) (by linarith)
  -- ### The second middle summand, the Mamikon value of the outer-corner path
  obtain ⟨γ, hγ, hγlin⟩ := exists_outerCornerBV_convexLinear paperGerverConstants.2.1
    paperGerverConstants.2.2
  have hγmem : ∀ (B : ConvexBody Point)
      (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (γ B).val s ∈ (supportingLineHalfPlane (B : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro B s
    rw [hγ B s]
    change inner ℝ (rotatingHallwayParts (B : Set Point) ((s : ℝ) : Real.Angle)).outerCorner
      (normalVector ((s : ℝ) : Real.Angle)) = supportValue (B : Set Point) ((s : ℝ) : Real.Angle)
    rw [outerCorner_eq_support_sum B (s : ℝ), inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_normalVector_self, real_inner_comm,
      inner_normalVector_tangentVector]
    ring
  have hmid2 := mamikon_quadratic_convex paperGerverConstants.2.1 paperGerverConstants.2.2
    hrl (by linarith) γ hγmem hγlin
  -- ### The four middle summands assemble to the middle functional on all bodies
  have hquadAll := ((hmid1.1.add hmid2.1).add hmid3.1).add hmid4.1
  have hconvAll := ((hmid1.2.add hmid2.2).add hmid3.2).add hmid4.2
  have hbody : IsConvexLinear specialCapCombination convexBodyCombination
      fun K : SpecialCapSpace ↦ K.val.val := specialCap_isConvexDomain.1
  have hquad := hquadAll.comp_isConvexLinear hbody
  have hconv := hconvAll.comp_isConvexLinear hbody
  have hmideq : (fun K : SpecialCapSpace ↦
      ((straightMamikonValue K.val.val 0 paperGerverConstants.2.1
          (tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩)
          (tangentLinePath K.val.val (Real.pi / 2) ⟨paperGerverConstants.2.1, hb1⟩) +
        mamikonFunctional K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 hrl
          (by linarith) (γ K.val.val) (hγmem K.val.val)) +
        straightMamikonValue K.val.val paperGerverConstants.2.2 (Real.pi / 2)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨paperGerverConstants.2.2, ha3⟩)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨Real.pi / 2, hb3⟩)) +
        tangentMamikonValue K.val.val (Real.pi / 2) Real.pi) = middleMamikon := by
    funext K
    have hpath1 : tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩ =
        supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (show (0 : ℝ) < Real.pi / 2 by linarith), Real.Angle.coe_zero]
    have hpath2 : tangentLinePath K.val.val (Real.pi / 2)
        ⟨paperGerverConstants.2.1, hb1⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hr2]
    have hpath3 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨paperGerverConstants.2.2, ha3⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hpath4 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨Real.pi / 2, hb3⟩ =
        supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hγeq : γ K.val.val = capOuterMiddleBV K :=
      Subtype.ext (funext fun s ↦ (hγ K.val.val s).trans (capOuterMiddleBV_val K s).symm)
    have hmam : mamikonFunctional K.val.val paperGerverConstants.2.1
        paperGerverConstants.2.2 hrl (by linarith) (γ K.val.val) (hγmem K.val.val) =
        segmentArea (edgeVertices K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
            ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).outerCorner) +
          curveAreaFunctional (capOuterMiddleBV K) +
          segmentArea ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).outerCorner)
            (edgeVertices K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 -
          convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 := by
      unfold mamikonFunctional
      rw [hγ K.val.val ⟨paperGerverConstants.2.1, le_rfl, hrl.le⟩,
        hγ K.val.val ⟨paperGerverConstants.2.2, hrl.le, le_rfl⟩, hγeq]
    change _ = middleMamikon K
    unfold middleMamikon
    rw [hpath1, hpath2, hpath3, hpath4, hmam]
  rw [hmideq] at hquad hconv
  exact ⟨hconv, hquad, htailR.2, htailR.1, htailL.2, htailL.1⟩

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
# The directional derivative of the upper bound `𝒬`

`upperBoundQ` is a signed sum of six area functionals of a cap-tail triple: the cap area, the two
tail arc areas, the inner-corner curve area and the two areas of the segments joining a tail
endpoint to the corresponding cap corner.  Each summand is quadratic along the barycentric
interpolation of cap-tail triples, so each segment function is differentiable at the base point
with the summand's `convexDirectionalDerivative` as its derivative; adding those six derivatives
computes the derivative of the segment function of `𝒬` itself.

Five of the twelve endpoint contributions cancel in pairs.  The remaining two are the segment
areas at the far ends of the two tails, and they vanish because the cap-tail constraints force the
support value of both tails in the direction `3π/2` to be zero, so all four points involved lie on
the horizontal axis.  What survives is `qVariationIntegral`: the cap surface integral, the
inner-corner integral, and the two tail integrals rewritten in opposite-angle coordinates.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The support-function variation integral for the cap and its two tail bodies. -/
@[expose]
def qVariationIntegral (X Y : CapTailSpace) : ℝ :=
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂surfaceAreaMeasure X.cap.val.val) -
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)),
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂capCornerAngleMeasure X.cap) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
    ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
      ∂(oppositeSurfaceData X.rightBody).1) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
    ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
      ∂(oppositeSurfaceData X.leftBody).1)

private theorem capTail_leftPair_isConvexLinear :
    IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint,
        (distinguishedCapSides Z.cap.val).2.corner)) := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  intro t Z W
  have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).2.endPoint =
      (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint +
        (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).2.endPoint := by
    change (edgeVertices (capTailCombination t Z W).leftBody
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 = _
    rw [(hcomb t Z W).2.2]
    exact ((convexBody_maps_linear t Z.leftBody W.leftBody).2.1 _).2
  have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner =
      (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).2.corner +
        (t : ℝ) • (distinguishedCapSides W.cap.val).2.corner :=
    capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.2
  change ((rightLeftTailArcs (capTailCombination t Z W).rightBody
    (capTailCombination t Z W).leftBody).2.endPoint,
    (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner) = _
  rw [hvertex, hcorner]
  rfl

private theorem capTail_rightPair_isConvexLinear :
    IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((distinguishedCapSides Z.cap.val).1.corner,
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint)) := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  intro t Z W
  have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner =
      (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).1.corner +
        (t : ℝ) • (distinguishedCapSides W.cap.val).1.corner :=
    capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.1
  have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).1.startPoint =
      (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint +
        (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).1.startPoint := by
    change (edgeVertices (capTailCombination t Z W).rightBody
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 = _
    rw [(hcomb t Z W).2.1]
    exact ((convexBody_maps_linear t Z.rightBody W.rightBody).2.1 _).1
  change ((distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner,
    (rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).1.startPoint) = _
  rw [hcorner, hvertex]
  rfl

private theorem capTail_far_segmentAreas (X Y : CapTailSpace) :
    (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint = 0) ∧
    (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint = 0) := by
  -- ### The far endpoints of the two tails lie on the horizontal axis
  have hsupp : ∀ Z : CapTailSpace,
      supportValue (Z.rightBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 ∧
        supportValue (Z.leftBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    intro Z
    have hcapval :
        supportValue (Z.cap.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
      Z.cap.val.property.2.2.2.1
    have hr := Z.right_eq (Real.pi / 2) (by simp)
    have hl := Z.left_eq 0 (by simp)
    rw [show ((Real.pi + Real.pi / 2 : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hr
    rw [show ((Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring,
      show ((3 * Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hl
    exact ⟨by linarith, by linarith⟩
  have hheight : ∀ K : ConvexBody Point,
      supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 →
      (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 0 ∧
        (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 0 := by
    intro K hK
    have hn : normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        -normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [show ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) from by congr 1; ring]
      exact normalVector_add_pi _
    have key : ∀ p : Point,
        inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = 0 → p 1 = 0 := by
      intro p hp
      rw [hn, inner_neg_right, inner_normalVector_real, Real.cos_pi_div_two,
        Real.sin_pi_div_two] at hp
      linarith
    have hfst : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem K _).2
    have hsnd : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem K _).2
    exact ⟨key _ (hfst.trans hK), key _ (hsnd.trans hK)⟩
  have hzeroSegment : ∀ p q : Point, p 1 = 0 → q 1 = 0 → segmentArea p q = 0 := by
    intro p q hp hq
    simp [segmentArea, planeCrossProduct, hp, hq]
  have hrightFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint = 0 :=
    hzeroSegment _ _ (hheight X.rightBody (hsupp X).1).2 (hheight Y.rightBody (hsupp Y).1).2
  have hleftFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint = 0 :=
    hzeroSegment _ _ (hheight X.leftBody (hsupp X).2).1 (hheight Y.leftBody (hsupp Y).2).1
  exact ⟨hrightFar, hleftFar⟩

private theorem capTail_left_segment_variation (X Y : CapTailSpace)
    (hL : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (distinguishedCapSides X.cap.val).2.corner) :
    convexDirectionalDerivative capTailCombination
     (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
       (distinguishedCapSides Z.cap.val).2.corner) X Y =
     segmentArea (distinguishedCapSides X.cap.val).2.corner
         (distinguishedCapSides Y.cap.val).2.corner -
       segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
         (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint := by
  have hleftPair := capTail_leftPair_isConvexLinear
  have hvar := segmentArea_variation.2
    (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
    (distinguishedCapSides X.cap.val).2.corner
    (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint
    (distinguishedCapSides Y.cap.val).2.corner
  have hbulk : (planeCrossProduct
      ((rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint +
        (distinguishedCapSides Y.cap.val).2.corner)
      ((distinguishedCapSides X.cap.val).2.corner -
        (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint) -
      2 * planeCrossProduct (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
        (distinguishedCapSides X.cap.val).2.corner) / 2 = 0 := by
    rw [← hL]
    simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
    ring
  rw [hbulk, zero_add] at hvar
  exact (convexDirectionalDerivative_comp_isConvexLinear hleftPair
    (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar

theorem upperBoundQ_variation (X Y : CapTailSpace)
    (hR : (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint =
      (distinguishedCapSides X.cap.val).1.corner)
    (hL : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (distinguishedCapSides X.cap.val).2.corner) :
    convexDirectionalDerivative capTailCombination upperBoundQ X Y = qVariationIntegral X Y := by
  obtain ⟨hcomb, -⟩ := capTail_isConvexDomain
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  -- ### The three components of a cap-tail triple depend convex-linearly on it
  have hcap : IsConvexLinear capTailCombination specialCapCombination
      (fun Z : CapTailSpace ↦ Z.cap) := fun t Z W ↦
    Subtype.ext (Subtype.ext ((hcomb t Z W).1.trans
      (specialCap_isConvexDomain.1 t Z.cap W.cap).symm))
  have hright : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.rightBody) := fun t Z W ↦ (hcomb t Z W).2.1
  have hleft : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.leftBody) := fun t Z W ↦ (hcomb t Z W).2.2
  -- ### The two segment endpoint pairs depend convex-linearly on the triple
  have hleftPair := capTail_leftPair_isConvexLinear
  have hrightPair := capTail_rightPair_isConvexLinear
  -- ### Quadraticity of the six summands of `𝒬`
  have hq1 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) :=
    specialCapArea_variation.1.comp_isConvexLinear hcap
  have hq2 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) :=
    (convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).1
      |>.comp_isConvexLinear hleft
  have hq3 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
        (distinguishedCapSides Z.cap.val).2.corner) :=
    segmentArea_variation.1.comp_isConvexLinear hleftPair
  have hq4 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) :=
    capInnerCorner_variation.2.1.comp_isConvexLinear hcap
  have hq5 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) :=
    segmentArea_variation.1.comp_isConvexLinear hrightPair
  have hq6 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) :=
    (convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).1
      |>.comp_isConvexLinear hright
  -- ### The four summands whose derivatives contribute an integral
  have hd1 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂surfaceAreaMeasure X.cap.val.val :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun K : SpecialCapSpace ↦ ClassicalResults.area (K.val.val : Set Point)) X Y).trans
      (specialCapArea_variation.2 X.cap Y.cap)
  have hd2 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
        (supportValue Y.leftBody t - supportValue X.leftBody t)
          ∂surfaceAreaMeasure X.leftBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hleft
      (fun M : ConvexBody Point ↦ convexArcArea M (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).2
        X.leftBody Y.leftBody)
  have hd4 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂capCornerAngleMeasure X.cap) +
        (segmentArea (distinguishedCapSides X.cap.val).2.corner
            (distinguishedCapSides Y.cap.val).2.corner -
          segmentArea (distinguishedCapSides X.cap.val).1.corner
            (distinguishedCapSides Y.cap.val).1.corner) :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun M : SpecialCapSpace ↦ curveAreaFunctional (capMiddleBV M)) X Y).trans
      (capInnerCorner_variation.2.2 X.cap Y.cap)
  have hd6 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
        (supportValue Y.rightBody t - supportValue X.rightBody t)
          ∂surfaceAreaMeasure X.rightBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hright
      (fun M : ConvexBody Point ↦ convexArcArea M (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).2
        X.rightBody Y.rightBody)
  -- ### The two segment summands: their bulk terms vanish because the base endpoints coincide
  have hd3 := capTail_left_segment_variation X Y hL
  have hd5 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y =
      segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint -
        segmentArea (distinguishedCapSides X.cap.val).1.corner
          (distinguishedCapSides Y.cap.val).1.corner := by
    have hvar := segmentArea_variation.2
      (distinguishedCapSides X.cap.val).1.corner
      (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
      (distinguishedCapSides Y.cap.val).1.corner
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint
    have hbulk : (planeCrossProduct
        ((distinguishedCapSides Y.cap.val).1.corner +
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint)
        ((rightLeftTailArcs X.rightBody X.leftBody).1.startPoint -
          (distinguishedCapSides X.cap.val).1.corner) -
        2 * planeCrossProduct (distinguishedCapSides X.cap.val).1.corner
          (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint) / 2 = 0 := by
      rw [hR]
      simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
      ring
    rw [hbulk, zero_add] at hvar
    exact (convexDirectionalDerivative_comp_isConvexLinear hrightPair
      (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar
  -- ### The derivative of `𝒬` is the signed sum of the six derivatives
  have hsplit : ∀ t : ℝ, segmentFunctional capTailCombination upperBoundQ X Y t =
      segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
              (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea
              (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
              (distinguishedCapSides Z.cap.val).2.corner) X Y t -
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
              (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody
              (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)) X Y t := by
    intro t
    simp only [segmentFunctional]
    split_ifs with ht
    · rfl
    · norm_num
  have hD1 := hq1.hasDerivWithinAt_segmentFunctional X Y
  have hD2 := hq2.hasDerivWithinAt_segmentFunctional X Y
  have hD3 := hq3.hasDerivWithinAt_segmentFunctional X Y
  have hD4 := hq4.hasDerivWithinAt_segmentFunctional X Y
  have hD5 := hq5.hasDerivWithinAt_segmentFunctional X Y
  have hD6 := hq6.hasDerivWithinAt_segmentFunctional X Y
  rw [hd1] at hD1
  rw [hd2] at hD2
  rw [hd3] at hD3
  rw [hd4] at hD4
  rw [hd5] at hD5
  rw [hd6] at hD6
  have hderiv := convexDirectionalDerivative_eq_of_hasDerivWithinAt capTailCombination
    upperBoundQ X Y ((((((hD1.add hD2).add hD3).sub hD4).add hD5).add hD6).congr
      (fun t _ ↦ hsplit t) (hsplit 0))
  obtain ⟨hrightFar, hleftFar⟩ := capTail_far_segmentAreas X Y
  -- ### The two tail integrals in opposite-angle coordinates
  have hrightTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
      (supportValue Y.rightBody t - supportValue X.rightBody t)
        ∂surfaceAreaMeasure X.rightBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
        ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
          ∂(oppositeSurfaceData X.rightBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.rightBody
      (a := paperGerverConstants.2.1) (b := Real.pi / 2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.rightBody u - supportValue X.rightBody u)
      ((continuous_supportValue Y.rightBody).sub
        (continuous_supportValue X.rightBody)).measurable).symm
  have hleftTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
      (supportValue Y.leftBody t - supportValue X.leftBody t)
        ∂surfaceAreaMeasure X.leftBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
        ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
          ∂(oppositeSurfaceData X.leftBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.leftBody
      (a := Real.pi / 2) (b := Real.pi / 2 + paperGerverConstants.2.2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.leftBody u - supportValue X.leftBody u)
      ((continuous_supportValue Y.leftBody).sub
        (continuous_supportValue X.leftBody)).measurable).symm
  -- ### Collecting the six contributions
  rw [hderiv]
  simp only [qVariationIntegral]
  linarith [hrightTail, hleftTail, hrightFar, hleftFar]

end MovingSofa

end

end

end

end

end

end
