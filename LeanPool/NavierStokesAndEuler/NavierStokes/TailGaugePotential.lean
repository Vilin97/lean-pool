/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBaseEndpoint

/-!
# A radial gauge for the actual slow-base potential

Subtracting the swirl potential at the fixed physical coordinate `s = 1`
removes every radial integration constant, including those of the positive
slow orders.  The subtraction is a genuine curl-free axial field.  In the
heat exterior the resulting potential is a finite, anchored heat primitive,
which has a smooth extension through the terminal central plane.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.TailGaugePotential

open Set Filter MeasureTheory ProblemStatement
open scoped Topology ContDiff


/-- Point: an abbreviation for `AxisymmetricFields.ProfilePoint`. -/
abbrev Point := AxisymmetricFields.ProfilePoint

/-- The radial anchor is physical and independent of the similarity scale. -/
noncomputable def radialAnchor (p : Point) : Point := (p.1, (1, p.2.2))

/-- Radial normalize, given by `K p - K (radialAnchor p)`. -/
noncomputable def radialNormalize (K : Point → ℝ) (p : Point) : ℝ :=
  K p - K (radialAnchor p)

theorem radialAnchor_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n radialAnchor :=
  contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd)

theorem radialNormalize_contDiffAt {K : Point → ℝ} {p : Point} {n : WithTop ℕ∞}
    (hK : ContDiffAt ℝ n K p) (hA : ContDiffAt ℝ n K (radialAnchor p)) :
    ContDiffAt ℝ n (radialNormalize K) p :=
  hK.sub (hA.comp p radialAnchor_contDiff.contDiffAt)

theorem radial_slice_hasDerivAt {K : Point → ℝ} {p : Point}
    (hK : DifferentiableAt ℝ K p) :
    HasDerivAt (fun s => K (p.1, (s, p.2.2))) (AxisymmetricFields.partialS K p) p.2.1 := by
  simpa only [AxisymmetricFields.partialS, Prod.eta, Function.comp_def, one_smul, id_eq] using
    hK.hasFDerivAt.comp_hasDerivAt p.2.1
      ((hasDerivAt_const p.2.1 p.1).prodMk
        ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))

theorem partialS_radialNormalize {K : Point → ℝ} {p : Point}
    (hK : DifferentiableAt ℝ K p) (hA : DifferentiableAt ℝ K (radialAnchor p)) :
    AxisymmetricFields.partialS (radialNormalize K) p = AxisymmetricFields.partialS K p := by
  have hN : DifferentiableAt ℝ (radialNormalize K) p :=
    hK.sub (hA.comp p ((radialAnchor_contDiff (n := 1)).differentiable (by
        norm_num)).differentiableAt)
  exact (radial_slice_hasDerivAt hN).unique
    ((radial_slice_hasDerivAt hK).sub_const (K (radialAnchor p)))

theorem radialNormalize_anchor (K : Point → ℝ) (t z : ℝ) :
    radialNormalize K (t, (1, z)) = 0 := sub_self _

/-- This is the entire summed swirl potential, with all slow orders retained. -/
noncomputable def gaugedSwirl (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) : Point → ℝ :=
  radialNormalize (SlowBorelBase.swirlPotential a h C d)

theorem gaugedSwirl_apply (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) (p : Point) :
    gaugedSwirl a h C d p =
      SlowBorelBase.swirlPotential a h C d p - SlowBorelBase.swirlPotential a h C d (p.1, (1,
          p.2.2)) := rfl

/-- Potential, given by `AxisymmetricFields.potential (SlowBorelBase.streamFactor a h C d)
(gaugedSwirl a h C d)`. -/
noncomputable def potential (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) : VelocityField
    :=
  AxisymmetricFields.potential (SlowBorelBase.streamFactor a h C d) (gaugedSwirl a h C d)

theorem potential_eq_sub_gauge (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients)
    (w : SpaceTime) :
    potential a h C d w = BaseResidual.summedPotential a h C d w -
      SlowBorelBase.swirlPotential a h C d (w.1, (1, w.2 2)) • coordinateVector 2 := by
  simp only [potential, BaseResidual.summedPotential, AxisymmetricFields.potential, gaugedSwirl,
    radialNormalize, radialAnchor, AxisymmetricFields.profilePoint, sub_smul]
  abel

theorem gaugedSwirl_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) {p : Point} (ht : p.1 < 1) :
    ContDiffAt ℝ ∞ (gaugedSwirl a h C d) p :=
  radialNormalize_contDiffAt
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 1)
        _ ht)
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 1)
        _ ht)

theorem potential_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) :
    ContDiffOn ℝ ∞ (potential a h C d) (Iio 1 ×ˢ (univ : Set Space)) :=
  AxisymmetricFields.contDiffOn_potential
    (SlowBorelBase.physicalProfile_smoothOn ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 0)
        _)
    (fun _ hp => (gaugedSwirl_smoothAt ha hh hh1 hd hp.1).contDiffWithinAt)

/-- Equality of the actual Euclidean curls, also on the spatial axis. -/
theorem spatialCurl_potential {a : ℕ → ℕ} (ha : StrictMono a) {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) {w : SpaceTime} (ht : w.1 < 1) :
    SpatialCurl.spatialCurl (potential a h C d) w = SlowBorelBase.baseVelocity a h C d w := by
  have hH : DifferentiableAt ℝ (SlowBorelBase.streamFactor a h C d)
      (AxisymmetricFields.profilePoint w.1 w.2) :=
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 0)
        _ ht).differentiableAt
      (by simp)
  have hK : DifferentiableAt ℝ (SlowBorelBase.swirlPotential a h C d)
      (AxisymmetricFields.profilePoint w.1 w.2) :=
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 1)
        _ ht).differentiableAt
      (by simp)
  have hA : DifferentiableAt ℝ (SlowBorelBase.swirlPotential a h C d)
      (radialAnchor (AxisymmetricFields.profilePoint w.1 w.2)) :=
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1 (SlowBorelBase.bundleComponent_smooth hd C 1)
        _ ht).differentiableAt
      (by simp)
  have hN := (gaugedSwirl_smoothAt (C := C) ha hh hh1 hd
    (p := AxisymmetricFields.profilePoint w.1 w.2) ht).differentiableAt (by simp)
  have he : AxisymmetricFields.partialS (gaugedSwirl a h C d) (AxisymmetricFields.profilePoint w.1
      w.2) =
      AxisymmetricFields.partialS (SlowBorelBase.swirlPotential a h C d)
          (AxisymmetricFields.profilePoint w.1 w.2) :=
    partialS_radialNormalize hK hA
  change AxisymmetricFields.velocity _ _ w = AxisymmetricFields.velocity _ _ w
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity _ _ (w.1, w.2) 0 =
      AxisymmetricFields.velocity _ _ (w.1, w.2) 0
    rw [AxisymmetricFields.velocity_zero _ _ _ _ hH hN, AxisymmetricFields.velocity_zero _ _ _ _ hH
        hK, he]
  · change AxisymmetricFields.velocity _ _ (w.1, w.2) 1 =
      AxisymmetricFields.velocity _ _ (w.1, w.2) 1
    rw [AxisymmetricFields.velocity_one _ _ _ _ hH hN, AxisymmetricFields.velocity_one _ _ _ _ hH
        hK, he]
  · change AxisymmetricFields.velocity _ _ (w.1, w.2) 2 =
      AxisymmetricFields.velocity _ _ (w.1, w.2) 2
    rw [AxisymmetricFields.velocity_two _ _ _ _ hH hN, AxisymmetricFields.velocity_two _ _ _ _ hH
        hK]

/-! ## An actual smooth heat primitive through the terminal time -/

/-- The heat profile uses its proved smooth extension at negative time
remaining; on the past side this is exactly the original heat coefficient. -/
noncomputable def extendedHeatCoefficient (C h : ℝ) (p : Point) : ℝ :=
  C * (p.2.1 ^ RadialHeatProfile.spatialExponent (1 + h) *
    HeatProfileExtension.extension (1 + h) (2 * (1 - p.1) / p.2.1)) /
      Real.sqrt (2 * p.2.1)

theorem extendedHeatCoefficient_eq (C h : ℝ) {p : Point}
    (ht : p.1 ≤ 1) (hs : 0 < p.2.1) :
    extendedHeatCoefficient C h p = BaseExterior.heatCoefficient C h p := by
  rw [BaseExterior.heatCoefficient_eq]
  unfold extendedHeatCoefficient TerminalStress.physicalHeat RadialHeatProfile.spatialProfile
  rw [HeatProfileExtension.extension_eq_profile (1 + h)
    (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht)) hs.le)]

theorem extendedHeatCoefficient_smoothAt (C : ℝ) {h : ℝ} (hh : 0 < h)
    {p : Point} (hs : 0 < p.2.1) : ContDiffAt ℝ ∞ (extendedHeatCoefficient C h) p := by
  have he : ContDiffAt ℝ ∞ (HeatProfileExtension.extension (1 + h))
      (2 * (1 - p.1) / p.2.1) :=
    (HeatProfileExtension.extension_contDiff (show 1 < 1 + h by linarith)).contDiffAt
  have hg : ContDiffAt ℝ ∞ (fun q : Point => 2 * (1 - q.1) / q.2.1) p :=
    (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_fst)).div contDiffAt_snd.fst hs.ne'
  exact (contDiffAt_const.mul
    ((contDiffAt_snd.fst.rpow_const_of_ne hs.ne').mul (he.comp p hg))).div
      ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (by positivity))
      (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

/-- Translating the radial variable by one makes the anchored integral a
standard radial history on a domain stable under contraction to zero. -/
noncomputable def shiftedRadialDomain : ProfileHistories.RadialDomain where
  carrier := {p | -1 < p.1}
  isOpen := isOpen_lt continuous_const continuous_fst
  scale_mem := by
    intro p hp v hv
    change -1 < v * p.1
    change -1 < p.1 at hp
    by_cases hpos : 0 ≤ p.1
    · exact lt_of_lt_of_le (by norm_num) (mul_nonneg hv.1 hpos)
    · have hneg : p.1 ≤ 0 := le_of_not_ge hpos
      have hle : p.1 ≤ v * p.1 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (neg_nonneg.mpr hneg)]
      exact hp.trans_le hle

/-- Shifted heat, given by `extendedHeatCoefficient C h (p.2, (p.1 + 1, 0))`. -/
noncomputable def shiftedHeat (C h : ℝ) (p : ℝ × ℝ) : ℝ :=
  extendedHeatCoefficient C h (p.2, (p.1 + 1, 0))

theorem shiftedHeat_smooth (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (shiftedHeat C h) shiftedRadialDomain.carrier := by
  intro p hp
  have hs : 0 < p.1 + 1 := by change -1 < p.1 at hp; linarith
  exact ((extendedHeatCoefficient_smoothAt C hh (p := (p.2, (p.1 + 1, 0))) hs).comp p
    (contDiffAt_snd.prodMk ((contDiffAt_fst.add contDiffAt_const).prodMk
        contDiffAt_const))).contDiffWithinAt

/-- A finite heat primitive anchored at physical `s = 1`, for every time.
It equals `-∫ᵣ₌₁ˢ F(t,r)dr` and has no gauge divergence as `t → 1`. -/
noncomputable def heatPrimitive (C h : ℝ) (p : Point) : ℝ :=
  -ProfileHistories.primitive (shiftedHeat C h) (p.2.1 - 1, p.1)

theorem heatPrimitive_anchor (C h t z : ℝ) : heatPrimitive C h (t, (1, z)) = 0 := by
  simp [heatPrimitive, ProfileHistories.primitive]

theorem heatPrimitive_eq_integral (C h : ℝ) (p : Point) :
    heatPrimitive C h p =
      -(∫ r in (1 : ℝ)..p.2.1, extendedHeatCoefficient C h (p.1, (r, p.2.2))) := by
  simpa only [heatPrimitive, ProfileHistories.primitive, shiftedHeat, extendedHeatCoefficient,
    zero_add, sub_add_cancel] using congrArg (fun r : ℝ => -r)
    (intervalIntegral.integral_comp_add_right
      (fun r => extendedHeatCoefficient C h (p.1, (r, p.2.2)))
      (a := 0) (b := p.2.1 - 1) (1 : ℝ))

theorem heatPrimitive_smoothAt (C : ℝ) {h : ℝ} (hh : 0 < h)
    {p : Point} (hs : 0 < p.2.1) : ContDiffAt ℝ ∞ (heatPrimitive C h) p := by
  have hp : (p.2.1 - 1, p.1) ∈ shiftedRadialDomain.carrier := by
    change -1 < p.2.1 - 1
    linarith
  exact (((ProfileHistories.primitive_smooth shiftedRadialDomain (shiftedHeat_smooth C
      hh)).contDiffAt
    (shiftedRadialDomain.isOpen.mem_nhds hp)).comp p
      ((contDiffAt_snd.fst.sub contDiffAt_const).prodMk contDiffAt_fst)).neg

theorem heatPrimitive_hasDerivAt (C : ℝ) {h : ℝ} (hh : 0 < h)
    (t z : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => heatPrimitive C h (t, (r, z)))
      (-extendedHeatCoefficient C h (t, (s, z))) s := by
  have hp : (s - 1, t) ∈ shiftedRadialDomain.carrier := by
    change -1 < s - 1
    linarith
  have hd := ProfileHistories.primitive_hasDerivAt shiftedRadialDomain (shiftedHeat_smooth C hh) hp
  simpa only [heatPrimitive, shiftedHeat, extendedHeatCoefficient, Function.comp_def,
    sub_add_cancel, mul_one, id_eq] using (hd.comp s ((hasDerivAt_id s).sub_const 1)).fun_neg

/-- Heat potential, defined pointwise by `heatPrimitive C h (AxisymmetricFields.profilePoint w.1
w.2) • coordinateVector 2`. -/
noncomputable def heatPotential (C h : ℝ) : VelocityField :=
  fun w => heatPrimitive C h (AxisymmetricFields.profilePoint w.1 w.2) • coordinateVector 2

theorem heatPotential_smoothAt (C : ℝ) {h : ℝ} (hh : 0 < h) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    ContDiffAt ℝ ∞ (heatPotential C h) w :=
  ((heatPrimitive_smoothAt C hh (p := AxisymmetricFields.profilePoint w.1 w.2) hs).comp w
    AxisymmetricFields.contDiff_profilePoint.contDiffAt).smul contDiffAt_const

/-! ## Identifying the complete summed potential in the heat exterior -/

theorem gaugedSwirl_eq_heatPrimitive {a : ℕ → ℕ} (ha : StrictMono a) {h C R E : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (hext : BaseExterior.ExteriorCoefficients d R)
    (hheat : EqOn (BaseExterior.leadingAngular h C d) (BaseExterior.heatCoefficient E h)
      (BaseExterior.exteriorDomain h R)) {p : Point} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hseg : ∀ r ∈ uIcc (1 : ℝ) p.2.1,
      (p.1, (r, p.2.2)) ∈ BaseExterior.exteriorDomain h R) :
    gaugedSwirl a h C d p = heatPrimitive E h p := by
  let f : ℝ → ℝ := fun r => SlowBorelBase.swirlPotential a h C d (p.1, (r, p.2.2)) -
    heatPrimitive E h (p.1, (r, p.2.2))
  have hdf : ∀ r ∈ uIcc (1 : ℝ) p.2.1, HasDerivAt f 0 r := by
    intro r hr
    have hpos : 0 < r := (lt_min (by norm_num : (0 : ℝ) < 1) hs).trans_le hr.1
    have hK : DifferentiableAt ℝ (SlowBorelBase.swirlPotential a h C d) (p.1, (r, p.2.2)) :=
      (SlowBorelBase.physicalProfile_smoothAt (p := (p.1, (r, p.2.2))) ha hh hh1
        (SlowBorelBase.bundleComponent_smooth hd C 1) _ ht).differentiableAt (by simp)
    have hKd := radial_slice_hasDerivAt hK
    rw [BaseExterior.exterior_swirl_derivative ha hh hh1 hd hext (hseg r hr),
      hheat (hseg r hr)] at hKd
    have hHd := heatPrimitive_hasDerivAt E hh p.1 p.2.2 hpos
    rw [extendedHeatCoefficient_eq (p := (p.1, (r, p.2.2))) E h ht.le hpos] at hHd
    have he := hKd.fun_sub hHd
    simp only [sub_self] at he
    exact he
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hdf
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 1 p.2.1)
  simp only [intervalIntegral.integral_zero, f, heatPrimitive_anchor, sub_zero] at hi
  change SlowBorelBase.swirlPotential a h C d p -
    SlowBorelBase.swirlPotential a h C d (p.1, (1, p.2.2)) = heatPrimitive E h p
  linarith

theorem potential_eq_heatPotential {a : ℕ → ℕ} (ha : StrictMono a) {h C R E : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (hext : BaseExterior.ExteriorCoefficients d R)
    (hheat : EqOn (BaseExterior.leadingAngular h C d) (BaseExterior.heatCoefficient E h)
      (BaseExterior.exteriorDomain h R)) {w : SpaceTime} (ht : w.1 < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy w.2)
    (hseg : ∀ r ∈ uIcc (1 : ℝ) (AxisymmetricFields.radialEnergy w.2),
      (w.1, (r, w.2 2)) ∈ BaseExterior.exteriorDomain h R) :
    potential a h C d w = heatPotential E h w := by
  have hH := BaseExterior.exterior_stream_zero (a := a) (C := C) hh hh1 hR hext
    (hseg _ (right_mem_uIcc))
  have hK := gaugedSwirl_eq_heatPrimitive ha hh hh1 hd hext hheat
    (p := AxisymmetricFields.profilePoint w.1 w.2) ht hs hseg
  simp only [potential, AxisymmetricFields.potential, AxisymmetricFields.profilePoint,
    hH, mul_zero, zero_smul, zero_add, heatPotential] at *
  exact congrArg (fun r : ℝ => r • coordinateVector 2) hK

/-- A single full spacetime neighborhood places every point of the radial
integration segment in the actual heat exterior on the past side. -/
theorem exists_terminal_segment_neighborhood {h R : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) {x : Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      (∀ w ∈ U, 0 < AxisymmetricFields.radialEnergy w.2) ∧
      (∀ w ∈ U, w.1 < 1 → ∀ r ∈ uIcc (1 : ℝ) (AxisymmetricFields.radialEnergy w.2),
        (w.1, (r, w.2 2)) ∈ BaseExterior.exteriorDomain h R) := by
  let c : ℝ := min 1 (AxisymmetricFields.radialEnergy x / 2)
  have hc : 0 < c := lt_min (by norm_num) (half_pos hs)
  let b : ℝ := c / (R + 1)
  have hb : 0 < b := div_pos hc (by positivity)
  let U : Set SpaceTime := {w | AxisymmetricFields.radialEnergy x / 2 <
      AxisymmetricFields.radialEnergy w.2 ∧
    1 - w.1 < SimilarityCoordinates.forwardScalar (2 * h) (w.2 2) b}
  have hfcont : Continuous (fun w : SpaceTime =>
      SimilarityCoordinates.forwardScalar (2 * h) (w.2 2) b) :=
    continuous_const.sub
      ((((AxisymmetricFields.projection 2).continuous.comp continuous_snd).pow 2).mul
          continuous_const)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const
      ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)).inter
      (isOpen_lt (continuous_const.sub continuous_fst) hfcont)
  have hxU : (1, x) ∈ U := by
    constructor
    · linarith
    · simpa [SimilarityCoordinates.forwardScalar, hx] using hb
  refine ⟨U, hU, hxU, ?_, ?_⟩
  · intro w hw
    exact (half_pos hs).trans hw.1
  · intro w hw ht r hr
    have hq : 0 < SimilarityProfile.q h (w.1, (r, w.2 2)) := SimilarityProfile.q_pos hh hh1 ht
    have hqb : SimilarityProfile.q h (w.1, (r, w.2 2)) < b :=
      ModulatedExterior.coordinateQ_lt_of_forward_lt (by linarith) (by linarith)
        hb (sub_pos.mpr ht) hw.2
    have hbeq : b * (R + 1) = c := div_mul_cancel₀ _ (by positivity)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcrad : c ≤ AxisymmetricFields.radialEnergy w.2 := (min_le_right _ _).trans hw.1.le
    have hcr : c ≤ r := (le_min hc1 hcrad).trans hr.1
    refine ⟨ht, ?_⟩
    change R < r / SimilarityProfile.q h (w.1, (r, w.2 2))
    apply (lt_div_iff₀ hq).mpr
    calc
      R * SimilarityProfile.q h (w.1, (r, w.2 2)) ≤ R * b :=
        mul_le_mul_of_nonneg_left hqb.le hR
      _ < c := by nlinarith
      _ ≤ r := hcr

/-- An explicit smooth ambient extension of the gauge-corrected potential
near every nonzero point of the terminal central plane. -/
theorem central_oneSidedExtension {a : ℕ → ℕ} (ha : StrictMono a) {h C R E : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (hext : BaseExterior.ExteriorCoefficients d R)
    (hheat : EqOn (BaseExterior.leadingAngular h C d) (BaseExterior.heatCoefficient E h)
      (BaseExterior.exteriorDomain h R)) {x : Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    Nonempty (JointResidualLimits.OneSidedExtension (potential a h C d) x) := by
  obtain ⟨U, hU, hxU, hrad, hseg⟩ := exists_terminal_segment_neighborhood hh hh1 hR hx hs
  refine ⟨{
    value := heatPotential E h
    domain := U
    isOpen := hU
    mem := hxU
    smooth := fun w hw => (heatPotential_smoothAt E hh (hrad w hw)).contDiffWithinAt
    agrees := ?_ }⟩
  intro w hw
  exact (potential_eq_heatPotential ha hh hh1 hR hd hext hheat hw.2.1
    (hrad w hw.1) (hseg w hw.1 hw.2.1)).symm

/-- At each positive scale, the gauge subtracts the radial constant of
every active term in the actual common-cutoff sum. -/
theorem gaugedSwirl_finite_sum {a : ℕ → ℕ} (ha : StrictMono a) {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (d : SlowBorelBase.Coefficients)
    {p : Point} (ht : p.1 < 1) : ∃ N : ℕ,
    gaugedSwirl a h C d p = SimilarityProfile.q h p ^ (1 / 2 - CoordinateAlgebra.A h) *
      (SlowBorelBase.bundleComponent C d 1 0 (SimilarityProfile.inner h p) -
        SlowBorelBase.bundleComponent C d 1 0 (SimilarityProfile.inner h (radialAnchor p)) +
      ∑ j ∈ Finset.range N, SlowBorelBase.coefficientWeight a h (SimilarityProfile.q h p) j *
        (SlowBorelBase.bundleComponent C d 1 j (SimilarityProfile.inner h p) -
          SlowBorelBase.bundleComponent C d 1 j (SimilarityProfile.inner h (radialAnchor p)))) := by
  obtain ⟨N, hN⟩ := SlowBorelBase.slowSum_finite_at_scale ha h (SimilarityProfile.q_pos hh hh1 ht)
  refine ⟨N, ?_⟩
  change SimilarityProfile.q h p ^ (1 / 2 - CoordinateAlgebra.A h) *
      SlowBorelBase.slowSum a h (SlowBorelBase.bundleComponent C d 1)
        (SimilarityProfile.q h p, SimilarityProfile.inner h p) -
    SimilarityProfile.q h p ^ (1 / 2 - CoordinateAlgebra.A h) *
      SlowBorelBase.slowSum a h (SlowBorelBase.bundleComponent C d 1)
        (SimilarityProfile.q h p, SimilarityProfile.inner h (radialAnchor p)) = _
  rw [hN, hN]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The primitive hypotheses above are discharged for the actual repaired
coefficient scheme with its literal leading profile and exterior support. -/
theorem realized_central_oneSidedExtension {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) {D : ProfileHistories.RadialDomain}
    (Q : ProfileHistories.Profiles D) {S : Set ℝ} {lo hi : ℝ}
    (M : AssembledSlowBase.FiniteModification W Q S lo hi)
    {s : GlobalSlowProfiles.Scheme S F.data.h W.axis.normalization}
    {d : SlowBorelBase.Coefficients} (hd : ModulatedExterior.RealizesScheme s M.contains d)
    (hbase : s.base = (AssembledSlowBase.modifiedScheme W Q M).base)
    (houter : s.B = AssembledSlowBase.nominalOuterRadius W)
    (hds : SlowBorelBase.SmoothCoefficients d) {a : ℕ → ℕ} (ha : StrictMono a)
    {x : Space} (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (potential a F.data.h W.axis.normalization d) x) :=
  central_oneSidedExtension ha F.data.h_pos F.data.h_lt_half
      (BaseExterior.nominalExteriorRadius_pos W).le
    hds (ModulatedExterior.realized_exterior_coefficients W Q M hd hbase houter)
    (fun _ hp => ModulatedExterior.realized_angular_pure_heat W Q M hd hbase hp) hx hs

/-! ## All terminal points away from the singular origin -/

theorem potential_eq_anchoredPotential (a : ℕ → ℕ) (h C : ℝ)
    (d : SlowBorelBase.Coefficients) :
    potential a h C d = SlowBaseEndpoint.anchoredPotential a h C d := rfl

/-- Nonzero axial extension, given by `SlowBaseEndpoint.anchoredPotentialNonzeroAxial ha hh hh1
hd C hx`. -/
noncomputable def nonzeroAxialExtension {a : ℕ → ℕ} (ha : StrictMono a) {h C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (potential a h C d) x :=
  SlowBaseEndpoint.anchoredPotentialNonzeroAxial ha hh hh1 hd C hx

theorem awayExtensions {a : ℕ → ℕ} (ha : StrictMono a) {h C R E : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (hext : BaseExterior.ExteriorCoefficients d R)
    (hheat : EqOn (BaseExterior.leadingAngular h C d) (BaseExterior.heatCoefficient E h)
      (BaseExterior.exteriorDomain h R)) :
    JointResidualLimits.AwayExtensions (potential a h C d) := by
  intro x hx
  by_cases hz : x 2 = 0
  · exact central_oneSidedExtension ha hh hh1 hR hd hext hheat hz
      (SlowBaseEndpoint.radialEnergy_pos_of_nonzero_of_axial_zero hx hz)
  · exact ⟨nonzeroAxialExtension ha hh hh1 hd hz⟩

theorem realized_awayExtensions {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) {D : ProfileHistories.RadialDomain}
    (Q : ProfileHistories.Profiles D) {S : Set ℝ} {lo hi : ℝ}
    (M : AssembledSlowBase.FiniteModification W Q S lo hi)
    {s : GlobalSlowProfiles.Scheme S F.data.h W.axis.normalization}
    {d : SlowBorelBase.Coefficients} (hd : ModulatedExterior.RealizesScheme s M.contains d)
    (hbase : s.base = (AssembledSlowBase.modifiedScheme W Q M).base)
    (houter : s.B = AssembledSlowBase.nominalOuterRadius W)
    (hds : SlowBorelBase.SmoothCoefficients d) {a : ℕ → ℕ} (ha : StrictMono a) :
    JointResidualLimits.AwayExtensions (potential a F.data.h W.axis.normalization d) :=
  awayExtensions ha F.data.h_pos F.data.h_lt_half (BaseExterior.nominalExteriorRadius_pos W).le
    hds (ModulatedExterior.realized_exterior_coefficients W Q M hd hbase houter)
    (fun _ hp => ModulatedExterior.realized_angular_pure_heat W Q M hd hbase hp)

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The actual entrance-aligned slow base with its selected cutoff schedule,
in the anchored gauge. -/
noncomputable def finalPotential (upper : ℝ) (B : ℕ) : VelocityField :=
  potential (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v)

theorem finalPotential_eq_sub_gauge (upper : ℝ) (B : ℕ) (w : SpaceTime) :
    finalPotential H v upper B w = FinalSlowBase.vectorPotential H v upper B w -
      SlowBorelBase.swirlPotential (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
        (FinalSlowBase.coefficients H v) (w.1, (1, w.2 2)) • coordinateVector 2 :=
  potential_eq_sub_gauge _ _ _ _ w

theorem finalPotential_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (finalPotential H v upper B) BaseResidual.past :=
  potential_smooth (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (FinalSlowBase.coefficients_smooth H v)

theorem finalPotential_sameCurl (upper : ℝ) (B : ℕ) {w : SpaceTime} (ht : w.1 < 1) :
    SpatialCurl.spatialCurl (finalPotential H v upper B) w = FinalSlowBase.velocity H v upper B w :=
  spatialCurl_potential (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (FinalSlowBase.coefficients_smooth H v) ht

theorem finalPotential_awayExtensions (upper : ℝ) (B : ℕ) :
    JointResidualLimits.AwayExtensions (finalPotential H v upper B) :=
  realized_awayExtensions W v.profiles v.finiteModification
    (FinalSlowBase.realizesScheme H v) (EntranceAlignedBase.modulated_base_eq H v)
    (EntranceAlignedBase.modulated_outer H v) (FinalSlowBase.coefficients_smooth H v)
    (FinalSlowBase.scales_strictMono H v upper B)

end FinalBase

/-- A closed choice of the already constructed leading profile, repaired
hierarchy, modulation, and common cutoff schedule. -/
noncomputable def constructedPotential (upper : ℝ) (B : ℕ) : VelocityField :=
  finalPotential FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
      upper B

theorem constructedPotential_properties (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (constructedPotential upper B) BaseResidual.past ∧
    JointResidualLimits.AwayExtensions (constructedPotential upper B) ∧
    EqOn (SpatialCurl.spatialCurl (constructedPotential upper B))
      (FinalSlowBase.velocity FinalSlowBase.actualProfile.certificate
        FinalSlowBase.actualProfile.modulation upper B) BaseResidual.past :=
  ⟨finalPotential_smooth _ _ upper B, finalPotential_awayExtensions _ _ upper B,
    fun _ ht => finalPotential_sameCurl _ _ upper B ht.1⟩

end NavierStokes.TailGaugePotential
