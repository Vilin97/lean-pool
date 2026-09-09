/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalStress
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatProfileExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.EdgeWeightJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalHeatCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalPressure
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone

@[expose] public section

/-!
# Actual terminal stress factors at the outer edge

The logarithmic edge coordinate is applied to the actual physical heat carrier
and to `OutgoingTail.tailShape`.  A positive global physical chart keeps the
parameter coefficients smooth without assuming a normalized stress factor.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingTail NavierStokes.TerminalStress

namespace NavierStokes.TerminalEdgeFactor

abbrev EdgeParam := ℝ × ℝ

noncomputable def timeOf (p : EdgeParam) : ℝ := 1 - Real.exp p.1
noncomputable def axisPoint (p : EdgeParam) : SimilarityProfile.PhysicalPoint :=
  (timeOf p, (0, p.2))
noncomputable def chartQ (d : TailData) (p : EdgeParam) : ℝ :=
  SimilarityProfile.q d.h (axisPoint p)
noncomputable def chartEta (d : TailData) (p : EdgeParam) : ℝ :=
  SimilarityProfile.eta d.h (axisPoint p)
noncomputable def outerRadius (d : TailData) (y0 : ℝ) (p : EdgeParam) : ℝ :=
  Real.sqrt (2 * chartQ d p * Real.exp (y0 + 3))
noncomputable def radius (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  outerRadius d y0 y.1 * Real.exp (-y.2 / 2)
noncomputable def chartPoint (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    SimilarityProfile.PhysicalPoint := radiusPoint (timeOf y.1) (radius d y0 y) y.1.2

theorem timeOf_lt_one (p : EdgeParam) : timeOf p < 1 := by
  unfold timeOf
  linarith [Real.exp_pos p.1]

theorem timeOf_contDiff : ContDiff ℝ ∞ timeOf :=
  contDiff_const.sub contDiff_fst.exp

theorem axisPoint_contDiff : ContDiff ℝ ∞ axisPoint :=
  timeOf_contDiff.prodMk (contDiff_const.prodMk contDiff_snd)

theorem chartQ_pos (d : TailData) (p : EdgeParam) : 0 < chartQ d p :=
  SimilarityProfile.q_pos d.h_pos d.h_lt_half (timeOf_lt_one p)

theorem chartQ_contDiff (d : TailData) : ContDiff ℝ ∞ (chartQ d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (SimilarityProfile.q_smoothAt d.h_pos d.h_lt_half
    (p := axisPoint p) (timeOf_lt_one p)).comp p axisPoint_contDiff.contDiffAt

theorem chartEta_contDiff (d : TailData) : ContDiff ℝ ∞ (chartEta d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (SimilarityProfile.eta_smoothAt d.h_pos d.h_lt_half
    (p := axisPoint p) (timeOf_lt_one p)).comp p axisPoint_contDiff.contDiffAt

theorem outerRadius_pos (d : TailData) (y0 : ℝ) (p : EdgeParam) : 0 < outerRadius d y0 p := by
  apply Real.sqrt_pos.mpr
  exact mul_pos (mul_pos (by norm_num) (chartQ_pos d p)) (Real.exp_pos _)

theorem outerRadius_contDiff (d : TailData) (y0 : ℝ) : ContDiff ℝ ∞ (outerRadius d y0) := by
  apply ((contDiff_const.mul (chartQ_contDiff d)).mul contDiff_const).sqrt
  intro p
  exact ne_of_gt (mul_pos (mul_pos (by norm_num) (chartQ_pos d p)) (Real.exp_pos _))

theorem radius_pos (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : 0 < radius d y0 y :=
  mul_pos (outerRadius_pos d y0 y.1) (Real.exp_pos _)

theorem radius_contDiff (d : TailData) (y0 : ℝ) : ContDiff ℝ ∞ (radius d y0) :=
  ((outerRadius_contDiff d y0).comp contDiff_fst).mul
    ((contDiff_snd.neg.div_const 2).exp)

theorem chartPoint_contDiff (d : TailData) (y0 : ℝ) : ContDiff ℝ ∞ (chartPoint d y0) :=
  (timeOf_contDiff.comp contDiff_fst).prodMk
    (((radius_contDiff d y0).pow 2).div_const 2 |>.prodMk contDiff_fst.snd)

theorem radius_square (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    radius d y0 y ^ 2 = 2 * chartQ d y.1 * Real.exp (y0 + 3 - y.2) := by
  have hq := chartQ_pos d y.1
  rw [radius, mul_pow, outerRadius, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  norm_num
  ring

theorem chartX (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    SimilarityProfile.X d.h (chartPoint d y0 y) = Real.exp (y0 + 3 - y.2) := by
  change (radius d y0 y ^ 2 / 2) / chartQ d y.1 = _
  rw [radius_square]
  field_simp [(chartQ_pos d y.1).ne']

theorem chart_logX (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    Real.log (SimilarityProfile.X d.h (chartPoint d y0 y)) = y0 + 3 - y.2 := by
  rw [chartX, Real.log_exp]

noncomputable def carrier (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  physicalHeat C (1 + d.h) (chartPoint d y0 y)

theorem carrier_eq (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    carrier C d y0 y = heatAmplitude C (1 + d.h) (timeOf y.1) (radius d y0 y) := rfl

theorem carrier_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (carrier C d y0) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact (physicalHeat_contDiffAt C (by linarith [d.h_pos])
    (p := chartPoint d y0 y) (timeOf_lt_one y.1)
    (div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num))).comp y
      (chartPoint_contDiff d y0).contDiffAt

theorem carrier_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    0 < carrier C d y0 y :=
  heatAmplitude_pos hC (by linarith [d.h_pos]) (timeOf_lt_one y.1) (radius_pos d y0 y)

noncomputable def carrierRadial (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  radius d y0 y * SimilarityProfile.partialS (physicalHeat C (1 + d.h)) (chartPoint d y0 y)

theorem carrierRadial_eq (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    carrierRadial C d y0 y =
      deriv (heatAmplitude C (1 + d.h) (timeOf y.1)) (radius d y0 y) := by
  have hp := physicalHeat_contDiffAt C (a := 1 + d.h) (by linarith [d.h_pos])
    (p := chartPoint d y0 y) (timeOf_lt_one y.1)
    (div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num))
  exact (radialSlice_hasDerivAt (hp.differentiableAt (by simp))).deriv.symm

theorem carrierRadial_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (carrierRadial C d y0) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hp := physicalHeat_contDiffAt C (a := 1 + d.h) (by linarith [d.h_pos])
    (p := chartPoint d y0 y) (timeOf_lt_one y.1)
    (div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num))
  exact (radius_contDiff d y0).contDiffAt.mul
    ((partialS_contDiffAt hp (m := ∞) (by simp)).comp y
      (chartPoint_contDiff d y0).contDiffAt)

noncomputable def denominator (d : TailData) (p : EdgeParam) : ℝ :=
  timeDenominator d.h (timeOf p) p.2

theorem denominator_pos (d : TailData) (p : EdgeParam) : 0 < denominator d p :=
  timeDenominator_pos d.h_pos d.h_lt_half (timeOf_lt_one p)

theorem denominator_contDiff (d : TailData) : ContDiff ℝ ∞ (denominator d) := by
  change ContDiff ℝ ∞ (fun p => chartQ d p * CoordinateAlgebra.L d.h (chartEta d p))
  exact (chartQ_contDiff d).mul
    (contDiff_const.sub (contDiff_const.mul ((chartEta_contDiff d).pow 2)))

/-- A radial logarithmic distance, with its outer radius kept explicit. -/
noncomputable def edgeCoordinate (R r : ℝ) : ℝ := -2 * Real.log (r / R)

theorem edgeCoordinate_hasDerivAt {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    HasDerivAt (edgeCoordinate R) (-2 / r) r := by
  convert! (((hasDerivAt_id r).div_const R).log (div_pos hr hR).ne').const_mul (-2) using 1
  dsimp only [id]
  field_simp

theorem edgeCoordinate_nonpos {R r : ℝ} (hR : 0 < R) (hRr : R ≤ r) :
    edgeCoordinate R r ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Real.log_nonneg ((le_div_iff₀ hR).mpr (by simpa using hRr)))

theorem radius_edgeCoordinate (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ} (hr : 0 < r) :
    radius d y0 (p, edgeCoordinate (outerRadius d y0 p) r) = r := by
  have hR := outerRadius_pos d y0 p
  have he : -edgeCoordinate (outerRadius d y0 p) r / 2 =
      Real.log (r / outerRadius d y0 p) := by unfold edgeCoordinate; ring
  rw [radius, he, Real.exp_log (div_pos hr hR)]
  field_simp

theorem edgeCoordinate_radius (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    edgeCoordinate (outerRadius d y0 y.1) (radius d y0 y) = y.2 := by
  have hR := (outerRadius_pos d y0 y.1).ne'
  unfold edgeCoordinate radius
  rw [mul_div_cancel_left₀ _ hR, Real.log_exp]
  ring

theorem physical_logX (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ} (hr : 0 < r) :
    Real.log (SimilarityProfile.X d.h (radiusPoint (timeOf p) r p.2)) =
      y0 + 3 - edgeCoordinate (outerRadius d y0 p) r := by
  have h := chart_logX d y0 (p, edgeCoordinate (outerRadius d y0 p) r)
  simpa only [chartPoint, radius_edgeCoordinate d y0 p hr] using h

/-- Continuous positive-radius functions with a zero tail are genuinely integrable. -/
theorem integrableOn_Ioi_of_eventually_zero {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (Ioi 0)) (hz : f =ᶠ[atTop] fun _ => 0) :
    IntegrableOn f (Ioi r) := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 hz
  have hi : IntegrableOn f (Icc r (max r b)) :=
    (hf.mono (fun u hu => hr.trans_le hu.1)).integrableOn_Icc
  apply (hi.integrable_indicator measurableSet_Icc).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  by_cases hmax : u ≤ max r b
  · simp only [indicator_of_mem (show u ∈ Icc r (max r b) from ⟨hu.le, hmax⟩)]
  · have hbu : b ≤ u := (le_max_right r b).trans (le_of_not_ge hmax)
    rw [indicator_of_notMem (show u ∉ Icc r (max r b) from fun h => hmax h.2), hb u hbu]

noncomputable def radialFlatDensity (c : ℝ) (j : ℕ) (a : ℝ → ℝ) (R u : ℝ) : ℝ :=
  (2 / u) * FlatPrimitive.integrand c j a (edgeCoordinate R u)

theorem radialFlatDensity_integrable {c R r : ℝ} (hc : 0 < c) (hR : 0 < R) (hr : 0 < r)
    (j : ℕ) {a : ℝ → ℝ} (ha : Continuous a) :
    IntegrableOn (radialFlatDensity c j a R) (Ioi r) := by
  apply integrableOn_Ioi_of_eventually_zero hr
  · intro u hu
    exact ((continuousAt_const.div continuousAt_id hu.ne').mul
      ((FlatPrimitive.integrand_continuous hc j ha).continuousAt.comp
        (edgeCoordinate_hasDerivAt hR hu).continuousAt)).continuousWithinAt
  · filter_upwards [eventually_ge_atTop R] with u hu
    simp only [radialFlatDensity, FlatPrimitive.integrand,
      FlatCutoff.edge_of_nonpos c (edgeCoordinate_nonpos hR hu), zero_div, zero_mul, mul_zero]

/-- An actual radial-to-edge change of variables, proved by the improper FTC. -/
theorem radialFlatDensity_integral {c R r : ℝ} (hc : 0 < c) (hR : 0 < R) (hr : 0 < r)
    (j : ℕ) {a : ℝ → ℝ} (ha : Continuous a) :
    (∫ u in Ioi r, radialFlatDensity c j a R u) =
      FlatPrimitive.primitive c j a (edgeCoordinate R r) := by
  have hd : ∀ u ∈ Ici r, HasDerivAt
      (fun v => -FlatPrimitive.primitive c j a (edgeCoordinate R v))
      (radialFlatDensity c j a R u) u := by
    intro u hu
    convert! ((FlatPrimitive.primitive_hasDerivAt hc j ha (edgeCoordinate R u)).comp u
      (edgeCoordinate_hasDerivAt hR (hr.trans_le hu))).neg using 1
    unfold radialFlatDensity
    ring
  have hz : Tendsto (fun v => -FlatPrimitive.primitive c j a (edgeCoordinate R v)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop R] with u hu
    simp only [FlatPrimitive.primitive_of_nonpos c j a (edgeCoordinate_nonpos hR hu), neg_zero]
  simpa only [sub_neg_eq_add, zero_add] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hd (radialFlatDensity_integrable hc hR hr j ha) hz

theorem chart_tau_identity (d : TailData) (p : EdgeParam) :
    1 - timeOf p = chartQ d p * (1 - chartEta d p ^ 2) := by
  exact SimilarityCoordinates.tau_coordinate_identity
    (by linarith [d.h_pos] : 0 < 2 * d.h)
    (by linarith [d.h_lt_half] : 2 * d.h < 1)
    (p := (1 - timeOf p, p.2)) (sub_pos.mpr (timeOf_lt_one p))

/-- The physical heat argument retains the varying factor `1-eta²`. -/
theorem physical_heat_argument (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    2 * (1 - timeOf y.1) / (radius d y0 y ^ 2 / 2) =
      2 * (1 - chartEta d y.1 ^ 2) / Real.exp (y0 + 3 - y.2) := by
  rw [chart_tau_identity, radius_square]
  field_simp [(chartQ_pos d y.1).ne']

noncomputable def logTaper (d : TailData) (y0 : ℝ) (y : ℝ) : ℝ := tailShape d (y - y0)
noncomputable def radialTaper (d : TailData) (y0 : ℝ) (p : EdgeParam) : ℝ → ℝ :=
  radialSlice (flattening d.h (logTaper d y0)) (timeOf p) p.2

theorem logTaper_contDiff (d : TailData) (y0 : ℝ) : ContDiff ℝ ∞ (logTaper d y0) :=
  (tailShape_contDiff d).comp (contDiff_id.sub contDiff_const)

theorem logTaper_hasDerivAt (d : TailData) (y0 y : ℝ) :
    HasDerivAt (logTaper d y0) (tailShapeDeriv d (y - y0)) y := by
  convert! (tailShape_hasDerivAt d (y - y0)).comp y ((hasDerivAt_id y).sub_const y0) using 1
  simp

theorem logTaper_deriv_at_radius (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    deriv (logTaper d y0) (Real.log (SimilarityProfile.X d.h (radiusPoint (timeOf p) r p.2))) =
      (FlatCutoff.edge 4 (edgeCoordinate (outerRadius d y0 p) r) /
        edgeCoordinate (outerRadius d y0 p) r ^ 3) *
        taperSlopeFactor d (edgeCoordinate (outerRadius d y0 p) r) := by
  rw [(logTaper_hasDerivAt d y0 _).deriv, physical_logX d y0 p hr]
  rw [show y0 + 3 - edgeCoordinate (outerRadius d y0 p) r - y0 =
    3 - edgeCoordinate (outerRadius d y0 p) r by ring]
  exact tailShapeDeriv_factorization d _

theorem radialTaper_contDiffAt (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) : ContDiffAt ℝ ∞ (radialTaper d y0 p) r := by
  change ContDiffAt ℝ ∞ (fun u => logTaper d y0 (Real.log ((u ^ 2 / 2) / chartQ d p))) r
  exact (logTaper_contDiff d y0).contDiffAt.comp r
    (((contDiffAt_id.pow 2).div_const 2).div_const (chartQ d p) |>.log
      (div_pos (div_pos (sq_pos_of_pos hr) (by norm_num)) (chartQ_pos d p)).ne')

theorem radialTaper_deriv (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    deriv (radialTaper d y0 p) r = (2 / r) *
      ((FlatCutoff.edge 4 (edgeCoordinate (outerRadius d y0 p) r) /
        edgeCoordinate (outerRadius d y0 p) r ^ 3) *
        taperSlopeFactor d (edgeCoordinate (outerRadius d y0 p) r)) := by
  change deriv (radialSlice (flattening d.h (logTaper d y0)) (timeOf p) p.2) r = _
  rw [(flattening_radial_hasDerivAt (z := p.2) d.h_pos d.h_lt_half (timeOf_lt_one p) hr
    ((logTaper_contDiff d y0).differentiable (by simp) _)).deriv,
    logTaper_deriv_at_radius d y0 p hr]
  ring

theorem radialTaper_plateau (d : TailData) (y0 : ℝ) (p : EdgeParam) :
    radialTaper d y0 p =ᶠ[atTop] fun _ => 1 := by
  apply radial_flattening_plateau d.h_pos d.h_lt_half (timeOf_lt_one p)
  filter_upwards [eventually_ge_atTop (y0 + 3)] with y hy
  exact tailShape_late d (by linarith)

noncomputable def boundaryCoefficient (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  (2 * carrier C d y0 y / radius d y0 y) * taperSlopeFactor d y.2

noncomputable def timeCoefficient (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  (radius d y0 y ^ 3 * carrier C d y0 y / (2 * denominator d y.1)) * taperSlopeFactor d y.2

noncomputable def correctionCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ :=
  (radius d y0 y * carrier C d y0 y - radius d y0 y ^ 2 * carrierRadial C d y0 y) *
    taperSlopeFactor d y.2

theorem boundaryCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (boundaryCoefficient C d y0) :=
  (((contDiff_const.mul (carrier_contDiff C d y0)).div (radius_contDiff d y0)
    (fun y => (radius_pos d y0 y).ne')).mul
      ((taperSlopeFactor_contDiff d).comp contDiff_snd))

theorem timeCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (timeCoefficient C d y0) :=
  ((((radius_contDiff d y0).pow 3).mul (carrier_contDiff C d y0)).div
    (contDiff_const.mul ((denominator_contDiff d).comp contDiff_fst))
    (fun y => (mul_pos (by norm_num : (0 : ℝ) < 2) (denominator_pos d y.1)).ne')).mul
      ((taperSlopeFactor_contDiff d).comp contDiff_snd)

theorem correctionCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (correctionCoefficient C d y0) :=
  (((radius_contDiff d y0).mul (carrier_contDiff C d y0)).sub
    (((radius_contDiff d y0).pow 2).mul (carrierRadial_contDiff C d y0))).mul
      ((taperSlopeFactor_contDiff d).comp contDiff_snd)

theorem carrier_at_radius (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    carrier C d y0 (p, edgeCoordinate (outerRadius d y0 p) r) =
      heatAmplitude C (1 + d.h) (timeOf p) r := by
  rw [carrier_eq, radius_edgeCoordinate d y0 p hr]

theorem carrierRadial_at_radius (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    carrierRadial C d y0 (p, edgeCoordinate (outerRadius d y0 p) r) =
      deriv (heatAmplitude C (1 + d.h) (timeOf p)) r := by
  rw [carrierRadial_eq, radius_edgeCoordinate d y0 p hr]

theorem time_weight_eq_density (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    r ^ 2 * timeResidual C d.h (logTaper d y0) (timeOf p) p.2 r =
      radialFlatDensity 4 3 (fun v => timeCoefficient C d y0 (p, v)) (outerRadius d y0 p) r := by
  unfold timeResidual radialFlatDensity FlatPrimitive.integrand timeCoefficient
  dsimp only
  rw [logTaper_deriv_at_radius d y0 p hr, carrier_at_radius C d y0 p hr,
    radius_edgeCoordinate d y0 p hr]
  change _ = (2 / r) * ((FlatCutoff.edge 4 (edgeCoordinate (outerRadius d y0 p) r) /
    edgeCoordinate (outerRadius d y0 p) r ^ 3) *
      (r ^ 3 * heatAmplitude C (1 + d.h) (timeOf p) r /
        (2 * timeDenominator d.h (timeOf p) p.2) *
          taperSlopeFactor d (edgeCoordinate (outerRadius d y0 p) r)))
  by_cases he : edgeCoordinate (outerRadius d y0 p) r = 0
  · simp [he]
  · field_simp [hr.ne', he, (timeDenominator_pos d.h_pos d.h_lt_half (timeOf_lt_one p)).ne']

theorem correction_eq_density (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    correction (heatAmplitude C (1 + d.h) (timeOf p)) (radialTaper d y0 p) r =
      radialFlatDensity 4 3 (fun v => correctionCoefficient C d y0 (p, v))
        (outerRadius d y0 p) r := by
  unfold correction radialFlatDensity FlatPrimitive.integrand correctionCoefficient
  dsimp only
  rw [radialTaper_deriv d y0 p hr, carrier_at_radius C d y0 p hr,
    carrierRadial_at_radius C d y0 p hr, radius_edgeCoordinate d y0 p hr]
  ring

theorem time_weight_integrable (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun u => u ^ 2 * timeResidual C d.h (logTaper d y0) (timeOf p) p.2 u) (Ioi r) :=
      by
  apply (radialFlatDensity_integrable (by norm_num : (0 : ℝ) < 4)
    (outerRadius_pos d y0 p) hr 3
    ((timeCoefficient_contDiff C d y0).continuous.comp
      (continuous_const.prodMk continuous_id))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (time_weight_eq_density C d y0 p (hr.trans hu)).symm

theorem correction_integrable (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (correction (heatAmplitude C (1 + d.h) (timeOf p)) (radialTaper d y0 p))
      (Ioi r) := by
  apply (radialFlatDensity_integrable (by norm_num : (0 : ℝ) < 4)
    (outerRadius_pos d y0 p) hr 3
    ((correctionCoefficient_contDiff C d y0).continuous.comp
      (continuous_const.prodMk continuous_id))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (correction_eq_density C d y0 p (hr.trans hu)).symm

theorem time_weight_integral (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    (∫ u in Ioi (radius d y0 y),
      u ^ 2 * timeResidual C d.h (logTaper d y0) (timeOf y.1) y.1.2 u) =
        ParametricFlatFactor.primitive 4 3 (timeCoefficient C d y0) y := by
  calc
    _ = ∫ u in Ioi (radius d y0 y),
        radialFlatDensity 4 3 (fun v => timeCoefficient C d y0 (y.1, v))
          (outerRadius d y0 y.1) u := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact time_weight_eq_density C d y0 y.1 ((radius_pos d y0 y).trans hu)
    _ = _ := by
      rw [radialFlatDensity_integral (a := fun v => timeCoefficient C d y0 (y.1, v))
        (by norm_num : (0 : ℝ) < 4)
        (outerRadius_pos d y0 y.1) (radius_pos d y0 y) 3
        ((timeCoefficient_contDiff C d y0).continuous.comp
          (continuous_const.prodMk continuous_id)), edgeCoordinate_radius]
      rfl

theorem correction_integral (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    (∫ u in Ioi (radius d y0 y),
      correction (heatAmplitude C (1 + d.h) (timeOf y.1)) (radialTaper d y0 y.1) u) =
        ParametricFlatFactor.primitive 4 3 (correctionCoefficient C d y0) y := by
  calc
    _ = ∫ u in Ioi (radius d y0 y),
        radialFlatDensity 4 3 (fun v => correctionCoefficient C d y0 (y.1, v))
          (outerRadius d y0 y.1) u := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact correction_eq_density C d y0 y.1 ((radius_pos d y0 y).trans hu)
    _ = _ := by
      rw [radialFlatDensity_integral (a := fun v => correctionCoefficient C d y0 (y.1, v))
        (by norm_num : (0 : ℝ) < 4)
        (outerRadius_pos d y0 y.1) (radius_pos d y0 y) 3
        ((correctionCoefficient_contDiff C d y0).continuous.comp
          (continuous_const.prodMk continuous_id)), edgeCoordinate_radius]
      rfl

theorem viscous_weight_integrable (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u => u ^ 2 * viscousResidual
      (heatAmplitude C (1 + d.h) (timeOf p)) (radialTaper d y0 p) u) (Ioi r) := by
  apply integrableOn_Ioi_of_eventually_zero hr
  · intro u hu
    have hK := heatAmplitude_contDiffAt C (a := 1 + d.h)
      (by linarith [d.h_pos]) (timeOf_lt_one p) hu
    have hKr := contDiffAt_deriv hK (m := ∞) (by simp)
    have hg := radialTaper_contDiffAt d y0 p hu
    have hgr := contDiffAt_deriv hg (m := ∞) (by simp)
    have hgrr := contDiffAt_deriv hgr (m := ∞) (by simp)
    have hV : ContDiffAt ℝ ∞ (fun v => v ^ 2 * viscousResidual
        (heatAmplitude C (1 + d.h) (timeOf p)) (radialTaper d y0 p) v) u :=
      (contDiffAt_id.pow 2).mul
        ((hK.neg.mul (hgrr.add (hgr.div contDiffAt_id hu.ne'))).sub
          ((contDiffAt_const.mul hKr).mul hgr))
    exact hV.continuousAt.continuousWithinAt
  · have hg := deriv_eventually_zero_of_eventually_const (radialTaper_plateau d y0 p)
    have hgg := deriv_eventually_zero_of_eventually_const hg
    filter_upwards [hg, hgg] with u hu huu
    simp only [viscousResidual, hu, huu, zero_div, add_zero, mul_zero, sub_self]

noncomputable def angularStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  terminalStress C d.h (logTaper d y0) (timeOf y.1) y.1.2 (radius d y0 y)

noncomputable def angularFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  boundaryCoefficient C d y0 y + (y.2 ^ 3 / radius d y0 y ^ 2) *
    (ParametricFlatFactor.factor 4 3 (timeCoefficient C d y0) y +
      ParametricFlatFactor.factor 4 3 (correctionCoefficient C d y0) y)

theorem angularFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (angularFactor C d y0) :=
  (boundaryCoefficient_contDiff C d y0).add
    (((contDiff_snd.pow 3).div ((radius_contDiff d y0).pow 2)
      (fun y => (sq_pos_of_pos (radius_pos d y0 y)).ne')).mul
        ((ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
          (timeCoefficient_contDiff C d y0)).add
          (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
            (correctionCoefficient_contDiff C d y0))))

/-- The leading angular stress itself, with all backward-integral hypotheses
proved for the actual heat carrier and actual outgoing taper. -/
theorem angularStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    angularStress C d y0 y = (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * angularFactor C d y0 y := by
  have hf : ContDiff ℝ 2 (logTaper d y0) :=
    (logTaper_contDiff d y0).of_le (WithTop.coe_le_coe.mpr le_top)
  have hform := terminalStress_formula C d.h_pos d.h_lt_half (timeOf_lt_one y.1)
    (radius_pos d y0 y) hf (viscous_weight_integrable C d y0 y.1 (radius_pos d y0 y))
    (correction_integrable C d y0 y.1 (radius_pos d y0 y))
    (time_weight_integrable C d y0 y.1 (radius_pos d y0 y))
    (outgoing_boundary_tendsto_zero d C y0 (t := timeOf y.1) (z := y.1.2) (timeOf_lt_one y.1))
  change angularStress C d y0 y =
    heatAmplitude C (1 + d.h) (timeOf y.1) (radius d y0 y) *
      deriv (radialTaper d y0 y.1) (radius d y0 y) +
      ((∫ u in Ioi (radius d y0 y),
        u ^ 2 * timeResidual C d.h (logTaper d y0) (timeOf y.1) y.1.2 u) +
        ∫ u in Ioi (radius d y0 y),
          correction (heatAmplitude C (1 + d.h) (timeOf y.1)) (radialTaper d y0 y.1) u) /
          radius d y0 y ^ 2 at hform
  rw [hform, radialTaper_deriv d y0 y.1 (radius_pos d y0 y), edgeCoordinate_radius,
    time_weight_integral, correction_integral,
    ParametricFlatFactor.primitive_eq_scale_mul_factor,
    ParametricFlatFactor.primitive_eq_scale_mul_factor, ← carrier_eq C d y0 y]
  unfold angularFactor boundaryCoefficient FlatPrimitive.scale
  ring

theorem angularFactor_zero (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) :
    angularFactor C d y0 (p, 0) =
      (2 * carrier C d y0 (p, 0) / radius d y0 (p, 0)) * taperSlopeFactor d 0 := by
  simp only [angularFactor, zero_pow (by norm_num : 3 ≠ 0), zero_div, zero_mul,
    add_zero, boundaryCoefficient]

theorem angularFactor_zero_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) (p : EdgeParam) :
    0 < angularFactor C d y0 (p, 0) := by
  rw [angularFactor_zero]
  exact mul_pos (div_pos (mul_pos (by norm_num) (carrier_pos hC d y0 (p, 0)))
    (radius_pos d y0 (p, 0))) (taperSlopeFactor_zero_pos d)

theorem angularFactor_eventually_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) (p : EdgeParam) :
    ∀ᶠ y in 𝓝 (p, (0 : ℝ)), 0 < angularFactor C d y0 y :=
  (angularFactor_contDiff C d y0).continuous.continuousAt.eventually
    (Ioi_mem_nhds (angularFactor_zero_pos hC d y0 p))

theorem angularStress_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (angularStress C d y0) := by
  have heq : angularStress C d y0 = fun y : EdgeParam × ℝ =>
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * angularFactor C d y0 y :=
    funext (angularStress_factorization C d y0)
  rw [heq]
  exact ((FlatCutoff.edge_div_pow_contDiff (by norm_num : (0 : ℝ) < 4) 3).comp
    contDiff_snd).mul (angularFactor_contDiff C d y0)

theorem angularStress_normalized (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam)
    {δ : ℝ} (hδ : 0 < δ) :
    angularStress C d y0 (p, δ) / (Real.exp (-4 / δ ^ 2) / δ ^ 3) =
      angularFactor C d y0 (p, δ) := by
  rw [angularStress_factorization, FlatCutoff.edge_of_pos 4 hδ]
  have hden : Real.exp (-4 / δ ^ 2) / δ ^ 3 ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hden

/-- The same edge coordinate in the regular radial variable `s=r²/2`. -/
noncomputable def logCoordinate (S s : ℝ) : ℝ := edgeCoordinate S s / 2

theorem logCoordinate_hasDerivAt {S s : ℝ} (hS : 0 < S) (hs : 0 < s) :
    HasDerivAt (logCoordinate S) (-1 / s) s := by
  convert! (edgeCoordinate_hasDerivAt hS hs).div_const 2 using 1
  ring

theorem logCoordinate_nonpos {S s : ℝ} (hS : 0 < S) (hSs : S ≤ s) :
    logCoordinate S s ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (edgeCoordinate_nonpos hS hSs) (by norm_num)

noncomputable def outerS (d : TailData) (y0 : ℝ) (p : EdgeParam) : ℝ :=
  chartQ d p * Real.exp (y0 + 3)

theorem outerS_pos (d : TailData) (y0 : ℝ) (p : EdgeParam) : 0 < outerS d y0 p :=
  mul_pos (chartQ_pos d p) (Real.exp_pos _)

theorem radialS_eq (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    radius d y0 y ^ 2 / 2 = outerS d y0 y.1 * Real.exp (-y.2) := by
  rw [radius_square]
  unfold outerS
  rw [sub_eq_add_neg, Real.exp_add]
  ring

theorem radialS_logCoordinate (d : TailData) (y0 : ℝ) (p : EdgeParam) {s : ℝ} (hs : 0 < s) :
    radius d y0 (p, logCoordinate (outerS d y0 p) s) ^ 2 / 2 = s := by
  rw [radialS_eq]
  have he : -logCoordinate (outerS d y0 p) s = Real.log (s / outerS d y0 p) := by
    unfold logCoordinate edgeCoordinate
    ring
  rw [he, Real.exp_log (div_pos hs (outerS_pos d y0 p))]
  field_simp [(outerS_pos d y0 p).ne']

theorem logCoordinate_radialS (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    logCoordinate (outerS d y0 y.1) (radius d y0 y ^ 2 / 2) = y.2 := by
  rw [radialS_eq]
  unfold logCoordinate edgeCoordinate
  rw [mul_div_cancel_left₀ _ (outerS_pos d y0 y.1).ne', Real.log_exp]
  ring

theorem physical_logX_s (d : TailData) (y0 : ℝ) (p : EdgeParam) {s : ℝ} (hs : 0 < s) :
    Real.log (s / chartQ d p) = y0 + 3 - logCoordinate (outerS d y0 p) s := by
  have h := chart_logX d y0 (p, logCoordinate (outerS d y0 p) s)
  change Real.log ((radius d y0 (p, logCoordinate (outerS d y0 p) s) ^ 2 / 2) /
    chartQ d p) = _ at h
  rwa [radialS_logCoordinate d y0 p hs] at h

theorem carrier_at_s (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam) {s : ℝ} (hs : 0 < s) :
    carrier C d y0 (p, logCoordinate (outerS d y0 p) s) =
      physicalHeat C (1 + d.h) (timeOf p, (s, p.2)) := by
  unfold carrier physicalHeat chartPoint radiusPoint
  dsimp only
  rw [radialS_logCoordinate d y0 p hs]

noncomputable def scalarFlatDensity (c : ℝ) (j : ℕ) (a : ℝ → ℝ) (S s : ℝ) : ℝ :=
  (1 / s) * FlatPrimitive.integrand c j a (logCoordinate S s)

theorem scalarFlatDensity_integrable {c S s : ℝ} (hc : 0 < c) (hS : 0 < S) (hs : 0 < s)
    (j : ℕ) {a : ℝ → ℝ} (ha : Continuous a) :
    IntegrableOn (scalarFlatDensity c j a S) (Ioi s) := by
  apply integrableOn_Ioi_of_eventually_zero hs
  · intro u hu
    exact ((continuousAt_const.div continuousAt_id hu.ne').mul
      ((FlatPrimitive.integrand_continuous hc j ha).continuousAt.comp
        (logCoordinate_hasDerivAt hS hu).continuousAt)).continuousWithinAt
  · filter_upwards [eventually_ge_atTop S] with u hu
    simp only [scalarFlatDensity, FlatPrimitive.integrand,
      FlatCutoff.edge_of_nonpos c (logCoordinate_nonpos hS hu), zero_div, zero_mul, mul_zero]

theorem scalarFlatDensity_integral {c S s : ℝ} (hc : 0 < c) (hS : 0 < S) (hs : 0 < s)
    (j : ℕ) {a : ℝ → ℝ} (ha : Continuous a) :
    (∫ u in Ioi s, scalarFlatDensity c j a S u) =
      FlatPrimitive.primitive c j a (logCoordinate S s) := by
  have hd : ∀ u ∈ Ici s, HasDerivAt
      (fun v => -FlatPrimitive.primitive c j a (logCoordinate S v))
      (scalarFlatDensity c j a S u) u := by
    intro u hu
    convert! ((FlatPrimitive.primitive_hasDerivAt hc j ha (logCoordinate S u)).comp u
      (logCoordinate_hasDerivAt hS (hs.trans_le hu))).neg using 1
    unfold scalarFlatDensity
    ring
  have hz : Tendsto (fun v => -FlatPrimitive.primitive c j a (logCoordinate S v)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop S] with u hu
    simp only [FlatPrimitive.primitive_of_nonpos c j a (logCoordinate_nonpos hS hu), neg_zero]
  simpa only [sub_neg_eq_add, zero_add] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hd (scalarFlatDensity_integrable hc hS hs j ha) hz

noncomputable def chi (d : TailData) (p : EdgeParam) : ℝ :=
  2 * chartEta d p /
    (chartQ d p ^ CoordinateAlgebra.D d.h * CoordinateAlgebra.L d.h (chartEta d p))

theorem chartL_pos (d : TailData) (p : EdgeParam) : 0 < CoordinateAlgebra.L d.h (chartEta d p) :=
  SimilarityProfile.L_pos d.h_pos d.h_lt_half (timeOf_lt_one p)

theorem chi_contDiff (d : TailData) : ContDiff ℝ ∞ (chi d) := by
  apply (contDiff_const.mul (chartEta_contDiff d)).div
    (((chartQ_contDiff d).rpow_const_of_ne (fun p => (chartQ_pos d p).ne')).mul
      (contDiff_const.sub (contDiff_const.mul ((chartEta_contDiff d).pow 2))))
  intro p
  exact (mul_pos (Real.rpow_pos_of_pos (chartQ_pos d p) _) (chartL_pos d p)).ne'

theorem chi_eq_logScale (d : TailData) (p : EdgeParam) :
    chi d p = CoordinateAlgebra.qAxial (chartQ d p) d.h (chartEta d p) / chartQ d p := by
  unfold chi CoordinateAlgebra.qAxial
  field_simp [(chartQ_pos d p).ne',
    (Real.rpow_pos_of_pos (chartQ_pos d p) (CoordinateAlgebra.D d.h)).ne',
    (chartL_pos d p).ne']

noncomputable def pressureCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ :=
  carrier C d y0 y ^ 2 * tailShape d (3 - y.2) * taperSlopeFactor d y.2

theorem pressureCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (pressureCoefficient C d y0) :=
  (((carrier_contDiff C d y0).pow 2).mul
    ((tailShape_contDiff d).comp (contDiff_const.sub contDiff_snd))).mul
      ((taperSlopeFactor_contDiff d).comp contDiff_snd)

noncomputable def pressureFactor (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ :=
  chi d y.1 * ParametricFlatFactor.factor 4 3 (pressureCoefficient C d y0) y

theorem pressureFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (pressureFactor C d y0) :=
  ((chi_contDiff d).comp contDiff_fst).mul
    (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
      (pressureCoefficient_contDiff C d y0))

noncomputable def axialCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ :=
  (radius d y0 y ^ 2 / 2) * pressureFactor C d y0 y

theorem axialCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (axialCoefficient C d y0) :=
  (((radius_contDiff d y0).pow 2).div_const 2).mul (pressureFactor_contDiff C d y0)

noncomputable def axialFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  ParametricFlatFactor.factor 4 0 (axialCoefficient C d y0) y / radius d y0 y

theorem axialFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (axialFactor C d y0) :=
  (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 0
    (axialCoefficient_contDiff C d y0)).div (radius_contDiff d y0)
      (fun y => (radius_pos d y0 y).ne')

/-- The actual canonical pressure gradient on the physical chart. -/
noncomputable def pressureGradient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ :=
  SimilarityProfile.partialZ
    (canonicalPressure (swirlCoefficient C d.h (logTaper d y0))) (chartPoint d y0 y)

/-- The actual axial backward stress, written in the regular radius `s=r²/2`. -/
noncomputable def axialStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) : ℝ :=
  (∫ s in Ioi (radius d y0 y ^ 2 / 2),
    SimilarityProfile.partialZ (canonicalPressure (swirlCoefficient C d.h (logTaper d y0)))
      (timeOf y.1, (s, y.1.2))) / radius d y0 y

/-! ## A profile chart including both endpoints `η = ±1`

These expressions use the actual heat profile on `|η| ≤ 1`.  Its proven
smooth extension and a positive extension of `L` supply coefficients on a
neighborhood of that closed interval.  No value of the implicit coordinates
at zero backward time is used.
-/

noncomputable def positiveExtension (m x : ℝ) : ℝ :=
  m / 2 + (x - m / 2) * OutgoingSchedule.sigma ((x - m / 2) / (m / 2))

theorem positiveExtension_contDiff (m : ℝ) :
    ContDiff ℝ ∞ (positiveExtension m) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (OutgoingSchedule.sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

theorem positiveExtension_pos {m : ℝ} (hm : 0 < m) (x : ℝ) :
    0 < positiveExtension m x := by
  unfold positiveExtension
  by_cases hx : x ≤ m / 2
  · rw [OutgoingSchedule.sigma_zero (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hx) (by positivity)), mul_zero, add_zero]
    positivity
  · exact add_pos_of_pos_of_nonneg (by positivity)
      (mul_nonneg (sub_nonneg.mpr (le_of_not_ge hx)) (OutgoingSchedule.sigma_nonneg _))

theorem positiveExtension_eq {m x : ℝ} (hm : 0 < m) (hx : m ≤ x) :
    positiveExtension m x = x := by
  unfold positiveExtension
  rw [OutgoingSchedule.sigma_one ((le_div_iff₀ (by positivity : 0 < m / 2)).mpr
    (by linarith))]
  ring

noncomputable def profileL (d : TailData) (η : ℝ) : ℝ :=
  positiveExtension (1 - 2 * d.h) (CoordinateAlgebra.L d.h η)

theorem profileL_contDiff (d : TailData) : ContDiff ℝ ∞ (profileL d) :=
  (positiveExtension_contDiff _).comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))

theorem profileL_pos (d : TailData) (η : ℝ) : 0 < profileL d η :=
  positiveExtension_pos (by linarith [d.h_lt_half]) _

theorem profileL_eq (d : TailData) {η : ℝ} (hη : η ^ 2 ≤ 1) :
    profileL d η = CoordinateAlgebra.L d.h η := by
  apply positiveExtension_eq (by linarith [d.h_lt_half])
  unfold CoordinateAlgebra.L
  nlinarith [d.h_pos]

theorem eta_sq_le_one {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : η ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg (show 0 ≤ η + 1 by linarith [hη.1])
    (show 0 ≤ 1 - η by linarith [hη.2])]

noncomputable def profileS (y0 x : ℝ) : ℝ := Real.exp (y0 + 3 - x)
noncomputable def profileRadius (y0 x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.exp (y0 + 3)) * Real.exp (-x / 2)
noncomputable def profileZ (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  2 * (1 - y.1 ^ 2) / profileS y0 y.2

theorem profileS_pos (y0 x : ℝ) : 0 < profileS y0 x := Real.exp_pos _
theorem profileS_contDiff (y0 : ℝ) : ContDiff ℝ ∞ (profileS y0) :=
  (contDiff_const.sub contDiff_id).exp

theorem profileRadius_pos (y0 x : ℝ) : 0 < profileRadius y0 x :=
  mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)

theorem profileRadius_contDiff (y0 : ℝ) : ContDiff ℝ ∞ (profileRadius y0) :=
  contDiff_const.mul (contDiff_id.neg.div_const 2).exp

theorem profileRadius_square (y0 x : ℝ) :
    profileRadius y0 x ^ 2 = 2 * profileS y0 x := by
  unfold profileRadius profileS
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  norm_num
  ring

theorem profileZ_contDiff (y0 : ℝ) : ContDiff ℝ ∞ (profileZ y0) :=
  (contDiff_const.mul (contDiff_const.sub (contDiff_fst.pow 2))).div
    ((profileS_contDiff y0).comp contDiff_snd) (fun y => (profileS_pos y0 y.2).ne')

theorem profileZ_nonneg (y0 : ℝ) {y : ℝ × ℝ} (hη : y.1 ^ 2 ≤ 1) :
    0 ≤ profileZ y0 y := div_nonneg (by nlinarith) (profileS_pos y0 y.2).le

noncomputable def profileCarrier (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  C * (profileS y0 y.2) ^ RadialHeatProfile.spatialExponent (1 + d.h) *
    HeatProfileExtension.extension (1 + d.h) (profileZ y0 y)

noncomputable def profileCarrierRadial (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  C * (profileS y0 y.2) ^ (RadialHeatProfile.spatialExponent (1 + d.h) - 1) *
    (RadialHeatProfile.spatialExponent (1 + d.h) *
        HeatProfileExtension.extension (1 + d.h) (profileZ y0 y) -
      profileZ y0 y * deriv (HeatProfileExtension.extension (1 + d.h)) (profileZ y0 y)) *
    profileRadius y0 y.2

theorem profileCarrier_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileCarrier C d y0) :=
  (contDiff_const.mul (((profileS_contDiff y0).comp contDiff_snd).rpow_const_of_ne
    (fun y => (profileS_pos y0 y.2).ne'))).mul
      ((HeatProfileExtension.extension_contDiff (by linarith [d.h_pos])).comp
        (profileZ_contDiff y0))

theorem profileCarrierRadial_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileCarrierRadial C d y0) := by
  have hH : ContDiff ℝ ∞ (HeatProfileExtension.extension (1 + d.h)) :=
    HeatProfileExtension.extension_contDiff (by linarith [d.h_pos])
  have hH' : ContDiff ℝ ∞ (deriv (HeatProfileExtension.extension (1 + d.h))) :=
    (contDiff_infty_iff_deriv.mp hH).2
  exact ((contDiff_const.mul
    (((profileS_contDiff y0).comp contDiff_snd).rpow_const_of_ne
      (fun y => (profileS_pos y0 y.2).ne'))).mul
    ((contDiff_const.mul (hH.comp (profileZ_contDiff y0))).sub
      ((profileZ_contDiff y0).mul (hH'.comp (profileZ_contDiff y0))))).mul
    ((profileRadius_contDiff y0).comp contDiff_snd)

theorem profileCarrier_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hη : y.1 ^ 2 ≤ 1) : 0 < profileCarrier C d y0 y :=
  mul_pos (mul_pos hC (Real.rpow_pos_of_pos (profileS_pos y0 y.2) _))
    (HeatProfileExtension.extension_pos (by linarith [d.h_pos]) (profileZ_nonneg y0 hη))

noncomputable def profileChi (d : TailData) (η : ℝ) : ℝ := 2 * η / profileL d η

theorem profileChi_contDiff (d : TailData) : ContDiff ℝ ∞ (profileChi d) :=
  (contDiff_const.mul contDiff_id).div (profileL_contDiff d) (fun η => (profileL_pos d η).ne')

noncomputable def profileBoundaryCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  (2 * profileCarrier C d y0 y / profileRadius y0 y.2) * taperSlopeFactor d y.2

noncomputable def profileTimeCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  (profileRadius y0 y.2 ^ 3 * profileCarrier C d y0 y / (2 * profileL d y.1)) *
    taperSlopeFactor d y.2

noncomputable def profileCorrectionCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  (profileRadius y0 y.2 * profileCarrier C d y0 y -
    profileRadius y0 y.2 ^ 2 * profileCarrierRadial C d y0 y) * taperSlopeFactor d y.2

theorem profileBoundaryCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileBoundaryCoefficient C d y0) :=
  ((contDiff_const.mul (profileCarrier_contDiff C d y0)).div
    ((profileRadius_contDiff y0).comp contDiff_snd)
    (fun y => (profileRadius_pos y0 y.2).ne')).mul
    ((taperSlopeFactor_contDiff d).comp contDiff_snd)

theorem profileTimeCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileTimeCoefficient C d y0) :=
  (((((profileRadius_contDiff y0).comp contDiff_snd).pow 3).mul
    (profileCarrier_contDiff C d y0)).div
    (contDiff_const.mul ((profileL_contDiff d).comp contDiff_fst))
    (fun y => (mul_pos (by norm_num) (profileL_pos d y.1)).ne')).mul
    ((taperSlopeFactor_contDiff d).comp contDiff_snd)

theorem profileCorrectionCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileCorrectionCoefficient C d y0) :=
  ((((profileRadius_contDiff y0).comp contDiff_snd).mul
    (profileCarrier_contDiff C d y0)).sub
    ((((profileRadius_contDiff y0).comp contDiff_snd).pow 2).mul
      (profileCarrierRadial_contDiff C d y0))).mul
    ((taperSlopeFactor_contDiff d).comp contDiff_snd)

noncomputable def profileAngularFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  profileBoundaryCoefficient C d y0 y + (y.2 ^ 3 / profileRadius y0 y.2 ^ 2) *
    (ParametricFlatFactor.factor 4 3 (profileTimeCoefficient C d y0) y +
      ParametricFlatFactor.factor 4 3 (profileCorrectionCoefficient C d y0) y)

/-- The boundary term and the two actual terminal primitives in profile coordinates. -/
noncomputable def profileAngularStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * profileBoundaryCoefficient C d y0 y +
    (ParametricFlatFactor.primitive 4 3 (profileTimeCoefficient C d y0) y +
      ParametricFlatFactor.primitive 4 3 (profileCorrectionCoefficient C d y0) y) /
      profileRadius y0 y.2 ^ 2

theorem profileAngularFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileAngularFactor C d y0) :=
  (profileBoundaryCoefficient_contDiff C d y0).add
    (((contDiff_snd.pow 3).div (((profileRadius_contDiff y0).comp contDiff_snd).pow 2)
      (fun y => (sq_pos_of_pos (profileRadius_pos y0 y.2)).ne')).mul
      ((ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
        (profileTimeCoefficient_contDiff C d y0)).add
        (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
          (profileCorrectionCoefficient_contDiff C d y0))))

theorem profileAngularStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileAngularStress C d y0 y =
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * profileAngularFactor C d y0 y := by
  unfold profileAngularStress profileAngularFactor
  rw [ParametricFlatFactor.primitive_eq_scale_mul_factor,
    ParametricFlatFactor.primitive_eq_scale_mul_factor]
  unfold FlatPrimitive.scale
  ring

theorem profileAngularFactor_zero (C : ℝ) (d : TailData) (y0 η : ℝ) :
    profileAngularFactor C d y0 (η, 0) =
      (2 * profileCarrier C d y0 (η, 0) / profileRadius y0 0) * taperSlopeFactor d 0 := by
  simp only [profileAngularFactor, zero_pow (by norm_num : 3 ≠ 0), zero_div, zero_mul,
    add_zero, profileBoundaryCoefficient]

theorem profileAngularFactor_zero_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : 0 < profileAngularFactor C d y0 (η, 0) := by
  rw [profileAngularFactor_zero]
  exact mul_pos (div_pos (mul_pos (by norm_num)
    (profileCarrier_pos hC d y0 (eta_sq_le_one hη))) (profileRadius_pos y0 0))
    (taperSlopeFactor_zero_pos d)

noncomputable def profilePressureCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  profileCarrier C d y0 y ^ 2 * tailShape d (3 - y.2) * taperSlopeFactor d y.2

theorem profilePressureCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profilePressureCoefficient C d y0) :=
  (((profileCarrier_contDiff C d y0).pow 2).mul
    ((tailShape_contDiff d).comp (contDiff_const.sub contDiff_snd))).mul
    ((taperSlopeFactor_contDiff d).comp contDiff_snd)

noncomputable def profilePressureFactor (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  profileChi d y.1 * ParametricFlatFactor.factor 4 3 (profilePressureCoefficient C d y0) y

/-- The first genuine terminal primitive, before any factorization. -/
noncomputable def profilePressureGradient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  profileChi d y.1 * ParametricFlatFactor.primitive 4 3 (profilePressureCoefficient C d y0) y

theorem profilePressureFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profilePressureFactor C d y0) :=
  ((profileChi_contDiff d).comp contDiff_fst).mul
    (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 3
      (profilePressureCoefficient_contDiff C d y0))

theorem scale_three (c x : ℝ) : FlatPrimitive.scale c 3 x = FlatCutoff.edge c x := by
  by_cases hx : x = 0
  · subst x
    simp [FlatPrimitive.scale, FlatCutoff.edge_zero]
  · simp only [FlatPrimitive.scale, div_mul_cancel₀ _ (pow_ne_zero 3 hx)]

theorem profilePressureGradient_factorization (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : profilePressureGradient C d y0 y =
      FlatCutoff.edge 4 y.2 * profilePressureFactor C d y0 y := by
  unfold profilePressureGradient profilePressureFactor
  rw [ParametricFlatFactor.primitive_eq_scale_mul_factor, scale_three]
  ring

noncomputable def profileAxialCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ := profileS y0 y.2 * profilePressureFactor C d y0 y

noncomputable def profileAxialFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  ParametricFlatFactor.factor 4 0 (profileAxialCoefficient C d y0) y / profileRadius y0 y.2

/-- The second terminal primitive is the integral of the first one, with
the exact Jacobian `s = exp(Y-δ)` of the regular radial coordinate. -/
noncomputable def profileAxialStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..y.2, profileS y0 u * profilePressureGradient C d y0 (y.1, u)) /
    profileRadius y0 y.2

theorem profileAxialCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileAxialCoefficient C d y0) :=
  ((profileS_contDiff y0).comp contDiff_snd).mul (profilePressureFactor_contDiff C d y0)

theorem profileAxialFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileAxialFactor C d y0) :=
  (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 0
    (profileAxialCoefficient_contDiff C d y0)).div
    ((profileRadius_contDiff y0).comp contDiff_snd) (fun y => (profileRadius_pos y0 y.2).ne')

theorem profileAxialStress_eq_primitive (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileAxialStress C d y0 y =
      ParametricFlatFactor.primitive 4 0 (profileAxialCoefficient C d y0) y /
        profileRadius y0 y.2 := by
  unfold profileAxialStress ParametricFlatFactor.primitive FlatPrimitive.primitive
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [profilePressureGradient_factorization]
  simp only [FlatPrimitive.integrand, pow_zero, div_one, profileAxialCoefficient]
  ring

theorem profileAxialStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileAxialStress C d y0 y =
      FlatCutoff.edge 4 y.2 * y.2 ^ 3 * profileAxialFactor C d y0 y := by
  rw [profileAxialStress_eq_primitive, ParametricFlatFactor.primitive_eq_scale_mul_factor]
  simp only [FlatPrimitive.scale, pow_zero, div_one, profileAxialFactor]
  ring

/-! ## Identification of both physical pressure primitives -/

theorem pressure_density_eq (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam)
    {s : ℝ} (hs : 0 < s) :
    physicalHeat C (1 + d.h) (timeOf p, (s, p.2)) ^ 2 *
      tailShape d (Real.log (s / chartQ d p) - y0) *
      tailShapeDeriv d (Real.log (s / chartQ d p) - y0) / s =
      scalarFlatDensity 4 3 (fun v => pressureCoefficient C d y0 (p, v)) (outerS d y0 p) s := by
  unfold scalarFlatDensity FlatPrimitive.integrand pressureCoefficient
  dsimp only
  rw [carrier_at_s C d y0 p hs, physical_logX_s d y0 p hs]
  rw [show y0 + 3 - logCoordinate (outerS d y0 p) s - y0 =
      3 - logCoordinate (outerS d y0 p) s by ring,
    tailShapeDeriv_factorization]
  ring

theorem pressureGradient_eq_primitive (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : pressureGradient C d y0 y =
      chi d y.1 * ParametricFlatFactor.primitive 4 3 (pressureCoefficient C d y0) y := by
  change SimilarityProfile.partialZ (TerminalPressure.outgoingPressure C d y0)
    (chartPoint d y0 y) = _
  rw [TerminalPressure.outgoingPressure_partialZ C d y0 (timeOf_lt_one y.1)
    (show 0 < (chartPoint d y0 y).2.1 from
      div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num))]
  have hchi : TerminalPressure.logScaleDerivative d.h (chartPoint d y0 y) = chi d y.1 :=
    (chi_eq_logScale d y.1).symm
  rw [hchi]
  congr 1
  change (∫ s in Ioi (radius d y0 y ^ 2 / 2),
    physicalHeat C (1 + d.h) (timeOf y.1, (s, y.1.2)) ^ 2 *
      tailShape d (Real.log (s / chartQ d y.1) - y0) *
      tailShapeDeriv d (Real.log (s / chartQ d y.1) - y0) / s) = _
  calc
    _ = ∫ s in Ioi (radius d y0 y ^ 2 / 2), scalarFlatDensity 4 3
        (fun v => pressureCoefficient C d y0 (y.1, v)) (outerS d y0 y.1) s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact pressure_density_eq C d y0 y.1
        ((div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num)).trans hs)
    _ = FlatPrimitive.primitive 4 3 (fun v => pressureCoefficient C d y0 (y.1, v))
        (logCoordinate (outerS d y0 y.1) (radius d y0 y ^ 2 / 2)) :=
      scalarFlatDensity_integral (by norm_num) (outerS_pos d y0 y.1)
        (div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num)) 3
        ((ParametricFlatFactor.coefficient_slice_contDiff
          (pressureCoefficient_contDiff C d y0) y.1).continuous)
    _ = ParametricFlatFactor.primitive 4 3 (pressureCoefficient C d y0) y := by
      rw [logCoordinate_radialS]
      rfl

theorem pressureGradient_factorization (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : pressureGradient C d y0 y =
      FlatCutoff.edge 4 y.2 * pressureFactor C d y0 y := by
  rw [pressureGradient_eq_primitive, ParametricFlatFactor.primitive_eq_scale_mul_factor,
    scale_three]
  unfold pressureFactor
  ring

theorem pressureGradient_at_s (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam)
    {s : ℝ} (hs : 0 < s) :
    SimilarityProfile.partialZ (canonicalPressure (swirlCoefficient C d.h (logTaper d y0)))
      (timeOf p, (s, p.2)) =
      FlatCutoff.edge 4 (logCoordinate (outerS d y0 p) s) *
        pressureFactor C d y0 (p, logCoordinate (outerS d y0 p) s) := by
  have he := pressureGradient_factorization C d y0 (p, logCoordinate (outerS d y0 p) s)
  unfold pressureGradient chartPoint radiusPoint at he
  dsimp only at he
  rwa [radialS_logCoordinate d y0 p hs] at he

theorem axial_density_eq (C : ℝ) (d : TailData) (y0 : ℝ) (p : EdgeParam)
    {s : ℝ} (hs : 0 < s) :
    SimilarityProfile.partialZ (canonicalPressure (swirlCoefficient C d.h (logTaper d y0)))
      (timeOf p, (s, p.2)) =
      scalarFlatDensity 4 0 (fun v => axialCoefficient C d y0 (p, v)) (outerS d y0 p) s := by
  rw [pressureGradient_at_s C d y0 p hs]
  unfold scalarFlatDensity FlatPrimitive.integrand axialCoefficient
  dsimp only
  rw [radialS_logCoordinate d y0 p hs]
  simp only [pow_zero, div_one]
  field_simp [hs.ne']

theorem axialStress_eq_primitive (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : axialStress C d y0 y =
      ParametricFlatFactor.primitive 4 0 (axialCoefficient C d y0) y / radius d y0 y := by
  unfold axialStress
  congr 1
  calc
    _ = ∫ s in Ioi (radius d y0 y ^ 2 / 2), scalarFlatDensity 4 0
        (fun v => axialCoefficient C d y0 (y.1, v)) (outerS d y0 y.1) s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact axial_density_eq C d y0 y.1
        ((div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num)).trans hs)
    _ = FlatPrimitive.primitive 4 0 (fun v => axialCoefficient C d y0 (y.1, v))
        (logCoordinate (outerS d y0 y.1) (radius d y0 y ^ 2 / 2)) :=
      scalarFlatDensity_integral (by norm_num) (outerS_pos d y0 y.1)
        (div_pos (sq_pos_of_pos (radius_pos d y0 y)) (by norm_num)) 0
        ((ParametricFlatFactor.coefficient_slice_contDiff
          (axialCoefficient_contDiff C d y0) y.1).continuous)
    _ = ParametricFlatFactor.primitive 4 0 (axialCoefficient C d y0) y := by
      rw [logCoordinate_radialS]
      rfl

theorem axialStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    axialStress C d y0 y = FlatCutoff.edge 4 y.2 * y.2 ^ 3 * axialFactor C d y0 y := by
  rw [axialStress_eq_primitive, ParametricFlatFactor.primitive_eq_scale_mul_factor]
  simp only [FlatPrimitive.scale, pow_zero, div_one, axialFactor]
  ring

/-! ## Agreement with the physical section away from the endpoints -/

noncomputable def normalizedParam (η : ℝ) : EdgeParam := (Real.log (1 - η ^ 2), η)

theorem timeOf_normalizedParam {η : ℝ} (hη : η ^ 2 < 1) :
    timeOf (normalizedParam η) = η ^ 2 := by
  simp only [timeOf, normalizedParam, Real.exp_log (sub_pos.mpr hη)]
  ring

theorem chartQ_normalizedParam (d : TailData) {η : ℝ} (hη : η ^ 2 < 1) :
    chartQ d (normalizedParam η) = 1 := by
  unfold chartQ axisPoint
  rw [timeOf_normalizedParam hη]
  exact PhysicalHeatCoordinates.q_normalizedSection d.h_pos d.h_lt_half hη 0

theorem chartEta_normalizedParam (d : TailData) {η : ℝ} (hη : η ^ 2 < 1) :
    chartEta d (normalizedParam η) = η := by
  unfold chartEta axisPoint
  rw [timeOf_normalizedParam hη]
  exact PhysicalHeatCoordinates.eta_normalizedSection d.h_pos d.h_lt_half hη 0

theorem radius_normalizedParam (d : TailData) (y0 x : ℝ) {η : ℝ} (hη : η ^ 2 < 1) :
    radius d y0 (normalizedParam η, x) = profileRadius y0 x := by
  unfold radius outerRadius
  dsimp only
  rw [chartQ_normalizedParam d hη]
  simp only [mul_one]
  rfl

theorem radialS_normalizedParam (d : TailData) (y0 x : ℝ) {η : ℝ} (hη : η ^ 2 < 1) :
    radius d y0 (normalizedParam η, x) ^ 2 / 2 = profileS y0 x := by
  rw [radius_normalizedParam d y0 x hη, profileRadius_square]
  ring

theorem carrier_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    carrier C d y0 (normalizedParam η, x) = profileCarrier C d y0 (η, x) := by
  unfold carrier physicalHeat chartPoint radiusPoint RadialHeatProfile.spatialProfile
  dsimp only
  rw [timeOf_normalizedParam hη, radialS_normalizedParam d y0 x hη]
  unfold profileCarrier
  dsimp only
  rw [HeatProfileExtension.extension_eq_profile _ (profileZ_nonneg y0 hη.le)]
  unfold profileZ
  ring

theorem carrierRadial_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    carrierRadial C d y0 (normalizedParam η, x) = profileCarrierRadial C d y0 (η, x) := by
  rw [carrierRadial_eq]
  unfold heatAmplitude
  rw [deriv_const_mul_field,
    RadialHeatProfile.radialProfile_first_derivative (by linarith [d.h_pos])
      (sub_pos.mpr (timeOf_lt_one (normalizedParam η))) (radius_pos d y0 (normalizedParam η, x))]
  unfold RadialHeatProfile.radialFirst RadialHeatProfile.spatialFirst
  rw [timeOf_normalizedParam hη, radialS_normalizedParam d y0 x hη,
    radius_normalizedParam d y0 x hη]
  have hder := HeatProfileExtension.iteratedDeriv_extension_eq_profileJet
    (a := 1 + d.h) (by linarith [d.h_pos]) 1 (profileZ_nonneg y0 (y := (η, x)) hη.le)
  simp only [iteratedDeriv_one] at hder
  unfold profileCarrierRadial
  dsimp only
  rw [hder, HeatProfileExtension.extension_eq_profile _ (profileZ_nonneg y0 hη.le)]
  unfold profileZ
  ring

theorem denominator_normalizedParam (d : TailData) {η : ℝ} (hη : η ^ 2 < 1) :
    denominator d (normalizedParam η) = profileL d η := by
  change chartQ d (normalizedParam η) * CoordinateAlgebra.L d.h (chartEta d (normalizedParam η)) = _
  rw [chartQ_normalizedParam d hη, chartEta_normalizedParam d hη, one_mul, profileL_eq d hη.le]

theorem chi_normalizedParam (d : TailData) {η : ℝ} (hη : η ^ 2 < 1) :
    chi d (normalizedParam η) = profileChi d η := by
  unfold chi profileChi
  rw [chartQ_normalizedParam d hη, chartEta_normalizedParam d hη, Real.one_rpow,
    one_mul, profileL_eq d hη.le]

theorem boundaryCoefficient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    boundaryCoefficient C d y0 (normalizedParam η, x) = profileBoundaryCoefficient C d y0 (η, x) :=
      by
  unfold boundaryCoefficient profileBoundaryCoefficient
  rw [carrier_normalizedParam C d y0 x hη, radius_normalizedParam d y0 x hη]

theorem timeCoefficient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    timeCoefficient C d y0 (normalizedParam η, x) = profileTimeCoefficient C d y0 (η, x) := by
  unfold timeCoefficient profileTimeCoefficient
  rw [carrier_normalizedParam C d y0 x hη, radius_normalizedParam d y0 x hη,
    denominator_normalizedParam d hη]

theorem correctionCoefficient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    correctionCoefficient C d y0 (normalizedParam η, x) = profileCorrectionCoefficient C d y0 (η,
      x) := by
  unfold correctionCoefficient profileCorrectionCoefficient
  rw [carrier_normalizedParam C d y0 x hη, radius_normalizedParam d y0 x hη,
    carrierRadial_normalizedParam C d y0 x hη]

theorem pressureCoefficient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    pressureCoefficient C d y0 (normalizedParam η, x) = profilePressureCoefficient C d y0 (η, x) :=
      by
  unfold pressureCoefficient profilePressureCoefficient
  rw [carrier_normalizedParam C d y0 x hη]

theorem factor_congr_slice {P Q : Type*} (c : ℝ) (j : ℕ) (b : P × ℝ → ℝ)
    (a : Q × ℝ → ℝ) (p : P) (q : Q) (x : ℝ) (he : ∀ u, b (p, u) = a (q, u)) :
    ParametricFlatFactor.factor c j b (p, x) = ParametricFlatFactor.factor c j a (q, x) := by
  unfold ParametricFlatFactor.factor ParametricFlatFactor.kernel
  apply integral_congr_ae
  filter_upwards with t
  rw [he]

theorem angularFactor_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    angularFactor C d y0 (normalizedParam η, x) = profileAngularFactor C d y0 (η, x) := by
  unfold angularFactor profileAngularFactor
  rw [boundaryCoefficient_normalizedParam C d y0 x hη, radius_normalizedParam d y0 x hη,
    factor_congr_slice 4 3 _ _ _ _ x (fun u => timeCoefficient_normalizedParam C d y0 u hη),
    factor_congr_slice 4 3 _ _ _ _ x (fun u => correctionCoefficient_normalizedParam C d y0 u hη)]

theorem pressureFactor_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    pressureFactor C d y0 (normalizedParam η, x) = profilePressureFactor C d y0 (η, x) := by
  unfold pressureFactor profilePressureFactor
  rw [chi_normalizedParam d hη,
    factor_congr_slice 4 3 _ _ _ _ x (fun u => pressureCoefficient_normalizedParam C d y0 u hη)]

theorem axialCoefficient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    axialCoefficient C d y0 (normalizedParam η, x) = profileAxialCoefficient C d y0 (η, x) := by
  unfold axialCoefficient profileAxialCoefficient
  rw [radialS_normalizedParam d y0 x hη, pressureFactor_normalizedParam C d y0 x hη]

theorem axialFactor_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    axialFactor C d y0 (normalizedParam η, x) = profileAxialFactor C d y0 (η, x) := by
  unfold axialFactor profileAxialFactor
  rw [radius_normalizedParam d y0 x hη,
    factor_congr_slice 4 0 _ _ _ _ x (fun u => axialCoefficient_normalizedParam C d y0 u hη)]

theorem angularStress_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    angularStress C d y0 (normalizedParam η, x) = profileAngularStress C d y0 (η, x) := by
  rw [angularStress_factorization, profileAngularStress_factorization,
    angularFactor_normalizedParam C d y0 x hη]

theorem pressureGradient_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    pressureGradient C d y0 (normalizedParam η, x) = profilePressureGradient C d y0 (η, x) := by
  rw [pressureGradient_factorization, profilePressureGradient_factorization,
    pressureFactor_normalizedParam C d y0 x hη]

theorem axialStress_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    axialStress C d y0 (normalizedParam η, x) = profileAxialStress C d y0 (η, x) := by
  rw [axialStress_factorization, profileAxialStress_factorization,
    axialFactor_normalizedParam C d y0 x hη]

/-! ## Full profile stress, all jets, and the edge direction -/

noncomputable def profileStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (profileAngularStress C d y0 y, profileAxialStress C d y0 y)

noncomputable def profileStressFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (profileAngularFactor C d y0 y, y.2 ^ 6 * profileAxialFactor C d y0 y)

theorem profileStressFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileStressFactor C d y0) :=
  (profileAngularFactor_contDiff C d y0).prodMk
    ((contDiff_snd.pow 6).mul (profileAxialFactor_contDiff C d y0))

theorem profileStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileStress C d y0 y =
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • profileStressFactor C d y0 y := by
  apply Prod.ext
  · exact profileAngularStress_factorization C d y0 y
  · change profileAxialStress C d y0 y =
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * (y.2 ^ 6 * profileAxialFactor C d y0 y)
    rw [profileAxialStress_factorization]
    by_cases hx : y.2 = 0
    · simp [hx]
    · field_simp [hx]

theorem profileStress_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileStress C d y0) := by
  have he : profileStress C d y0 = fun y =>
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • profileStressFactor C d y0 y :=
    funext (profileStress_factorization C d y0)
  rw [he]
  exact ((FlatCutoff.edge_div_pow_contDiff (by norm_num : (0 : ℝ) < 4) 3).comp
    contDiff_snd).smul (profileStressFactor_contDiff C d y0)

theorem profileStressFactor_zero (C : ℝ) (d : TailData) (y0 η : ℝ) :
    profileStressFactor C d y0 (η, 0) = (profileAngularFactor C d y0 (η, 0), 0) := by
  simp [profileStressFactor]

theorem profileStressFactor_zero_ne {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : profileStressFactor C d y0 (η, 0) ≠ 0 := by
  intro he
  have hzero := congrArg Prod.fst he
  exact (profileAngularFactor_zero_pos hC d y0 hη).ne' hzero

/-- Actual full tensors, uniformly through both endpoints of the profile interval. -/
theorem profileStress_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ η ∈ Icc (-1 : ℝ) 1,
      ∀ x : ℝ, 0 < x → x ≤ b →
      ‖iteratedFDeriv ℝ i (profileStress C d y0) (η, x)‖ ≤ A * FlatCutoff.edge 4 x / x ^ N := by
  have he : profileStress C d y0 = fun y =>
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • profileStressFactor C d y0 y :=
    funext (profileStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.edge_smul_iteratedFDeriv_bound (by norm_num) 3
    (profileStressFactor_contDiff C d y0) isCompact_Icc n hb

theorem profileAngularStress_edge_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ) (η : ℝ) :
    iteratedFDeriv ℝ n (profileAngularStress C d y0) (η, 0) = 0 := by
  have he : profileAngularStress C d y0 =
      EdgeWeightJets.weighted 4 3 (profileAngularFactor C d y0) :=
    funext (profileAngularStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.weighted_iteratedFDeriv_zero (by norm_num) 3
    (profileAngularFactor_contDiff C d y0) n η

theorem profileAxialStress_edge_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ) (η : ℝ) :
    iteratedFDeriv ℝ n (profileAxialStress C d y0) (η, 0) = 0 := by
  have he : profileAxialStress C d y0 =
      EdgeWeightJets.weighted 4 0 (fun y : ℝ × ℝ => y.2 ^ 3 * profileAxialFactor C d y0 y) := by
    funext y
    simpa only [EdgeWeightJets.weighted, pow_zero, div_one, mul_assoc] using
      profileAxialStress_factorization C d y0 y
  rw [he]
  exact EdgeWeightJets.weighted_iteratedFDeriv_zero (by norm_num) 0
    ((contDiff_snd.pow 3).mul (profileAxialFactor_contDiff C d y0)) n η

noncomputable def profileTilt (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  y.2 ^ 6 * profileAxialFactor C d y0 y / profileAngularFactor C d y0 y

theorem profileTilt_eq_ratio (C : ℝ) (d : TailData) (y0 η : ℝ) {x : ℝ} (hx : 0 < x) :
    profileAxialStress C d y0 (η, x) / profileAngularStress C d y0 (η, x) =
      profileTilt C d y0 (η, x) := by
  have hw : FlatCutoff.edge 4 x / x ^ 3 ≠ 0 := div_ne_zero (FlatCutoff.edge_pos 4 hx).ne'
    (pow_ne_zero 3 hx.ne')
  have hvec := congrArg Prod.snd (profileStress_factorization C d y0 (η, x))
  change profileAxialStress C d y0 (η, x) =
    (FlatCutoff.edge 4 x / x ^ 3) * (x ^ 6 * profileAxialFactor C d y0 (η, x)) at hvec
  rw [hvec, profileAngularStress_factorization]
  exact mul_div_mul_left _ _ hw

theorem profileTilt_zero (C : ℝ) (d : TailData) (y0 η : ℝ) : profileTilt C d y0 (η, 0) = 0 := by
  simp [profileTilt]

theorem profileTilt_contDiffAt {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : ContDiffAt ℝ ∞ (profileTilt C d y0) (η, 0) :=
  ((contDiffAt_snd.pow 6).mul (profileAxialFactor_contDiff C d y0).contDiffAt).div
    (profileAngularFactor_contDiff C d y0).contDiffAt
    (profileAngularFactor_zero_pos hC d y0 hη).ne'

theorem profileTilt_tendsto_zero {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    Tendsto (profileTilt C d y0) (𝓝 (η, 0)) (𝓝 0) := by
  have he := (profileTilt_contDiffAt hC d y0 hη).continuousAt
  change Tendsto (profileTilt C d y0) (𝓝 (η, 0))
    (𝓝 (profileTilt C d y0 (η, 0))) at he
  simpa only [profileTilt_zero] using he

/-- The actual velocity shear ratio for the terminal product `K f_o`. -/
noncomputable def profileSpeed (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  1 - profileRadius y0 y.2 * profileCarrierRadial C d y0 y / profileCarrier C d y0 y -
    2 * tailShapeDeriv d (3 - y.2) / tailShape d (3 - y.2)

theorem profileSpeed_contDiffAt_of_ne (C : ℝ) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hK : profileCarrier C d y0 y ≠ 0) :
    ContDiffAt ℝ ∞ (profileSpeed C d y0) y := by
  apply ContDiffAt.sub
  · exact contDiffAt_const.sub
      ((((profileRadius_contDiff y0).comp contDiff_snd).contDiffAt.mul
        (profileCarrierRadial_contDiff C d y0).contDiffAt).div
        (profileCarrier_contDiff C d y0).contDiffAt hK)
  · exact (contDiffAt_const.mul ((tailShapeDeriv_contDiff d).comp
      (contDiff_const.sub contDiff_snd)).contDiffAt).div
      ((tailShape_contDiff d).comp (contDiff_const.sub contDiff_snd)).contDiffAt
      (tailShape_pos d _).ne'

theorem profileSpeed_contDiffAt {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hη : y.1 ^ 2 ≤ 1) : ContDiffAt ℝ ∞ (profileSpeed C d y0) y :=
  profileSpeed_contDiffAt_of_ne C d y0 (profileCarrier_pos hC d y0 hη).ne'

noncomputable def profileDomain (C : ℝ) (d : TailData) (y0 : ℝ) : Set (ℝ × ℝ) :=
  {y | profileCarrier C d y0 y ≠ 0}

theorem profileDomain_open (C : ℝ) (d : TailData) (y0 : ℝ) :
    IsOpen (profileDomain C d y0) :=
  isOpen_ne.preimage (profileCarrier_contDiff C d y0).continuous

theorem profileDomain_contains_closed {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    (Icc (-1 : ℝ) 1) ×ˢ (univ : Set ℝ) ⊆ profileDomain C d y0 := by
  intro y hy
  exact (profileCarrier_pos hC d y0 (eta_sq_le_one hy.1)).ne'

theorem profileSpeed_contDiffOn (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiffOn ℝ ∞ (profileSpeed C d y0) (profileDomain C d y0) :=
  fun _ hy => (profileSpeed_contDiffAt_of_ne C d y0 hy).contDiffWithinAt

theorem extended_heat_slope (d : TailData) {z : ℝ} (hz : 0 ≤ z) :
    -z * deriv (HeatProfileExtension.extension (1 + d.h)) z <
      d.h * HeatProfileExtension.extension (1 + d.h) z := by
  rcases eq_or_lt_of_le hz with he | hp
  · subst z
    simpa only [neg_zero, zero_mul, HeatProfileExtension.extension_zero
      (a := 1 + d.h) (by linarith [d.h_pos]),
      mul_one] using d.h_pos
  · have he := HeatProfileExtension.iteratedDeriv_extension_eq_profileJet
      (a := 1 + d.h) (by linarith [d.h_pos]) 1 hp.le
    simp only [iteratedDeriv_one] at he
    rw [he, HeatProfileExtension.extension_eq_profile _ hp.le,
      ← (RadialHeatProfile.profile_hasDerivAt (by linarith [d.h_pos]) hp).deriv]
    exact (div_lt_iff₀ (RadialHeatProfile.profile_pos (by linarith [d.h_pos]) hp.le)).mp
      (RadialHeatProfile.profile_h_logSlope_lt d.h_pos hp)

theorem profileCarrier_radial_gap {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hη : y.1 ^ 2 ≤ 1) :
    profileRadius y0 y.2 * profileCarrierRadial C d y0 y + profileCarrier C d y0 y < 0 := by
  have hs := profileS_pos y0 y.2
  have hlog := extended_heat_slope d (profileZ_nonneg y0 hη)
  have hb : 2 * (RadialHeatProfile.spatialExponent (1 + d.h) *
      HeatProfileExtension.extension (1 + d.h) (profileZ y0 y) -
      profileZ y0 y * deriv (HeatProfileExtension.extension (1 + d.h)) (profileZ y0 y)) +
      HeatProfileExtension.extension (1 + d.h) (profileZ y0 y) < 0 := by
    unfold RadialHeatProfile.spatialExponent
    nlinarith
  have hi := mul_neg_of_pos_of_neg
    (mul_pos hC (Real.rpow_pos_of_pos hs (RadialHeatProfile.spatialExponent (1 + d.h)))) hb
  convert! hi using 1
  unfold profileCarrierRadial profileCarrier
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp [hs.ne']
  ring_nf
  rw [profileRadius_square]
  ring

theorem profileSpeed_zero_gt_two {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : 2 < profileSpeed C d y0 (η, 0) := by
  have hK := profileCarrier_pos hC d y0 (y := (η, 0)) (eta_sq_le_one hη)
  have hgap := profileCarrier_radial_gap hC d y0 (y := (η, 0)) (eta_sq_le_one hη)
  have hdiv : profileRadius y0 0 * profileCarrierRadial C d y0 (η, 0) /
      profileCarrier C d y0 (η, 0) < -1 := (div_lt_iff₀ hK).mpr (by linarith)
  have hz : tailShapeDeriv d 3 = 0 := by
    have he := tailShapeDeriv_factorization d 0
    simpa only [sub_zero, FlatCutoff.edge_zero, zero_div, zero_mul] using he
  simp only [profileSpeed, sub_zero, hz, mul_zero, zero_div]
  linarith

noncomputable def profileConeGap (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  2 - (profileSpeed C d y0 y - 2) * profileTilt C d y0 y ^ 2

theorem profileConeGap_zero (C : ℝ) (d : TailData) (y0 η : ℝ) :
    profileConeGap C d y0 (η, 0) = 2 := by
  simp [profileConeGap, profileTilt_zero]

theorem compact_positive_collar {E : Type*} [NormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) {f : E × ℝ → ℝ}
    (hf : ∀ p ∈ K, ContinuousAt f (p, 0)) (hpos : ∀ p ∈ K, 0 < f (p, 0)) :
    ∃ ε m : ℝ, 0 < ε ∧ 0 < m ∧ ∀ p ∈ K, ∀ x : ℝ, |x| < ε → m ≤ f (p, x) := by
  have hc : ContinuousOn (fun p => f (p, 0)) K := by
    intro p hp
    exact ((hf p hp).comp (f := fun q : E => (q, (0 : ℝ)))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  obtain ⟨m, hm, hmb⟩ := UniformCone.positive_uniform_margin hK hc hpos
  have hE : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ p ∈ K, m / 2 < f (p, x) := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    exact ((hf p hp).comp (f := fun q : ℝ × E => (q.2, q.1))
      (continuousAt_snd.prodMk continuousAt_fst)).eventually
      (Ioi_mem_nhds (lt_of_lt_of_le (show m / 2 < m by linarith) (hmb p hp)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hE
  refine ⟨ε, m / 2, hε, by positivity, ?_⟩
  intro p hp x hx
  exact (hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx) p hp).le

/-- One strict relative cone margin on a collar, uniformly for `-1 ≤ η ≤ 1`.
The shear is the finite, actual terminal velocity shear; its value is proved
strictly larger than two on the boundary. -/
theorem profile_uniform_cone {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    ∃ ε m : ℝ, 0 < ε ∧ 0 < m ∧ ∀ η ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, |x| < ε →
      m ≤ profileAngularFactor C d y0 (η, x) ∧
      m ≤ profileSpeed C d y0 (η, x) - 2 ∧ m ≤ profileConeGap C d y0 (η, x) := by
  let f : ℝ × ℝ → ℝ := fun y => min (profileAngularFactor C d y0 y)
    (min (profileSpeed C d y0 y - 2) (profileConeGap C d y0 y))
  have hc : ∀ η ∈ Icc (-1 : ℝ) 1, ContinuousAt f (η, 0) := by
    intro η hη
    have hs := (profileSpeed_contDiffAt hC d y0 (y := (η, 0)) (eta_sq_le_one hη)).continuousAt
    have ht := (profileTilt_contDiffAt hC d y0 hη).continuousAt
    exact (profileAngularFactor_contDiff C d y0).continuous.continuousAt.min
      ((hs.sub continuousAt_const).min
        (continuousAt_const.sub ((hs.sub continuousAt_const).mul (ht.pow 2))))
  have hp : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < f (η, 0) := by
    intro η hη
    apply lt_min (profileAngularFactor_zero_pos hC d y0 hη)
    apply lt_min (sub_pos.mpr (profileSpeed_zero_gt_two hC d y0 hη))
    rw [profileConeGap_zero]
    norm_num
  obtain ⟨ε, m, hε, hm, hb⟩ := compact_positive_collar isCompact_Icc hc hp
  refine ⟨ε, m, hε, hm, ?_⟩
  intro η hη x hx
  exact (le_min_iff.mp (hb η hη x hx)).imp_right (fun h => le_min_iff.mp h)

/-! ## The shear formula is the derivative of the actual profile velocity -/

noncomputable def profileAngularVelocity (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  profileCarrier C d y0 y * tailShape d (3 - y.2)

theorem profileAngularVelocity_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileAngularVelocity C d y0) :=
  (profileCarrier_contDiff C d y0).mul
    ((tailShape_contDiff d).comp (contDiff_const.sub contDiff_snd))

theorem profileS_hasDerivAt (y0 x : ℝ) : HasDerivAt (profileS y0) (-profileS y0 x) x := by
  convert! (((hasDerivAt_const x (y0 + 3)).sub (hasDerivAt_id x)).exp) using 1
  simp [profileS]

theorem profileZ_hasDerivAt (y0 η x : ℝ) :
    HasDerivAt (fun u => profileZ y0 (η, u)) (profileZ y0 (η, x)) x := by
  convert! (hasDerivAt_const x (2 * (1 - η ^ 2))).div
    (profileS_hasDerivAt y0 x) (profileS_pos y0 x).ne' using 1
  unfold profileZ
  dsimp only
  field_simp [(profileS_pos y0 x).ne'] ; ring

theorem profileCarrier_hasDerivAt_edge (C : ℝ) (d : TailData) (y0 η x : ℝ) :
    HasDerivAt (fun u => profileCarrier C d y0 (η, u))
      (-(profileRadius y0 x * profileCarrierRadial C d y0 (η, x)) / 2) x := by
  have hs := profileS_pos y0 x
  have hpow := (profileS_hasDerivAt y0 x).rpow_const
    (p := RadialHeatProfile.spatialExponent (1 + d.h)) (Or.inl hs.ne')
  have hH := ((HeatProfileExtension.extension_contDiff (a := 1 + d.h)
    (by linarith [d.h_pos])).differentiable (by simp) (profileZ y0 (η, x))).hasDerivAt
  have hp := (hpow.fun_mul (hH.comp x (profileZ_hasDerivAt y0 η x))).const_mul C
  simp only [Function.comp_def] at hp
  convert! hp using 1
  · funext u
    unfold profileCarrier
    dsimp only [Function.comp_apply]
    ring
  · unfold profileCarrierRadial
    dsimp only
    rw [Real.rpow_sub hs, Real.rpow_one]
    field_simp [hs.ne']
    ring_nf
    rw [profileRadius_square]
    ring

theorem profileAngularVelocity_hasDerivAt_edge (C : ℝ) (d : TailData) (y0 η x : ℝ) :
    HasDerivAt (fun u => profileAngularVelocity C d y0 (η, u))
      (-(profileRadius y0 x * profileCarrierRadial C d y0 (η, x)) / 2 * tailShape d (3 - x) -
        profileCarrier C d y0 (η, x) * tailShapeDeriv d (3 - x)) x := by
  have hf := (tailShape_hasDerivAt d (3 - x)).comp x
    ((hasDerivAt_const x 3).sub (hasDerivAt_id x))
  convert! (profileCarrier_hasDerivAt_edge C d y0 η x).mul hf using 1
  dsimp only [Function.comp_apply]
  ring

/-- Since `δ=Y-2 log r`, `1+2 ∂δ log(K f_o)` is exactly the radial shear
`1-r ∂r(K f_o)/(K f_o)`.  Here its logarithmic derivative is proved directly. -/
theorem profileSpeed_eq_log_deriv {C : ℝ} (hC : 0 < C) (d : TailData) (y0 η x : ℝ)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    profileSpeed C d y0 (η, x) =
      1 + 2 * deriv (fun u => profileAngularVelocity C d y0 (η, u)) x /
        profileAngularVelocity C d y0 (η, x) := by
  rw [(profileAngularVelocity_hasDerivAt_edge C d y0 η x).deriv]
  unfold profileSpeed profileAngularVelocity
  dsimp only
  field_simp [(profileCarrier_pos hC d y0 (y := (η, x)) (eta_sq_le_one hη)).ne',
    (tailShape_pos d (3 - x)).ne']
  ring

/-- The strict cone inequalities for the actual stress hold throughout one
positive-width terminal collar, uniformly through the closed profile interval. -/
theorem profile_relative_cone {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x < ε →
      0 < profileAngularStress C d y0 (η, x) ∧ 2 < profileSpeed C d y0 (η, x) ∧
      (profileSpeed C d y0 (η, x) - 2) * profileAxialStress C d y0 (η, x) ^ 2 <
        2 * profileAngularStress C d y0 (η, x) ^ 2 := by
  obtain ⟨ε, m, hε, hm, hb⟩ := profile_uniform_cone hC d y0
  refine ⟨ε, hε, ?_⟩
  intro η hη x hx hxε
  obtain ⟨ha, hv, hg⟩ := hb η hη x (by simpa only [abs_of_pos hx] using hxε)
  have hTa : 0 < profileAngularStress C d y0 (η, x) := by
    rw [profileAngularStress_factorization]
    exact mul_pos (div_pos (FlatCutoff.edge_pos 4 hx) (pow_pos hx _)) (hm.trans_le ha)
  refine ⟨hTa, by linarith, ?_⟩
  have hg' : (profileSpeed C d y0 (η, x) - 2) *
      (profileAxialStress C d y0 (η, x) / profileAngularStress C d y0 (η, x)) ^ 2 < 2 := by
    rw [profileTilt_eq_ratio C d y0 η hx]
    change m ≤ 2 - (profileSpeed C d y0 (η, x) - 2) * profileTilt C d y0 (η, x) ^ 2 at hg
    linarith
  apply (div_lt_iff₀ (sq_pos_of_pos hTa)).mp
  simpa only [div_pow, mul_div_assoc] using hg'

/-! ## The same weighted estimates on compact physical parameter sets -/

noncomputable def physicalStress (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ × ℝ := (angularStress C d y0 y, axialStress C d y0 y)

noncomputable def physicalStressFactor (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : EdgeParam × ℝ) : ℝ × ℝ := (angularFactor C d y0 y, y.2 ^ 6 * axialFactor C d y0 y)

theorem physicalStressFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (physicalStressFactor C d y0) :=
  (angularFactor_contDiff C d y0).prodMk ((contDiff_snd.pow 6).mul (axialFactor_contDiff C d y0))

theorem physicalStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : EdgeParam × ℝ) :
    physicalStress C d y0 y =
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • physicalStressFactor C d y0 y := by
  apply Prod.ext
  · exact angularStress_factorization C d y0 y
  · change axialStress C d y0 y =
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * (y.2 ^ 6 * axialFactor C d y0 y)
    rw [axialStress_factorization]
    by_cases hx : y.2 = 0
    · simp [hx]
    · field_simp [hx]

theorem physicalStress_jets (C : ℝ) (d : TailData) (y0 : ℝ) {S : Set EdgeParam}
    (hS : IsCompact S) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ S, ∀ x : ℝ, 0 < x → x ≤ b →
      ‖iteratedFDeriv ℝ i (physicalStress C d y0) (p, x)‖ ≤ A * FlatCutoff.edge 4 x / x ^ N := by
  have he : physicalStress C d y0 = fun y =>
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • physicalStressFactor C d y0 y :=
    funext (physicalStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.edge_smul_iteratedFDeriv_bound (by norm_num) 3
    (physicalStressFactor_contDiff C d y0) hS n hb

theorem physicalStress_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (physicalStress C d y0) := by
  have he : physicalStress C d y0 = fun y =>
      (FlatCutoff.edge 4 y.2 / y.2 ^ 3) • physicalStressFactor C d y0 y :=
    funext (physicalStress_factorization C d y0)
  rw [he]
  exact ((FlatCutoff.edge_div_pow_contDiff (by norm_num : (0 : ℝ) < 4) 3).comp
    contDiff_snd).smul (physicalStressFactor_contDiff C d y0)

theorem profileStress_of_nonpos (C : ℝ) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hy : y.2 ≤ 0) : profileStress C d y0 y = 0 := by
  rw [profileStress_factorization, FlatCutoff.edge_of_nonpos 4 hy, zero_div, zero_smul]

theorem physicalStress_of_nonpos (C : ℝ) (d : TailData) (y0 : ℝ)
    {y : EdgeParam × ℝ} (hy : y.2 ≤ 0) : physicalStress C d y0 y = 0 := by
  rw [physicalStress_factorization, FlatCutoff.edge_of_nonpos 4 hy, zero_div, zero_smul]

theorem physicalStress_normalizedParam (C : ℝ) (d : TailData) (y0 x : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    physicalStress C d y0 (normalizedParam η, x) = profileStress C d y0 (η, x) := by
  exact Prod.ext (angularStress_normalizedParam C d y0 x hη) (axialStress_normalizedParam C d y0 x
    hη)

/-! ## The genuine root-form cone on the terminal collar -/

noncomputable def profileSwirlCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ := profileAngularVelocity C d y0 y / profileRadius y0 y.2

theorem profileSwirlCoefficient_pos {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hη : y.1 ∈ Icc (-1 : ℝ) 1) :
    0 < profileSwirlCoefficient C d y0 y :=
  div_pos (mul_pos (profileCarrier_pos hC d y0 (eta_sq_le_one hη)) (tailShape_pos d _))
    (profileRadius_pos y0 y.2)

noncomputable def profileP (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  profileSpeed C d y0 y + profileAngularStress C d y0 y / profileSwirlCoefficient C d y0 y

noncomputable def profileJ (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  profileAxialStress C d y0 y / profileSwirlCoefficient C d y0 y

/-- Applying the exact true-cone equivalence to the actual terminal stress,
with `P-v=Tθ/F` and `J=Tz/F`, rather than taking a large-amplitude limit. -/
theorem profile_true_cone {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x < ε →
      2 < profileP C d y0 (η, x) ∧ profileSpeed C d y0 (η, x) <
        ConeAlgebra.coneBound (profileP C d y0 (η, x)) (profileJ C d y0 (η, x)) := by
  obtain ⟨ε, hε, hb⟩ := profile_relative_cone hC d y0
  refine ⟨ε, hε, ?_⟩
  intro η hη x hx hxε
  obtain ⟨hT, hv, hm⟩ := hb η hη x hx hxε
  have hF := profileSwirlCoefficient_pos hC d y0 (y := (η, x)) hη
  apply (ConeAlgebra.true_cone_iff hv).mpr
  constructor
  · exact lt_add_of_pos_right _ (div_pos hT hF)
  · have hd := div_lt_div_of_pos_right hm (sq_pos_of_pos hF)
    simp only [profileP, profileJ, add_sub_cancel_left, div_pow]
    simpa only [mul_div_assoc] using hd

end NavierStokes.TerminalEdgeFactor
