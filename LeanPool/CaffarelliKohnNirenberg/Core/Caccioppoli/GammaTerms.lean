/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI1
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI2Bound
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# The `γ`-form Caccioppoli terms

`paper/ckn.tex`, Lemma `lem:caccioppoli-gamma` (`eq:caccioppoli-gamma`), reruns
the proof of the Caccioppoli inequality `lem:caccioppoli` changing only the
bounds on the first two of the four error terms.  This file records those two
replacement bounds as standalone theorems about the same raw integrals that
`CKN.Core.Caccioppoli.RawI1` and `CKN.Core.Caccioppoli.RawI2Bound` bound.

* `I₁`: the test-function weight `|∂ₛφ + Δφ|` is bounded pointwise by
  `C r² ρ⁻⁵`, and `∫∫_{Q_ρ}|u|²` is estimated by Hölder with `1 = 2/3 + 1/3`,
  `∫∫_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∫∫_{Q_ρ}|u|³)^{2/3} = C ρ³ γ(ρ)²`.  Hence
  `I₁ ≤ C κ² γ(ρ)²` with `κ = r/ρ` (`caccioppoli_I1_gamma_heat_cutoff_raw_bound`).
* `I₂`: the Poincaré input is dropped; instead
  `||u|² − ⨍_{B_ρ}|u|²| |u| ≤ 2|u|³ + (⨍_{B_ρ}|u|²)^{3/2}` pointwise, the
  spatial average enters through the Jensen bound
  `⨍_{B_ρ}|u|² ≤ (⨍_{B_ρ}|u|³)^{2/3}`, and `∫∫_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
  `I₂ ≤ C κ⁻² γ(ρ)³` (`caccioppoli_I2_gamma_heat_cutoff_raw_bound`).

The remaining two terms `I₃`, `I₄` keep their proved bounds, so the conclusion
of `eq:caccioppoli-gamma` follows by the normalisation lemmas recorded here.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-! ## The two elementary estimates behind the replacement bounds -/

/-- Hölder's inequality on a measure space with conjugate exponents `3/2` and `3`
in the form used for `I₁`: the integral of a nonnegative function is bounded by
`(∫ A^{3/2})^{2/3}` times the `1/3` power of the total mass. -/
theorem caccioppoli_holder_l2_le_l3
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : α → ℝ≥0∞}
    (hA : AEMeasurable A μ) :
    (∫⁻ x, A x ∂μ) ≤
      (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ) := by
  have hconj : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hone : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hA hone
  calc
    (∫⁻ x, A x ∂μ) = ∫⁻ x, A x * (fun _ : α => (1 : ℝ≥0∞)) x ∂μ := by simp
    _ ≤ (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (1 / (3 / 2 : ℝ)) *
        (∫⁻ x, (fun _ : α => (1 : ℝ≥0∞)) x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := h
    _ = (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ) := by
      rw [show (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) by norm_num]
      congr 2
      · simp

/-- The `I₁` integration step, in the form used here: a pointwise bound on one
factor and an `L¹` bound on the other give a bound on the product of the two,
with no measurability hypotheses on either factor.  This is the established
`caccioppoli_I1_toReal_lintegral_bound` with its two unused measurability
arguments dropped. -/
private theorem caccioppoli_toReal_lintegral_bound_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U H : α → ℝ≥0∞} {C E : ℝ≥0∞}
    (hC : C ≠ ∞) (hHC : H ≤ᵐ[μ] fun _ => C)
    (hE : (∫⁻ x, U x ∂μ) ≤ E) (hCE : C * E ≠ ∞) :
    (∫⁻ x, U x * H x ∂μ).toReal ≤ (C * E).toReal :=
  ENNReal.toReal_mono hCE (caccioppoli_I1_lintegral_bound hC hHC hE)

/-- The pointwise inequality behind `I₂` in its `γ`-form: for `N, m ≥ 0`,
`|N² − m| N ≤ 2 N³ + m^{3/2}`.  This combines the triangle inequality for the
mean subtraction with the Young inequality `mN ≤ m^{3/2} + N³`. -/
theorem caccioppoli_abs_sq_sub_mul_le (N m : ℝ) (hN : 0 ≤ N) (hm : 0 ≤ m) :
    |N ^ 2 - m| * N ≤ 2 * N ^ 3 + m ^ (3 / 2 : ℝ) := by
  have hN3 : 0 ≤ N ^ 3 := by positivity
  have hmp : 0 ≤ m ^ (3 / 2 : ℝ) := Real.rpow_nonneg hm _
  rcases le_or_gt m (N ^ 2) with h | h
  · rw [abs_of_nonneg (by linarith only [h])]
    have hle : (N ^ 2 - m) * N ≤ N ^ 3 := by
      have hstep : N ^ 2 - m ≤ N ^ 2 := by linarith only [hm]
      calc
        (N ^ 2 - m) * N ≤ N ^ 2 * N := mul_le_mul_of_nonneg_right hstep hN
        _ = N ^ 3 := by ring
    linarith only [hle, hN3, hmp]
  · rw [abs_of_neg (by linarith only [h])]
    have hNm : N ≤ m ^ (1 / 2 : ℝ) := by
      have hsqrt : Real.sqrt (N ^ 2) ≤ Real.sqrt m := Real.sqrt_le_sqrt h.le
      rwa [Real.sqrt_sq hN, Real.sqrt_eq_rpow] at hsqrt
    have hpowid : m ^ (3 / 2 : ℝ) = m * m ^ (1 / 2 : ℝ) := by
      have hmpos : 0 < m := by
        have hNsq : 0 ≤ N ^ 2 := by positivity
        linarith only [h, hNsq]
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hmpos,
        Real.rpow_one]
    have hmul : m * N ≤ m ^ (3 / 2 : ℝ) := by
      have hstep := mul_le_mul_of_nonneg_left hNm hm
      simpa only [← hpowid] using hstep
    have hle : (m - N ^ 2) * N ≤ m * N := by
      have hNsq : 0 ≤ N ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith only [hNsq]) hN
    linarith only [hle, hmul, hN3]

/-- The `ℝ≥0∞` form of `caccioppoli_abs_sq_sub_mul_le`, ready for integration.
The two `N³` terms are kept separate so that each can be matched against the
velocity integral `∫∫_{Q_ρ}|u|³`, and the exponent `3` of `N` is the real one so
that the term is literally `(ENNReal.ofReal N) ^ (3 : ℝ)`, the integrand of the
velocity identity `caccioppoli_I2_velocity_integral_identity`. -/
theorem caccioppoli_ennreal_abs_sq_sub_mul_le (N m : ℝ) (hN : 0 ≤ N)
    (hm : 0 ≤ m) :
    ENNReal.ofReal |N ^ 2 - m| * ENNReal.ofReal N ≤
      ENNReal.ofReal N ^ (3 : ℝ) + ENNReal.ofReal N ^ (3 : ℝ) +
        ENNReal.ofReal m ^ (3 / 2 : ℝ) := by
  have h := caccioppoli_abs_sq_sub_mul_le N m hN hm
  have hcube : ENNReal.ofReal (N ^ 3) = ENNReal.ofReal N ^ (3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hN (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    simp
  calc
    ENNReal.ofReal |N ^ 2 - m| * ENNReal.ofReal N
        = ENNReal.ofReal (|N ^ 2 - m| * N) := by
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * N ^ 3 + m ^ (3 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (2 * N ^ 3) + ENNReal.ofReal (m ^ (3 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal N ^ (3 : ℝ) + ENNReal.ofReal N ^ (3 : ℝ) +
          ENNReal.ofReal m ^ (3 / 2 : ℝ) := by
        rw [show 2 * N ^ 3 = N ^ 3 + N ^ 3 by ring,
          ENNReal.ofReal_add (by positivity) (by positivity),
          hcube,
          ← ENNReal.ofReal_rpow_of_nonneg hm (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- The `L²` estimate for the velocity in the `γ`-form Caccioppoli inequality:
Hölder's inequality on `Q_ρ` with `1 = 2/3 + 1/3` combined with
`∫∫_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
`∫∫_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∫∫_{Q_ρ}|u|³)^{2/3} = (4π/3)^{1/3} ρ³ γ(ρ)²`. -/
theorem caccioppoli_velocity_l2_gamma_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hA : AEMeasurable (fun w =>
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ))) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
        gamma u (x₀, t₀) ρ ^ 2) := by
  let A : ParabolicPoint → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)
  have hAg : ∀ w, A w ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
    intro w
    dsimp only [A]
    rw [← ENNReal.rpow_mul]
    rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num]
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by unfold gamma; positivity
  have hhold := caccioppoli_holder_l2_le_l3
    (μ := volume.restrict (parabolicCylinder x₀ t₀ ρ)) hA
  have hid := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hvol : (volume.restrict (parabolicCylinder x₀ t₀ ρ)) Set.univ =
      ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5) := by
    rw [Measure.restrict_apply_univ]
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ3 : 0 ≤ ρ ^ 3 := by positivity
    rw [volume_parabolicCylinder, volume_vec3Ball_eq]
    rw [← ENNReal.ofReal_pow hρ.le]
    rw [← ENNReal.ofReal_mul hρ3, ← ENNReal.ofReal_mul (mul_nonneg hρ3 hπ)]
    congr 1
    ring
  have hpow1 : (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
      ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by
    have hρpart : (ρ ^ 2) ^ (2 / 3 : ℝ) = ρ ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
      norm_num
    have hγpart : (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
        gamma u (x₀, t₀) ρ ^ 2 := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hγ]
      norm_num
    calc
      (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ)
          = (ρ ^ 2) ^ (2 / 3 : ℝ) * (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) :=
            Real.mul_rpow (by positivity) (by positivity)
      _ = ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by rw [hρpart, hγpart]
  have hpow2 : ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ) =
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ5 : 0 ≤ ρ ^ 5 := by positivity
    have hρpart : (ρ ^ 5) ^ (1 / 3 : ℝ) = ρ ^ (5 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 5, ← Real.rpow_mul hρ.le]
      norm_num
    calc
      ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ)
          = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (ρ ^ 5) ^ (1 / 3 : ℝ) :=
            Real.mul_rpow hπ hρ5
      _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by rw [hρpart]
  calc
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w)
        ≤ (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
            (volume.restrict (parabolicCylinder x₀ t₀ ρ) Set.univ) ^
              (1 / 3 : ℝ) := hhold
    _ = (ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5)) ^ (1 / 3 : ℝ) := by
        rw [lintegral_congr fun w => hAg w, hid, hvol]
    _ = ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
          gamma u (x₀, t₀) ρ ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          hpow1, hpow2,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hρ.le _)
            (sq_nonneg _))]
        apply congrArg ENNReal.ofReal
        have hρadd : ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) = ρ ^ 3 := by
          rw [← Real.rpow_add hρ]
          rw [show (4 : ℝ) / 3 + 5 / 3 = 3 by norm_num]
          simp
        calc
          ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 *
              ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) =
              (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
                (ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) *
                  gamma u (x₀, t₀) ρ ^ 2 := by ring
          _ = _ := by rw [hρadd]

/-! ## The `I₁` replacement bound -/

/-- The pointwise bound on the heat-cut-off weight of `I₁` used in the proof of
Lemma `lem:caccioppoli-gamma`: on the parabolic cylinder `Q_ρ` the weight
`|∂ₛφ + Δφ|` is dominated by the constant
`(32/ρ² + 3C''/ρ²)(8·10⁶ r²/ρ³) + 6(C'/ρ)(5·10⁶ r²/ρ⁴)`, exactly as in the
established `I₁` estimate.  The estimate is a statement about the cut-off alone and
does not involve the solution. -/
private theorem caccioppoli_I1_cutoff_operator_dominated
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2) :
    (fun z : ParabolicPoint => ENNReal.ofReal
        |timePartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|)
      ≤ᵐ[volume.restrict (parabolicCylinder x₀ t₀ ρ)]
        (fun _ => ENNReal.ofReal
          ((32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
              (8000000 * r ^ 2 / ρ ^ 3) +
            6 * (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4))) := by
  filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)] with z hz
  have htime' := (mem_parabolicCylinder.mp hz).2.2
  have hz' : (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 ρ := by
    rcases mem_parabolicCylinder.mp hz with ⟨hspace, hlo, hup⟩
    rw [parabolicCylinder]
    exact ⟨by simpa using hspace, ⟨by linarith only [hlo], by linarith only [hup]⟩⟩
  have hp := caccioppoli_I1_heat_cutoff_pointwise_on_cylinder
    hρ hε hr hscale hεr htime' hz'
  exact ENNReal.ofReal_le_ofReal hp

/-- The `I₁` error term of the Caccioppoli inequality, as a function of any
upper bound `E` for the velocity energy `∫∫_{Q_ρ}|u|²` with `E ≥ 0`.  This is the
established `I₁` estimate with the energy bound left as a parameter, so that the
`γ`-form velocity bound can be substituted for the `α`-form one. -/
private theorem caccioppoli_I1_raw_of_energy_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r E : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hεr : ε < r ^ 2) (hE0 : 0 ≤ E)
    (hE : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
        ENNReal.ofReal E) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      ((32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4)) * E := by
  let C₁ : ℝ :=
    (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
        (8000000 * r ^ 2 / ρ ^ 3) +
      6 * (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4)
  change caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
      (ρ := ρ) (ε := ε) (r := r) hρ hε ≤ C₁ * E
  have hCgrad : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hCsecond : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 :=
    (abs_nonneg (spatialSecondPartial
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) 0 0 (x₀, t₀))).trans
      (caccioppoli_heat_cutoff_second_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε (x₀, t₀) 0 0)
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    have hA : 0 ≤ 32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      positivity
    have hB : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hCgrad hρ.le
    positivity
  have hHC : (fun z : ParabolicPoint => ENNReal.ofReal
      |timePartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|)
      ≤ᵐ[volume.restrict (parabolicCylinder x₀ t₀ ρ)]
        (fun _ => ENNReal.ofReal C₁) := by
    have h := caccioppoli_I1_cutoff_operator_dominated (x₀ := x₀) (t₀ := t₀)
      hρ hε hr hscale hεr
    simpa only [C₁] using h
  have hprod : ENNReal.ofReal C₁ * ENNReal.ofReal E ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound := caccioppoli_toReal_lintegral_bound_of_ae
    ENNReal.ofReal_ne_top hHC hE hprod
  have hright : (ENNReal.ofReal C₁ * ENNReal.ofReal E).toReal = C₁ * E := by
    rw [← ENNReal.ofReal_mul hC₁]
    exact ENNReal.toReal_ofReal (mul_nonneg hC₁ hE0)
  change (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|).toReal ≤
      C₁ * E
  exact hbound.trans_eq hright

/-- **The `I₁` replacement bound of Lemma `lem:caccioppoli-gamma`.**  Combining
the pointwise bound on the heat-cut-off weight with Hölder's inequality
`1 = 2/3 + 1/3` on `Q_ρ` and the `γ`-form velocity bound
`∫∫_{Q_ρ}|u|² ≤ (4π/3)^{1/3} ρ³ γ(ρ)²`, the first error term satisfies
`I₁ ≤ C r²ρ⁻⁵ ρ³γ(ρ)² = C κ²γ(ρ)²` with `κ = r/ρ`, the constant being the same
one that appears in the established `I₁` bound times `(4π/3)^{1/3}`. -/
theorem caccioppoli_I1_gamma_heat_cutoff_raw_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hεr : ε < r ^ 2)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hA : AEMeasurable (fun w =>
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ))) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
          6 * cutoffGradientConstant * 5000000) *
        (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (r ^ 2 / ρ ^ 5) *
          (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2) := by
  let K₁ : ℝ := (32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
    6 * cutoffGradientConstant * 5000000
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by unfold gamma; positivity
  have hE0 : 0 ≤ (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hE : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
        (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2)) := by
    refine (caccioppoli_velocity_l2_gamma_bound (u := u) hρ hvelocity hA).trans_eq ?_
    apply congrArg ENNReal.ofReal
    ring
  calc
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε
        ≤ ((32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
              (8000000 * r ^ 2 / ρ ^ 3) +
            6 * (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4)) *
            ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
              (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2)) :=
          caccioppoli_I1_raw_of_energy_bound hρ hε hr hscale hεr hE0 hE
    _ = K₁ * (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (r ^ 2 / ρ ^ 5) *
          (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2) := by
        dsimp [K₁]
        field_simp [hρ.ne']

/-- **Normalized `I₁`.**  Reading the `I₁` replacement bound as
`I₁ ≤ K (r²/ρ⁵) ρ³γ(ρ)²` with `K = (4π/3)^{1/3}((32 + 3C'')8·10⁶ + 6C'5·10⁶)`
and assuming `K ≤ C₂₅²`, the first two terms of `eq:caccioppoli-gamma` give
`I₁ ≤ (C₂₅ κ γ(ρ))²` with `κ = r/ρ`. -/
theorem caccioppoli_I1_gamma_normalized
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r C₂₅ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hεr : ε < r ^ 2)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hA : AEMeasurable (fun w =>
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hKbound : (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
        ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
          6 * cutoffGradientConstant * 5000000) ≤ C₂₅ ^ 2) :
    caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ) ^ 2 := by
  have hraw : caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
          ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
            6 * cutoffGradientConstant * 5000000)) *
        (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2) := by
    calc
      _ ≤ ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
            6 * cutoffGradientConstant * 5000000) *
            (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (r ^ 2 / ρ ^ 5) *
              (ρ ^ 3 * gamma u (x₀, t₀) ρ ^ 2) :=
          caccioppoli_I1_gamma_heat_cutoff_raw_bound
            hρ hε hr hscale hεr hvelocity hA
      _ = _ := by ring
  exact caccioppoli_I1_normalization hρ hr hKbound hraw

/-! ## The `I₂` replacement bound -/

/-- **The `I₂` replacement bound of Lemma `lem:caccioppoli-gamma`.**  Here the
Poincaré input used by the established `I₂` bound is replaced by the pointwise bound
`||u|² − c| |u| ≤ 2|u|³ + c^{3/2}` together with the Jensen bound `hmean` on the
spatial average `c` (in the application `c` is `⨍_{B_ρ}|u|²`).  Since
`∫∫_{Q_ρ}|u|³ = ρ²γ(ρ)³` and the cut-off gradient contributes a factor `r⁻²`,
this gives `I₂ ≤ C r⁻²ρ²γ(ρ)³ = C κ⁻²γ(ρ)³` with `κ = r/ρ`, matching the
displayed bound in the proof of Lemma `lem:caccioppoli-gamma`. -/
theorem caccioppoli_I2_gamma_heat_cutoff_raw_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {c : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hc : ∀ w, 0 ≤ c w)
    (hcm : AEMeasurable c (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hmean : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      3 * (1500 * cutoffGradientConstant + 900000) * (ρ ^ 2 / r ^ 2) *
        gamma u (x₀, t₀) ρ ^ 3 := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu0 : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hu : AEMeasurable (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact ((ENNReal.continuous_ofReal.comp hcont).comp_aestronglyMeasurable
        hu0).aemeasurable |>.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hgrad : ∀ w ∈ parabolicCylinder x₀ t₀ ρ,
      ∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w| ≤
        (1500 * cutoffGradientConstant + 900000) / r ^ 2 := by
    intro w hw
    have hraw := caccioppoli_heat_cutoff_gradient_sum_bound
      (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      (z := w) hρ hε hr hscale hw
    have hρr : 2 * r ≤ ρ := by nlinarith only [hscale]
    have hfirst : cutoffGradientConstant / ρ * (1000 / r) ≤
        500 * cutoffGradientConstant / r ^ 2 := by
      have hmul : 1000 / (ρ * r) ≤ 500 / r ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos hρ hr) (sq_pos_of_pos hr)).2
        have hmul' := mul_le_mul_of_nonneg_right hρr hr.le
        nlinarith only [hmul']
      calc
        cutoffGradientConstant / ρ * (1000 / r) =
            cutoffGradientConstant * (1000 / (ρ * r)) := by
          field_simp [hρ.ne', hr.ne']
        _ ≤ cutoffGradientConstant * (500 / r ^ 2) :=
          mul_le_mul_of_nonneg_left hmul hC
        _ = 500 * cutoffGradientConstant / r ^ 2 := by ring
    have hsecond : 300000 * r ^ 2 / r ^ 4 = 300000 / r ^ 2 := by
      field_simp [hr.ne']
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (add_le_add hfirst hsecond.le) (by positivity)) |>.trans_eq (by ring)
  let G : ℝ := (1500 * cutoffGradientConstant + 900000) / r ^ 2
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by unfold gamma; positivity
  have hV : 0 ≤ ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3 := by positivity
  have hvel3' : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) := by
    simpa only [Prod.fst, Prod.snd] using
      caccioppoli_I2_velocity_integral_identity
        (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hAmeas : AEMeasurable (fun w =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := hu.pow_const 3
  have hBmeas : AEMeasurable (fun w => ENNReal.ofReal (c w) ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) :=
    (ENNReal.continuous_ofReal.measurable.pow_const (3 / 2 : ℝ)
      ).comp_aemeasurable hcm
  have hpt : ∀ᵐ w ∂(volume.restrict (parabolicCylinder x₀ t₀ ρ)),
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
      ENNReal.ofReal G *
        ((ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
          ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    have hN : 0 ≤ vec3EuclideanNorm (u w) := vec3EuclideanNorm_nonneg _
    have hcore := caccioppoli_ennreal_abs_sq_sub_mul_le
      (vec3EuclideanNorm (u w)) (c w) hN (hc w)
    have hscalar : ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
        ENNReal.ofReal G := ENNReal.ofReal_le_ofReal (hgrad w hw)
    calc
      _ = ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) *
            (ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
              ENNReal.ofReal (vec3EuclideanNorm (u w))) := by ring
      _ ≤ ENNReal.ofReal G *
            ((ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
              ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) :=
          mul_le_mul' hscalar hcore
  have hsum3 : ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) +
        ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) +
        ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) =
      ENNReal.ofReal (3 * (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) := by
    rw [← ENNReal.ofReal_add hV hV, ← ENNReal.ofReal_add (add_nonneg hV hV) hV]
    apply congrArg ENNReal.ofReal
    ring
  have hchain : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≤
      ENNReal.ofReal (G * (3 * (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3))) := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ENNReal.ofReal G *
            ((ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
              ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal G *
            ((∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
              (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
              (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                ENNReal.ofReal (c w) ^ (3 / 2 : ℝ))) := by
          have h1 : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
                ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
                ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) =
              (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
                    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
                (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) :=
            lintegral_add_left' (hAmeas.add hAmeas)
              (fun w => ENNReal.ofReal (c w) ^ (3 / 2 : ℝ))
          have h2 : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
                ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
              (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) +
                (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) :=
            lintegral_add_left' hAmeas
              (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, h2]
      _ ≤ ENNReal.ofReal G *
            (ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) +
              ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) +
              ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) := by
          exact mul_le_mul (le_refl _)
            (add_le_add (add_le_add hvel3'.le hvel3'.le) hmean)
            bot_le bot_le
      _ = ENNReal.ofReal (G * (3 * (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3))) := by
          rw [hsum3, ← ENNReal.ofReal_mul hG]
  have hfinal : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)).toReal ≤
      G * (3 * (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
    rwa [ENNReal.toReal_ofReal (mul_nonneg hG (mul_nonneg (by norm_num) hV))] at h
  calc
    caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε
        ≤ G * (3 * (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) := hfinal
    _ = 3 * (1500 * cutoffGradientConstant + 900000) * (ρ ^ 2 / r ^ 2) *
          gamma u (x₀, t₀) ρ ^ 3 := by
        dsimp [G]
        ring

end CKN
