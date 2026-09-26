/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorantQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantExponents

/-!
# The near-force remainder on a margin cell of `prop:bootstrap`

The spatial pressure gradient of `prop:bootstrap` splits, about each centre of
the origin carrier, into a Riesz part driven by the localized divergence source
and a remainder: the gradient of the harmonic pressure part plus the far-force
potential.  This file bounds the clipped-cell time integral of the `6/5` power
of the remainder's spatial `L^{6/5}` slice norm by the affine A slot
`originKPAffineASlot`, on every *margin cell* — centre in the closure of the
carrier of radius `R₁`, radius at most `(1 - R₁)/4` — above one absolute
Calderón–Zygmund threshold.

The collar on which the remainder is estimated is *fixed*, of radius
`ρ = (1 - R₁)/2`, never proportional to the cell radius: the pointwise
derivative estimate for the harmonic part costs `ρ⁻⁴`, so a collar
proportional to `r` would leave a negative power of `r`.  With a fixed collar
the cell contributes its own volume `(4π/3) r³` and the clipped time window
contributes `r²` through two Hölder steps, one in space against the collar and
one in time against the window.  The resulting powers are `r^{17/5}` for the
energy and pressure contributions and `r^{5 - 12/(5q)}` for the force
contribution, both above the growth exponent
`θ = 5(1 - (6/5)/min ((1/τ + 8/25)⁻¹) q) ≤ 71/25`.

The two data powers produced are `ε^{4/5}` and `ε^{6/(5q)}`, which are exactly
the sizes of the slot's pressure-mass term `c·128·ε^{4/5}` and of the `6/5`
power of its source term `(c·3X)^{6/5} ≥ (3c)^{6/5}·ε^{6/(5q)}`.  No additive
absolute constant survives, so the estimate is compatible with a vanishing
slot at vanishing data.
-/

public section

section

/-!
# Hölder below exponent one and its slice-then-time form

This module records two measure-theoretic inequalities in `ℝ≥0∞` that feed the
`A`-slot pressure-gradient estimate.

* `originASlot_lintegral_rpow_le` is Hölder's inequality for a single exponent `t`
  with `0 < t < 1`: it compares the `t`-power integral with the full integral times
  a power of the total mass.
* `originASlot_slice_time_rpow_bound` combines a spatial Hölder step with a temporal
  one: it controls the `6/5`-power of the space integral, integrated in time, by the
  product-measure integral of the `c`-power of the integrand, with the exponents
  dictated by the two applications of the first inequality.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Hölder's inequality for an exponent `t` strictly between zero and one: the integral of
`g ^ t` is bounded by a power of the total mass times the `t`-power of the integral of `g`. -/
theorem originASlot_lintegral_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ y, g y ^ t ∂μ) ≤ μ Set.univ ^ (1 - t) * (∫⁻ y, g y ∂μ) ^ t := by
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hpq : Real.HolderConjugate (1 / t) (1 / (1 - t)) := by
    constructor
    · rw [one_div, inv_inv, one_div, inv_inv, inv_one]
      ring
    · exact one_div_pos.mpr ht0
    · exact one_div_pos.mpr (sub_pos.mpr ht1)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
      (hg.pow_const t) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one] at h
  have hR1 : (∫⁻ a, (g a ^ t) ^ (1 / t) ∂μ) = ∫⁻ a, g a ∂μ := by
    apply lintegral_congr
    intro a
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht0', ENNReal.rpow_one]
  have hR2 : (1 : ℝ) / (1 / t) = t := by rw [one_div_one_div]
  have hR3 : (∫⁻ a, (1 : ℝ≥0∞) ^ (1 / (1 - t)) ∂μ) = μ Set.univ := by simp
  have hR4 : (1 : ℝ) / (1 / (1 - t)) = 1 - t := by rw [one_div_one_div]
  rw [hR1, hR2, hR3, hR4] at h
  exact h.trans (le_of_eq (mul_comm _ _))

/-- The slice-then-time Hölder bound: the `6/5`-power of the spatial integral of `G ^ a`,
integrated over the time window, is bounded by powers of the spatial and temporal volumes
times the `6a/(5c)`-power of the product-measure integral of `G ^ c`. -/
theorem originASlot_slice_time_rpow_bound
    {B : Set Vec3} {W : Set ℝ} {G : Vec3 × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.restrict B).prod (volume.restrict W)))
    {a c : ℝ} (ha : 0 < a) (hac : 6 * a < 5 * c) :
    (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ)) ≤
      volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) * volume W ^ (1 - 6 * a / (5 * c)) *
        (∫⁻ w in B ×ˢ W, G w ^ c) ^ (6 * a / (5 * c)) := by
  have hc0 : 0 < c := by nlinarith only [ha, hac]
  have hlt : a < c := by nlinarith only [ha, hac]
  have ht_pos : 0 < a / c := div_pos ha hc0
  have ht_lt_one : a / c < 1 := (div_lt_one hc0).mpr hlt
  set t : ℝ := 6 * a / (5 * c) with ht_def
  have ht0 : 0 < t := by
    rw [ht_def]; exact div_pos (by linarith only [ha]) (by linarith only [hc0])
  have ht1 : t < 1 := by
    rw [ht_def]
    exact (div_lt_one (by linarith only [hc0] : (0 : ℝ) < 5 * c)).mpr hac
  have hspat_ae : ∀ᵐ s ∂(volume.restrict W),
      (∫⁻ y in B, G (y, s) ^ a) ≤
        volume B ^ (1 - a / c) * (∫⁻ y in B, G (y, s) ^ c) ^ (a / c) := by
    filter_upwards [hG.aestronglyMeasurable.prodMk_right] with s hs
    have hle := originASlot_lintegral_rpow_le (volume.restrict B)
      (hs.aemeasurable.pow_const c) ht_pos ht_lt_one
    rw [Measure.restrict_apply_univ] at hle
    have heq : (∫⁻ y, (G (y, s) ^ c) ^ (a / c) ∂(volume.restrict B))
        = ∫⁻ y in B, G (y, s) ^ a := by
      apply lintegral_congr
      intro y
      rw [← ENNReal.rpow_mul, mul_div_cancel₀ a (ne_of_gt hc0)]
    rw [heq] at hle
    exact hle
  have hH_meas : AEMeasurable (fun s => ∫⁻ y in B, G (y, s) ^ c) (volume.restrict W) :=
    (hG.pow_const c).lintegral_prod_left'
  have hstep_ae : ∀ᵐ s ∂(volume.restrict W),
      (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ) ≤
        volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (∫⁻ y in B, G (y, s) ^ c) ^ t := by
    filter_upwards [hspat_ae] with s hs
    have h1 := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 6 / 5)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5)] at h1
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h1
    have e1 : (1 - a / c) * (6 / 5 : ℝ) = (6 / 5 : ℝ) * (1 - a / c) := by ring
    have e2 : (a / c) * (6 / 5 : ℝ) = t := by rw [ht_def]; field_simp
    rw [e1, e2] at h1
    exact h1
  have hmono : (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ y in B, G (y, s) ^ c) ^ t :=
    lintegral_mono_ae hstep_ae
  have hpull : (∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ y in B, G (y, s) ^ c) ^ t)
      = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) := by
    rw [lintegral_const_mul'' _ (hH_meas.pow_const t)]
  have htime : (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) ≤
      volume W ^ (1 - t) * (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) ^ t := by
    have h := originASlot_lintegral_rpow_le (volume.restrict W) hH_meas ht0 ht1
    rwa [Measure.restrict_apply_univ] at h
  have hTonelli : (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) = ∫⁻ w in B ×ˢ W, G w ^ c := by
    rw [← lintegral_prod_symm _ (hG.pow_const c), Measure.prod_restrict]
    rfl
  calc
    (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ))
        ≤ ∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
            (∫⁻ y in B, G (y, s) ^ c) ^ t := hmono
    _ = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) := hpull
    _ ≤ volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (volume W ^ (1 - t) * (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) ^ t) :=
        mul_le_mul' le_rfl htime
    _ = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (volume W ^ (1 - t) * (∫⁻ w in B ×ˢ W, G w ^ c) ^ t) := by rw [hTonelli]
    _ = _ := by rw [mul_assoc]

end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-! ### Exponent and volume arithmetic -/

/-- The growth exponent of `prop:bootstrap` never exceeds `5 - 12/(5q)`. -/
theorem harmonicRemainder_theta_le_force {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ≤ 5 - 12 / (5 * q) := by
  have hlo : (25 : ℝ) / 11 ≤ min ((1 / τ + 8 / 25)⁻¹) q := endgame_kappa_ge hτ hq
  have hpos : (0 : ℝ) < min ((1 / τ + 8 / 25)⁻¹) q := by linarith only [hlo]
  have hq0 : (0 : ℝ) < q := by linarith only [hq]
  have hkq : min ((1 / τ + 8 / 25)⁻¹) q ≤ q := min_le_right _ _
  have hdiv : (6 / 5 : ℝ) / q ≤ (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q :=
    div_le_div_of_nonneg_left (by norm_num) hpos hkq
  have hval : (5 : ℝ) * ((6 / 5 : ℝ) / q) = 6 / q := by
    field_simp
  have hdiff : (6 : ℝ) / q - 12 / (5 * q) = 18 / (5 * q) := by
    field_simp
    ring
  have hpos18 : (0 : ℝ) ≤ 18 / (5 * q) := by positivity
  have hcmp : (12 : ℝ) / (5 * q) ≤ 6 / q := by linarith only [hdiff, hpos18]
  linarith only [hdiv, hval, hcmp]

/-- The spatial volume of a ball of radius at most `1/2` is at most one. -/
theorem harmonicRemainder_volume_ball_le_one {x : Vec3} {ρ : ℝ}
    (hρhi : ρ ≤ 1 / 2) : volume (vec3Ball x ρ) ≤ 1 := by
  rw [volume_vec3Ball_eq]
  have hπ : ENNReal.ofReal (Real.pi * 4 / 3) ≤ ENNReal.ofReal 5 :=
    ENNReal.ofReal_le_ofReal (by linarith only [Real.pi_lt_d2])
  have hr : ENNReal.ofReal ρ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hρhi
  calc
    ENNReal.ofReal ρ ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) ≤
        ENNReal.ofReal (1 / 2) ^ 3 * ENNReal.ofReal 5 := by gcongr
    _ = ENNReal.ofReal (5 / 8) := by
      rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ 1 := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The unit cylinder has volume at least one. -/
theorem harmonicRemainder_one_le_volume_unit :
    (1 : ℝ≥0∞) ≤ volume (parabolicCylinder (0 : Vec3) 0 1) := by
  rw [volume_parabolicCylinder, volume_vec3Ball_eq]
  have hπ : ENNReal.ofReal 1 ≤ ENNReal.ofReal (Real.pi * 4 / 3) :=
    ENNReal.ofReal_le_ofReal (by linarith only [Real.pi_gt_three])
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal 1 ^ 3 * ENNReal.ofReal 1 * ENNReal.ofReal (1 ^ 2) := by
      simp
    _ ≤ ENNReal.ofReal 1 ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) *
        ENNReal.ofReal (1 ^ 2) := by gcongr
    _ = _ := by norm_num

/-! ### The two data powers against the affine slot -/

/-- The force-source bound of the unit data size dominates the plain data power
`ε^{1/q}`, because the unit cylinder has volume at least one. -/
theorem harmonicRemainder_data_power_le_forceSource {q ε : ℝ} (hq : 5 / 2 < q) :
    ENNReal.ofReal ε ^ (1 / q) ≤ forceSourceMorreyBound q ε := by
  have hq0 : (0 : ℝ) < q := by linarith only [hq]
  have hexp : (0 : ℝ) < 5 / 6 - 1 / q := by
    have hdiff : (2 : ℝ) / 5 - 1 / q = (2 * q - 5) / (5 * q) := by
      field_simp
    have hnum : (0 : ℝ) < 2 * q - 5 := by linarith only [hq]
    have hfrac : (0 : ℝ) < (2 * q - 5) / (5 * q) := by positivity
    have h : (1 : ℝ) / q < 2 / 5 := by linarith only [hdiff, hfrac]
    linarith only [h]
  have hone : (1 : ℝ≥0∞) ≤
      volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / q : ℝ) :=
    ENNReal.one_le_rpow harmonicRemainder_one_le_volume_unit hexp
  unfold forceSourceMorreyBound
  calc
    ENNReal.ofReal ε ^ (1 / q) = 1 * ENNReal.ofReal ε ^ (1 / q) := (one_mul _).symm
    _ ≤ _ := mul_le_mul' hone le_rfl

/-- The remainder's two data powers are paid by two of the three terms of the
affine A slot: the pressure-mass term and the `6/5` power of the source term. -/
theorem harmonicRemainder_two_terms_le_originKPAffineASlot
    (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞) (hq : 5 / 2 < q) :
    (3 * ENNReal.ofReal (|C_CZ| + 1)) ^ (6 / 5 : ℝ) *
        ENNReal.ofReal ε ^ (6 / (5 * q)) +
      ENNReal.ofReal (|C_CZ| + 1) * 128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ) ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  have hq0 : (0 : ℝ) < q := by linarith only [hq]
  set c := ENNReal.ofReal (|C_CZ| + 1) with hc
  set X := 3 * KU * KD + forceSourceMorreyBound q ε with hX
  have hexp : (1 / q) * (6 / 5 : ℝ) = 6 / (5 * q) := by
    field_simp
  have hsource : (3 * c) ^ (6 / 5 : ℝ) * ENNReal.ofReal ε ^ (6 / (5 * q)) ≤
      (c * (3 * X)) ^ (6 / 5 : ℝ) := by
    have hdata : ENNReal.ofReal ε ^ (6 / (5 * q)) ≤
        forceSourceMorreyBound q ε ^ (6 / 5 : ℝ) := by
      rw [← hexp, ENNReal.rpow_mul]
      exact ENNReal.rpow_le_rpow (harmonicRemainder_data_power_le_forceSource hq)
        (by norm_num)
    calc
      (3 * c) ^ (6 / 5 : ℝ) * ENNReal.ofReal ε ^ (6 / (5 * q)) ≤
          (3 * c) ^ (6 / 5 : ℝ) * forceSourceMorreyBound q ε ^ (6 / 5 : ℝ) :=
        mul_le_mul' le_rfl hdata
      _ = ((3 * c) * forceSourceMorreyBound q ε) ^ (6 / 5 : ℝ) :=
        (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
      _ ≤ (c * (3 * X)) ^ (6 / 5 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        calc
          (3 * c) * forceSourceMorreyBound q ε = c * (3 * forceSourceMorreyBound q ε) := by
            ring
          _ ≤ c * (3 * X) := by
            refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
            rw [hX]
            exact le_add_self
  have hmass : c * 128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ) =
      c * (128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ)) := by ring
  rw [hmass]
  unfold originKPAffineASlot
  rw [← hX, ← hc]
  exact add_le_add (hsource.trans (le_add_left le_rfl)) le_rfl

/-! ### The space-then-time Hölder step in the shape used below -/

/-- One slice-then-time Hölder estimate in the form used on a margin cell: a
collar of volume at most one, a time window of measure at most `D`, and a
space-time mass at most `E` give the `6/5` time moment of the slice masses of
the `a`-th power with the single data power `E^{6a/(5c)}`. -/
theorem harmonicRemainder_time_moment_le
    {B : Set Vec3} {W : Set ℝ} {G : Vec3 × ℝ → ℝ≥0∞} {a c m : ℝ} {D E : ℝ≥0∞}
    (hG : AEMeasurable G ((volume.restrict B).prod (volume.restrict W)))
    (ha : 0 < a) (hac : 6 * a < 5 * c) (hm : m = 6 * a / (5 * c))
    (hB : volume B ≤ 1) (hW : volume W ≤ D)
    (hD : (∫⁻ w in B ×ˢ W, G w ^ c) ≤ E) :
    (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ)) ≤ D ^ (1 - m) * E ^ m := by
  have hc0 : 0 < c := by linarith only [ha, hac]
  have hm0 : 0 ≤ m := by
    rw [hm]; positivity
  have hm1 : m ≤ 1 := by
    rw [hm, div_le_one (by positivity)]
    linarith only [hac]
  have hac' : a / c ≤ 1 := by
    rw [div_le_one hc0]
    linarith only [ha, hac]
  have hspace : volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) ≤ 1 := by
    refine ENNReal.rpow_le_one hB ?_
    have : 0 ≤ 1 - a / c := by linarith only [hac']
    positivity
  have htime : volume W ^ (1 - 6 * a / (5 * c)) ≤ D ^ (1 - m) := by
    rw [hm]
    exact ENNReal.rpow_le_rpow hW (by rw [← hm]; linarith only [hm1])
  have hmass : (∫⁻ w in B ×ˢ W, G w ^ c) ^ (6 * a / (5 * c)) ≤ E ^ m := by
    rw [hm]
    exact ENNReal.rpow_le_rpow hD (by rw [← hm]; exact hm0)
  refine (originASlot_slice_time_rpow_bound hG ha hac).trans ?_
  calc
    volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) * volume W ^ (1 - 6 * a / (5 * c)) *
        (∫⁻ w in B ×ˢ W, G w ^ c) ^ (6 * a / (5 * c)) ≤
        1 * D ^ (1 - m) * E ^ m := by
      exact mul_le_mul' (mul_le_mul' hspace htime) hmass
    _ = D ^ (1 - m) * E ^ m := by rw [one_mul]

/-! ### The radius powers -/

/-- The cell volume power times a window power is below the growth power, on
every cell of radius at most one. -/
theorem harmonicRemainder_radius_power_le {r θ e : ℝ} (hr : 0 < r)
    (hx1 : ENNReal.ofReal r ≤ 1) (hθ : θ ≤ 3 + 2 * e) :
    ENNReal.ofReal r ^ (3 : ℝ) * (ENNReal.ofReal r ^ (2 : ℝ)) ^ e ≤
      ENNReal.ofReal r ^ θ := by
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx1 hθ

end CKN.Core.Step4
