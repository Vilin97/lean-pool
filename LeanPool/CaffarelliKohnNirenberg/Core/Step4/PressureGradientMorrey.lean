/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.Decay
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyForm

/-!
# Pressure Gradient Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

section

/-!
# Pressure Gradient Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The rate-three exponent bookkeeping for the pressure-gradient decay. -/

/-- Morrey exponent of the pressure-gradient source produced from exponent `κ`. -/
def pressureGradientSourceExponent (κ : ℝ) : ℝ := 5 - 6 / κ

theorem pressureGradientSourceExponent_eq
    {κ : ℝ} :
    pressureGradientSourceExponent κ = 5 - 6 / κ := by
  rfl

theorem pressureGradientSourceExponent_nonneg
    {κ : ℝ} (hκ : 6 / 5 ≤ κ) :
    0 ≤ pressureGradientSourceExponent κ := by
  unfold pressureGradientSourceExponent
  have hκ0 : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hineq : 6 ≤ 5 * κ := by
    linarith only [hκ]
  have hdiv : 6 / κ ≤ 5 := (div_le_iff₀ hκ0).2 hineq
  linarith only [hdiv]

theorem pressureGradientSourceExponent_lt_three
    {κ : ℝ} (hκ : 0 < κ) (hκ3 : κ < 3) :
    pressureGradientSourceExponent κ < 3 := by
  unfold pressureGradientSourceExponent
  have hdiv : 2 < 6 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith only [hκ3]
  linarith only [hdiv]

theorem pressureGradientSourceExponent_routeA :
    pressureGradientSourceExponent (25 / 11 : ℝ) = 59 / 25 := by
  unfold pressureGradientSourceExponent
  norm_num

theorem pressureGradientSourceExponent_endgame :
    pressureGradientSourceExponent (25 / 9 : ℝ) = 71 / 25 := by
  unfold pressureGradientSourceExponent
  norm_num

theorem pressureGradientRateThree_admissible :
    0 ≤ pressureGradientSourceExponent (25 / 11 : ℝ) ∧
      pressureGradientSourceExponent (25 / 11 : ℝ) < 3 ∧
      0 ≤ pressureGradientSourceExponent (25 / 9 : ℝ) ∧
      pressureGradientSourceExponent (25 / 9 : ℝ) < 3 := by
  rw [pressureGradientSourceExponent_routeA,
    pressureGradientSourceExponent_endgame]
  norm_num

/-! The scalar estimate used after the spatial harmonic estimate has been
    integrated in time.  The source term is intentionally left abstract here;
    the solution-level theorem supplies it from the one-scale estimate. -/

theorem pressure_gradient_two_scale_decay_from_components
    {Φ V : ℝ → ℝ} {C₃ ρ r : ℝ}
    (hC₃ : 0 ≤ C₃) (hρ : 0 < ρ) (hr : 0 < r) (hrr : r ≤ ρ / 8)
    (hΦ : 0 ≤ Φ ρ)
    (hdecomp : Φ r ≤ V r + Φ (r / 2))
    (hpart : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ)
    (hharm : Φ (r / 2) ≤ C₃ * (r / ρ) ^ (3 : ℕ) *
      (Φ ρ + V ρ)) :
    Φ r ≤ 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
  exact pressure_gradient_two_scale_decay hC₃ hρ hr hrr hΦ hdecomp hpart hharm

/-! A geometric-scale form of the standard decay iteration.  This is the
    exact discrete form used by the Morrey wrapper. -/

theorem pressure_gradient_geometric_decay
    {θ σ A B : ℝ} {a : ℕ → ℝ}
    (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hθσ : θ < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a 0) (haA : a 0 ≤ A)
    (hrec : ∀ n, a (n + 1) ≤ θ * a n + B * σ ^ n) :
    ∀ n, a n ≤ (A + B / (σ - θ)) * σ ^ n := by
  exact geometric_decay_iteration hθ hσ hθσ hA hB ha haA hrec

end CKN.Core.Step4
end

end

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The exponent forced by the convection source and the force. -/








theorem routeA_morreyNorm_add_le
    {f g : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm 3 25 (fun z => f z + g z) ≤
      morreyNorm 3 25 f + morreyNorm 3 25 g := by
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  let μ : Measure ParabolicPoint :=
    volume.restrict (parabolicCylinder z.1 z.2 r.1)
  have hsum := MeasureTheory.eLpNorm_add_le (μ := μ)
    (f := f) (g := g) (p := ENNReal.ofReal (3 : ℝ)) (by norm_num)
  have hfμ : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.restrict
  have hgμ : AEStronglyMeasurable g μ := hg.aestronglyMeasurable.restrict
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (hfμ.add hgμ),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfμ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hgμ] at hsum
  have hsum' :
      (cylinderPowerIntegral 3 (fun z => f z + g z) z r.1) ^
          (1 / (3 : ℝ)) ≤
        (cylinderPowerIntegral 3 f z r.1) ^ (1 / (3 : ℝ)) +
          (cylinderPowerIntegral 3 g z r.1) ^ (1 / (3 : ℝ)) := by
    simp only [Pi.add_apply, ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat,
      one_div,
    cylinderPowerIntegral, μ] at hsum ⊢
    simp_rw [Real.enorm_eq_ofReal_abs] at hsum
    exact hsum
  have hcell : morreyCell 3 25 (fun z => f z + g z) z r.1 ≤
      morreyCell 3 25 f z r.1 + morreyCell 3 25 g z r.1 := by
    unfold morreyCell
    change (ENNReal.ofReal r.1) ^
        (-((5 : ℝ) * (1 - (3 : ℝ) / 25) / 3)) *
        (cylinderPowerIntegral 3 (fun z => f z + g z) z r.1) ^
          (1 / (3 : ℝ)) ≤ _
    calc
      _ ≤ (ENNReal.ofReal r.1) ^
          (-((5 : ℝ) * (1 - (3 : ℝ) / 25) / 3)) *
          ((cylinderPowerIntegral 3 f z r.1) ^ (1 / (3 : ℝ)) +
            (cylinderPowerIntegral 3 g z r.1) ^ (1 / (3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
      _ = morreyCell 3 25 f z r.1 + morreyCell 3 25 g z r.1 := by
        simp only [morreyCell]
        norm_num
        rw [mul_add]
  exact hcell.trans (add_le_add
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} =>
      morreyCell 3 25 f z s.1) r))
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} =>
      morreyCell 3 25 g z s.1) r)))

theorem routeA_morreyNorm_const_mul_finite
    {c : ℝ} (hc : 0 < c) {f : ParabolicPoint → ℝ}
    (hN : morreyNorm 3 25 f < ∞) :
    morreyNorm 3 25 (fun z => c * f z) < ∞ := by
  have hc0 : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hcell : ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell 3 25 (fun z => c * f z) z r.1 ≤
        ENNReal.ofReal c * morreyNorm 3 25 f := by
    intro z r
    unfold morreyCell
    have hI : cylinderPowerIntegral 3 (fun z => c * f z) z r.1 =
        (ENNReal.ofReal c) ^ (3 : ℝ) * cylinderPowerIntegral 3 f z r.1 := by
      unfold cylinderPowerIntegral
      calc
        _ = ∫⁻ w in parabolicCylinder z.1 z.2 r.1,
            (ENNReal.ofReal c) ^ (3 : ℝ) *
              (ENNReal.ofReal |f w|) ^ (3 : ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [] with w
          rw [abs_mul, abs_of_pos hc, ENNReal.ofReal_mul hc.le,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        _ = (ENNReal.ofReal c) ^ (3 : ℝ) *
            ∫⁻ w in parabolicCylinder z.1 z.2 r.1,
              (ENNReal.ofReal |f w|) ^ (3 : ℝ) := by
          exact lintegral_const_mul' (ENNReal.ofReal c ^ (3 : ℝ)) _
            (by finiteness)
    rw [hI]
    have hroot :
        ((ENNReal.ofReal c) ^ (3 : ℝ) * cylinderPowerIntegral 3 f z r.1) ^
            (1 / (3 : ℝ)) =
          ENNReal.ofReal c * (cylinderPowerIntegral 3 f z r.1) ^
            (1 / (3 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul]
      rw [show (3 : ℝ) * (1 / 3) = 1 by norm_num, ENNReal.rpow_one]
    rw [hroot]
    have hfcell : morreyCell 3 25 f z r.1 ≤ morreyNorm 3 25 f := by
      unfold morreyNorm
      exact le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} =>
        morreyCell 3 25 f z s.1) r)
    calc
      _ = ENNReal.ofReal c * morreyCell 3 25 f z r.1 := by
        ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hfcell hc0.le
  have hle : morreyNorm 3 25 (fun z => c * f z) ≤
      ENNReal.ofReal c * morreyNorm 3 25 f := by
    unfold morreyNorm
    refine iSup_le fun z => iSup_le fun r => ?_
    exact hcell z r
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)

theorem routeA_morreyNorm_mono_ae
    {p q : ℝ} (hp : 0 ≤ p) {f g : ParabolicPoint → ℝ}
    (hfg : ∀ᵐ z ∂(volume : Measure ParabolicPoint), |f z| ≤ |g z|) :
    morreyNorm p q f ≤ morreyNorm p q g := by
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  have hcell : morreyCell p q f z r.1 ≤ morreyCell p q g z r.1 := by
    unfold morreyCell
    apply mul_le_mul_right
    apply ENNReal.rpow_le_rpow (by
      unfold cylinderPowerIntegral
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hfg] with w hw
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hw) hp) (by positivity)
  exact hcell.trans (le_iSup_of_le z
    (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q g z s.1) r))


end CKN.Core.Step4
