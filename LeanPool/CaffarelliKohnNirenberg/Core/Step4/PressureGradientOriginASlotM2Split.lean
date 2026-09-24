/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotSourceCorrectionSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCentredSourceCorrection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # The three-term Morrey majorant of the centred source correction

The centred correction splits pointwise into the divergence source on the
source ball, the cutoff-derivative quadratic terms on the collar, and the
mean-gradient terms on the collar.  Each is measured on its own carrier, the
last two by a Morrey Hölder product at the endpoint exponent, and the
endpoint is transferred to the exponent-dependent one for free on a carrier
of radius at most one.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The centred cutoff vanishes off the plateau-and-transition ball. -/
theorem originASlot_cutoff_zero_off_collar (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ x, x ∉ vec3Ball x₀ (3 * ρ / 4) → mollifiedBallCutoff x₀ hρ x = 0 := by
  intro x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => hx ?_)
  have hball := mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hmem
  rwa [euclideanBall_eq_vec3Ball (by positivity : (0 : ℝ) < 3 * ρ / 4)] at hball

/-- Every first spatial derivative of the centred cutoff vanishes off the
plateau-and-transition ball. -/
theorem originASlot_dcutoff_zero_off_collar (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ (k : Fin 3), ∀ x, x ∉ vec3Ball x₀ (3 * ρ / 4) →
      spatialDeriv (mollifiedBallCutoff x₀ hρ) k x = 0 := by
  intro k x hx
  refine image_eq_zero_of_notMem_tsupport (fun hmem => hx ?_)
  have hmem' := (tsupport_fderiv_apply_subset ℝ (basisVec k)) hmem
  have hball := mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hmem'
  rwa [euclideanBall_eq_vec3Ball (by positivity : (0 : ℝ) < 3 * ρ / 4)] at hball

/-- The carrier-restricted correction is dominated by the divergence source,
the mean-free quadratic terms and the mean-gradient terms, each on its own
carrier. -/
theorem originASlot_correction_carrier_abs_le
    {R₀ ρ Kη : ℝ} {x₀ : Vec3} {S S₃ : Set ParabolicPoint}
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) (hKη : 0 ≤ Kη)
    (hdη : ∀ k x, |dη k x| ≤ Kη)
    (hηsupp : ∀ x, x ∉ vec3Ball x₀ (3 * ρ / 4) → η x = 0)
    (hdηsupp : ∀ k x, x ∉ vec3Ball x₀ (3 * ρ / 4) → dη k x = 0)
    (hSball : ∀ w ∈ S, w.1 ∈ vec3Ball (0 : Vec3) R₀)
    (hS₃ : ∀ w ∈ S, w.1 ∈ vec3Ball x₀ (3 * ρ / 4) → w ∈ S₃)
    (u' f' : ParabolicPoint → Vec3) (Du' : ParabolicPoint → Fin 3 → Vec3)
    (c : ℝ → Vec3) (j : Fin 3) (w : ParabolicPoint) :
    |S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη
          (fun y => u' (y, v.2)) (fun y => f' (y, v.2)) (fun y => Du' (y, v.2)) (c v.2) j v.1)
        w| ≤
      |S.indicator (fun v : ParabolicPoint => (∑ k, Du' v j k * u' v k) - f' v j) w| +
      Kη * (∑ k, |S₃.indicator
        (fun v : ParabolicPoint => u' v j * (u' v k - c v.2 k)) w|) +
      (∑ k, |S₃.indicator (fun v : ParabolicPoint => Du' v j k * c v.2 k) w|) := by
  classical
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    unfold centredRawSourceCorrection
    rw [Set.indicator_of_mem (hSball w hw)]
    have habc : ∀ a b d : ℝ, |a + b - d| ≤ |a| + |b| + |d| := by
      intro a b d
      have h₁ : |a + b - d| ≤ |a + b| + |d| := abs_sub (a + b) d
      have h₂ : |a + b| ≤ |a| + |b| := abs_add_le a b
      linarith only [h₁, h₂]
    have h1 : |(η w.1 - 1) * ((∑ k, Du' w j k * u' w k) - f' w j)| ≤
        |(∑ k, Du' w j k * u' w k) - f' w j| := by
      rw [abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith only [hη0 w.1, hη1 w.1]
    have h2 : ∀ k : Fin 3, |dη k w.1 * u' w j * (u' w k - c w.2 k)| ≤
        Kη * |S₃.indicator (fun v : ParabolicPoint => u' v j * (u' v k - c v.2 k)) w| := by
      intro k
      by_cases hc : w.1 ∈ vec3Ball x₀ (3 * ρ / 4)
      · rw [Set.indicator_of_mem (hS₃ w hw hc), mul_assoc, abs_mul]
        exact mul_le_mul_of_nonneg_right (hdη k w.1) (abs_nonneg _)
      · rw [hdηsupp k w.1 hc, zero_mul, zero_mul, abs_zero]
        positivity
    have h3 : ∀ k : Fin 3, |η w.1 * (Du' w j k * c w.2 k)| ≤
        |S₃.indicator (fun v : ParabolicPoint => Du' v j k * c v.2 k) w| := by
      intro k
      by_cases hc : w.1 ∈ vec3Ball x₀ (3 * ρ / 4)
      · rw [Set.indicator_of_mem (hS₃ w hw hc), abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rw [abs_of_nonneg (hη0 w.1)]
        exact hη1 w.1
      · rw [hηsupp w.1 hc, zero_mul, abs_zero]
        exact abs_nonneg _
    have hsum2 : |∑ k, dη k w.1 * u' w j * (u' w k - c w.2 k)| ≤
        Kη * (∑ k, |S₃.indicator
          (fun v : ParabolicPoint => u' v j * (u' v k - c v.2 k)) w|) := by
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => h2 k)
    have hsum3 : |η w.1 * (∑ k, Du' w j k * c w.2 k)| ≤
        ∑ k, |S₃.indicator (fun v : ParabolicPoint => Du' v j k * c v.2 k) w| := by
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => h3 k)
    calc
      |(η w.1 - 1) * ((∑ k, Du' w j k * u' w k) - f' w j) +
          (∑ k, dη k w.1 * u' w j * (u' w k - c w.2 k)) -
          η w.1 * (∑ k, Du' w j k * c w.2 k)|
          ≤ |(η w.1 - 1) * ((∑ k, Du' w j k * u' w k) - f' w j)| +
            |∑ k, dη k w.1 * u' w j * (u' w k - c w.2 k)| +
            |η w.1 * (∑ k, Du' w j k * c w.2 k)| :=
        habc _ _ _
      _ ≤ _ := add_le_add (add_le_add h1 hsum2) hsum3
  · rw [Set.indicator_of_notMem hw]
    simp only [abs_zero]
    positivity

/-- The parabolic Morrey seminorm is unchanged by taking absolute values. -/
theorem morreyNorm_abs_eq {p τ : ℝ} (hp : 0 ≤ p) (F : ParabolicPoint → ℝ) :
    morreyNorm p τ (fun w => |F w|) = morreyNorm p τ F := by
  refine le_antisymm ?_ ?_ <;>
    refine routeA_morreyNorm_mono_ae hp (Filter.Eventually.of_forall fun w => ?_)
  · rw [abs_abs]
  · rw [abs_abs]

/-- A three-term sum of absolute values has the sum of the seminorms. -/
theorem morreyNorm_sum_three_abs_le {p τ : ℝ} (hp : 1 ≤ p) {g : Fin 3 → ParabolicPoint → ℝ}
    (hg : ∀ k, AEMeasurable (g k) volume) :
    morreyNorm p τ (fun w => ∑ k, |g k w|) ≤ ∑ k, morreyNorm p τ (g k) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have habs : ∀ k, AEMeasurable (fun w => |g k w|) volume := by
    intro k
    simpa only [Real.norm_eq_abs] using (hg k).norm
  have h12 := (morrey_norm_add_le (τ := τ) hp (habs 1) (habs 2)).trans
    (add_le_add (le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 (g 1))) (le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 (g 2))))
  have h012 := (morrey_norm_add_le (τ := τ) hp (habs 0) ((habs 1).add (habs 2))).trans
    (add_le_add (le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 (g 0))) h12)
  have hfun : (fun w : ParabolicPoint => ∑ k, |g k w|) =
      fun z => |g 0 z| + ((fun w => |g 1 w|) + fun w => |g 2 w|) z := by
    funext w
    simp only [Fin.sum_univ_three, Pi.add_apply, add_assoc]
  rw [hfun, Fin.sum_univ_three, add_assoc]
  exact h012

/-- A field dominated pointwise by three terms has the sum of their seminorms. -/
theorem morreyNorm_le_three_terms {p τ : ℝ} (hp : 1 ≤ p) {F A B C : ParabolicPoint → ℝ}
    (hA : AEMeasurable A volume) (hB : AEMeasurable B volume) (hC : AEMeasurable C volume)
    (hdom : ∀ w, |F w| ≤ |A w| + |B w| + |C w|) :
    morreyNorm p τ F ≤ morreyNorm p τ A + morreyNorm p τ B + morreyNorm p τ C := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hstep : morreyNorm p τ F ≤ morreyNorm p τ (fun w => |A w| + |B w| + |C w|) := by
    refine routeA_morreyNorm_mono_ae hp0 (Filter.Eventually.of_forall fun w => ?_)
    refine (hdom w).trans (le_of_eq ?_)
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |A w| + |B w| + |C w|)]
  refine hstep.trans ?_
  have hAa : AEMeasurable (fun w => |A w|) volume := by
    simpa only [Real.norm_eq_abs] using hA.norm
  have hBa : AEMeasurable (fun w => |B w|) volume := by
    simpa only [Real.norm_eq_abs] using hB.norm
  have hCa : AEMeasurable (fun w => |C w|) volume := by
    simpa only [Real.norm_eq_abs] using hC.norm
  have h12 := morrey_norm_add_le (τ := τ) hp hAa hBa
  have h012 := morrey_norm_add_le (τ := τ) hp (hAa.add hBa) hCa
  refine h012.trans ?_
  refine add_le_add (h12.trans (add_le_add ?_ ?_)) ?_
  · exact le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 A)
  · exact le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 B)
  · exact le_of_eq (morreyNorm_abs_eq (τ := τ) hp0 C)

/-- The endpoint Morrey exponent splits as the velocity and gradient pair. -/
theorem originASlot_endpoint_exponent_inv {τ : ℝ} (hτ : 25/3 ≤ τ) :
    1 / ((1/τ + 8/25 : ℝ)⁻¹) = 1 / τ + 1 / (25/8 : ℝ) := by
  have hτpos : (0 : ℝ) < τ := by linarith only [hτ]
  rw [one_div, inv_inv]
  norm_num

/-- The product of an `L³` Morrey factor and an `L²` Morrey factor on nested
carriers is an `L^{6/5}` Morrey object at the matched exponent. -/
theorem originASlot_product_morreyNorm_le
    {τ : ℝ} (hτ : 25/3 ≤ τ) {S T : Set ParabolicPoint}
    {a b : ParabolicPoint → ℝ} {KA KB : ℝ≥0∞}
    (hsub : S ⊆ T)
    (ham : AEMeasurable (S.indicator a) volume)
    (hbm : AEMeasurable (T.indicator b) volume)
    (ha : morreyNorm 3 τ (S.indicator a) ≤ KA)
    (hb : morreyNorm 2 (25/8 : ℝ) (T.indicator b) ≤ KB) :
    morreyNorm (6/5 : ℝ) ((1/τ + 8/25 : ℝ)⁻¹)
      (S.indicator (fun w => a w * b w)) ≤ KA * KB := by
  classical
  have hfun : S.indicator (fun w => a w * b w) =
      fun w => S.indicator a w * T.indicator b w := by
    funext w
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw,
        Set.indicator_of_mem (hsub hw)]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
  rw [hfun]
  refine (morreyNorm_mul_le (p := (6/5 : ℝ)) (p₁ := (3 : ℝ)) (p₂ := (2 : ℝ))
    (q := ((1/τ + 8/25 : ℝ)⁻¹)) (q₁ := τ) (q₂ := (25/8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (originASlot_endpoint_exponent_inv hτ) ham hbm).trans ?_
  exact mul_le_mul' ha hb

/-- On a carrier of radius at most one the exponent-dependent Morrey
seminorm is below the endpoint one. -/
theorem originASlot_morreyNorm_endpoint_drop {τ q R : ℝ} (hτ : 25/3 ≤ τ) (hq : 5/2 < q)
    (hR : 0 < R) (hR1 : R ≤ 1)
    {F : ParabolicPoint → ℝ} {z₀ : ParabolicPoint}
    (hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, F w = 0) :
    morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q) F ≤
      morreyNorm (6/5 : ℝ) ((1/τ + 8/25 : ℝ)⁻¹) F := by
  have hτpos : (0 : ℝ) < τ := by linarith only [hτ]
  have hk0pos : (0 : ℝ) < (1/τ + 8/25 : ℝ)⁻¹ := by positivity
  have hmin : min ((1/τ + 8/25 : ℝ)⁻¹) q ≤ (1/τ + 8/25 : ℝ)⁻¹ := min_le_left _ _
  have hminge : (25 : ℝ)/11 ≤ min ((1/τ + 8/25 : ℝ)⁻¹) q := endgame_kappa_ge hτ hq
  have hminpos : (0 : ℝ) < min ((1/τ + 8/25 : ℝ)⁻¹) q := by linarith only [hminge]
  have hbound := morreyNorm_lower_morrey_exponent (p := (6/5 : ℝ))
    (q := (1/τ + 8/25 : ℝ)⁻¹) (q' := min ((1/τ + 8/25 : ℝ)⁻¹) q)
    (by norm_num : (1 : ℝ) ≤ 6/5) (by linarith only [hminge, hmin])
    (by linarith only [hminge]) hmin hR hsupp
  refine hbound.trans ?_
  refine mul_le_of_le_one_left' ?_
  refine ENNReal.rpow_le_one ?_ ?_
  · rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hR1
  · have hinvle : 1 / ((1/τ + 8/25 : ℝ)⁻¹) ≤ 1 / min ((1/τ + 8/25 : ℝ)⁻¹) q :=
      one_div_le_one_div_of_le hminpos hmin
    linarith only [hinvle]

/-- The carrier-restricted centred correction has a Morrey majorant built from
the divergence source, the mean-free quadratic budget and the mean-gradient
budget. -/
theorem originASlot_correction_morreyNorm_le
    {τ q R₀ ρ R Kη : ℝ} {x₀ : Vec3} {z₀ : ParabolicPoint}
    {S S₃ Sρ : Set ParabolicPoint}
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u' f' : ParabolicPoint → Vec3} {Du' : ParabolicPoint → Fin 3 → Vec3} {c : ℝ → Vec3}
    {XA KU KD Mfree Mc : ℝ≥0∞}
    (hτ : 25/3 ≤ τ) (hq : 5/2 < q) (hKη : 0 ≤ Kη)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hdη : ∀ k x, |dη k x| ≤ Kη)
    (hηsupp : ∀ x, x ∉ vec3Ball x₀ (3 * ρ / 4) → η x = 0)
    (hdηsupp : ∀ k x, x ∉ vec3Ball x₀ (3 * ρ / 4) → dη k x = 0)
    (hSball : ∀ w ∈ S, w.1 ∈ vec3Ball (0 : Vec3) R₀)
    (hS₃ : ∀ w ∈ S, w.1 ∈ vec3Ball x₀ (3 * ρ / 4) → w ∈ S₃)
    (hsub : S₃ ⊆ Sρ) (hcyl : S₃ ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (j : Fin 3)
    (hAm : AEMeasurable
      (S.indicator (fun v : ParabolicPoint => (∑ k, Du' v j k * u' v k) - f' v j)) volume)
    (hum : AEMeasurable (S₃.indicator (fun v : ParabolicPoint => u' v j)) volume)
    (hwm : ∀ k, AEMeasurable
      (Sρ.indicator (fun v : ParabolicPoint => u' v k - c v.2 k)) volume)
    (hcm : ∀ k, AEMeasurable (S₃.indicator (fun v : ParabolicPoint => c v.2 k)) volume)
    (hdm : ∀ k, AEMeasurable (Sρ.indicator (fun v : ParabolicPoint => Du' v j k)) volume)
    (hA : morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint => (∑ k, Du' v j k * u' v k) - f' v j)) ≤ XA)
    (hu : morreyNorm 3 τ (S₃.indicator (fun v : ParabolicPoint => u' v j)) ≤ KU)
    (hw : ∀ k, morreyNorm 2 (25/8 : ℝ)
      (Sρ.indicator (fun v : ParabolicPoint => u' v k - c v.2 k)) ≤ Mfree)
    (hc : ∀ k, morreyNorm 3 τ (S₃.indicator (fun v : ParabolicPoint => c v.2 k)) ≤ Mc)
    (hd : ∀ k, morreyNorm 2 (25/8 : ℝ)
      (Sρ.indicator (fun v : ParabolicPoint => Du' v j k)) ≤ KD) :
    morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη
          (fun y => u' (y, v.2)) (fun y => f' (y, v.2)) (fun y => Du' (y, v.2)) (c v.2) j v.1))
      ≤ XA + ENNReal.ofReal Kη * (3 * (KU * Mfree)) + 3 * (KD * Mc) := by
  classical
  set κ : ℝ := min ((1/τ + 8/25 : ℝ)⁻¹) q with hκdef
  set Bt : Fin 3 → ParabolicPoint → ℝ := fun k =>
    S₃.indicator (fun v : ParabolicPoint => u' v j * (u' v k - c v.2 k)) with hBt
  set Ct : Fin 3 → ParabolicPoint → ℝ := fun k =>
    S₃.indicator (fun v : ParabolicPoint => Du' v j k * c v.2 k) with hCt
  have hBtk : ∀ k, Bt k =
      S₃.indicator (fun v : ParabolicPoint => u' v j * (u' v k - c v.2 k)) := fun _ => rfl
  have hCtk : ∀ k, Ct k =
      S₃.indicator (fun v : ParabolicPoint => Du' v j k * c v.2 k) := fun _ => rfl
  have hBtm : ∀ k, AEMeasurable (Bt k) volume := by
    intro k
    have hprod : Bt k = fun w => S₃.indicator (fun v : ParabolicPoint => u' v j) w *
        Sρ.indicator (fun v : ParabolicPoint => u' v k - c v.2 k) w := by
      funext w
      by_cases hw : w ∈ S₃
      · rw [hBtk k, Set.indicator_of_mem hw, Set.indicator_of_mem hw,
          Set.indicator_of_mem (hsub hw)]
      · rw [hBtk k, Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
    rw [hprod]
    exact hum.mul (hwm k)
  have hCtm : ∀ k, AEMeasurable (Ct k) volume := by
    intro k
    have hprod : Ct k = fun w => S₃.indicator (fun v : ParabolicPoint => c v.2 k) w *
        Sρ.indicator (fun v : ParabolicPoint => Du' v j k) w := by
      funext w
      by_cases hw : w ∈ S₃
      · rw [hCtk k, Set.indicator_of_mem hw, Set.indicator_of_mem hw,
          Set.indicator_of_mem (hsub hw), mul_comm]
      · rw [hCtk k, Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, zero_mul]
    rw [hprod]
    exact (hcm k).mul (hdm k)
  have hBsupp : ∀ k, ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, Bt k w = 0 := by
    intro k w hw
    exact Set.indicator_of_notMem (fun hc' => hw (hcyl hc')) _
  have hCsupp : ∀ k, ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, Ct k w = 0 := by
    intro k w hw
    exact Set.indicator_of_notMem (fun hc' => hw (hcyl hc')) _
  have hBbound : ∀ k, morreyNorm (6/5 : ℝ) κ (Bt k) ≤ KU * Mfree := by
    intro k
    refine (originASlot_morreyNorm_endpoint_drop hτ hq hR hR1 (hBsupp k)).trans ?_
    rw [hBtk k]
    exact originASlot_product_morreyNorm_le hτ hsub hum (hwm k) hu (hw k)
  have hCbound : ∀ k, morreyNorm (6/5 : ℝ) κ (Ct k) ≤ Mc * KD := by
    intro k
    refine (originASlot_morreyNorm_endpoint_drop hτ hq hR hR1 (hCsupp k)).trans ?_
    have hprod : Ct k = S₃.indicator (fun v : ParabolicPoint => c v.2 k * Du' v j k) := by
      funext w
      rw [hCtk k]
      by_cases hw : w ∈ S₃
      · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, mul_comm]
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
    rw [hprod]
    exact originASlot_product_morreyNorm_le hτ hsub (hcm k) (hdm k) (hc k) (hd k)
  have hsumB : morreyNorm (6/5 : ℝ) κ (fun w => ∑ k, |Bt k w|) ≤ 3 * (KU * Mfree) := by
    refine (morreyNorm_sum_three_abs_le (by norm_num : (1 : ℝ) ≤ 6/5) hBtm).trans ?_
    calc
      (∑ k, morreyNorm (6/5 : ℝ) κ (Bt k)) ≤ ∑ _k : Fin 3, KU * Mfree :=
        Finset.sum_le_sum fun k _ => hBbound k
      _ = 3 * (KU * Mfree) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
  have hsumC : morreyNorm (6/5 : ℝ) κ (fun w => ∑ k, |Ct k w|) ≤ 3 * (KD * Mc) := by
    refine (morreyNorm_sum_three_abs_le (by norm_num : (1 : ℝ) ≤ 6/5) hCtm).trans ?_
    calc
      (∑ k, morreyNorm (6/5 : ℝ) κ (Ct k)) ≤ ∑ _k : Fin 3, KD * Mc :=
        Finset.sum_le_sum fun k _ => (hCbound k).trans (le_of_eq (mul_comm _ _))
      _ = 3 * (KD * Mc) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
  have hBm : AEMeasurable (fun w => Kη * ∑ k, |Bt k w|) volume := by
    refine AEMeasurable.const_mul ?_ _
    refine Finset.aemeasurable_fun_sum _ fun k _ => ?_
    simpa only [Real.norm_eq_abs] using (hBtm k).norm
  have hCm : AEMeasurable (fun w => ∑ k, |Ct k w|) volume := by
    refine Finset.aemeasurable_fun_sum _ fun k _ => ?_
    simpa only [Real.norm_eq_abs] using (hCtm k).norm
  have hdomall : ∀ w : ParabolicPoint,
      |S.indicator (fun v : ParabolicPoint =>
          centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη
            (fun y => u' (y, v.2)) (fun y => f' (y, v.2)) (fun y => Du' (y, v.2))
            (c v.2) j v.1) w| ≤
        |S.indicator (fun v : ParabolicPoint => (∑ k, Du' v j k * u' v k) - f' v j) w| +
          |Kη * (∑ k, |Bt k w|)| + |(∑ k, |Ct k w|)| := by
    intro w
    have h := originASlot_correction_carrier_abs_le (S₃ := S₃) hη0 hη1 hKη hdη hηsupp hdηsupp
      hSball hS₃ u' f' Du' c j w
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Kη * (∑ k, |Bt k w|)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (∑ k, |Ct k w|))]
    simpa only [hBtk, hCtk] using h
  refine (morreyNorm_le_three_terms (by norm_num : (1 : ℝ) ≤ 6/5) hAm hBm hCm hdomall).trans ?_
  refine add_le_add (add_le_add hA ?_) hsumC
  refine (morreyNorm_const_mul_le (by norm_num : (0 : ℝ) < 6/5) Kη _).trans ?_
  rw [abs_of_nonneg hKη]
  exact mul_le_mul' le_rfl hsumB

end CKN.Core.Step4
