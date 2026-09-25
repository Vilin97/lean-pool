/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-!
# Pk Bounds Unconditional P56

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

lemma pressure_integral_mul_le_volume_rpow {μ : Measure Vec3}
    [IsFiniteMeasure μ] {f g : Vec3 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hXfin : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^
      (3 / 2 : ℝ)) ∂μ < ⊤) :
    ∫ y, f y * g y ∂μ ≤
      (μ Set.univ).toReal ^ (1 / 3 : ℝ) *
        (∫ y, (f y * g y) ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
  have hprod0 : ∀ y, 0 ≤ f y * g y := fun y => mul_nonneg (hf0 y) (hg0 y)
  have hmul : AEMeasurable (fun y => (f y * g y) ^ (3 / 2 : ℝ)) μ :=
    (hf.mul hg).pow_const (3 / 2)
  have hF : AEMeasurable
      (fun y => ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ))) μ :=
    hmul.ennreal_ofReal
  have hOne : AEMeasurable (fun _ : Vec3 => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have hHolder := ENNReal.lintegral_mul_norm_pow_le hF hOne
    (show (0 : ℝ) ≤ 2 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num)
  have hLHS : ∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 3 : ℝ) ∂μ =
      ∫⁻ y, ENNReal.ofReal (f y * g y) ∂μ := by
    apply lintegral_congr
    intro y
    rw [ENNReal.one_rpow, mul_one,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hprod0 y) (3 / 2))
        (show (0 : ℝ) ≤ 2 / 3 by norm_num),
      ← Real.rpow_mul (hprod0 y), show (3 : ℝ) / 2 * (2 / 3) = 1 by norm_num,
      Real.rpow_one]
  rw [hLHS, lintegral_one] at hHolder
  have hRfin : (∫⁻ y, ENNReal.ofReal ((f y * g y) ^ (3 / 2 : ℝ)) ∂μ) ^
        (2 / 3 : ℝ) * (μ Set.univ) ^ (1 / 3 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hXfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (IsFiniteMeasure.measure_univ_lt_top.ne))).ne
  have htoReal := ENNReal.toReal_mono hRfin hHolder
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at htoReal
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hprod0)
        (hf.mul hg).aestronglyMeasurable,
      ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall (fun y => Real.rpow_nonneg (hprod0 y) (3 / 2)))
        hmul.aestronglyMeasurable] at htoReal
  rw [mul_comm] at htoReal
  exact htoReal

private lemma pressureP56_bound_hGpow_1 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
            fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
          (2 / 3 : ℝ);
      @Integrable ℝ _ _ _ Prod.instMeasurableSpace (fun (w : Vec3 × ℝ) => |p w| ^ (3 / 2 : ℝ))
          (Measure.prod (Measure.restrict volume Bρ) (Measure.restrict volume Tρ)) →
        ∀ᵐ (s : ℝ) ∂Measure.restrict volume Tρ,
          ‖G s‖ₑ ^ (3 / 2 : ℝ) = ∫⁻ (x : Vec3) in Bρ, ENNReal.ofReal (F (x, s) ^ (3 / 2 : ℝ))
    := by
  intro p z ρ Bρ Tρ F G hpPowBT
  have hs := hpPowBT.prod_left_ae
  filter_upwards [hs] with s hs
  have hI : 0 ≤ ∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ) :=
    integral_nonneg_of_ae (Eventually.of_forall fun x => by
      dsimp [F]
      positivity)
  have hconv := ofReal_integral_eq_lintegral_ofReal hs
    (Eventually.of_forall fun x => by
      dsimp [F]
      positivity)
  rw [show G s = (∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ)) ^
      (2 / 3 : ℝ) by rfl]
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hI _),
    ← ENNReal.ofReal_rpow_of_nonneg hI (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num
  exact hconv

private lemma pressureP56_bound_hGnorm_2 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let Bρ : Set Vec3 := vec3Ball z.1 ρ;
        let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
        let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
        let G : ℝ → ℝ := fun (s : ℝ) =>
          HPow.hPow (α := ℝ)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
              fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
            (2 / 3 : ℝ);
        ∫⁻ (z : Vec3 × ℝ) in Bρ ×ˢ Tρ, ENNReal.ofReal (|p z| ^ (3 / 2 : ℝ)) =
            ∫⁻ (s : ℝ) in Tρ, ∫⁻ (x : Vec3) in Bρ, ENNReal.ofReal (|p (x, s)| ^ (3 / 2 : ℝ)) →
          ∫⁻ (w : Vec3 × ℝ) in Bρ ×ˢ Tρ, ENNReal.ofReal (F w ^ (3 / 2 : ℝ)) =
              ENNReal.ofReal (ρ ^ (2 : ℕ) * delta p z ρ ^ (3 : ℕ)) →
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume Tρ,
                ‖G s‖ₑ ^ (3 / 2 : ℝ) =
                  ∫⁻ (x : Vec3) in Bρ, ENNReal.ofReal (F (x, s) ^ (3 / 2 : ℝ))) →
              (0 : ℝ) ≤ delta p z ρ →
                @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G (3 / 2 : ℝ)
                    (Measure.restrict volume Tρ) ≤
                  ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) * ENNReal.ofReal (delta p z ρ ^ (2 : ℕ))
    := by
  intro p z ρ hρ Bρ Tρ F G hswap hlinBT hGpow hδ
  calc
    _ = (∫⁻ s in Tρ, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
      congr 1
      norm_num
    _ = (∫⁻ s in Tρ, ∫⁻ x in Bρ,
        ENNReal.ofReal ((F (x, s)) ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      congr 1
      apply lintegral_congr_ae
      exact hGpow
    _ = (∫⁻ w in Bρ ×ˢ Tρ,
        ENNReal.ofReal ((F w) ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      rw [← hswap]
    _ = ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) ^ (2 / 3 : ℝ) := by
      rw [hlinBT]
    _ ≤ ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) *
        ENNReal.ofReal ((delta p z ρ) ^ 2) := by
      apply le_of_eq
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (sq_nonneg _) (pow_nonneg hδ _)) (by norm_num)]
      apply congrArg ENNReal.ofReal
      rw [show (ρ ^ (2 : ℕ) : ℝ) = ρ ^ (2 : ℝ) by norm_num,
        show (delta p z ρ ^ (3 : ℕ) : ℝ) = delta p z ρ ^ (3 : ℝ) by
          norm_num]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul hρ.le, ← Real.rpow_mul hδ]
      norm_num

private lemma pressureP56_bound_hpoint_3 :
    ∀ {_ : ℝ} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ}
      (hρ : (0 : ℝ) < ρ),
      (0 : ℝ) < r →
        r ≤ ρ / (2 : ℝ) →
          let Bρ : Set Vec3 := vec3Ball z.1 ρ;
          let Br : Set Vec3 := vec3Ball z.1 r;
          let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
          let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
          let G : ℝ → ℝ := fun (s : ℝ) =>
            HPow.hPow (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
                fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
              (2 / 3 : ℝ);
          let D : ℝ :=
            (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
              ((18 : ℝ) * cutoffSecondDerivativeConstant + (240 : ℝ) * cutoffGradientConstant);
          let K : ℝ := D / ρ ^ (2 : ℝ);
          AEStronglyMeasurable (m₀ := Prod.instMeasurableSpace) p
              (Measure.prod (Measure.restrict volume Bρ) (Measure.restrict volume Tρ)) →
            @Integrable ℝ _ _ _ Prod.instMeasurableSpace (fun (w : Vec3 × ℝ) => |p w| ^ (3 / 2 : ℝ))
                (Measure.prod (Measure.restrict volume Bρ) (Measure.restrict volume Tρ)) →
              (0 : ℝ) ≤ cutoffGradientConstant →
                (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume Tρ,
                    ∀ x ∈ Br,
                      |pressureP5 (mollifiedBallCutoff z.1 hρ) p s x| +
                          |pressureP6 (mollifiedBallCutoff z.1 hρ) p s x| ≤
                        K * G s
    := by
  intro q p f z ρ r hρ hr hhalf Bρ Br Tρ F G D K hpBT hpPowBT hC₁ hC₂
  have hpslices := hpPowBT.prod_left_ae
  have hpmeasSlices := hpBT.prodMk_right
  filter_upwards [hpslices, hpmeasSlices] with s hs hpm
  have hp3 : Integrable (fun y : Vec3 =>
      ‖p (y, s)‖ ^ (3 / 2 : ℝ)) (volume.restrict Bρ) := by
    simpa only [Real.norm_eq_abs] using hs
  let _ : IsFiniteMeasure (volume.restrict Bρ) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := z.1) (r := ρ))
  have hpmabs : AEStronglyMeasurable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict Bρ) :=
    continuous_abs.comp_aestronglyMeasurable hpm
  have hp1 := integrable_norm_rpow_of_le hpmabs (p := (1 : ℝ))
    (q := (3 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [Real.norm_eq_abs, abs_abs] using hp3)
  have hp : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict Bρ) := by
    simpa only [Real.norm_eq_abs, abs_abs, Real.rpow_one] using hp1
  have hfixed := pressureP56_fixed_bound hρ hr hhalf hp hpm
    (hηeq := rfl) (mollifiedBallCutoff_smooth z.1 hρ)
    (mollifiedBallCutoff_hasCompactSupport z.1 hρ)
    (pressure_cutoff_support_subset_ball z.1 hρ)
  have hfin : ∫⁻ y in Bρ, ENNReal.ofReal
      (((1 : ℝ) * |p (y, s)|) ^ (3 / 2 : ℝ)) < ⊤ := by
    have hne := (lintegral_ofReal_ne_top_iff_integrable
      hp3.aestronglyMeasurable (Eventually.of_forall fun y =>
        Real.rpow_nonneg (norm_nonneg _) _)).2 hp3
    have hne' : ∫⁻ y in Bρ, ENNReal.ofReal
        (((1 : ℝ) * |p (y, s)|) ^ (3 / 2 : ℝ)) ≠ ⊤ := by
      simpa only [one_mul, Real.norm_eq_abs] using hne
    exact lt_top_iff_ne_top.mpr hne'
  have hsp := pressure_integral_mul_le_volume_rpow
    (μ := volume.restrict Bρ) (f := fun _ : Vec3 => (1 : ℝ))
    (g := fun y => |p (y, s)|) aemeasurable_const hpmabs.aemeasurable
    (fun _ => by norm_num) (fun _ => abs_nonneg _) hfin
  have hspace : ∫ y in Bρ, |p (y, s)| ≤
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ * G s := by
    have hv := pressure_volume_ball (x₀ := z.1) hρ
    have hvr : (volume Bρ).toReal ^ (1 / 3 : ℝ) =
        (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ := by
      rw [hv, ENNReal.toReal_ofReal (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [show (ρ ^ (3 : ℕ) : ℝ) = ρ ^ (3 : ℝ) by norm_num]
      have hrho : (ρ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = ρ := by
        rw [← Real.rpow_mul hρ.le]
        norm_num
      rw [hrho]
      congr 1
      ring_nf
    calc
      ∫ y in Bρ, |p (y, s)| ≤
          (volume Bρ).toReal ^ (1 / 3 : ℝ) *
            (∫ y in Bρ, ((1 : ℝ) * |p (y, s)|) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) := by simpa using hsp
      _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ * G s := by
        rw [hvr]
        simp [G, F, mul_assoc]
  have hsum : ∀ x ∈ Br,
      |pressureP5 (mollifiedBallCutoff z.1 hρ) p s x| +
        |pressureP6 (mollifiedBallCutoff z.1 hρ) p s x| ≤ K * G s := by
    intro x hx
    calc
      _ ≤ (18 * cutoffSecondDerivativeConstant +
          240 * cutoffGradientConstant) / ρ ^ 3 *
          (∫ y in Bρ, |p (y, s)|) := hfixed x hx
      _ ≤ (18 * cutoffSecondDerivativeConstant +
          240 * cutoffGradientConstant) / ρ ^ 3 *
          ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ * G s) := by
        exact mul_le_mul_of_nonneg_left hspace (by positivity)
      _ = K * G s := by
        dsimp [K, D]
        field_simp [ne_of_gt hρ]
        calc
          _ = (18 * cutoffSecondDerivativeConstant +
              240 * cutoffGradientConstant) * (G s * ρ ^ (2 : ℝ)) := by
            exact mul_assoc (18 * cutoffSecondDerivativeConstant +
              240 * cutoffGradientConstant) (G s) (ρ ^ (2 : ℝ))
          _ = (18 * cutoffSecondDerivativeConstant +
              240 * cutoffGradientConstant) * (ρ ^ (2 : ℝ) * G s) := by
            exact congrArg (fun y : ℝ =>
              (18 * cutoffSecondDerivativeConstant +
                240 * cutoffGradientConstant) * y)
              (mul_comm (G s) (ρ ^ (2 : ℝ)))
          _ = (18 * cutoffSecondDerivativeConstant +
              240 * cutoffGradientConstant) * (ρ ^ (2 : ℕ) * G s) := by
            rw [Real.rpow_two]
          _ = _ := by
            exact (mul_assoc (18 * cutoffSecondDerivativeConstant +
              240 * cutoffGradientConstant) (ρ ^ (2 : ℕ)) (G s)).symm
  exact hsum

private lemma pressureP56_bound_hP5_4 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
            fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
          (2 / 3 : ℝ);
      let D : ℝ :=
        (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
          ((18 : ℝ) * cutoffSecondDerivativeConstant + (240 : ℝ) * cutoffGradientConstant);
      let K : ℝ := D / ρ ^ (2 : ℝ);
      ∀ (J : Set ℝ),
        Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
          (0 : ℝ) ≤ K →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume Tr,
                ∀ x_1 ∈ Br,
                  |pressureP5 (mollifiedBallCutoff z.1 hρ) p x x_1| +
                      |pressureP6 (mollifiedBallCutoff z.1 hρ) p x x_1| ≤
                    K * G x) →
              ∀ᵐ (w : ParabolicPoint) ∂Measure.restrict volume (parabolicCylinder z.1 z.2 r),
                ‖pressureP5 (mollifiedBallCutoff z.1 hρ) p w.2 w.1‖ₑ ≤ ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro p z ρ r hρ Bρ Br Tr F G D K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP5 (mollifiedBallCutoff z.1 hρ) p s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs x hx
    have h6 : 0 ≤ |pressureP6 (mollifiedBallCutoff z.1 hρ) p s x| := abs_nonneg _
    linarith only [hs x hx, h6]
  have hlift := pressure_lift_time_ae (B := Br) (T := Tr) htime
  have hsubc : parabolicCylinder z.1 z.2 r ⊆ Br ×ˢ Tr := by
    intro w hw
    rw [parabolicCylinder] at hw
    exact hw
  have hc := ae_restrict_of_ae_restrict_of_subset hsubc hlift
  have hmem := ae_restrict_mem (μ := volume) (show MeasurableSet
      (parabolicCylinder z.1 z.2 r) from by
    change MeasurableSet (vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2)
    exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)
  filter_upwards [hc, hmem] with w hw hwm
  change w ∈ vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2 at hwm
  have habs := hw w.1 hwm.1
  have hGpos : 0 ≤ G w.2 := by dsimp [G]; positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

private lemma pressureP56_bound_hP6_5 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
            fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
          (2 / 3 : ℝ);
      let D : ℝ :=
        (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
          ((18 : ℝ) * cutoffSecondDerivativeConstant + (240 : ℝ) * cutoffGradientConstant);
      let K : ℝ := D / ρ ^ (2 : ℝ);
      ∀ (J : Set ℝ),
        Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
          (0 : ℝ) ≤ K →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume Tr,
                ∀ x_1 ∈ Br,
                  |pressureP5 (mollifiedBallCutoff z.1 hρ) p x x_1| +
                      |pressureP6 (mollifiedBallCutoff z.1 hρ) p x x_1| ≤
                    K * G x) →
              ∀ᵐ (w : ParabolicPoint) ∂Measure.restrict volume (parabolicCylinder z.1 z.2 r),
                ‖pressureP6 (mollifiedBallCutoff z.1 hρ) p w.2 w.1‖ₑ ≤ ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro p z ρ r hρ Bρ Br Tr F G D K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP6 (mollifiedBallCutoff z.1 hρ) p s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs x hx
    have h5 : 0 ≤ |pressureP5 (mollifiedBallCutoff z.1 hρ) p s x| := abs_nonneg _
    linarith only [hs x hx, h5]
  have hlift := pressure_lift_time_ae (B := Br) (T := Tr) htime
  have hsubc : parabolicCylinder z.1 z.2 r ⊆ Br ×ˢ Tr := by
    intro w hw
    rw [parabolicCylinder] at hw
    exact hw
  have hc := ae_restrict_of_ae_restrict_of_subset hsubc hlift
  have hmem := ae_restrict_mem (μ := volume) (show MeasurableSet
      (parabolicCylinder z.1 z.2 r) from by
    change MeasurableSet (vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2)
    exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)
  filter_upwards [hc, hmem] with w hw hwm
  change w ∈ vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2 at hwm
  have habs := hw w.1 hwm.1
  have hGpos : 0 ≤ G w.2 := by dsimp [G]; positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

private lemma pressureP56_bound_hscale_6 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ r : ℝ},
      (0 : ℝ) < ρ →
        (0 : ℝ) < r →
          let Bρ : Set Vec3 := vec3Ball z.1 ρ;
          let Br : Set Vec3 := vec3Ball z.1 r;
          let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
          let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => |p w|;
          let G : ℝ → ℝ := fun (s : ℝ) =>
            HPow.hPow (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
                fun (x : Vec3) => F (x, s) ^ (3 / 2 : ℝ))
              (2 / 3 : ℝ);
          let D : ℝ :=
            (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
              ((18 : ℝ) * cutoffSecondDerivativeConstant + (240 : ℝ) * cutoffGradientConstant);
          let K : ℝ := D / ρ ^ (2 : ℝ);
          ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                ((2 : ℝ≥0∞) *
                  (HMul.hMul (β := ℝ≥0∞) (ENNReal.ofReal K ^ (3 / 2 : ℝ))
                        ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) *
                      ∫⁻ (s : ℝ) in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
                    (2 / 3 : ℝ)) ≤
              ENNReal.ofReal
                ((2 : ℝ) * D * ((4 : ℝ) * Real.pi / (3 : ℝ)) ^ (2 / 3 : ℝ) * (r / ρ) ^ (2 / 3 : ℝ) *
                  delta p z ρ ^ (2 : ℕ)) →
            ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                ((2 : ℝ≥0∞) *
                  (HMul.hMul (β := ℝ≥0∞) (ENNReal.ofReal K ^ (3 / 2 : ℝ))
                        ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) *
                      ∫⁻ (s : ℝ) in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
                    (2 / 3 : ℝ)) ≤
              ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ))
    := by
  intro p z ρ r hρ hr Bρ Br Tr F G D K hscale0
  have hconst : 2 * D * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) =
      pressureP56Constant := by
    dsimp [D, pressureP56Constant]
  have hle : 2 * D * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
      (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 ≤
      pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2 := by
    rw [hconst]
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by positivity)
    · positivity
  exact hscale0.trans (ENNReal.ofReal_le_ofReal hle)

theorem pressureP56_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (eLpNorm' (fun w : ParabolicPoint =>
          pressureP5 (mollifiedBallCutoff z.1 hρ) p w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) +
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP6 (mollifiedBallCutoff z.1 hρ) p w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r))) ≤
      ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Br : Set Vec3 := vec3Ball z.1 r
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let F : Vec3 × ℝ → ℝ := fun w => |p w|
  let G : ℝ → ℝ := fun s =>
    (∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
  let D : ℝ := (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
    (18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant)
  let K : ℝ := D / ρ ^ (2 : ℝ)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hBmeas : MeasurableSet Bρ := by
    exact vec3Ball_measurable z.1 ρ
  have hTmeas : MeasurableSet Tρ := measurableSet_Ioc
  have hpglobal : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.1
  have hpprod : AEStronglyMeasurable p
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hpglobal
  have hpBT : AEStronglyMeasurable p
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) :=
    hpprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hpPowGlobal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hdata.2.2.2.2.2.2.1
  have hpPowBT : Integrable (fun w : Vec3 × ℝ =>
      |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) := by
    have h := hpPowGlobal.integrable_norm_rpow (by norm_num) (by norm_num)
    change Integrable (fun w : Vec3 × ℝ =>
      ‖p w‖ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal)
      ((volume.restrict Ω').prod (volume.restrict J)) at h
    have h' : Integrable (fun w : Vec3 × ℝ =>
        |p w| ^ (3 / 2 : ℝ))
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
        Real.norm_eq_abs] using h
    exact h'.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hFglobal : AEStronglyMeasurable
      (fun w : ParabolicPoint => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hpabs := continuous_abs.comp_aestronglyMeasurable hpglobal
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      hpabs
  have hFglobalT : AEStronglyMeasurable
      (fun w : ParabolicPoint => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' Tρ)) := by
    apply hFglobal.mono_measure
    apply Measure.restrict_mono_set volume
    intro w hw
    exact ⟨hw.1, htime hw.2⟩
  have hGae : AEMeasurable (fun s : ℝ =>
      ∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ))
      (volume.restrict Tρ) := by
    exact pressure_slice_integral_aemeasurable (J := Tρ)
      hBmeas hTmeas hball hFglobalT
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hc : Continuous (fun x : ℝ => x ^ (2 / 3 : ℝ)) :=
      Real.continuous_rpow_const (by norm_num)
    exact (hc.measurable.comp_aemeasurable hGae).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg
      (integral_nonneg_of_ae (Eventually.of_forall fun x => by
        dsimp [F]
        positivity)) _)
  have hdelta : ∫ w in parabolicCylinder z.1 z.2 ρ,
      |p w| ^ (3 / 2 : ℝ) = ρ ^ 2 * delta p z ρ ^ 3 :=
    sws_integral_abs_pow_eq_delta_cube hsol z hρ hsub
  have hFpCyl : Integrable (fun w : ParabolicPoint =>
      |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change Integrable (fun w : Vec3 × ℝ => |p w| ^ (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Bρ ×ˢ Tρ))
    rw [← Measure.prod_restrict]
    exact hpPowBT
  have hlinCyl : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFpCyl]
    · rw [hdelta]
    · exact Eventually.of_forall (fun w => Real.rpow_nonneg
        (abs_nonneg _) _)
  have hswap := pressure_prod_lintegral_swap (B := Bρ) (T := Tρ)
    (F := fun w => |p w| ^ (3 / 2 : ℝ)) hpPowBT.aemeasurable
  have hlinBT : (∫⁻ w in Bρ ×ˢ Tρ,
      ENNReal.ofReal ((F w) ^ (3 / 2 : ℝ))) =
      ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) := by
    change (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) = _
    exact hlinCyl
  have hGpow := @pressureP56_bound_hGpow_1 p z ρ hpPowBT
  have hδ : 0 ≤ delta p z ρ := by unfold delta; positivity
  have hGnorm := @pressureP56_bound_hGnorm_2 p z ρ hρ hswap hlinBT hGpow hδ
  have hholder := time_holder (t₀ := z.2) hr hhalf hGmeas hGnonneg
  have hX : (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) *
        ENNReal.ofReal ((delta p z ρ) ^ 2) := by
    calc
      _ = (∫⁻ s in Tr, ENNReal.ofReal (G s) ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro s
        rw [Real.enorm_eq_ofReal (by
          dsimp [G]
          positivity)]
      _ ≤ eLpNorm' G (3 / 2 : ℝ) (volume.restrict Tρ) := hholder.2
      _ ≤ _ := hGnorm
  have hC : 0 ≤ cutoffGradientConstant ∧ 0 ≤ cutoffSecondDerivativeConstant :=
    pressure_cutoff_constants_nonneg (x₀ := z.1) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hD : 0 ≤ D := by positivity
  have hK : 0 ≤ K := by unfold K; positivity
  have hpoint := @pressureP56_bound_hpoint_3 q p f z ρ r hρ hr hhalf hpBT hpPowBT hC₁ hC₂
  have hTr : Tr ⊆ Tρ := by
    intro s hs
    have hρ0 : 0 ≤ ρ := by
      have : 0 ≤ ρ / 2 := le_of_lt (lt_of_lt_of_le hr hhalf)
      linarith only [this]
    have hsq : r ^ 2 ≤ ρ ^ 2 := by
      apply (sq_le_sq₀ hr.le hρ0).2
      linarith only [hhalf, hρ0]
    exact ⟨by linarith only [hs.1, hsq], hs.2⟩
  have hpointTr := ae_restrict_of_ae_restrict_of_subset hTr hpoint
  have hP5 := @pressureP56_bound_hP5_4 p z ρ r hρ J htime hK hpointTr
  have hP6 := @pressureP56_bound_hP6_5 p z ρ r hρ J htime hK hpointTr
  have hGr : AEStronglyMeasurable G (volume.restrict Tr) :=
    hGmeas.mono_measure (Measure.restrict_mono_set volume hTr)
  have hscale0 := pressureP56_scale_cylinder (A := D) (K := K) (V := Br) (X :=
      ∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) hr hρ hD
      (by rfl) hX (pressure_volume_ball hr)
  have hscale : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
      (2 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume Br *
        (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2) := by
    exact @pressureP56_bound_hscale_6 p z ρ r hρ hr hscale0
  exact pressureP56_cylinder_bound (η := mollifiedBallCutoff z.1 hρ)
    (p := p) (x₀ := z.1) (t₀ := z.2) (r := r) (ρ := ρ) (K := K)
    (C₁₂ := pressureP12Constant) (δ := delta p z ρ) hρ hr hhalf hK hGr hP5 hP6
    (by simpa [Bρ, Br, Tr, mul_assoc] using hscale)

end CKN
