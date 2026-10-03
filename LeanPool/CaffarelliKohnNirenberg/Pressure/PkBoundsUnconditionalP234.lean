/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-!
# Pk Bounds Unconditional P234

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

private lemma pressureP234_bound_hGbound_1 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {ρ : ℝ},
      (0 : ℝ) < ρ →
        let Bρ : Set Vec3 := vec3Ball z.1 ρ;
        let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
        let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => spatialGradientSq u Du w;
        let G : ℝ → ℝ := fun (s : ℝ) =>
          HPow.hPow (α := ℝ)
            |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
                fun (x : Vec3) => F (x, s)|
            (1 / 2 : ℝ);
        let _ : ℝ :=
          (9 : ℝ) * sobolevPoincareL6Constant.toReal *
              ((18 : ℝ) * cutoffSecondDerivativeConstant + (720 : ℝ) * cutoffGradientConstant) *
            (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
        @Integrable _ _ _ _ Prod.instMeasurableSpace F
            (Measure.prod (Measure.restrict volume Bρ) (Measure.restrict volume Tρ)) →
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) G
              (Measure.restrict volume Tρ) →
            ∫⁻ (w : Vec3 × ℝ) in Bρ ×ˢ Tρ, ENNReal.ofReal (F w) ≤
                ENNReal.ofReal (ρ * beta u Du z ρ ^ (2 : ℕ)) →
              @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G (2 : ℝ)
                  (Measure.restrict volume Tρ) ≤
                ENNReal.ofReal (√ρ * beta u Du z ρ)
    := by
  intro u Du z ρ hρ Bρ Tρ F G D hgradInt hGmeas hbeta
  have h := pressure_time_norm_bound (B := Bρ) (T := Tρ) (F := F)
    (G := G) (D := ENNReal.ofReal (ρ * beta u Du z ρ ^ 2))
    (p₀ := 2) (by norm_num) hgradInt hGmeas
    (by
      intro s
      dsimp [G]
      rw [abs_of_nonneg]
      exact integral_nonneg_of_ae (Eventually.of_forall fun x => by
        dsimp [F]
        unfold spatialGradientSq
        positivity))
    (by
      intro w
      dsimp [F]
      unfold spatialGradientSq
      positivity) hbeta
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hroot : (ENNReal.ofReal (ρ * beta u Du z ρ ^ 2)) ^
      (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hρ.le (sq_nonneg _))
      (by norm_num)]
    have hreal : (ρ * beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ) =
        Real.sqrt ρ * beta u Du z ρ := by
      rw [show beta u Du z ρ ^ 2 = beta u Du z ρ ^ (2 : ℝ) by
        norm_num [Real.rpow_natCast]]
      rw [Real.mul_rpow hρ.le (Real.rpow_nonneg hβ 2),
        Real.sqrt_eq_rpow, ← Real.rpow_mul hβ]
      norm_num
    rw [hreal]
  rw [← hroot]
  exact h

private lemma pressureP234_bound_hpoint_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
          (0 : ℝ) < r →
            r ≤ ρ / (2 : ℝ) →
              let Bρ : Set Vec3 := vec3Ball z.1 ρ;
              let Br : Set Vec3 := vec3Ball z.1 r;
              let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
              let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => spatialGradientSq u Du w;
              let G : ℝ → ℝ := fun (s : ℝ) =>
                HPow.hPow (α := ℝ)
                  |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
                      fun (x : Vec3) => F (x, s)|
                  (1 / 2 : ℝ);
              let D : ℝ :=
                (9 : ℝ) * sobolevPoincareL6Constant.toReal *
                    ((18 : ℝ) * cutoffSecondDerivativeConstant +
                      (720 : ℝ) * cutoffGradientConstant) *
                  (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
              let K : ℝ := D * alpha u z ρ / ρ ^ (3 / 2 : ℝ);
              ∀ (Ω' : Set Vec3) (J : Set ℝ),
                localBox Ω I Ω' J →
                  vec3Ball z.1 ρ ⊆ Ω' →
                    Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
                      (∀ᵐ (t : ℝ) ∂Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2),
                          HPow.hPow (α := ℝ)
                                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                  (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                  utensorNorm u z.1 ρ t y ^ (3 / 2 : ℝ))
                                (2 / 3 : ℝ) ≤
                              (9 : ℝ) * sobolevPoincareL6Constant.toReal *
                                  HPow.hPow (α := ℝ)
                                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                      (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                      vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ))
                                    (1 / 2 : ℝ) *
                                HPow.hPow (α := ℝ)
                                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                    (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                    spatialGradientSq u Du (y, t))
                                  (1 / 2 : ℝ) ∧
                            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                utensorNorm u z.1 ρ t y) ≤
                              (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
                                      ((9 : ℝ) * sobolevPoincareL6Constant.toReal) *
                                    ρ *
                                  HPow.hPow (α := ℝ)
                                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                      (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                      vec3EuclideanNorm (u (y, t)) ^ (2 : ℕ))
                                    (1 / 2 : ℝ) *
                                HPow.hPow (α := ℝ)
                                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                    (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                    spatialGradientSq u Du (y, t))
                                  (1 / 2 : ℝ)) →
                        (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2),
                            HPow.hPow (α := ℝ)
                                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                  (Measure.restrict volume (vec3Ball z.1 ρ)) fun (y : Vec3) =>
                                  vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                (1 / 2 : ℝ) ≤
                              √ρ * alpha u z ρ) →
                          (0 : ℝ) ≤ cutoffGradientConstant →
                            (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                              ∀ᵐ (s : ℝ) ∂Measure.restrict volume Tρ,
                                ∀ x ∈ Br,
                                  |pressureP2 (mollifiedBallCutoff z.1 hρ) u
                                            (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                              ⨍ (y : Vec3) in Bρ, u (y, t) j)
                                            s x| +
                                        |pressureP3 (mollifiedBallCutoff z.1 hρ) u
                                            (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                              ⨍ (y : Vec3) in Bρ, u (y, t) j)
                                            s x| +
                                      |pressureP4 (mollifiedBallCutoff z.1 hρ) u
                                          (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                            ⨍ (y : Vec3) in Bρ, u (y, t) j)
                                          s x| ≤
                                    K * G s
    := by
  intro Ω I q u Du p f hsol z ρ r hρ hr hhalf Bρ Br Tρ F G D K Ω' J hbox hball htime hU henergy
    hC₁ hC₂
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
  filter_upwards [hU, henergy, hslices'] with s hUs hEs hss
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2
      (volume.restrict Bρ) :=
    hss.1.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict Bρ) := huB.aestronglyMeasurable.aemeasurable
  have hfixed := pressureP234_fixed_slice_bound hρ hr hhalf huB humeas
  have hE := hEs
  have hcoef : (18 * cutoffSecondDerivativeConstant +
      720 * cutoffGradientConstant) / ρ ^ 3 *
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (9 *
        sobolevPoincareL6Constant.toReal) * ρ *
        (Real.sqrt ρ * alpha u z ρ) = K := by
    dsimp [K, D]
    field_simp [ne_of_gt hρ]
    rw [pressure_rpow_three_halves hρ]
    have hsqrt : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
    calc
      (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) *
          sobolevPoincareL6Constant.toReal * Real.sqrt ρ *
          alpha u z ρ * (ρ * Real.sqrt ρ) =
        ((18 * cutoffSecondDerivativeConstant +
          720 * cutoffGradientConstant) *
          sobolevPoincareL6Constant.toReal * alpha u z ρ * ρ) *
          (Real.sqrt ρ) ^ 2 := by ring
      _ = (18 * cutoffSecondDerivativeConstant +
          720 * cutoffGradientConstant) * ρ ^ 2 *
          sobolevPoincareL6Constant.toReal * alpha u z ρ := by
        rw [hsqrt]
        ring
  have hbound : ∀ x ∈ Br,
      |pressureP2 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average (volume.restrict Bρ)
            (fun y => u (y, t) j)) s x| +
        |pressureP3 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average (volume.restrict Bρ)
            (fun y => u (y, t) j)) s x| +
        |pressureP4 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average (volume.restrict Bρ)
            (fun y => u (y, t) j)) s x| ≤ K * G s := by
    intro x hx
    have hfx := hfixed x hx
    have hreal :
        ∫ y in Bρ, pressureUTensorNorm u
            (fun t j => MeasureTheory.average
              (volume.restrict Bρ) (fun y => u (y, t) j)) s y ≤
          (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
            (9 * sobolevPoincareL6Constant.toReal) * ρ *
            (Real.sqrt ρ * alpha u z ρ) * G s := by
      calc
        _ ≤ (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
            (9 * sobolevPoincareL6Constant.toReal) * ρ *
            (∫ y in Bρ, vec3EuclideanNorm (u (y, s)) ^ 2) ^
              (1 / 2 : ℝ) *
            (∫ y in Bρ, spatialGradientSq u Du (y, s)) ^
              (1 / 2 : ℝ) := hUs.2
        _ ≤ (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
            (9 * sobolevPoincareL6Constant.toReal) * ρ *
            (Real.sqrt ρ * alpha u z ρ) *
            (∫ y in Bρ, spatialGradientSq u Du (y, s)) ^
              (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hEs (by positivity)
          · exact Real.rpow_nonneg
              (integral_nonneg_of_ae (Eventually.of_forall fun y => by
                unfold spatialGradientSq
                positivity)) _
        _ = _ := by
          change _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
            (9 * sobolevPoincareL6Constant.toReal) * ρ *
            (Real.sqrt ρ * alpha u z ρ) *
            |∫ y in Bρ, F (y, s)| ^ (1 / 2 : ℝ)
          have hFnonneg : 0 ≤ ∫ y in Bρ, F (y, s) := by
            exact integral_nonneg_of_ae (Eventually.of_forall fun y => by
              dsimp [F]
              unfold spatialGradientSq
              positivity)
          rw [abs_of_nonneg hFnonneg]
    have hsum :
        |pressureP2 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict Bρ) (fun y => u (y, t) j)) s x| +
          |pressureP3 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict Bρ) (fun y => u (y, t) j)) s x| +
          |pressureP4 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict Bρ) (fun y => u (y, t) j)) s x| ≤ K * G s := by
      calc
        _ ≤ (18 * cutoffSecondDerivativeConstant +
            720 * cutoffGradientConstant) / ρ ^ 3 *
            (∫ y in Bρ, pressureUTensorNorm u
              (fun t j => MeasureTheory.average
                (volume.restrict Bρ) (fun y => u (y, t) j)) s y) := hfx
        _ ≤ (18 * cutoffSecondDerivativeConstant +
            720 * cutoffGradientConstant) / ρ ^ 3 *
            ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
              (9 * sobolevPoincareL6Constant.toReal) * ρ *
              (Real.sqrt ρ * alpha u z ρ) * G s) := by
          exact mul_le_mul_of_nonneg_left hreal (by positivity)
        _ = K * G s := by
          rw [← hcoef]
          ring
    exact hsum
  exact hbound

private lemma pressureP234_bound_hP₂_3 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => spatialGradientSq u Du w;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
              fun (x : Vec3) => F (x, s)|
          (1 / 2 : ℝ);
      let D : ℝ :=
        (9 : ℝ) * sobolevPoincareL6Constant.toReal *
            ((18 : ℝ) * cutoffSecondDerivativeConstant + (720 : ℝ) * cutoffGradientConstant) *
          (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      let K : ℝ := D * alpha u z ρ / ρ ^ (3 / 2 : ℝ);
      ∀ (J : Set ℝ),
        Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
          (0 : ℝ) ≤ K →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume Tr,
                ∀ x_1 ∈ Br,
                  |pressureP2 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                        |pressureP3 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                      |pressureP4 (mollifiedBallCutoff z.1 hρ) u
                          (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x x_1| ≤
                    K * G x) →
              ∀ᵐ (w : ParabolicPoint) ∂Measure.restrict volume (parabolicCylinder z.1 z.2 r),
                ‖pressureP2 (mollifiedBallCutoff z.1 hρ) u
                      (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) w.2 w.1‖ₑ ≤
                  ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro u Du z ρ r hρ Bρ Br Tr F G D K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP2 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs
    intro x hx
    have h3 : 0 ≤ |pressureP3 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    have h4 : 0 ≤ |pressureP4 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    linarith only [hs x hx, h3, h4]
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
  have hGpos : 0 ≤ G w.2 := by
    dsimp [G]
    positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

private lemma pressureP234_bound_hP₃_4 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => spatialGradientSq u Du w;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
              fun (x : Vec3) => F (x, s)|
          (1 / 2 : ℝ);
      let D : ℝ :=
        (9 : ℝ) * sobolevPoincareL6Constant.toReal *
            ((18 : ℝ) * cutoffSecondDerivativeConstant + (720 : ℝ) * cutoffGradientConstant) *
          (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      let K : ℝ := D * alpha u z ρ / ρ ^ (3 / 2 : ℝ);
      ∀ (J : Set ℝ),
        Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
          (0 : ℝ) ≤ K →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume Tr,
                ∀ x_1 ∈ Br,
                  |pressureP2 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                        |pressureP3 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                      |pressureP4 (mollifiedBallCutoff z.1 hρ) u
                          (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x x_1| ≤
                    K * G x) →
              ∀ᵐ (w : ParabolicPoint) ∂Measure.restrict volume (parabolicCylinder z.1 z.2 r),
                ‖pressureP3 (mollifiedBallCutoff z.1 hρ) u
                      (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) w.2 w.1‖ₑ ≤
                  ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro u Du z ρ r hρ Bρ Br Tr F G D K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP3 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs
    intro x hx
    have h2 : 0 ≤ |pressureP2 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    have h4 : 0 ≤ |pressureP4 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    linarith only [hs x hx, h2, h4]
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
  have hGpos : 0 ≤ G w.2 := by
    dsimp [G]
    positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

private lemma pressureP234_bound_hP₄_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => spatialGradientSq u Du w;
      let G : ℝ → ℝ := fun (s : ℝ) =>
        HPow.hPow (α := ℝ)
          |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Bρ)
              fun (x : Vec3) => F (x, s)|
          (1 / 2 : ℝ);
      let D : ℝ :=
        (9 : ℝ) * sobolevPoincareL6Constant.toReal *
            ((18 : ℝ) * cutoffSecondDerivativeConstant + (720 : ℝ) * cutoffGradientConstant) *
          (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      let K : ℝ := D * alpha u z ρ / ρ ^ (3 / 2 : ℝ);
      ∀ (J : Set ℝ),
        Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
          (0 : ℝ) ≤ K →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume Tr,
                ∀ x_1 ∈ Br,
                  |pressureP2 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                        |pressureP3 (mollifiedBallCutoff z.1 hρ) u
                            (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x
                            x_1| +
                      |pressureP4 (mollifiedBallCutoff z.1 hρ) u
                          (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) x x_1| ≤
                    K * G x) →
              ∀ᵐ (w : ParabolicPoint) ∂Measure.restrict volume (parabolicCylinder z.1 z.2 r),
                ‖pressureP4 (mollifiedBallCutoff z.1 hρ) u
                      (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in Bρ, u (y, t) j) w.2 w.1‖ₑ ≤
                  ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro u Du z ρ r hρ Bρ Br Tr F G D K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP4 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs
    intro x hx
    have h2 : 0 ≤ |pressureP2 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    have h3 : 0 ≤ |pressureP3 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average (volume.restrict Bρ)
          (fun y => u (y, t) j)) s x| := abs_nonneg _
    linarith only [hs x hx, h2, h3]
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
  have hGpos : 0 ≤ G w.2 := by
    dsimp [G]
    positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

theorem pressureP234_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (eLpNorm' (fun w : ParabolicPoint =>
          pressureP2 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) +
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP3 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) +
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP4 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r))) ≤
      ENNReal.ofReal (pressureP12Constant * (r / ρ) *
        alpha u z ρ * beta u Du z ρ) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Br : Set Vec3 := vec3Ball z.1 r
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let F : Vec3 × ℝ → ℝ := fun w => spatialGradientSq u Du w
  let G : ℝ → ℝ := fun s =>
    |∫ x in Bρ, F (x, s)| ^ (1 / 2 : ℝ)
  let D : ℝ := 9 * sobolevPoincareL6Constant.toReal *
    (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) *
    (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)
  let K : ℝ := D * alpha u z ρ / ρ ^ (3 / 2 : ℝ)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hgradInt : Integrable F ((volume.restrict Bρ).prod
      (volume.restrict Tρ)) := by
    have hc := pressure_gradient_integrable hsol hρ hsub
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod] at hc
    change Integrable (fun w : Vec3 × ℝ => spatialGradientSq u Du w)
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Bρ ×ˢ Tρ)) at hc
    rw [← Measure.prod_restrict] at hc
    simpa [F] using hc
  have hGae : AEMeasurable (fun s => ∫ x in Bρ, F (x, s))
      (volume.restrict Tρ) := by
    have hswap := hgradInt.aestronglyMeasurable.prod_swap.integral_prod_right'
    simpa only [Prod.swap_prod_mk] using hswap.aemeasurable
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hc : Continuous (fun x : ℝ => |x| ^ (1 / 2 : ℝ)) :=
      continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))
    exact (hc.measurable.comp_aemeasurable hGae).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg (abs_nonneg _) _)
  have hbeta : (∫⁻ w in Bρ ×ˢ Tρ, ENNReal.ofReal (F w)) ≤
      ENNReal.ofReal (ρ * beta u Du z ρ ^ 2) := by
    have heq := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
      hsol z hρ hsub
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod] at heq
    change (∫⁻ w in vec3Ball z.1 ρ ×ˢ Ioc (z.2 - ρ ^ 2) z.2,
        ENNReal.ofReal (spatialGradientSq u Du w) ∂
          ((volume : Measure Vec3).prod (volume : Measure ℝ))) =
      ENNReal.ofReal (ρ * beta u Du z ρ ^ 2) at heq
    have heq' := heq.le
    rw [show (volume : Measure (Vec3 × ℝ)) =
        (volume : Measure Vec3).prod (volume : Measure ℝ) from
          Measure.volume_eq_prod Vec3 ℝ]
    exact heq'
  have hGbound := @pressureP234_bound_hGbound_1 u Du z ρ hρ hgradInt hGmeas hbeta
  have hU := U_bounds hsol hρ hsub
  have henergy := pressure_energy_bound hsol hρ hsub
  have hC := pressure_cutoff_constants_nonneg (x₀ := z.1) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hS : 0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint := @pressureP234_bound_hpoint_2 Ω I q u Du p f hsol z ρ r hρ hr hhalf Ω' J hbox
    hball htime hU henergy hC₁ hC₂
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
  have hP₂ := @pressureP234_bound_hP₂_3 u Du z ρ r hρ J htime hK hpointTr
  have hP₃ := @pressureP234_bound_hP₃_4 u Du z ρ r hρ J htime hK hpointTr
  have hP₄ := @pressureP234_bound_hP₄_5 u Du z ρ r hρ J htime hK hpointTr
  have hholder := time_holder (t₀ := z.2) hr hhalf hGmeas hGnonneg
  have hX : (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
      (2 / 3 : ℝ) ≤ ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
    calc
      _ = (∫⁻ s in Tr, ENNReal.ofReal (G s) ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro s
        rw [Real.enorm_eq_ofReal (by positivity : 0 ≤ G s)]
      _ ≤ ENNReal.ofReal r ^ (1 / 3 : ℝ) *
          eLpNorm' G 2 (volume.restrict Tρ) := hholder.1
      _ ≤ _ := by
        have hrpow : ENNReal.ofReal r ^ (1 / 3 : ℝ) =
            ENNReal.ofReal (r ^ (1 / 3 : ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num)
        rw [hrpow]
        gcongr
  have hscale0 := pressureP234_scale_cylinder (V := Br) (X :=
      ∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) hr hρ hα hD
      (by rfl) hX (pressure_volume_ball hr)
  have hscale : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
      (3 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume Br *
        (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (pressureP12Constant * (r / ρ) *
        alpha u z ρ * beta u Du z ρ) := by
    have hconst : 3 * D *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) = pressureP234Constant := by
      dsimp [D, pressureP234Constant]
    have hle : 3 * D *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * (r / ρ) *
        alpha u z ρ * beta u Du z ρ ≤
        pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ := by
      rw [hconst]
      calc
        pressureP234Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ =
            (pressureP234Constant * (r / ρ) * alpha u z ρ) *
              beta u Du z ρ := by ring
        _ ≤ (pressureP12Constant * (r / ρ) * alpha u z ρ) *
              beta u Du z ρ := by
          apply mul_le_mul_of_nonneg_right
          · calc
              pressureP234Constant * (r / ρ) * alpha u z ρ =
                  pressureP234Constant * ((r / ρ) * alpha u z ρ) := by ring
              _ ≤ pressureP12Constant * ((r / ρ) * alpha u z ρ) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
              _ = pressureP12Constant * (r / ρ) * alpha u z ρ := by ring
          · exact hβ
        _ = _ := by ring
    have hscale0' : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (3 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume Br *
          (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)) ≤
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) := by
      exact hscale0.trans (ENNReal.ofReal_le_ofReal hle)
    simpa [D, K, Bρ, Br, Tr, mul_assoc] using hscale0'
  have hGr : AEStronglyMeasurable G (volume.restrict Tr) :=
    hGmeas.mono_measure (Measure.restrict_mono_set volume hTr)
  exact pressureP234_cylinder_bound (η := mollifiedBallCutoff z.1 hρ)
    (u := u) (c := fun t j => MeasureTheory.average
      (volume.restrict Bρ) (fun y => u (y, t) j)) (x₀ := z.1) (t₀ := z.2)
    (r := r) (ρ := ρ) (K := K) (C₁₂ := pressureP12Constant)
    (α := alpha u z ρ) (β := beta u Du z ρ) hρ hr hhalf hK hGr hP₂ hP₃ hP₄
    (by simpa [Bρ, Br, Tr] using hscale)

end CKN
