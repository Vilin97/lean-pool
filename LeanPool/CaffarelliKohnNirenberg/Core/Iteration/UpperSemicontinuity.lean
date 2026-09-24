/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuityBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.AELocalEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Upper semicontinuity of the time-slice energy

The product-cutoff argument below uses the almost-every-time local energy
inequality and the compactly supported smooth cutoffs from the setting layer.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private lemma local_energy_pointwise_bound_hinner_1 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {x₀ : Vec3} {r : ℝ},
      (∀ (x : Vec3), (0 : ℝ) ≤ η x) →
        (∀ x ∈ vec3Ball x₀ r, η x = (1 : ℝ)) →
          tsupport η ⊆ Ω →
            ∀ (T : ℝ),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) => vec3EuclideanNorm (u (x, T)) ^ (2 : ℕ) * η x) volume →
                LE.le (α := ℝ)
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                    (Measure.restrict volume (vec3Ball x₀ r)) fun (y : Vec3) =>
                    vec3EuclideanNorm (u (y, T)) ^ (2 : ℕ))
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                    fun (x : Vec3) => vec3EuclideanNorm (u (x, T)) ^ (2 : ℕ) * η x)
    := by
  intro Ω u f η x₀ r hη_nonneg hη_one hηΩ T hsη
  have hballΩ : vec3Ball x₀ r ⊆ Ω := by
    intro x hx
    have hmem : x ∈ tsupport η :=
      subset_tsupport (f := η) (Function.mem_support.mpr (by
        rw [hη_one x hx]
        norm_num))
    exact hηΩ hmem
  have hmono :
      ∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, T))) ^ 2 * η y ≤
        ∫ x in Ω, (vec3EuclideanNorm (u (x, T))) ^ 2 * η x := by
    apply setIntegral_mono_set hsη.integrableOn
    · exact Filter.Eventually.of_forall (fun x =>
        mul_nonneg (sq_nonneg _) (hη_nonneg x))
    · exact Filter.Eventually.of_forall (fun x hx => hballΩ hx)
  calc
    ∫ y in vec3Ball x₀ r, (vec3EuclideanNorm (u (y, T))) ^ 2 =
        ∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, T))) ^ 2 * η y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (vec3Ball_measurable x₀ r)] with y hy
      rw [hη_one y hy]
      ring
    _ ≤ ∫ x in Ω, (vec3EuclideanNorm (u (x, T))) ^ 2 * η x := hmono

private lemma local_energy_pointwise_bound_hdrop_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {θ : ℝ → ℝ} {b h : ℝ},
      let χ : ℝ → ℝ := fun (s : ℝ) => (1 : ℝ) - backwardTimeCutoff b h s;
      (∀ (z : Vec3 × ℝ), (0 : ℝ) ≤ η z.1 * θ z.2 * χ z.2) →
        ∀ (T : ℝ),
          (((@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) => vec3EuclideanNorm (u (x, T)) ^ (2 : ℕ) * η x) +
                (2 : ℝ) *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio T))
                    fun (s : ℝ) =>
                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                      fun (x : Vec3) => spatialGradientSq u Du (x, s) * (η x * θ s * χ s)) ≤
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio T))
                fun (s : ℝ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) =>
                  localEnergyRhs u p f (fun (z : Vec3 × ℝ) => η z.1 * θ z.2 * χ z.2) (x, s)) →
            LE.le (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                fun (x : Vec3) => vec3EuclideanNorm (u (x, T)) ^ (2 : ℕ) * η x)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio T))
                fun (s : ℝ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) =>
                  localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2 * χ w.2) (x, s))
    := by
  intro Ω u Du p f η θ b h χ htest_nonneg T hineq
  have hdiss : 0 ≤ 2 * ∫ s in Iio T, ∫ x in Ω,
      spatialGradientSq u Du (x, s) * (η x * θ s * χ s) := by
    have hnon : ∀ᵐ s ∂volume.restrict (Iio T),
        0 ≤ ∫ x in Ω, spatialGradientSq u Du (x, s) *
          (η x * θ s * χ s) := by
      filter_upwards [] with s
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      have hsquare : 0 ≤ spatialGradientSq u Du (x, s) := by
        unfold spatialGradientSq
        positivity
      exact mul_nonneg hsquare (htest_nonneg (x, s))
    exact mul_nonneg (by norm_num) (integral_nonneg_of_ae hnon)
  linarith only [hineq, hdiss]

private lemma local_energy_pointwise_bound_hEmul_3 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {θ : ℝ → ℝ} {b h : ℝ},
      (0 : ℝ) < h →
        let χ : ℝ → ℝ := fun (s : ℝ) => (1 : ℝ) - backwardTimeCutoff b h s;
        ContDiff ℝ (⊤ : ℕ∞) χ →
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) => spatialGradientSq u Du z * (η z.1 * θ z.2)) volume ∧
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : Vec3 × ℝ) =>
                    localEnergyRhs u p f (fun (z : Vec3 × ℝ) => η z.1 * θ z.2) z)
                  volume ∧
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : ParabolicPoint) => vec3EuclideanNorm (u z) ^ (2 : ℕ) * (η z.1 * θ z.2))
                  volume →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : Vec3 × ℝ) =>
                vec3EuclideanNorm (u z) ^ (2 : ℕ) * (η z.1 * θ z.2) * deriv χ z.2)
              volume
    := by
  intro u Du p f η θ b h hh χ hχ hEint
  apply hEint.2.2.mul_bdd
  · exact (((hχ.continuous_deriv (by simp)).comp
      (continuous_snd : Continuous (fun z : Vec3 × ℝ => z.2))).measurable).aestronglyMeasurable
  · have hderiv : ∀ z : Vec3 × ℝ,
        deriv χ z.2 = -deriv (backwardTimeCutoff b h) z.2 := by
      intro z
      dsimp [χ]
      change deriv ((fun _ : ℝ => (1 : ℝ)) - backwardTimeCutoff b h) z.2 =
        -deriv (backwardTimeCutoff b h) z.2
      rw [deriv_sub (differentiableAt_const (c := (1 : ℝ)))
        ((backwardTimeCutoff_smooth (t := b) (h := h)).differentiable
          (by simp) z.2)]
      rw [deriv_const]
      simp
    filter_upwards [] with z
    rw [hderiv z]
    simpa only [Real.norm_eq_abs, abs_neg] using
      (backwardTimeCutoff_abs_deriv_le (t := b) (h := h) (s := z.2) hh)

private lemma local_energy_pointwise_bound_hEslice_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3}
      {η : Vec3 → ℝ} {θ : ℝ → ℝ} {b h : ℝ},
      (Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) fun (z : Vec3 × ℝ) =>
          η z.1 * θ z.2) →
        let χ : ℝ → ℝ := fun (s : ℝ) => (1 : ℝ) - backwardTimeCutoff b h s;
        ∀ (s : ℝ),
          Eq (α := ℝ)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
              fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
              vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)
    := by
  intro Ω I u f η θ b h hψ χ s
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hzero : η x * θ s = 0 := by
    by_contra hne
    have hmem : (x, s) ∈ tsupport
        (fun w : Vec3 × ℝ => η w.1 * θ w.2) :=
      subset_tsupport (f := fun w : Vec3 × ℝ => η w.1 * θ w.2)
        (Function.mem_support.mpr hne)
    exact hx (hψ.2.2 hmem).1
  simp [hzero]

private lemma local_energy_pointwise_bound_hRtime_5 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {θ : ℝ → ℝ} {b h : ℝ},
      let χ : ℝ → ℝ := fun (s : ℝ) => (1 : ℝ) - backwardTimeCutoff b h s;
      (∀ᵐ (y : ℝ),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) => vec3EuclideanNorm (u (x, y)) ^ (2 : ℕ) * (η (x, y).1 * θ (x, y).2))
            volume) →
        ∀ (T : ℝ),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : Vec3 × ℝ) =>
                localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) z * χ z.2)
              volume →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : Vec3 × ℝ) =>
                  vec3EuclideanNorm (u z) ^ (2 : ℕ) * (η z.1 * θ z.2) * deriv χ z.2)
                volume →
              (∀ (s : ℝ),
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                      fun (x : Vec3) =>
                      localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) (x, s) * χ s)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                      localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) (x, s) * χ s)) →
                (∀ (s : ℝ),
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)) →
                  (∀ (s : ℝ),
                      Eq (α := ℝ)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume Ω) fun (x : Vec3) =>
                          localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2 * χ w.2) (x, s))
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume Ω) fun (x : Vec3) =>
                          localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) (x, s) * χ s +
                            vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)) →
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                        (Measure.restrict volume (Iio T)) fun (s : ℝ) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) =>
                          localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2 * χ w.2)
                            (x, s)) =
                      HAdd.hAdd (α := ℝ)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume (Iio T)) fun (s : ℝ) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                            localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) (x, s) * χ s)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume (Iio T)) fun (s : ℝ) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                            vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) * (η x * θ s) * deriv χ s)
    := by
  intro Ω u p f η θ b h χ hEslice T hRmul hEmul hRslice hEslice hsplit
  have hRfull : Integrable (fun s : ℝ => ∫ x,
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s) volume :=
    hRmul.integral_prod_right
  have hEfull : Integrable (fun s : ℝ => ∫ x,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s) volume :=
    hEmul.integral_prod_right
  have hRset : Integrable (fun s : ℝ => ∫ x in Ω,
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s) volume := by
    apply hRfull.congr
    filter_upwards [] with s
    exact (hRslice s).symm
  have hEset : Integrable (fun s : ℝ => ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s) volume := by
    apply hEfull.congr
    filter_upwards [] with s
    exact (hEslice s).symm
  calc
    ∫ s in Iio T, ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2 * χ w.2) (x, s) =
        ∫ s in Iio T,
          ((∫ x in Ω, localEnergyRhs u p f
            (fun w => η w.1 * θ w.2) (x, s) * χ s) +
            (∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 *
              (η x * θ s) * deriv χ s)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hRmul.prod_left_ae,
        ae_restrict_of_ae hEmul.prod_left_ae] with s hRs hEs
      rw [hsplit s, integral_add hRs.integrableOn hEs.integrableOn]
    _ = (∫ s in Iio T, ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s) +
        (∫ s in Iio T, ∫ x in Ω,
          (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s) := by
      exact integral_add hRset.integrableOn hEset.integrableOn
    _ = (∫ s in Iio T, ∫ x,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s) +
        (∫ s in Iio T, ∫ x,
          (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s) := by
      congr 1
      · apply integral_congr_ae
        filter_upwards [] with s
        exact hRslice s
      · apply integral_congr_ae
        filter_upwards [] with s
        exact hEslice s

private lemma local_energy_pointwise_bound_hRpart_6 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      {η : Vec3 → ℝ} {θ : ℝ → ℝ} {x₀ : Vec3} {R b h : ℝ},
      (0 : ℝ) < h →
        let χ : ℝ → ℝ := fun (s : ℝ) => (1 : ℝ) - backwardTimeCutoff b h s;
        (∀ (s : ℝ), (0 : ℝ) ≤ χ s) →
          (∀ (s : ℝ), χ s ≤ (1 : ℝ)) →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : Vec3 × ℝ) => localEnergyRhs u p f (fun (z : Vec3 × ℝ) => η z.1 * θ z.2) z)
                volume →
              (∀ (z : Vec3 × ℝ),
                  z.1 ∉ euclideanClosedBall x₀ R →
                    localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) z = (0 : ℝ)) →
                ∀ T ≤ b + h,
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (z : Vec3 × ℝ) =>
                        localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) z * χ z.2)
                      volume →
                    LE.le (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                        (Measure.restrict volume (Iio T)) fun (s : ℝ) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                          localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) (x, s) * χ s)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                        (Measure.restrict volume (euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h)))
                        fun (z : Vec (3 : ℕ) × ℝ) =>
                        |localEnergyRhs u p f (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) z|)
    := by
  intro u p f η θ x₀ R b h hh χ hχ_nonneg hχ_le hRint hRzeroK T hTupper hRmul
  let A : Set (Vec3 × ℝ) := Set.univ ×ˢ Iio T
  let B : Set (Vec3 × ℝ) :=
    euclideanClosedBall x₀ R ×ˢ Ico (b - h) T
  have hA : MeasurableSet A :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Iio
  have hB : MeasurableSet B :=
    (isClosed_euclideanClosedBall x₀ R).measurableSet.prod measurableSet_Ico
  have hBbig : B ⊆ euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h) := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, le_trans (le_of_lt hz.2.2) hTupper⟩⟩
  have htarget : Integrable (B.indicator (fun z : Vec3 × ℝ =>
      |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z|)) volume := by
    exact hRint.norm.indicator hB
  have hmono : ∫ z in A,
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) z * χ z.2 ≤
      ∫ z in A, B.indicator (fun z : Vec3 × ℝ =>
        |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z|) z := by
    apply integral_mono_ae hRmul.integrableOn htarget.integrableOn
    filter_upwards [ae_restrict_mem hA] with z hz
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB]
      calc
        localEnergyRhs u p f (fun w => η w.1 * θ w.2) z * χ z.2 ≤
            |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| * χ z.2 := by
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (hχ_nonneg z.2)
        _ ≤ |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := by
          exact mul_le_of_le_one_right (abs_nonneg _) (hχ_le z.2)
    · simp only [Set.indicator, hzB, ↓reduceIte]
      by_cases hzK : z.1 ∉ euclideanClosedBall x₀ R
      · simp [hRzeroK z hzK]
      · have hzK' : z.1 ∈ euclideanClosedBall x₀ R := not_not.mp hzK
        have hzlow : z.2 < b - h := by
          by_contra hzlow'
          have hzupper : z.2 < T := hz.2
          have hzB' : z ∈ B :=
            ⟨hzK', ⟨le_of_not_gt hzlow', hzupper⟩⟩
          exact hzB hzB'
        have hcut : χ z.2 = 0 := by
          dsimp [χ]
          rw [backwardTimeCutoff_eq_one_of_le hh (le_of_lt hzlow)]
          norm_num
        simp [hcut]
  have hFub := setIntegral_univ_Iio_probe
    (g := fun z : Vec3 × ℝ =>
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) z * χ z.2)
    (t := T) hRmul.integrableOn
  have hindicator : ∫ z in A, B.indicator (fun z : Vec3 × ℝ =>
      |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z|) z =
      ∫ z in B, |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := by
    have hAB : A ∩ B = B := by
      ext z
      constructor
      · rintro ⟨hzA, hzB⟩
        exact hzB
      · intro hzB
        exact ⟨⟨Set.mem_univ _, hzB.2.2⟩, hzB⟩
    rw [setIntegral_indicator hB]
    rw [hAB]
  have hBbound : ∫ z in B,
      |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| ≤
      ∫ z in euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h),
        |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := by
    apply setIntegral_mono_set hRint.norm.integrableOn
    · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
    · exact Filter.Eventually.of_forall hBbig
  calc
    ∫ s in Iio T, ∫ x,
        localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s =
        ∫ z in A, localEnergyRhs u p f
          (fun w => η w.1 * θ w.2) z * χ z.2 := by
      simpa only [A, Prod.snd] using hFub.symm
    _ ≤ ∫ z in A, B.indicator (fun z : Vec3 × ℝ =>
        |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z|) z := hmono
    _ = ∫ z in B, |localEnergyRhs u p f
        (fun w => η w.1 * θ w.2) z| := hindicator
    _ ≤ ∫ z in euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h),
        |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := hBbound

private lemma local_energy_pointwise_bound_hEpart_7 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {θ : ℝ → ℝ} {x₀ : Vec3} {r R a b h : ℝ},
      (0 : ℝ) < r →
        r < R →
          (0 : ℝ) < h →
            h < b - a →
              (Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I)
                  fun (z : Vec3 × ℝ) => η z.1 * θ z.2) →
                (∀ (x : Vec3), (0 : ℝ) ≤ η x) →
                  (∀ (x : Vec3), η x ≤ (1 : ℝ)) →
                    (∀ x ∈ vec3Ball x₀ r, η x = (1 : ℝ)) →
                      tsupport η ⊆ euclideanBall x₀ R →
                        tsupport η ⊆ Ω →
                          (∀ s ∈ Icc a (b + h), θ s = (1 : ℝ)) →
                            ∀ {S : ℝ≥0∞},
                              S =
                                  @essSup _ _ _ MeasureSpace.toMeasurableSpace
                                    (fun (x : ℝ) =>
                                      timeSliceBallEnergy x₀ R x fun (w : ParabolicPoint) =>
                                        vec3EuclideanNorm (u w))
                                    (Measure.restrict volume (Ioc a b)) →
                                S ≠ ∞ →
                                  let χ : ℝ → ℝ := fun (s : ℝ) =>
                                    (1 : ℝ) - backwardTimeCutoff b h s;
                                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                        (fun (z : ParabolicPoint) =>
                                          spatialGradientSq u Du z * (η z.1 * θ z.2))
                                        volume ∧
                                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                          (fun (z : Vec3 × ℝ) =>
                                            localEnergyRhs u p f
                                              (fun (z : Vec3 × ℝ) => η z.1 * θ z.2) z)
                                          volume ∧
                                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                          (fun (z : ParabolicPoint) =>
                                            vec3EuclideanNorm (u z) ^ (2 : ℕ) * (η z.1 * θ z.2))
                                          volume →
                                    (∀ᵐ (y : ℝ),
                                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                          (fun (x : Vec3) =>
                                            vec3EuclideanNorm (u (x, y)) ^ (2 : ℕ) *
                                              (η (x, y).1 * θ (x, y).2))
                                          volume) →
                                      ∀ T ∈ Ioc b (b + h),
                                        b ≤ T →
                                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                              (fun (z : Vec3 × ℝ) =>
                                                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                                                    (η z.1 * θ z.2) *
                                                  deriv χ z.2)
                                              volume →
                                            (∀ (s : ℝ),
                                                Eq (α := ℝ)
                                                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                    (Measure.restrict volume Ω) fun (x : Vec3) =>
                                                    vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) *
                                                        (η x * θ s) *
                                                      deriv χ s)
                                                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                    volume fun (x : Vec3) =>
                                                    vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) *
                                                        (η x * θ s) *
                                                      deriv χ s)) →
                                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                  (Measure.restrict volume (Iio T)) fun (s : ℝ) =>
                                                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                    volume fun (x : Vec3) =>
                                                    vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) *
                                                        (η x * θ s) *
                                                      deriv χ s) ≤
                                                S.toReal
    := by
  intro Ω I u Du p f η θ x₀ r R a b h hr hrr hh hsmall hψ hη_nonneg hη_le hη_one hη_support hηΩ
    hθ_one S hSdef hS χ hEint hEslice T hT hTle hEmul hEslice
  have hEbaseSlice : ∀ s, ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) =
      ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) := by
    intro s
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : η x * θ s = 0 := by
      by_contra hne
      have hmem : (x, s) ∈ tsupport
          (fun w : Vec3 × ℝ => η w.1 * θ w.2) :=
        subset_tsupport (f := fun w : Vec3 × ℝ => η w.1 * θ w.2)
          (Function.mem_support.mpr hne)
      exact hx (hψ.2.2 hmem).1
    simp [hzero]
  have hEbaseFull : Integrable (fun s : ℝ => ∫ x,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) volume :=
    hEint.2.2.integral_prod_right
  have hAint : Integrable (fun s : ℝ => ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) volume := by
    apply hEbaseFull.congr
    filter_upwards [] with s
    exact (hEbaseSlice s).symm
  have hθ_one_ab : ∀ s, s ∈ Icc a b → θ s = 1 := by
    intro s hs
    exact hθ_one s ⟨hs.1, by linarith only [hs.2, hh]⟩
  have hAouter := cutoff_slice_le hr hrr hη_nonneg hη_le hη_one
    hη_support hηΩ hθ_one_ab hSdef hS hEint.2.2
  have hAouter' : ∀ᵐ s ∂volume.restrict (Ioc a b),
      (∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) ≤
        S.toReal := by
    filter_upwards [hAouter, ae_restrict_mem measurableSet_Ioc] with s hs hsab
    simpa [hθ_one_ab s ⟨hsab.1.le, hsab.2⟩, mul_assoc] using hs
  have hwindow : Ioc (b - h) b ⊆ Ioc a b := by
    intro s hs
    exact ⟨by linarith only [hs.1, hsmall], hs.2⟩
  have hAwindow := ae_restrict_of_ae_restrict_of_subset hwindow hAouter'
  have hweight := weighted_kernel_le (A := fun s : ℝ => ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s))
    (S := S.toReal) hh hAwindow hAint (ENNReal.toReal_nonneg)
  have hχderiv : ∀ s : ℝ,
      deriv χ s = -deriv (backwardTimeCutoff b h) s := by
    intro s
    dsimp [χ]
    change deriv ((fun _ : ℝ => (1 : ℝ)) - backwardTimeCutoff b h) s =
      -deriv (backwardTimeCutoff b h) s
    rw [deriv_sub (differentiableAt_const (c := (1 : ℝ)))
      ((backwardTimeCutoff_smooth (t := b) (h := h)).differentiable
        (by simp) s)]
    rw [deriv_const]
    simp
  have hEsetInt : Integrable (fun s : ℝ => ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s) volume := by
    apply hEmul.integral_prod_right.congr
    filter_upwards [] with s
    exact (hEslice s).symm
  have hEfactor : ∀ s, ∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s =
      (∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) *
        deriv χ s := by
    intro s
    calc
      ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s =
          ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s :=
        hEslice s
      _ = (∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) *
          deriv χ s := by rw [integral_mul_const]
      _ = (∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) *
          deriv χ s := by rw [hEbaseSlice s]
  have hAtimesInt : Integrable (fun s : ℝ =>
      (∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) *
        deriv χ s) volume := by
    apply hEsetInt.congr
    filter_upwards [] with s
    exact hEfactor s
  have hsupport : ∀ s, T ≤ s → deriv χ s = 0 := by
    intro s hs
    have hb : b ≤ s := le_trans hTle hs
    have hzero : -deriv (backwardTimeCutoff b h) s = 0 := by
      apply by_contra
      intro hne
      have hmem := backwardTimeCutoff_kernel_support (t := b) (h := h) hh
        (Function.mem_support.mpr hne)
      exact (not_le_of_gt (lt_of_lt_of_le hT.1 hs)) hmem.2
    rw [hχderiv s]
    linarith only [hzero]
  have hIio : ∫ s in Iio T, (∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) * deriv χ s =
      ∫ s, (∫ x in Ω,
      (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) * deriv χ s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    rw [hsupport s (le_of_not_gt hs)]
    simp
  calc
    ∫ s in Iio T, ∫ x,
        (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s =
        ∫ s in Iio T, (∫ x in Ω,
          (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) * deriv χ s := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact (hEslice s).symm |>.trans (hEfactor s)
    _ = ∫ s, (∫ x in Ω,
          (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) * deriv χ s := hIio
    _ = ∫ s, (∫ x in Ω,
          (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s)) *
            (-deriv (backwardTimeCutoff b h) s) := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [hχderiv]
    _ ≤ S.toReal := hweight

private lemma local_energy_pointwise_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} {θ : ℝ → ℝ} {x₀ : Vec3} {r R a b h : ℝ}
    (hr : 0 < r) (hrr : r < R) (hab : a < b) (hh : 0 < h)
    (hsmall : h < b - a)
    (hψ : (fun z : Vec3 × ℝ => η z.1 * θ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z : Vec3 × ℝ, 0 ≤ η z.1 * θ z.2)
    (hη_nonneg : ∀ x, 0 ≤ η x) (hη_le : ∀ x, η x ≤ 1)
    (hη_one : ∀ x, x ∈ vec3Ball x₀ r → η x = 1)
    (hη_support : tsupport η ⊆ euclideanBall x₀ R)
    (hηΩ : tsupport η ⊆ Ω)
    (hψsupport : tsupport (fun z : Vec3 × ℝ => η z.1 * θ z.2) ⊆
      tsupport η ×ˢ tsupport θ)
    (hθ_one : ∀ s, s ∈ Icc a (b + h) → θ s = 1)
    {S : ℝ≥0∞}
    (hSdef : S = essSup
      (timeSliceBallEnergy x₀ R · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc a b))) (hS : S ≠ ⊤)
    (hI : Icc a (b + h) ⊆ I) :
    ∀ᵐ T ∂volume.restrict (Ioc b (b + h)),
      ∫ y in vec3Ball x₀ r, (vec3EuclideanNorm (u (y, T))) ^ 2 ≤
        S.toReal + ∫ z in euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h),
          |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := by
  let χ : ℝ → ℝ := fun s => 1 - backwardTimeCutoff b h s
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := by
    exact contDiff_const.sub (backwardTimeCutoff_smooth (t := b) (h := h))
  have hχ_nonneg : ∀ s, 0 ≤ χ s := by
    intro s
    dsimp [χ]
    linarith only [backwardTimeCutoff_le_one (t := b) (h := h) (s := s)]
  have hχ_le : ∀ s, χ s ≤ 1 := by
    intro s
    dsimp [χ]
    linarith only [backwardTimeCutoff_nonneg (t := b) (h := h) (s := s)]
  have htest : (fun z : Vec3 × ℝ => η z.1 * θ z.2 * χ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
    have htest' := spaceTimeTestFunction_mul_smooth hψ
      (hχ.comp contDiff_snd)
    convert htest' using 1
    funext z
    rfl
  have htest_nonneg : ∀ z : Vec3 × ℝ, 0 ≤ η z.1 * θ z.2 * χ z.2 := by
    intro z
    exact mul_nonneg (hψ_nonneg z) (hχ_nonneg z.2)
  have hEae := suitableWeakSolution_localEnergyInequality_ae hsol htest
    htest_nonneg
  have hEint := suitableWeakSolution_energy_integrable hsol hψ hψ_nonneg
  have hRint := hEint.2.1
  have hRcompact : IsCompact (euclideanClosedBall x₀ R) :=
    isCompact_euclideanClosedBall x₀ (le_of_lt (lt_trans hr hrr))
  have hRerr : Integrable
      (fun z : Vec3 × ℝ => localEnergyRhs u p f (fun w => η w.1 * θ w.2) z) volume :=
    hRint
  have hψzero : ∀ z : Vec3 × ℝ, z.1 ∉ Ω → η z.1 * θ z.2 = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport (fun w : Vec3 × ℝ => η w.1 * θ w.2) :=
      subset_tsupport (f := fun w : Vec3 × ℝ => η w.1 * θ w.2)
        (Function.mem_support.mpr hne)
    exact hz (hψ.2.2 hmem).1
  have hRzeroΩ : ∀ z : Vec3 × ℝ, z.1 ∉ Ω →
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) z = 0 := by
    intro z hz
    apply localEnergyRhs_eq_zero_of_not_mem_tsupport_public hψ.1
    intro hmem
    exact hz (hψ.2.2 hmem).1
  have hRzeroK : ∀ z : Vec3 × ℝ,
      z.1 ∉ euclideanClosedBall x₀ R →
      localEnergyRhs u p f (fun w => η w.1 * θ w.2) z = 0 := by
    intro z hz
    apply localEnergyRhs_eq_zero_of_not_mem_tsupport_public hψ.1
    intro hmem
    have hηmem := (hψsupport hmem).1
    have heu := hη_support hηmem
    exact hz ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (le_of_lt (lt_trans hr hrr))).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt
        (lt_trans hr hrr)).mp heu).le)
  have hJI : Ioc b (b + h) ⊆ I :=
    (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc (le_of_lt hab) le_rfl)).trans hI
  have hEae' := ae_restrict_of_ae_restrict_of_subset hJI hEae
  have hEslice := hEint.2.2.prod_left_ae
  filter_upwards [hEae', ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae hEslice] with T hineq hT hsE
  have hTle : b ≤ T := hT.1.le
  have hTupper : T ≤ b + h := hT.2
  have hθT : θ T = 1 := hθ_one T ⟨by linarith only [hab, hT.1], hTupper⟩
  have hχT : χ T = 1 := by
    dsimp [χ]
    rw [backwardTimeCutoff_eq_zero_of_ge hh hTle]
    norm_num
  have hterminal :
      ∫ x in Ω, (vec3EuclideanNorm (u (x, T))) ^ 2 *
          (η x * θ T * χ T) =
        ∫ x in Ω, (vec3EuclideanNorm (u (x, T))) ^ 2 * η x := by
    rw [hθT, hχT]
    simp only [mul_one]
  rw [hterminal] at hineq
  have hsη : Integrable
      (fun x : Vec3 => (vec3EuclideanNorm (u (x, T))) ^ 2 * η x) volume := by
    simpa [hθT, mul_assoc] using hsE
  have hinner := @local_energy_pointwise_bound_hinner_1 Ω u f η x₀ r hη_nonneg hη_one hηΩ T hsη
  have hdrop := @local_energy_pointwise_bound_hdrop_2 Ω u Du p f η θ b h htest_nonneg T hineq
  have hRbound :
      ∫ s in Iio T, ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2 * χ w.2) (x, s) ≤
        S.toReal + ∫ z in euclideanClosedBall x₀ R ×ˢ Icc (b - h) (b + h),
          |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z| := by
    have hRbase : ∀ z : Vec3 × ℝ, z.1 ∉ Ω →
        localEnergyRhs u p f (fun w => η w.1 * θ w.2) z = 0 := hRzeroΩ
    have hRmul : Integrable
        (fun z : Vec3 × ℝ =>
          localEnergyRhs u p f (fun w => η w.1 * θ w.2) z * χ z.2) volume := by
      apply hRint.mul_bdd
      · exact ((hχ.continuous.comp continuous_snd).measurable).aestronglyMeasurable
      · filter_upwards [] with z
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg z.2)] using hχ_le z.2
    have hEmul := @local_energy_pointwise_bound_hEmul_3 u Du p f η θ b h hh hχ hEint
    have hRslice : ∀ s, ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s =
        ∫ x, localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s := by
      intro s
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [hRbase (x, s) hx]
    have hEslice := @local_energy_pointwise_bound_hEslice_4 Ω I u f η θ b h hψ
    have hsplit : ∀ s, ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2 * χ w.2) (x, s) =
        ∫ x in Ω,
          localEnergyRhs u p f (fun w => η w.1 * θ w.2) (x, s) * χ s +
            (vec3EuclideanNorm (u (x, s))) ^ 2 * (η x * θ s) * deriv χ s := by
      intro s
      apply integral_congr_ae
      filter_upwards [] with x
      simpa [mul_assoc] using
        (localEnergyRhs_mul_time hψ.1 hχ (z := (x, s)))
    have hRtime := @local_energy_pointwise_bound_hRtime_5 Ω u p f η θ b h (by assumption) T hRmul
      hEmul hRslice hEslice hsplit
    rw [hRtime]
    have hRpart := @local_energy_pointwise_bound_hRpart_6 u p f η θ x₀ R b h hh hχ_nonneg hχ_le
      hRint hRzeroK T hTupper hRmul
    have hEpart := @local_energy_pointwise_bound_hEpart_7 Ω I u Du p f η θ x₀ r R a b h hr hrr hh
      hsmall hψ hη_nonneg hη_le hη_one hη_support hηΩ hθ_one S hSdef hS hEint (by assumption) T hT
      hTle hEmul hEslice
    linarith only [hRpart, hEpart]
  exact hinner.trans (hdrop.trans hRbound)

private lemma alpha_usc_henergy_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {x₀ : Vec3} {r R t₁ t₂ : ℝ},
          (0 : ℝ) < r →
            r < R →
              t₁ < t₂ →
                ∀ (ε : ℝ),
                  let h₀ : ℝ := ε / (2 : ℝ);
                  (0 : ℝ) < h₀ →
                    Icc t₁ (t₂ + h₀) ⊆ I →
                      let η : Vec3 → ℝ := canonicalBallCutoff x₀ r R;
                      (∀ (x : Vec3), (0 : ℝ) ≤ η x) →
                        (∀ (x : Vec3), η x ≤ (1 : ℝ)) →
                          (∀ x ∈ vec3Ball x₀ r, η x = (1 : ℝ)) →
                            tsupport η ⊆ euclideanBall x₀ R →
                              tsupport η ⊆ Ω →
                                ∀ (θ : ℝ → ℝ),
                                  (∀ t ∈ Icc t₁ (t₂ + h₀), θ t = (1 : ℝ)) →
                                    (Membership.mem (γ := Set (Vec3 × ℝ → ℝ))
                                        (spaceTimeTestFunction Ω I) fun (z : Vec3 × ℝ) =>
                                        η z.1 * θ z.2) →
                                      (∀ (z : Vec3 × ℝ), (0 : ℝ) ≤ η z.1 * θ z.2) →
                                        (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => η z.1 * θ z.2) ⊆
                                            tsupport η ×ˢ tsupport θ →
                                          let S : ℝ≥0∞ :=
                                            @essSup _ _ _ MeasureSpace.toMeasurableSpace
                                              (fun (x : ℝ) =>
                                                timeSliceBallEnergy x₀ R x
                                                  fun (w : ParabolicPoint) =>
                                                  vec3EuclideanNorm (u w))
                                              (Measure.restrict volume (Ioc t₁ t₂));
                                          S ≠ ∞ →
                                            S =
                                                @essSup _ _ _ MeasureSpace.toMeasurableSpace
                                                  (fun (x : ℝ) =>
                                                    timeSliceBallEnergy x₀ R x
                                                      fun (w : ParabolicPoint) =>
                                                      vec3EuclideanNorm (u w))
                                                  (Measure.restrict volume (Ioc t₁ t₂)) →
                                              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                                    (fun (z : ParabolicPoint) =>
                                                      spatialGradientSq u Du z * (η z.1 * θ z.2))
                                                    volume ∧
                                                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                                      (fun (z : Vec3 × ℝ) =>
                                                        localEnergyRhs u p f
                                                          (fun (z : Vec3 × ℝ) => η z.1 * θ z.2) z)
                                                      volume ∧
                                                    @Integrable ℝ _ _ _
                                                      MeasureSpace.toMeasurableSpace
                                                      (fun (z : ParabolicPoint) =>
                                                        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                                                          (η z.1 * θ z.2))
                                                      volume →
                                                let ω : ℝ → ℝ := fun (h : ℝ) =>
                                                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                    (Measure.restrict volume
                                                      (euclideanClosedBall x₀ R ×ˢ
                                                        Icc (t₂ - h) (t₂ + h)))
                                                    fun (z : Vec (3 : ℕ) × ℝ) =>
                                                    |localEnergyRhs u p f
                                                        (fun (w : Vec3 × ℝ) => η w.1 * θ w.2) z|;
                                                (∀ᶠ (h : ℝ) in 𝓝[>] (0 : ℝ), h < h₀ ∧ h < t₂ - t₁) →
                                                  ∀ᶠ (h : ℝ) in 𝓝[>] (0 : ℝ),
                                                    ENNReal.toReal
                                                        (@essSup _ _ _
                                                          MeasureSpace.toMeasurableSpace
                                                          (fun (s : ℝ) =>
                                                            ENNReal.ofReal
                                                              (@integral _ _ _ _
                                                                MeasureSpace.toMeasurableSpace
                                                                (Measure.restrict volume
                                                                  (vec3Ball x₀ r))
                                                                fun (y : Vec3) =>
                                                                vec3EuclideanNorm (u (y, s)) ^
                                                                  (2 : ℕ)))
                                                          (Measure.restrict volume
                                                            (Ioc t₁ (t₂ + h)))) ≤
                                                      S.toReal + ω h
    := by
  intro Ω I q u Du p f hsol x₀ r R t₁ t₂ hr hrr ht ε h₀ hh₀ hIext η hηnonneg hηle hηone hηsupport
    hηΩ θ hθone hψ hψ_nonneg hψsupport S hS hSdef hEint ω hsmall
  filter_upwards [hsmall, self_mem_nhdsWithin] with h ⟨hh₀', hht⟩ hhpos
  have hh : 0 < h := by simpa only [mem_Ioi] using hhpos
  have hθh : ∀ s, s ∈ Icc t₁ (t₂ + h) → θ s = 1 := by
    intro s hs
    exact hθone s ⟨hs.1, le_trans hs.2 (by linarith only [hh₀'])⟩
  have hIh : Icc t₁ (t₂ + h) ⊆ I := by
    intro s hs
    exact hIext ⟨hs.1, le_trans hs.2 (by linarith only [hh₀'])⟩
  have hfuture := local_energy_pointwise_bound hsol
    (η := η) (θ := θ) (x₀ := x₀) (r := r) (R := R)
    (a := t₁) (b := t₂) (h := h) hr hrr ht hh hht hψ hψ_nonneg
    hηnonneg hηle hηone hηsupport hηΩ hψsupport hθh hSdef hS hIh
  have hold := cutoff_slice_le (Ω := Ω) (u := u) (η := η) (θ := θ)
    (x₀ := x₀) (r := r) (R := R) (a := t₁) (b := t₂)
    hr hrr hηnonneg hηle hηone hηsupport hηΩ
    (fun s hs => hθone s ⟨hs.1, le_trans hs.2 (by linarith only [hh₀])⟩)
    hSdef hS hEint.2.2
  have hOld : ∀ᵐ s ∂volume.restrict (Ioc t₁ t₂),
      ∫ y in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (y, s))) ^ 2 ≤ S.toReal := by
    have hEslice := hEint.2.2.prod_left_ae
    filter_upwards [hold, ae_restrict_of_ae hEslice,
      ae_restrict_mem measurableSet_Ioc] with s hs hslice hsIoc
    have hθs : θ s = 1 := hθone s ⟨hsIoc.1.le,
      le_trans hsIoc.2 (le_add_of_nonneg_right hh₀.le)⟩
    have hsη : Integrable
        (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ 2 * η x) volume := by
      simpa [hθs, mul_assoc] using hslice
    have hballΩ : vec3Ball x₀ r ⊆ Ω := by
      intro x hx
      have hmem : x ∈ tsupport η := subset_tsupport
        (f := η) (Function.mem_support.mpr (by rw [hηone x hx]; norm_num))
      exact hηΩ hmem
    have hmono : ∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2 * η y ≤
        ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x := by
      apply setIntegral_mono_set hsη.integrableOn
      · exact Filter.Eventually.of_forall (fun x =>
          mul_nonneg (sq_nonneg _) (hηnonneg x))
      · exact Filter.Eventually.of_forall (fun x hx => hballΩ hx)
    have hinner : ∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2 =
        ∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2 * η y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (vec3Ball_measurable x₀ r)] with y hy
      rw [hηone y hy]
      ring
    exact hinner ▸ hmono.trans hs
  have hfuture' : ∀ᵐ s ∂volume.restrict (Ioc t₂ (t₂ + h)),
      ∫ y in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (y, s))) ^ 2 ≤ S.toReal + ω h := hfuture
  have hinterval : Ioc t₁ (t₂ + h) = Ioc t₁ t₂ ∪ Ioc t₂ (t₂ + h) := by
    ext s
    constructor
    · intro hs
      by_cases hst : s ≤ t₂
      · exact Or.inl ⟨hs.1, hst⟩
      · exact Or.inr ⟨lt_of_not_ge hst, hs.2⟩
    · rintro (hs | hs)
      · exact ⟨hs.1, le_trans hs.2 (le_add_of_nonneg_right hh.le)⟩
      · exact ⟨lt_trans ht hs.1, hs.2⟩
  have hAE : ∀ᵐ s ∂volume.restrict (Ioc t₁ (t₂ + h)),
      ENNReal.ofReal (∫ y in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (y, s))) ^ 2) ≤
        ENNReal.ofReal (S.toReal + ω h) := by
    rw [hinterval, ae_restrict_union_iff]
    constructor
    · filter_upwards [hOld] with s hs
      have hωnonneg : 0 ≤ ω h := by
        apply integral_nonneg_of_ae
        exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
      exact ENNReal.ofReal_le_ofReal (hs.trans (le_add_of_nonneg_right hωnonneg))
    · filter_upwards [hfuture'] with s hs
      exact ENNReal.ofReal_le_ofReal hs
  let _ : (ae (volume.restrict (Ioc t₁ (t₂ + h)))).NeBot := by
    rw [MeasureTheory.ae_restrict_neBot]
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (by linarith only [ht, hh])).ne'
  have hco : IsCoboundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc t₁ (t₂ + h))))
      (fun s => ENNReal.ofReal (∫ y in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (y, s))) ^ 2)) := by
    apply isCoboundedUnder_le_of_eventually_le
      (l := ae (volume.restrict (Ioc t₁ (t₂ + h))))
    exact Filter.Eventually.of_forall (fun s => bot_le)
  have hEss := essSup_le_of_ae_le (ENNReal.ofReal (S.toReal + ω h)) hAE hco
  have hleft : essSup
        (fun s => ENNReal.ofReal (∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc t₁ (t₂ + h))) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hEss ENNReal.ofReal_lt_top)
  have hright : ENNReal.ofReal (S.toReal + ω h) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hleft hright).mpr hEss
  have hωnonneg : 0 ≤ ω h := by
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
  rw [ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg hωnonneg)] at hreal
  exact hreal

/-- The right-sided essential-supremum bound for a suitable weak solution.

The spatial cutoff is one on the inner ball and supported in the outer ball;
the time cutoff is one through the enlarged time interval.  The two pieces of
the time interval are then joined before taking the essential supremum. -/
theorem alpha_usc_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {r R t₁ t₂ : ℝ}
    (hr : 0 < r) (hrr : r < R) (ht : t₁ < t₂)
    (hrect : euclideanClosedBall x₀ R ×ˢ Icc t₁ t₂ ⊆
      spaceTimeSet Ω I) :
    Filter.limsup
        (fun h : ℝ =>
          (essSup
            (fun s => ENNReal.ofReal
              (∫ y in vec3Ball x₀ r,
                (vec3EuclideanNorm (u (y, s))) ^ 2))
            (volume.restrict (Ioc t₁ (t₂ + h)))).toReal)
        (𝓝[>] (0 : ℝ)) ≤
      (essSup
        (timeSliceBallEnergy x₀ R ·
          (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc t₁ t₂))).toReal := by
  have hR : 0 < R := lt_trans hr hrr
  have hx₀ : x₀ ∈ euclideanClosedBall x₀ R := by
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
      (by simpa [vecEuclideanNorm, vecNormSq, vecDot] using hR.le)
  have hrect₁ : (x₀, t₁) ∈ euclideanClosedBall x₀ R ×ˢ Icc t₁ t₂ :=
    ⟨hx₀, ⟨le_rfl, ht.le⟩⟩
  have hrect₂ : (x₀, t₂) ∈ euclideanClosedBall x₀ R ×ˢ Icc t₁ t₂ :=
    ⟨hx₀, ⟨ht.le, le_rfl⟩⟩
  have ht₁I : t₁ ∈ I := (hrect hrect₁).2
  have ht₂I : t₂ ∈ I := (hrect hrect₂).2
  obtain ⟨ε, hε, hεI⟩ :=
    Metric.mem_nhds_iff.mp (hsol.2.1.mem_nhds ht₂I)
  let h₀ : ℝ := ε / 2
  have hh₀ : 0 < h₀ := by
    dsimp [h₀]
    positivity
  have hupperI : t₂ + h₀ ∈ I := by
    apply hεI
    rw [Metric.mem_ball, Real.dist_eq]
    have hdiff : t₂ + h₀ - t₂ = h₀ := by ring
    rw [hdiff, abs_of_nonneg hh₀.le]
    dsimp [h₀]
    exact half_lt_self hε
  have hIext : Icc t₁ (t₂ + h₀) ⊆ I := by
    intro s hs
    exact hsol.2.2.1.out ht₁I hupperI hs
  let η : Vec3 → ℝ := canonicalBallCutoff x₀ r R
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact canonicalBallCutoff_smooth x₀ hr.le hrr
  have hηcompact : HasCompactSupport η := by
    exact canonicalBallCutoff_hasCompactSupport hr.le hrr
  have hηnonneg : ∀ x, 0 ≤ η x := by
    intro x
    exact canonicalBallCutoff_nonneg x₀ r R x
  have hηle : ∀ x, η x ≤ 1 := by
    intro x
    exact canonicalBallCutoff_le_one x₀ r R x
  have hηone : ∀ x, x ∈ vec3Ball x₀ r → η x = 1 := by
    intro x hx
    apply canonicalBallCutoff_eq_one_on_inner hr.le hrr
    exact vec3Ball_subset_euclideanBall hr hx
  have hηsupport : tsupport η ⊆ euclideanBall x₀ R := by
    exact canonicalBallCutoff_tsupport_subset_outer hr.le hrr
  have hηΩ : tsupport η ⊆ Ω := by
    intro x hx
    have hxeu := hηsupport hx
    have hxclosed : x ∈ euclideanClosedBall x₀ R := by
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hxeu).le
    have hrectx : (x, t₁) ∈ euclideanClosedBall x₀ R ×ˢ Icc t₁ t₂ :=
      ⟨hxclosed, ⟨le_rfl, ht.le⟩⟩
    exact (hrect hrectx).1
  have ht₀ : t₁ < t₂ + h₀ := by linarith only [ht, hh₀]
  obtain ⟨θ, hθsmooth, hθcompact, hθI, hθnonneg, hθone⟩ :=
    smooth_time_envelope ht₀ ht₁I (show t₂ + h₀ ∈ I from hupperI)
      hsol.2.1 hsol.2.2.1
  have hψ : (fun z : Vec3 × ℝ => η z.1 * θ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I :=
    product_test_function hηsmooth hηcompact hηΩ hθsmooth hθcompact hθI
  have hψ_nonneg : ∀ z : Vec3 × ℝ, 0 ≤ η z.1 * θ z.2 := by
    intro z
    exact mul_nonneg (hηnonneg z.1) (hθnonneg z.2)
  have hψsupport : tsupport (fun z : Vec3 × ℝ => η z.1 * θ z.2) ⊆
      tsupport η ×ˢ tsupport θ := by
    have hsupp : Function.support (fun z : Vec3 × ℝ => η z.1 * θ z.2) =
        Function.support η ×ˢ Function.support θ := by
      ext z
      simp only [Function.mem_support, Set.mem_prod, mul_ne_zero_iff]
    rw [tsupport, tsupport, tsupport, hsupp, closure_prod_eq]
  let S : ℝ≥0∞ := essSup
    (timeSliceBallEnergy x₀ R · (fun w => vec3EuclideanNorm (u w)))
    (volume.restrict (Ioc t₁ t₂))
  have hS : S ≠ ⊤ := by
    exact ne_of_lt (sws_timeSliceBallEnergy_essSup_lt_top hsol hR ht hrect)
  have hSdef : S = essSup
      (timeSliceBallEnergy x₀ R · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc t₁ t₂)) := rfl
  have hEint := suitableWeakSolution_energy_integrable hsol hψ hψ_nonneg
  have hRint : Integrable
      (fun z : Vec3 × ℝ => localEnergyRhs u p f
        (fun w => η w.1 * θ w.2) z) volume := hEint.2.1
  have hRcompact : IsCompact (euclideanClosedBall x₀ R) :=
    isCompact_euclideanClosedBall x₀ hR.le
  let ω : ℝ → ℝ := fun h =>
    ∫ z in euclideanClosedBall x₀ R ×ˢ Icc (t₂ - h) (t₂ + h),
      |localEnergyRhs u p f (fun w => η w.1 * θ w.2) z|
  have hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [ω] using strip_error_tendsto hRcompact hRint
  have hsmall : ∀ᶠ h in (𝓝[>] (0 : ℝ)), h < h₀ ∧ h < t₂ - t₁ := by
    filter_upwards [
      (eventually_lt_nhds (sub_pos.mpr ht)).filter_mono
        nhdsWithin_le_nhds,
      (eventually_lt_nhds hh₀).filter_mono nhdsWithin_le_nhds] with h hht hh₀'
    exact ⟨hh₀', hht⟩
  have henergy := @alpha_usc_henergy_1 Ω I q u Du p f hsol x₀ r R t₁ t₂ hr hrr ht ε hh₀ hIext
    hηnonneg hηle hηone hηsupport hηΩ θ hθone hψ hψ_nonneg hψsupport hS hSdef hEint hsmall
  have hF_nonneg : ∀ᶠ h in (𝓝[>] (0 : ℝ)), 0 ≤
      (essSup
          (fun s => ENNReal.ofReal
            (∫ y in vec3Ball x₀ r,
              (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc t₁ (t₂ + h)))).toReal := by
    filter_upwards [] with h
    exact ENNReal.toReal_nonneg
  have hF_bounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
      (fun h : ℝ =>
        (essSup
          (fun s => ENNReal.ofReal
            (∫ y in vec3Ball x₀ r,
              (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc t₁ (t₂ + h)))).toReal) := by
    have hωone : ∀ᶠ h in (𝓝[>] (0 : ℝ)), ω h < 1 :=
      (tendsto_order.1 hω).2 1 (by norm_num)
    refine isBoundedUnder_of_eventually_le (a := S.toReal + 1) ?_
    filter_upwards [henergy, hωone] with h hh hωh
    linarith only [hh, hωh]
  have hco : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
      (fun h : ℝ =>
        (essSup
          (fun s => ENNReal.ofReal
            (∫ y in vec3Ball x₀ r,
              (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc t₁ (t₂ + h)))).toReal) :=
    isCoboundedUnder_le_of_eventually_le _ hF_nonneg
  rw [Filter.limsup_le_iff' hco hF_bounded]
  intro y hy
  have hdiff : 0 < y -
      (essSup
        (timeSliceBallEnergy x₀ R ·
          (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc t₁ t₂))).toReal := sub_pos.mpr hy
  have hωlt : ∀ᶠ h in (𝓝[>] (0 : ℝ)), ω h < y -
      (essSup
        (timeSliceBallEnergy x₀ R ·
          (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc t₁ t₂))).toReal :=
    (tendsto_order.1 hω).2 _ hdiff
  filter_upwards [henergy, hωlt] with h hF hωh
  nlinarith only [hF, hωh]

/-- Conditional form of `lem:alpha-usc`.

`F h` is the inner-ball time-slice essential supremum on the enlarged time
interval, `S` is the outer-ball essential supremum before the endpoint, and
`henergy` is the estimate obtained from the a.e.-time local energy inequality
and a product cutoff.  The conclusion is the paper's right-sided limsup
bound. -/
theorem alpha_usc_of_local_energy_inequality
    {F ω : ℝ → ℝ} {S : ℝ}
    (hF_nonneg : ∀ᶠ h in (𝓝[>] (0 : ℝ)), 0 ≤ F h)
    (hF_bounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F)
    (henergy : ∀ᶠ h in (𝓝[>] (0 : ℝ)), F h ≤ S + ω h)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Filter.limsup F (𝓝[>] (0 : ℝ)) ≤ S := by
  have hco : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F :=
    isCoboundedUnder_le_of_eventually_le _ hF_nonneg
  rw [Filter.limsup_le_iff' hco hF_bounded]
  intro y hy
  have hdiff : 0 < y - S := sub_pos.mpr hy
  have hωlt : ∀ᶠ h in (𝓝[>] (0 : ℝ)), ω h < y - S :=
    (tendsto_order.1 hω).2 (y - S) hdiff
  filter_upwards [henergy, hωlt] with h hF hωh
  nlinarith only [hF, hωh]

end CKN
