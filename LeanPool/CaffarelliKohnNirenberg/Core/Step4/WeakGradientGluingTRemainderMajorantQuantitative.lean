/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorant
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsAE

/-! # Quantitative time bounds for the fixed pressure remainder

The harmonic bound retains the kinetic energy of each time slice rather than
replacing it by its essential supremum in time. The calculus and integral
estimates are adapted from `CKN.Pressure.HarmonicPartBoundsAE`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

private lemma euclideanBall_eq_vec3Ball_harmonic {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change (x ∈ euclideanBall x₀ r) ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma vec3EuclideanNorm_le_sqrt_three (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i : Fin 3, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg v) (by positivity)).mp hsq

private lemma pressure_utensor_integral_le_two_energy_hGpow_1 :
    ∀ {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {x₀ : Vec3} {ρ s : ℝ},
      (0 : ℝ) < ρ →
        (c s = fun (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in vec3Ball x₀ ρ, u (y, s) j) →
          let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ);
          let F : Vec3 → L2Vec3 := fun (y : Vec3) => WithLp.toLp (2 : ℝ≥0∞) (u (y, s));
          Integrable F μ → average μ F = WithLp.toLp (2 : ℝ≥0∞) (c s)
    := by
  intro u c x₀ ρ s hρ hc μ F hFint
  have hvreal : volume.real (vec3Ball x₀ ρ) ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr
      ⟨ne_of_gt (volume_vec3Ball_pos hρ),
        (volume_vec3Ball_lt_top (x := x₀) (r := ρ)).ne⟩
  rw [MeasureTheory.average_eq, hc]
  apply PiLp.ext
  intro i
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) i :
      L2Vec3 →L[ℝ] ℝ) hFint
  simpa [F, μ, MeasureTheory.average_eq, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, hvreal]
    using hi.symm

private lemma pressure_utensor_integral_le_two_energy_hosc_2 :
    ∀ (μ : Measure Vec3) (F G : Vec3 → L2Vec3),
      (∫⁻ (y : Vec3), ‖G y‖ₑ ^ (2 : ℝ) ∂μ) / (μ : Set Vec3 → ℝ≥0∞) univ ≤
          (4 : ℝ≥0∞) * ((∫⁻ (y : Vec3), ‖F y‖ₑ ^ (2 : ℝ) ∂μ) / (μ : Set Vec3 → ℝ≥0∞) univ) →
        (μ : Set Vec3 → ℝ≥0∞) univ ≠ (0 : ℝ≥0∞) →
          (μ : Set Vec3 → ℝ≥0∞) univ ≠ ∞ →
            ∫⁻ (y : Vec3), ‖G y‖ₑ ^ (2 : ℝ) ∂μ ≤ (4 : ℝ≥0∞) * ∫⁻ (y : Vec3), ‖F y‖ₑ ^ (2 : ℝ) ∂μ
    := by
  intro μ F G hosc' hμne hμtop'
  calc
    _ = μ Set.univ *
        ((∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ) := by
      rw [ENNReal.mul_div_cancel hμne hμtop']
    _ ≤ μ Set.univ *
        ((4 : ℝ≥0∞) *
          ((∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ)) := by gcongr
    _ = (4 : ℝ≥0∞) * (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) := by
      calc
        μ Set.univ * (4 *
            ((∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ)) =
            4 * (μ Set.univ *
              ((∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ)) := by ring
        _ = 4 * (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) := by
          rw [ENNReal.mul_div_cancel hμne hμtop']

private lemma pressure_utensor_integral_le_two_energy_hprodle_3 :
    ∀ (μ : Measure Vec3) (F G : Vec3 → L2Vec3),
      (0 : ℝ) ≤ ∫ (y : Vec3), ‖F y‖ ^ (2 : ℕ) ∂μ →
        ∫ (y : Vec3), ‖G y‖ ^ (2 : ℕ) ∂μ ≤ (4 : ℝ) * ∫ (y : Vec3), ‖F y‖ ^ (2 : ℕ) ∂μ →
          ∫ (y : Vec3), ‖F y‖ * ‖G y‖ ∂μ ≤
              (∫ (y : Vec3), ‖F y‖ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
                (∫ (y : Vec3), ‖G y‖ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) →
            ∫ (y : Vec3), ‖F y‖ * ‖G y‖ ∂μ ≤ (2 : ℝ) * ∫ (y : Vec3), ‖F y‖ ^ (2 : ℕ) ∂μ
    := by
  intro μ F G hFnonneg hGle hholder'
  calc
    _ ≤ (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫ y, (‖G y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := hholder'
    _ ≤ (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
        (4 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
      gcongr
    _ = 2 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ := by
      have hroot :
          (4 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) =
            2 * (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hFnonneg]
        norm_num
      rw [hroot]
      calc
        _ = 2 * ((∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^
            (1 / 2 : ℝ) *
            (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by
          by_cases hI : (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) = 0
          · simp [hI]
          · rw [← Real.rpow_add
              (lt_of_le_of_ne hFnonneg (Ne.symm hI))]
            norm_num

private lemma pressure_utensor_integral_le_two_energy
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {x₀ : Vec3}
    {ρ s : ℝ} (hρ : 0 < ρ)
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ)))
    (hc : c s = fun j : Fin 3 =>
      average (volume.restrict (vec3Ball x₀ ρ)) (fun y : Vec3 => u (y, s) j)) :
    ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y ≤
      2 * ∫ y in vec3Ball x₀ ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  let F : Vec3 → L2Vec3 := fun y => WithLp.toLp 2 (u (y, s))
  let cvec : Vec3 := c s
  let G : Vec3 → L2Vec3 := fun y => F y - WithLp.toLp 2 cvec
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, s))
  let gv : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, s) - cvec)
  have hμpos : 0 < μ Set.univ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      volume_vec3Ball_pos hρ
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      volume_vec3Ball_lt_top (x := x₀) (r := ρ)
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have humeas' : AEStronglyMeasurable (fun y : Vec3 => u (y, s)) μ :=
    humeas.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable F μ := by
    have hcont : Continuous (fun v : Vec3 => WithLp.toLp 2 v) := by
      exact PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 3 => ℝ)
    exact hcont.comp_aestronglyMeasurable humeas'
  have hF : MemLp F 2 μ := by
    apply hu.of_le_mul hFmeas
    on_goal 1 => filter_upwards [] with y
    simpa [F, vec3EuclideanNorm_eq_l2] using
      vec3EuclideanNorm_le_sqrt_three (u (y, s))
  have hGmeas : AEStronglyMeasurable G μ := by
    exact hFmeas.sub measurable_const.aestronglyMeasurable
  have hG : MemLp G 2 μ := by
    apply hF.sub (memLp_const (WithLp.toLp 2 cvec))
  have hFint : Integrable F μ := hF.integrable (by norm_num)
  have hFpow : Integrable (fun y => ‖F y‖ ^ (2 : ℝ)) μ :=
    hF.integrable_norm_rpow (by norm_num) (by norm_num)
  have hGpow : Integrable (fun y => ‖G y‖ ^ (2 : ℝ)) μ :=
    hG.integrable_norm_rpow (by norm_num) (by norm_num)
  have hmeanF := @pressure_utensor_integral_le_two_energy_hGpow_1 u c x₀ ρ s hρ hc hFint
  have hmeanF' : (⨍ y in vec3Ball x₀ ρ, F y ∂volume) =
      WithLp.toLp 2 (c s) := by
    change average μ F = WithLp.toLp 2 (c s)
    exact hmeanF
  have hosc := setLaverage_norm_sub_setAverage_rpow_le
    (μ := volume) (s := vec3Ball x₀ ρ) (f := F) (p := (2 : ℝ))
    (c := (0 : L2Vec3)) (by norm_num)
    (volume_vec3Ball_pos hρ) (volume_vec3Ball_lt_top (x := x₀) (r := ρ))
    (by simpa [IntegrableOn, μ] using hFint)
    (by simpa [IntegrableOn, μ] using hFpow)
  have hosc' :
      (∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ ≤
        (4 : ℝ≥0∞) *
          ((∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) / μ Set.univ) := by
    have h := hosc
    rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at h
    rw [hmeanF'] at h
    norm_num at h
    simpa [G, cvec, μ, sub_zero, ENNReal.rpow_two] using h
  have hFpow' : Integrable (fun y => (‖F y‖ : ℝ) ^ (2 : ℕ)) μ := by
    convert hFpow using 1
    ext y
    norm_num [Real.rpow_natCast]
  have hGpow' : Integrable (fun y => (‖G y‖ : ℝ) ^ (2 : ℕ)) μ := by
    convert hGpow using 1
    ext y
    norm_num [Real.rpow_natCast]
  have hFto :
      (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) =
        ENNReal.ofReal (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal ((‖F y‖ : ℝ) ^ (2 : ℕ)) ∂μ := by
        apply lintegral_congr
        intro y
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg (F y))]
        norm_num [Real.rpow_natCast]
      _ = _ := (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFpow'
        (Eventually.of_forall fun y => pow_nonneg (norm_nonneg _) 2)).symm
  have hGto :
      (∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂μ) =
        ENNReal.ofReal (∫ y, (‖G y‖ : ℝ) ^ (2 : ℕ) ∂μ) := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal ((‖G y‖ : ℝ) ^ (2 : ℕ)) ∂μ := by
        apply lintegral_congr
        intro y
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg (G y))]
        norm_num [Real.rpow_natCast]
      _ = _ := (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGpow'
        (Eventually.of_forall fun y => pow_nonneg (norm_nonneg _) 2)).symm
  have hμne : μ Set.univ ≠ 0 := ne_of_gt hμpos
  have hμtop' : μ Set.univ ≠ ∞ := ne_of_lt hμtop
  have hosc'' := @pressure_utensor_integral_le_two_energy_hosc_2 μ F G hosc' hμne hμtop'
  have hFnonneg : 0 ≤ ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ :=
    integral_nonneg fun y => pow_nonneg (norm_nonneg _) _
  have hGnonneg : 0 ≤ ∫ y, (‖G y‖ : ℝ) ^ (2 : ℕ) ∂μ :=
    integral_nonneg fun y => pow_nonneg (norm_nonneg _) _
  have hGle :
      (∫ y, (‖G y‖ : ℝ) ^ (2 : ℕ) ∂μ) ≤
        4 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ := by
    have hFtop : (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ := by
      rw [hFto]
      exact ENNReal.ofReal_ne_top
    have hRtop : (4 : ℝ≥0∞) *
        (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ :=
      (ENNReal.mul_lt_top (by norm_num)
        (lt_top_iff_ne_top.mpr hFtop)).ne
    have h := ENNReal.toReal_mono hRtop hosc''
    rw [hGto, hFto, ENNReal.toReal_mul] at h
    simpa [ENNReal.toReal_ofReal hGnonneg, ENNReal.toReal_ofReal hFnonneg] using h
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hF' : MemLp F (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hF
  have hG' : MemLp G (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hG
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) h22 hF' hG'
  have hholder' :
      ∫ y, (‖F y‖ : ℝ) * ‖G y‖ ∂μ ≤
        (∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ y, (‖G y‖ : ℝ) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    convert hholder using 1
    all_goals norm_num [Real.rpow_natCast]
  have hprodle := @pressure_utensor_integral_le_two_energy_hprodle_3 μ F G hFnonneg hGle hholder'
  have hUnorm : ∀ y, pressureUTensorNorm u c s y = gu y * gv y := by
    intro y
    have hmf : meanFreeVec u x₀ ρ s y = u (y, s) - c s := by
      funext j
      dsimp [meanFreeVec, meanFreeComponent]
      rw [hc]
    have hpt := utensorNorm_eq u x₀ ρ s y
    rw [hmf] at hpt
    change Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (-u (y, s) i * (u (y, s) j - c s j)) ^ (2 : ℕ)) = gu y * gv y
    rw [hc]
    simpa [utensorNorm, utensor, meanFreeVec, meanFreeComponent,
      gu, gv, cvec] using hpt
  have hFG : ∀ y, ‖F y‖ * ‖G y‖ = gu y * gv y := by
    intro y
    rw [show ‖F y‖ = gu y by
      change ‖WithLp.toLp 2 (u (y, s))‖ = vec3EuclideanNorm (u (y, s))
      rw [vec3EuclideanNorm_eq_l2]]
    rw [show ‖G y‖ = gv y by
      simp [G, F, gv, cvec, vec3EuclideanNorm_eq_l2]]
  have henergy :
      ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ =
        ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) := by
    apply integral_congr_ae
    filter_upwards [] with y
    simp [F, vec3EuclideanNorm_eq_l2]
  rw [show ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y =
      ∫ y, pressureUTensorNorm u c s y ∂μ by rfl]
  rw [show ∫ y, pressureUTensorNorm u c s y ∂μ =
      ∫ y, gu y * gv y ∂μ by
        apply integral_congr_ae
        exact Eventually.of_forall hUnorm]
  calc
    ∫ y, gu y * gv y ∂μ = ∫ y, (‖F y‖ : ℝ) * ‖G y‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => (hFG y).symm)
    _ ≤ 2 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ := hprodle
    _ = 2 * ∫ y in vec3Ball x₀ ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) := by rw [henergy]

/-- The harmonic estimate with the actual slice energy, before taking any time supremum. -/
theorem exists_harmonicPressurePart_Ck_slice_energy_of_sws :
    ∀ k : ℕ, ∃ C₁₆ : ℝ, 0 ≤ C₁₆ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
        (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
        {z : ParabolicPoint} {ρ : ℝ},
        (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖iteratedFDeriv ℝ k
                (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y : Vec3 => u (y, t) j)) p s) x‖ ≤
              C₁₆ * ρ ^ (-(2 + k : ℝ)) *
                (((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) / ρ) +
                  ((∫ y in vec3Ball z.1 ρ, |p (y, s)|) /
                    ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ))) := by
  intro k
  obtain ⟨C₁₆, hC₁₆, hbound⟩ := exists_harmonicPressurePart_Ck_constant k
  refine ⟨C₁₆, hC₁₆, ?_⟩
  intro Ω I q u Du p f hsol z ρ hρ hsub
  let c : ℝ → Vec3 := fun t j =>
    average (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
  have hdata := pressure_harmonic_potential_data_ae_of_sws_inner hsol hρ hsub
  have hp := sws_pressure_memLp_slice_ae hsol hρ hsub
  filter_upwards [hslices', hdata, hp] with s hs hdat hps
  have hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hs.1.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball z.1 ρ)) := hu.aestronglyMeasurable.aemeasurable
  have hUint := pressure_utensor_integrable_on_ball (c := c) hρ humeas hu
  have hUenergy := pressure_utensor_integral_le_two_energy (c := c) hρ humeas hu (by
    rfl : c s = fun j : Fin 3 =>
      average (volume.restrict (vec3Ball z.1 ρ))
        (fun y : Vec3 => u (y, s) j))
  have hE0 : 0 ≤ ∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) :=
    integral_nonneg (fun y => sq_nonneg _)
  have hUbound : ∫ y in vec3Ball z.1 ρ, pressureUTensorNorm u c s y ≤
      2 * ρ * ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) / ρ) := by
    convert hUenergy using 1
    field_simp
  let _ : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := z.1) (r := ρ))
  have hpInt : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball z.1 ρ)) :=
    (hps.integrable (by norm_num)).norm
  have hk : 0 < (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ := by positivity
  have hP0 : 0 ≤ ∫ y in vec3Ball z.1 ρ, |p (y, s)| :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hPbound : ∫ y in vec3Ball z.1 ρ, |p (y, s)| ≤
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ *
        ((∫ y in vec3Ball z.1 ρ, |p (y, s)|) /
          ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ)) := by
    rw [mul_div_cancel₀ _ hk.ne']
  have hdat' : PressureHarmonicPotentialData
      (vec3Ball z.1 (13 * ρ / 20)) (mollifiedBallCutoff z.1 hρ) u c p s := by
    have heq := euclideanBall_eq_vec3Ball_harmonic
      (x₀ := z.1) (r := 13 * ρ / 20) (by positivity)
    rw [heq] at hdat
    simpa [c] using hdat
  have hpoint := hbound
    (η := mollifiedBallCutoff z.1 hρ) (u := u) (c := c) (p := p) (s := s)
    (x₀ := z.1) (ρ := ρ) hρ hdat' rfl
    (fun y hy => by
      have houter := euclideanBall_eq_vec3Ball_harmonic
        (x₀ := z.1) (r := 3 * ρ / 4) (by positivity)
      have hinner := euclideanBall_eq_vec3Ball_harmonic
        (x₀ := z.1) (r := 13 * ρ / 20) (by positivity)
      have hyann : y ∉
          euclideanBall z.1 (3 * ρ / 4) \
            euclideanClosedBall z.1 (13 * ρ / 20) := by
        intro hyann
        apply hy
        constructor
        · rw [← houter]
          exact hyann.1
        · intro hyinner
          apply hyann.2
          apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
            (by positivity)).2
          have hyinner' : y ∈ euclideanBall z.1 (13 * ρ / 20) := by
            rw [hinner]
            exact hyinner
          exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt
            (by positivity)).1 hyinner').le
      have hz := pressure_cutoff_derivatives_vanish z.1 hρ hyann
      refine ⟨hz.1, hz.2, ?_⟩
      simp only [spatialLaplacian]
      rw [Finset.sum_eq_zero]
      intro i hi
      exact hz.2 i i)
    hUint hpInt (((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) / ρ))
    ((∫ y in vec3Ball z.1 ρ, |p (y, s)|) /
      ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ)) (div_nonneg hE0 hρ.le) (div_nonneg hP0 hk.le)
    hUbound hPbound
  simpa [c] using hpoint


private theorem integral_power_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (a : ℝ) :
    (∫⁻ y, g y ^ a ∂μ) ^ (3/2 : ℝ) ≤
      μ Set.univ ^ (1/2 : ℝ) * ∫⁻ y, g y ^ (a * (3/2)) ∂μ := by
  have hpq : (3/2 : ℝ).HolderConjugate 3 := by constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hg.pow_const a) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [← ENNReal.rpow_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  norm_num at h
  have ht := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at ht
  norm_num at ht
  simpa only [mul_comm] using ht

private theorem slice_integral_power_bound {B : Set Vec3} {J : Set ℝ}
    {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict J))) (a : ℝ) :
    AEMeasurable (fun s => ∫⁻ y in B, F (y,s) ^ a) (volume.restrict J) ∧
    (∫⁻ s in J, (∫⁻ y in B, F (y,s) ^ a) ^ (3/2 : ℝ)) ≤
      volume B ^ (1/2 : ℝ) * ∫⁻ w in B ×ˢ J, F w ^ (a * (3/2)) := by
  refine ⟨(hF.pow_const a).lintegral_prod_left', ?_⟩
  calc
    _ ≤ ∫⁻ s in J, volume B ^ (1/2 : ℝ) *
        ∫⁻ y in B, F (y,s) ^ (a * (3/2)) := by
      apply lintegral_mono_ae
      filter_upwards [hF.aestronglyMeasurable.prodMk_right] with s hs
      simpa only [Measure.restrict_apply_univ] using integral_power_le (volume.restrict B)
        hs.aemeasurable a
    _ = _ := by
      rw [lintegral_const_mul'' _ ((hF.pow_const _).lintegral_prod_left'),
        ← lintegral_prod_symm _ (hF.pow_const _), Measure.prod_restrict]
      rfl

private theorem three_terms_power_bound (a b c : ℝ≥0∞) :
    (a + b + c) ^ (3/2 : ℝ) ≤
      16 * (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) := by
  have htwo : (2 : ℝ≥0∞) ^ (3/2 : ℝ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have h (x y : ℝ≥0∞) : (x+y) ^ (3/2 : ℝ) ≤ 4 *
      (x ^ (3/2 : ℝ) + y ^ (3/2 : ℝ)) :=
    (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow x y (by norm_num)).trans
      (mul_le_mul' htwo le_rfl)
  calc
    _ ≤ 4 * ((a+b) ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) := h _ _
    _ ≤ 4 * (4 * (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ)) + 4 * c ^ (3/2 : ℝ)) :=
      mul_le_mul' le_rfl (add_le_add (h _ _) (le_mul_of_one_le_left' (by norm_num)))
    _ = _ := by ring

/-- The three coefficients of the slice-energy, pressure, and force integrals. -/
def fixedRemainderCoefficients (C ρ : ℝ) : Fin 3 → ℝ≥0∞ := ![
  ENNReal.ofReal (C * ρ ^ (-3 : ℝ) / ρ),
  ENNReal.ofReal (C * ρ ^ (-3 : ℝ) / ((Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ)),
  ENNReal.ofReal |400 * sliceForcePotentialConstant * (cutoffGradientConstant / ρ) * (ρ ^ 2)⁻¹|]

/-- A fixed-collar remainder majorant retaining the actual energy of each slice. -/
def fixedRemainderSliceMajorant (C ρ : ℝ) (x : Vec3)
    (u f : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (s : ℝ) : ℝ≥0∞ :=
  fixedRemainderCoefficients C ρ 0 *
      (∫⁻ y in vec3Ball x ρ, ENNReal.ofReal (vec3EuclideanNorm (u (y,s))) ^ (2 : ℝ)) +
    fixedRemainderCoefficients C ρ 1 *
      (∫⁻ y in vec3Ball x ρ, ENNReal.ofReal |p (y,s)|) +
    fixedRemainderCoefficients C ρ 2 *
      (∫⁻ y in vec3Ball x ρ, ENNReal.ofReal (vec3EuclideanNorm (f (y,s))))

/-- An explicit coefficient for the `3/2` time moment on a fixed collar. -/
def fixedRemainderMomentConstant (C ρ : ℝ) (x : Vec3) : ℝ≥0∞ :=
  16 * volume (vec3Ball x ρ) ^ (1/2 : ℝ) *
    (fixedRemainderCoefficients C ρ 0 ^ (3/2 : ℝ) +
      fixedRemainderCoefficients C ρ 1 ^ (3/2 : ℝ) +
      fixedRemainderCoefficients C ρ 2 ^ (3/2 : ℝ)) *
    (volume (parabolicCylinder (0 : Vec3) 0 1) + 1)

private theorem three_slice_mass_bound {B : Set Vec3} {J : Set ℝ}
    {U P F : Vec3 × ℝ → ℝ≥0∞}
    (hU : AEMeasurable U ((volume.restrict B).prod (volume.restrict J)))
    (hP : AEMeasurable P ((volume.restrict B).prod (volume.restrict J)))
    (hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict J)))
    (a b c D : ℝ≥0∞)
    (hUD : (∫⁻ w in B ×ˢ J, U w ^ (3 : ℝ)) ≤ D)
    (hPD : (∫⁻ w in B ×ˢ J, P w ^ (3 / 2 : ℝ)) ≤ D)
    (hFD : (∫⁻ w in B ×ˢ J, F w ^ (3 / 2 : ℝ)) ≤ D) :
    let M := fun s => a * (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) +
      b * (∫⁻ y in B, P (y,s)) + c * (∫⁻ y in B, F (y,s))
    AEMeasurable M (volume.restrict J) ∧
    (∫⁻ s in J, M s ^ (3/2 : ℝ)) ≤
      16 * volume B ^ (1/2 : ℝ) *
        (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) * D := by
  have hu := slice_integral_power_bound hU 2
  have hp := slice_integral_power_bound hP 1
  have hf := slice_integral_power_bound hF 1
  norm_num only [one_mul, ENNReal.rpow_one, show (2 : ℝ) * (3/2) = 3 by norm_num] at hu hp hf
  refine ⟨((aemeasurable_const.mul hu.1).add (aemeasurable_const.mul hp.1)).add
    (aemeasurable_const.mul hf.1), ?_⟩
  dsimp only
  calc
    _ ≤ ∫⁻ s in J, 16 *
        ((a * (∫⁻ y in B, U (y,s) ^ (2 : ℝ))) ^ (3/2 : ℝ) +
          (b * (∫⁻ y in B, P (y,s))) ^ (3/2 : ℝ) +
          (c * (∫⁻ y in B, F (y,s))) ^ (3/2 : ℝ)) :=
      lintegral_mono (fun _ => three_terms_power_bound _ _ _)
    _ = 16 * (a ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) ^ (3/2 : ℝ)) +
        b ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) +
        c ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, F (y,s)) ^ (3/2 : ℝ))) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/2)]
      have ha : AEMeasurable (fun s => a ^ (3/2 : ℝ) *
          (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) ^ (3/2 : ℝ)) (volume.restrict J) :=
        aemeasurable_const.mul (hu.1.pow_const _)
      have hb : AEMeasurable (fun s => b ^ (3/2 : ℝ) *
          (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) (volume.restrict J) :=
        aemeasurable_const.mul (hp.1.pow_const _)
      simp only [ENNReal.rpow_ofNat] at ha hb ⊢
      have hab : AEMeasurable (fun s =>
          a ^ (3/2 : ℝ) * (∫⁻ y in B, U (y,s) ^ (2 : ℕ)) ^ (3/2 : ℝ) +
          b ^ (3/2 : ℝ) * (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) (volume.restrict J) := ha.add hb
      have hum : AEMeasurable (fun s => (∫⁻ y in B, U (y,s) ^ (2 : ℕ)) ^ (3/2 : ℝ))
          (volume.restrict J) := by simpa only [ENNReal.rpow_ofNat] using hu.1.pow_const (3/2 : ℝ)
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hab,
        lintegral_add_left' ha, lintegral_const_mul'' _ hum,
        lintegral_const_mul'' _ (hp.1.pow_const (3/2 : ℝ)), lintegral_const_mul'' _
          (hf.1.pow_const (3/2 : ℝ))]
    _ ≤ 16 * (a ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D) +
        b ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D) +
        c ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D)) := by
      gcongr
      · exact hu.2.trans (mul_le_mul' le_rfl hUD)
      · exact hp.2.trans (mul_le_mul' le_rfl hPD)
      · exact hf.2.trans (mul_le_mul' le_rfl hFD)
    _ = _ := by ring

/-- The refined remainder majorant has an explicit moment linear in the unit data size. -/
theorem fixed_remainder_slice_majorant_moment_of_sws
    (C ε : ℝ) {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {z : ParabolicPoint} {ρ : ℝ}
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1) :
    AEMeasurable (fixedRemainderSliceMajorant C ρ z.1 u f p)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
      fixedRemainderSliceMajorant C ρ z.1 u f p s ^ (3/2 : ℝ)) ≤
      fixedRemainderMomentConstant C ρ z.1 * (ENNReal.ofReal ε + 1) := by
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2 - ρ ^ 2) z.2
  let V := volume (parabolicCylinder (0 : Vec3) 0 1)
  let U := fun w : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u w))
  let P := fun w : Vec3 × ℝ => ENNReal.ofReal |p w|
  let F := fun w : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (f w))
  obtain ⟨Ω', J', hbox, hsub⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 Ω' J' hbox
  have hlocal : B ×ˢ J ⊆ spaceTimeSet Ω' J' := hQ.trans hsub
  have hU : AEMeasurable U ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hd.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume hlocal)
  have hP : AEMeasurable P ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_abs.comp_aestronglyMeasurable
      hd.2.2.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume hlocal)
  have hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hd.2.2.2.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume hlocal)
  have hUε : (∫⁻ w in B ×ˢ J, U w ^ (3 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono (fun _ =>
      (le_add_right le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hPε : (∫⁻ w in B ×ˢ J, P w ^ (3/2 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono (fun _ =>
      (le_add_left le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hFε : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1, F w ^ q) ≤ ENNReal.ofReal ε :=
    (lintegral_mono (fun _ => le_add_left le_rfl)).trans hsmall
  have hFD : (∫⁻ w in B ×ˢ J, F w ^ (3/2 : ℝ)) ≤ V + ENNReal.ofReal ε := by
    apply (lintegral_mono_set hQ).trans
    calc
      _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1, 1 + F w ^ q := by
        apply lintegral_mono
        intro w
        by_cases hw : F w ≤ 1
        · exact (ENNReal.rpow_le_one hw (by norm_num)).trans le_self_add
        · exact (ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hw)
            (by linarith only [hsol.2.2.2.1] : (3/2 : ℝ) ≤ q)).trans le_add_self
      _ ≤ _ := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
          Measure.restrict_apply_univ]
        exact add_le_add le_rfl hFε
  have h := three_slice_mass_bound hU hP hF
    (fixedRemainderCoefficients C ρ 0) (fixedRemainderCoefficients C ρ 1)
    (fixedRemainderCoefficients C ρ 2) (V + ENNReal.ofReal ε)
    (hUε.trans le_add_self) (hPε.trans le_add_self) hFD
  refine ⟨h.1, h.2.trans ?_⟩
  have he : V + ENNReal.ofReal ε ≤ (V+1) * (ENNReal.ofReal ε + 1) := by
    calc
      _ ≤ (V+1) * 1 + (V+1) * ENNReal.ofReal ε :=
        add_le_add (by simp only [mul_one]; exact le_self_add)
          (le_mul_of_one_le_left' le_add_self)
      _ = _ := by ring
  exact (mul_le_mul' le_rfl he).trans_eq (mul_assoc _ _ _).symm

private theorem ofReal_integral_le_mass (B : Set Vec3) (g : Vec3 → ℝ) :
    ENNReal.ofReal (∫ y in B, g y) ≤ ∫⁻ y in B, ENNReal.ofReal |g y| := by
  have h := enorm_integral_le_lintegral_enorm (μ := volume.restrict B) g
  simp only [Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans h

/-- A universal harmonic constant gives a quantitative majorant for the actual fixed remainder. -/
theorem exists_fixed_remainder_quantitative_majorant :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
        {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ/2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤
              fixedRemainderSliceMajorant C ρ z.1 u f p s := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicPressurePart_Ck_slice_energy_of_sws 1
  refine ⟨C, hC, ?_⟩
  intro Ω I q u f Du p hsol z ρ hρ hsub
  have hhar := hbound hsol hρ hsub
  have hreg := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  have hforce := slice_force_source_data_ae_of_sws hsol hρ hsub
  filter_upwards [hhar, hreg, hforce] with s hhs hrs hfs
  intro i x hx
  let B := vec3Ball z.1 ρ
  let η := mollifiedBallCutoff z.1 hρ
  let h := harmonicPressurePart η u (sourceSliceCentredMean z.1 ρ u) p s
  let v := pressureP8 η f s
  let Ch := C * ρ ^ (-3 : ℝ)
  let kp := (Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ
  let Cf := 400 * sliceForcePotentialConstant * (cutoffGradientConstant / ρ) * (ρ ^ 2)⁻¹
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  have hkp : 0 < kp := by dsimp [kp]; positivity
  have hE : 0 ≤ ∫ y in B, vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hP : 0 ≤ ∫ y in B, |p (y,s)| := integral_nonneg (fun _ => abs_nonneg _)
  rw [euclideanBall_eq_vec3Ball_harmonic (by positivity : 0 < ρ/2)] at hrs
  have hd₁ := hrs.differentiableOn_one.differentiableAt ((isOpen_vec3Ball _ _).mem_nhds hx)
  have hd₂ := (contDiffOn_pressureP8_halfBall hρ hfs.2.2.1).differentiableOn_one.differentiableAt
    ((isOpen_vec3Ball _ _).mem_nhds hx)
  have hgrad : classicalGradient (h+v) x i = classicalGradient h x i + classicalGradient v x i :=
    congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (hd₁.hasFDerivAt.add hd₂.hasFDerivAt).fderiv
  have hhb : ‖classicalGradient h x i‖ₑ ≤
      fixedRemainderCoefficients C ρ 0 *
        (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (u (y,s))) ^ (2 : ℝ)) +
      fixedRemainderCoefficients C ρ 1 * (∫⁻ y in B, ENNReal.ofReal |p (y,s)|) := by
    have hh := hhs x hx
    rw [norm_iteratedFDeriv_one] at hh
    norm_num only [Nat.cast_one, show -(2 + (1 : ℝ)) = -3 by norm_num] at hh
    have hi : ‖classicalGradient h x i‖ ≤ ‖fderiv ℝ h x‖ :=
      ((fderiv ℝ h x).le_opNorm (basisVec i)).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_basisVec_le_one i))
    have hb : ‖classicalGradient h x i‖ ≤
        (Ch/ρ) * (∫ y in B, vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ)) +
        (Ch/kp) * (∫ y in B, |p (y,s)|) := by
      apply (hi.trans hh).trans_eq
      dsimp only [Ch, kp, B]
      ring
    rw [← ofReal_norm]
    apply (ENNReal.ofReal_le_ofReal hb).trans
    rw [ENNReal.ofReal_add (mul_nonneg (div_nonneg hCh hρ.le) hE)
      (mul_nonneg (div_nonneg hCh hkp.le) hP),
      ENNReal.ofReal_mul (div_nonneg hCh hρ.le), ENNReal.ofReal_mul (div_nonneg hCh hkp.le)]
    apply add_le_add (mul_le_mul' le_rfl _) (mul_le_mul' le_rfl _)
    · apply (ofReal_integral_le_mass B (fun y => vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ))).trans_eq
      apply lintegral_congr
      intro y
      rw [abs_of_nonneg (sq_nonneg _), ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
        ENNReal.rpow_ofNat]
    · simpa only [abs_abs] using ofReal_integral_le_mass B (fun y => |p (y,s)|)
  have hA : 0 ≤ (cutoffGradientConstant / ρ) * ∫ y in B, vec3EuclideanNorm (f (y,s)) :=
    mul_nonneg ((vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound z.1 hρ z.1))
      (integral_nonneg (fun _ => vec3EuclideanNorm_nonneg _))
  have hp8 := vec3EuclideanNorm_classicalGradient_pressureP8_le hρ hA hfs.2.2.1 hfs.2.2.2 hx
  have hvb : ‖classicalGradient v x i‖ₑ ≤ fixedRemainderCoefficients C ρ 2 *
      (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (f (y,s)))) := by
    have hb : |classicalGradient v x i| ≤ Cf * ∫ y in B, vec3EuclideanNorm (f (y,s)) := by
      have ht := (abs_apply_le_vec3EuclideanNorm _ i).trans hp8
      dsimp only [Cf, B, v, η]
      nlinarith only [ht]
    have hb' := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self Cf)
      (integral_nonneg (fun _ => vec3EuclideanNorm_nonneg _)))
    rw [Real.enorm_eq_ofReal_abs]
    apply (ENNReal.ofReal_le_ofReal hb').trans
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    apply mul_le_mul' le_rfl
    simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
      ofReal_integral_le_mass B (fun y => vec3EuclideanNorm (f (y,s)))
  change ‖classicalGradient (h+v) x i‖ₑ ≤ _
  rw [hgrad]
  exact (enorm_add_le _ _).trans (add_le_add hhb hvb)

/-- The explicit moment coefficient is finite for every fixed real collar radius. -/
theorem fixedRemainderMomentConstant_lt_top (C ρ : ℝ) (x : Vec3) :
    fixedRemainderMomentConstant C ρ x < ⊤ := by
  have hc (i : Fin 3) : fixedRemainderCoefficients C ρ i < ⊤ := by
    fin_cases i <;> exact ENNReal.ofReal_lt_top
  have hp (i : Fin 3) := ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/2) (hc i).ne
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) Integration.volume_vec3Ball_lt_top.ne))
    (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hp 0, hp 1⟩, hp 2⟩))
    (ENNReal.add_lt_top.mpr ⟨Integration.volume_parabolicCylinder_lt_top, by norm_num⟩)

private theorem lower_moment_le {J : Set ℝ} (M : ℝ → ℝ≥0∞) :
    (∫⁻ s in J, M s ^ (6/5 : ℝ)) ≤ volume J + ∫⁻ s in J, M s ^ (3/2 : ℝ) := by
  calc
    _ ≤ ∫⁻ s in J, 1 + M s ^ (3/2 : ℝ) := by
      apply lintegral_mono
      intro s
      by_cases hs : M s ≤ 1
      · exact (ENNReal.rpow_le_one hs (by norm_num)).trans le_self_add
      · exact (ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hs)
          (by norm_num)).trans le_add_self
    _ = _ := by rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
      Measure.restrict_apply_univ]

/-- Every clipped time window obeys the explicit `6/5` remainder bound. -/
theorem fixed_remainder_clipped_moment_of_sws
    (C ε : ℝ) {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {z : ParabolicPoint} {ρ : ℝ}
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1) (T : Set ℝ) :
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2 ∩ T,
      fixedRemainderSliceMajorant C ρ z.1 u f p s ^ (6/5 : ℝ)) ≤
      (ENNReal.ofReal (ρ ^ 2) + fixedRemainderMomentConstant C ρ z.1) *
        (ENNReal.ofReal ε + 1) := by
  have h := (fixed_remainder_slice_majorant_moment_of_sws C ε hsol hdom hsmall hQ).2
  apply (lintegral_mono_set inter_subset_left).trans
  apply (lower_moment_le _).trans
  have hv : volume (Ioc (z.2 - ρ ^ 2) z.2) = ENNReal.ofReal (ρ ^ 2) := by
    rw [Real.volume_Ioc]
    congr 1
    ring
  rw [hv, add_mul]
  exact add_le_add (le_mul_of_one_le_right' le_add_self) h

end CKN.Core.Step4
