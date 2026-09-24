/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBounds
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice

/-!
# Harmonic Part Bounds AE

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat

noncomputable section

namespace CKN

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
  haveI : IsFiniteMeasure μ := ⟨hμtop⟩
  have humeas' : AEStronglyMeasurable (fun y : Vec3 => u (y, s)) μ :=
    humeas.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable F μ := by
    have hcont : Continuous (fun v : Vec3 => WithLp.toLp 2 v) := by
      exact PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 3 => ℝ)
    exact hcont.comp_aestronglyMeasurable humeas'
  have hF : MemLp F 2 μ := by
    apply hu.of_le_mul hFmeas
    filter_upwards [] with y
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
  have hmeanF : average μ F = WithLp.toLp 2 (c s) := by
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
  have hosc'' :
      (∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂μ) ≤
        (4 : ℝ≥0∞) * (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) ∂μ) := by
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
  have hprodle :
      (∫ y, (‖F y‖ : ℝ) * ‖G y‖ ∂μ) ≤
        2 * ∫ y, (‖F y‖ : ℝ) ^ (2 : ℕ) ∂μ := by
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

private lemma harmonic_integral_mul_le_volume_rpow {μ : Measure Vec3}
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

private lemma harmonic_pressure_integral_eq_lpNorm_rpow
    {f : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ}
    (_ : 0 < r) (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ r))) :
    (∫ x in vec3Ball x₀ r, |f x| ^ (3 / 2 : ℝ)) =
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball x₀ r)) ^ (3 / 2 : ℝ) := by
  have h := integral_rpow_norm_eq_lpNorm_rpow
    (p := ENNReal.ofReal (3 / 2 : ℝ))
    (μ := volume.restrict (vec3Ball x₀ r))
    (hp0 := by norm_num) (hpTop := by norm_num) hf
  have hexp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
    norm_num
  simpa only [hexp, Real.norm_eq_abs] using h

private lemma harmonic_pressure_integral_le_lpNorm
    {f : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ r))) :
    ∫ x in vec3Ball x₀ r, |f x| ≤
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * r *
        lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball x₀ r)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ r)
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      volume_vec3Ball_lt_top (x := x₀) (r := r)
  haveI : IsFiniteMeasure μ := ⟨hμtop⟩
  have hfmeas : AEMeasurable (fun x : Vec3 => |f x|) μ :=
    (continuous_abs.comp_aestronglyMeasurable hf.aestronglyMeasurable).aemeasurable
  have hfint : Integrable (fun x : Vec3 => |f x|) μ := by
    have h := (hf.integrable (by norm_num)).norm
    simpa only [μ, Real.norm_eq_abs] using h
  have hfpow : Integrable (fun x : Vec3 => |f x| ^ (3 / 2 : ℝ)) μ := by
    have h := hf.integrable_norm_rpow (by norm_num) (by norm_num)
    have hexp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
      norm_num
    simpa only [μ, Real.norm_eq_abs, hexp] using h
  have hfin : ∫⁻ x, ENNReal.ofReal (((1 : ℝ) * |f x|) ^
      (3 / 2 : ℝ)) ∂μ < ⊤ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable
      hfpow.aestronglyMeasurable (Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg _) _)).2 hfpow
    exact lt_top_iff_ne_top.mpr (by simpa only [one_mul] using h)
  have hsp := harmonic_integral_mul_le_volume_rpow
    (μ := μ) (f := fun _ : Vec3 => (1 : ℝ)) (g := fun x => |f x|)
    aemeasurable_const hfmeas (fun _ => by norm_num) (fun x => abs_nonneg _)
    hfin
  have hvol : (μ Set.univ).toReal ^ (1 / 3 : ℝ) =
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * r := by
    rw [show μ Set.univ = volume (vec3Ball x₀ r) by
      simp [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter],
      pressure_volume_ball (x₀ := x₀) hr,
      ENNReal.toReal_ofReal (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
    have hrho : (r ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = r := by
      rw [← Real.rpow_mul hr.le]
      norm_num
    rw [hrho]
    congr 1
    ring_nf
  have hLp := harmonic_pressure_integral_eq_lpNorm_rpow hr hf
  have hL : (lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ r)) ^ (3 / 2 : ℝ)) ^
      (2 / 3 : ℝ) = lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ r)) := by
    rw [← Real.rpow_mul lpNorm_nonneg]
    norm_num
  simp only [one_mul] at hsp
  change ∫ x in vec3Ball x₀ r, |f x| ≤ _ at hsp
  rw [hvol, hLp, hL] at hsp
  exact hsp

theorem exists_harmonicPressurePart_Ck_ae_of_sws :
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
                (alpha u z ρ ^ 2 +
                  lpNorm (fun y : Vec3 => p (y, s))
                    (ENNReal.ofReal (3 / 2 : ℝ))
                    (volume.restrict (vec3Ball z.1 ρ))) := by
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
  have henergy := pressure_energy_bound hsol hρ hsub
  filter_upwards [hslices', hdata, hp, henergy] with s hs hdat hps hEs
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
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hE0 : 0 ≤ ∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) :=
    integral_nonneg_of_ae (Eventually.of_forall fun y =>
      pow_nonneg (vec3EuclideanNorm_nonneg _) _)
  have hI : (∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ≤ ρ * alpha u z ρ ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.rpow_nonneg hE0 (1 / 2 : ℝ))
      (by positivity)).2 hEs
    calc
      _ = ((∫ y in vec3Ball z.1 ρ,
          vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) ^
            (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num
      _ ≤ (Real.sqrt ρ * alpha u z ρ) ^ (2 : ℕ) := hsq
      _ = ρ * alpha u z ρ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hρ.le]
  have hUbound : ∫ y in vec3Ball z.1 ρ,
      pressureUTensorNorm u c s y ≤ 2 * ρ * alpha u z ρ ^ 2 := by
    calc
      _ ≤ 2 * ∫ y in vec3Ball z.1 ρ,
          vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) := hUenergy
      _ ≤ 2 * (ρ * alpha u z ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hI (by norm_num)
      _ = _ := by ring
  let _ : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := z.1) (r := ρ))
  have hpInt : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball z.1 ρ)) :=
    (hps.integrable (by norm_num)).norm
  have hPbound : ∫ y in vec3Ball z.1 ρ, |p (y, s)| ≤
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ *
        lpNorm (fun y : Vec3 => p (y, s))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball z.1 ρ)) :=
    harmonic_pressure_integral_le_lpNorm hρ hps
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
    hUint hpInt (alpha u z ρ ^ 2)
    (lpNorm (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball z.1 ρ))) (sq_nonneg _) lpNorm_nonneg
    hUbound hPbound
  simpa [c] using hpoint

end CKN
