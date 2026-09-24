/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyTools
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Caccioppoli Energy Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_rhs_terms_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ r ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I)
    {c : ParabolicPoint → ℝ}
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcm : AEMeasurable c
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (poincareSobolevL1VectorConstant * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ))
    (hcc : ∀ w, c w = c (x₀, w.2))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    ∀ t ≤ t₀, ∫ s in Iio t, ∫ x in Ω,
      localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) (x, s) ≤
      caccioppoli_I1_heat_cutoff_raw (u := u) (x₀ := x₀) (t₀ := t₀)
          (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I2_heat_cutoff_raw (u := u) (c := c) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I3_heat_cutoff_raw (p := p) (v := u) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I4_heat_cutoff_raw (u := u) (f := f) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε := by
  let _ : MeasurableSpace ParabolicPoint :=
    Measure.prod.measureSpace.toMeasurableSpace
  let _ : MeasurableSpace (Vec3 × ℝ) :=
    Measure.prod.measureSpace.toMeasurableSpace
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let F : Vec3 × ℝ → ℝ := fun z => backwardHeat_cutoff
    (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z
  let g1 : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (u z)) ^ 2 *
      (timePartial F z + ∑ i, spatialSecondPartial F i i z)
  let g2 : ParabolicPoint → ℝ := fun z =>
    ((vec3EuclideanNorm (u z)) ^ 2 - c z) *
      (∑ i, u z i * spatialPartial F i z)
  let g3 : ParabolicPoint → ℝ := fun z =>
    2 * (p z - 0) * (∑ i, u z i * spatialPartial F i z)
  let g4 : ParabolicPoint → ℝ := fun z =>
    2 * (∑ i, f z i * u z i) * F z
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr
    hsub hfuture
  have hFcont : ContDiff ℝ (⊤ : ℕ∞) F := by
    simpa only [F] using htest.1.1
  have hFsupp : tsupport F ⊆ euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
      Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
    simpa only [F] using caccioppoli_heat_cutoff_tsupport_subset hρ hε hFcont
  have hΩ : MeasurableSet Ω := hsol.1.measurableSet
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have huStrong : AEStronglyMeasurable u (volume.restrict Q) := by
    exact AEStronglyMeasurable.mono_measure hdata.1
      (Measure.restrict_mono hcyl le_rfl)
  have hfStrong : AEStronglyMeasurable f (volume.restrict Q) := by
    exact AEStronglyMeasurable.mono_measure hdata.2.2.2.1
      (Measure.restrict_mono hcyl le_rfl)
  have huNormStrong : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
      (volume.restrict Q) := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huStrong
  have hu : AEMeasurable (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
      (volume.restrict Q) := huNormStrong.aemeasurable
  have hp : AEMeasurable (fun z : ParabolicPoint => p z)
      (volume.restrict Q) := hdata.2.2.1.aemeasurable.mono_measure
        (Measure.restrict_mono hcyl le_rfl)
  have hf : AEMeasurable (fun z : ParabolicPoint => f z)
      (volume.restrict Q) := hdata.2.2.2.1.aemeasurable.mono_measure
        (Measure.restrict_mono hcyl le_rfl)
  have htimeC : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial F z) :=
    caccioppoli_timePartial_contDiff hFcont
  have hspC : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial F i z) := fun i =>
    spatialPartial_contDiff hFcont i
  have hssC : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial F i j z) := by
    intro i j
    exact spatialPartial_contDiff (spatialPartial_contDiff hFcont i) j
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial F i i z) := by
    apply ContDiff.sum
    intro i hi
    exact hssC i i
  have hL : AEMeasurable (fun z : ParabolicPoint =>
      timePartial F z + ∑ i, spatialSecondPartial F i i z)
      (volume.restrict Q) := by
    have hc := (htimeC.add hsum).continuous
    exact hc.aemeasurable
  have hLstrong : AEStronglyMeasurable (fun z : ParabolicPoint =>
      timePartial F z + ∑ i, spatialSecondPartial F i i z)
      (volume.restrict Q) := by
    exact (htimeC.add hsum).continuous.aestronglyMeasurable
  have hD : AEMeasurable (fun z : ParabolicPoint =>
      ∑ i, u z i * spatialPartial F i z) (volume.restrict Q) := by
    have hvec : AEStronglyMeasurable
        (fun z : ParabolicPoint => fun i => spatialPartial F i z)
        (volume.restrict Q) := by
      exact (continuous_pi (fun i => (hspC i).continuous)).aestronglyMeasurable
    have hpair : AEStronglyMeasurable
        (fun z : ParabolicPoint => (u z, fun i => spatialPartial F i z))
        (volume.restrict Q) := huStrong.prodMk hvec
    have hc : Continuous (fun z : Vec3 × (Fin 3 → ℝ) =>
        ∑ i, z.1 i * z.2 i) := by fun_prop
    exact hc.comp_aestronglyMeasurable hpair |>.aemeasurable
  have hg1 : AEMeasurable (fun z : ParabolicPoint =>
      (vec3EuclideanNorm (u z)) ^ 2 *
        (timePartial F z + ∑ i, spatialSecondPartial F i i z))
      (volume.restrict Q) := by
    exact ((huNormStrong.pow 2).mul hLstrong).aemeasurable
  have hg2 : AEMeasurable (fun z : ParabolicPoint =>
      ((vec3EuclideanNorm (u z)) ^ 2 - c z) *
        (∑ i, u z i * spatialPartial F i z))
      (volume.restrict Q) := by
    have hsq : AEMeasurable (fun z : ParabolicPoint =>
        (vec3EuclideanNorm (u z)) ^ 2) (volume.restrict Q) :=
      (huNormStrong.pow 2).aemeasurable
    exact ((hsq.aestronglyMeasurable.sub hcm.aestronglyMeasurable).mul
      hD.aestronglyMeasurable).aemeasurable
  have hg3 : AEMeasurable (fun z : ParabolicPoint =>
      2 * (p z - 0) * (∑ i, u z i * spatialPartial F i z))
      (volume.restrict Q) := by
    exact (((hp.aestronglyMeasurable.sub
      measurable_const.aestronglyMeasurable).const_mul (2 : ℝ)).mul
        hD.aestronglyMeasurable).aemeasurable
  have hg4 : AEMeasurable (fun z : ParabolicPoint =>
      2 * (∑ i, f z i * u z i) * F z)
      (volume.restrict Q) := by
    have hfu : AEMeasurable (fun z : ParabolicPoint =>
        ∑ i, f z i * u z i) (volume.restrict Q) := by
      have hpair : AEStronglyMeasurable
          (fun z : ParabolicPoint => (f z, u z)) (volume.restrict Q) :=
        hfStrong.prodMk huStrong
      have hc : Continuous (fun z : Vec3 × Vec3 =>
          ∑ i, z.1 i * z.2 i) := by fun_prop
      exact hc.comp_aestronglyMeasurable hpair |>.aemeasurable
    have hFmeas : AEMeasurable F (volume.restrict Q) := hFcont.continuous.aemeasurable
    exact (hfu.const_mul 2).mul hFmeas
  have hg1' : AEMeasurable g1 (volume.restrict Q) := by
    simpa only [g1] using hg1
  have hg2' : AEMeasurable g2 (volume.restrict Q) := by
    simpa only [g2] using hg2
  have hg3' : AEMeasurable g3 (volume.restrict Q) := by
    simpa only [g3] using hg3
  have hg4' : AEMeasurable g4 (volume.restrict Q) := by
    simpa only [g4] using hg4
  have hne1 := caccioppoli_I1_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hεr hsub hfuture
  have hne2 := caccioppoli_I2_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hsub hA hcenter hvelocity
  have hne3 := caccioppoli_I3_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hsub hvelocity
  have hne4 := caccioppoli_I4_heat_cutoff_raw_ne_top hsol hρ hε hr hsub
    hvelocity
  have hraw1 : (∫⁻ z in Q, ENNReal.ofReal |g1 z|) ≠ ∞ := by
    have hle : (∫⁻ z in Q, ENNReal.ofReal |g1 z|) ≤
        ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
          ENNReal.ofReal |timePartial F z + ∑ i,
            spatialSecondPartial F i i z| := by
      apply lintegral_mono
      intro z
      dsimp [g1]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _),
        ENNReal.ofReal_mul (sq_nonneg _),
        ← Real.rpow_natCast (vec3EuclideanNorm (u z)) 2,
        ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
          (by norm_num)]
      norm_num [Real.rpow_natCast]
    have htop : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
        (2 : ℝ) * ENNReal.ofReal |timePartial F z + ∑ i,
          spatialSecondPartial F i i z|) < ∞ := by
      have hne : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
          (2 : ℝ) * ENNReal.ofReal |timePartial F z + ∑ i,
            spatialSecondPartial F i i z|) ≠ ∞ := by
        dsimp [Q, F]
        exact hne1
      exact lt_top_iff_ne_top.mpr hne
    exact ne_of_lt (hle.trans_lt htop)

  have hraw2 : (∫⁻ z in Q, ENNReal.ofReal |g2 z|) ≠ ∞ := by
    have hpoint : ∀ z, ENNReal.ofReal |g2 z| ≤
        ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
      intro z
      have hd := caccioppoli_partial_sum_abs (u := u) (F := F) (z := z)
      have hreal : |g2 z| ≤
          |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
            (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) := by
        dsimp [g2]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      calc
        _ ≤ ENNReal.ofReal (|(vec3EuclideanNorm (u z)) ^ 2 - c z| *
            (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_mul (abs_nonneg _),
            ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
          ring
    have hle := lintegral_mono (μ := volume.restrict Q) hpoint
    have htop : (∫⁻ z in Q, ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|)) < ∞ := by
      have hne : (∫⁻ z in Q, ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
        dsimp [Q, F]
        exact hne2
      exact lt_top_iff_ne_top.mpr hne
    exact ne_of_lt (hle.trans_lt htop)
  have hraw3 : (∫⁻ z in Q, ENNReal.ofReal |g3 z|) ≠ ∞ := by
    have hpoint : ∀ z, ENNReal.ofReal |g3 z| ≤
        (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
      intro z
      have hd := caccioppoli_partial_sum_abs (u := u)
        (F := show ParabolicPoint → ℝ from F) (z := z)
      have hd' : |∑ i, u z i * spatialPartial F i z| ≤
          vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
        simpa only using hd
      have hreal : |g3 z| ≤
          2 * |p z| * (vec3EuclideanNorm (u z) *
            ∑ i, |spatialPartial F i z|) := by
        calc
          |g3 z| = 2 * |p z| * |∑ i, u z i * spatialPartial F i z| := by
            simp [g3, abs_mul]
          _ ≤ 2 * |p z| *
                (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) :=
            mul_le_mul_of_nonneg_left hd' (by positivity)
      calc
        _ ≤ ENNReal.ofReal (2 * |p z| * (vec3EuclideanNorm (u z) *
            ∑ i, |spatialPartial F i z|)) := ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |p z|),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
          norm_num
          ring
    have hle := lintegral_mono (μ := volume.restrict Q) hpoint
    have htop : (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|)) < ∞ := by
      have hne : (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
        dsimp [Q, F]
        exact hne3
      exact lt_top_iff_ne_top.mpr hne
    exact ne_of_lt (hle.trans_lt htop)
  have hraw4 : (∫⁻ z in Q, ENNReal.ofReal |g4 z|) ≠ ∞ := by
    have hpoint : ∀ z, ENNReal.ofReal |g4 z| ≤
        (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f z)) *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (F (show Vec3 × ℝ from z)) := by
      intro z
      have hF0 : 0 ≤ F (show Vec3 × ℝ from z) := by
        simpa only [F] using htest.2 z
      have hreal := caccioppoli_force_abs_le (u := u) (f := f)
        (F := show ParabolicPoint → ℝ from F)
        hF0 (z := z)
      calc
        _ = ENNReal.ofReal |(2 * (∑ i, f z i * u z i) *
            F (show Vec3 × ℝ from z))| := by rfl
        _ ≤ ENNReal.ofReal (2 * vec3EuclideanNorm (f z) *
            vec3EuclideanNorm (u z) * F (show Vec3 × ℝ from z)) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [g4, abs_of_nonneg hF0] using hreal
        _ = _ := by
          have hfn : 0 ≤ vec3EuclideanNorm (f z) := vec3EuclideanNorm_nonneg _
          have hun : 0 ≤ vec3EuclideanNorm (u z) := vec3EuclideanNorm_nonneg _
          rw [ENNReal.ofReal_mul (mul_nonneg
              (mul_nonneg (by norm_num) hfn) hun),
            ENNReal.ofReal_mul (mul_nonneg (by norm_num) hfn),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    have hle := lintegral_mono (μ := volume.restrict Q) hpoint
    have htop : (∫⁻ z in Q, (2 : ℝ≥0∞) *
          ENNReal.ofReal (vec3EuclideanNorm (f z)) *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
            ENNReal.ofReal (F (show Vec3 × ℝ from z))) < ∞ := by
      have hne : (∫⁻ z in Q, (2 : ℝ≥0∞) *
          ENNReal.ofReal (vec3EuclideanNorm (f z)) *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
            ENNReal.ofReal (F (show Vec3 × ℝ from z))) ≠ ∞ := by
        dsimp [Q, F]
        exact hne4
      exact lt_top_iff_ne_top.mpr hne
    exact ne_of_lt (hle.trans_lt htop)

  have hi1 : IntegrableOn g1 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg1' hraw1
  have hi2 : IntegrableOn g2 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg2' hraw2
  have hi3 : IntegrableOn g3 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg3' hraw3
  have hi4 : IntegrableOn g4 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg4' hraw4
  intro t ht
  let S : Set ParabolicPoint := Ω ×ˢ Iio t
  have hS : MeasurableSet S := hΩ.prod measurableSet_Iio
  have hzero := caccioppoli_terms_zero_ae_outside_cylinder
    (Ω := Ω) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) hρ hΩ hFcont hFsupp
    (u := u) (p := p) (f := f) (t := t) ht
  have hz1 : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g1 z = 0 := by
    filter_upwards [hzero] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by simpa only [g1] using hz.1)
  have hz2 : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g2 z = 0 := by
    filter_upwards [hzero] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by
        dsimp only [g2]
        apply mul_eq_zero.mpr
        right
        exact hz.2.2.2.2)
  have hz3 : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g3 z = 0 := by
    filter_upwards [hzero] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by simpa only [g3] using hz.2.2.1)
  have hz4 : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g4 z = 0 := by
    filter_upwards [hzero] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by simpa only [g4] using hz.2.2.2.1)
  have hi1S : IntegrableOn g1 S volume :=
    caccioppoli_integrable_term_on hS hi1 hz1
  have hi2S : IntegrableOn g2 S volume :=
    caccioppoli_integrable_term_on hS hi2 hz2
  have hi3S : IntegrableOn g3 S volume :=
    caccioppoli_integrable_term_on hS hi3 hz3
  have hi4S : IntegrableOn g4 S volume :=
    caccioppoli_integrable_term_on hS hi4 hz4
  have hterm1 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi1 hz1
  have hterm2 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi2 hz2
  have hterm3 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi3 hz3
  have hterm4 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi4 hz4
  let gC : ParabolicPoint → ℝ := fun z =>
    c z * (∑ i, u z i * spatialPartial F i z)
  have hRint := (suitableWeakSolution_energy_integrable hsol htest.1 htest.2).2.1
  have hRS : IntegrableOn
      (fun z : ParabolicPoint => localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z) S volume := by
    change Integrable (fun z : ParabolicPoint => localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
      (volume.restrict S)
    rw [volume_parabolicPoint_eq_prod]
    rw [← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    change Integrable (μ := (volume : Measure (Vec3 × ℝ)).restrict S)
      (fun z : Vec3 × ℝ => localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
    have hRrestrict := hRint.mono_measure (Measure.restrict_le_self :
      volume.restrict S ≤ volume)
    exact hRrestrict
  have hsumS : IntegrableOn (fun z : ParabolicPoint =>
      g1 z + g2 z + g3 z + g4 z) S volume := by
    exact ((hi1S.add hi2S).add hi3S).add hi4S
  have hgc : IntegrableOn gC S volume := by
    have hsub := hRS.sub hsumS
    apply hsub.congr_fun_ae
    filter_upwards [] with z
    change localEnergyRhs u p f F z -
      (g1 z + g2 z + g3 z + g4 z) = gC z
    have hdec := caccioppoli_localEnergyRhs_decompose
      (u := u) (p := p) (f := f)
      (ψ := show Vec3 × ℝ → ℝ from F) z
    rw [hdec]
    dsimp [gC, g1, g2, g3, g4]
    ring
  let K : Set Vec3 := euclideanClosedBall x₀ (3 * ρ / 4)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_euclideanClosedBall x₀ (by positivity)
  have hKΩ : K ⊆ Ω := by
    intro x hx
    have hmem : (x, t₀ - ρ ^ 2) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity)).1 hx
      have hxr' : vec3EuclideanNorm (x - x₀) ≤ ρ := by
        have hρ34 : 3 * ρ / 4 ≤ ρ := by linarith only [hρ]
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
          pow_two] using hx'.trans hρ34
      exact ⟨hxr', ⟨le_rfl, sub_le_self _ (sq_nonneg ρ)⟩⟩
    exact (hsub hmem).1
  obtain ⟨R, Ω₁, J, hρR, hbox, hball, hT, _⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  have hKR : K ⊆ vec3Ball x₀ R := by
    intro x hx
    rw [mem_vec3Ball]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by positivity)).1 hx
    have hlt : 3 * ρ / 4 < R := by linarith only [hρR, hρ]
    simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
      pow_two] using hx'.trans_lt hlt
  have hKΩ₁ : K ⊆ Ω₁ := fun x hx => hball x (hKR hx)
  have hmem := ae_restrict_of_ae_restrict_of_subset hT
    (slice_memLp_ae_of_sws hsol hbox)
  have hUs : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      IntegrableOn (fun x : Vec3 => u (x, s)) K volume := by
    filter_upwards [hmem] with s hs
    let _ : IsFiniteMeasure (volume.restrict K) := by
      exact isFiniteMeasure_restrict.mpr hKcompact.measure_lt_top.ne
    have hKmem : MemLp (fun x : Vec3 => u (x, s)) 2
        (volume.restrict K) :=
      hs.1.mono_measure (Measure.restrict_mono_set volume hKΩ₁)
    change Integrable (fun x : Vec3 => u (x, s)) (volume.restrict K)
    exact hKmem.integrable (by norm_num)
  have hpair := caccioppoli_heat_cutoff_cancel hsol hρ hε hr hεr hsub hfuture
  have hFsuppK : tsupport F ⊆ K ×ˢ (Set.univ : Set ℝ) := by
    intro z hz
    exact ⟨(hFsupp hz).1, mem_univ _⟩
  have hDslice : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 := by
    filter_upwards [hpair, hUs] with s hs hUs'
    exact (caccioppoli_pairing_zero_to_slice_integral hKcompact hKΩ hFcont
      hFsuppK hUs' (hs s)).2
  have hDsliceInter : ∀ᵐ s ∂volume.restrict
      (Iio t ∩ Ioc (t₀ - ρ ^ 2) t₀),
      ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun s hs => hs.2) hDslice
  have hDsliceInter' : ∀ᵐ s ∂volume,
      s ∈ Iio t ∩ Ioc (t₀ - ρ ^ 2) t₀ →
        ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 :=
    (ae_restrict_iff' (measurableSet_Iio.inter measurableSet_Ioc)).mp hDsliceInter
  have hneq : ∀ᵐ s ∂volume, s ≠ t₀ - ρ ^ 2 :=
    Measure.ae_ne (volume : Measure ℝ) (t₀ - ρ ^ 2)
  have hCslice : ∀ᵐ s ∂volume.restrict (Iio t),
      ∫ x in Ω, gC (x, s) = 0 := by
    apply (ae_restrict_iff' measurableSet_Iio).2
    filter_upwards [hDsliceInter', hneq] with s hs hne
    intro hsIio
    by_cases hsJ : s ∈ Ioc (t₀ - ρ ^ 2) t₀
    · have hd := hs ⟨hsIio, hsJ⟩
      calc
        ∫ x in Ω, gC (x, s) =
            ∫ x in Ω, c (x₀, s) *
              (∑ i, u (x, s) i * spatialPartial F i (x, s)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [gC]
          rw [hcc (x, s)]
        _ = c (x₀, s) *
            (∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s)) := by
          rw [integral_const_mul]
        _ = 0 := by rw [hd, mul_zero]
    · have hst : s < t₀ := lt_of_lt_of_le hsIio ht
      have hle : s ≤ t₀ - ρ ^ 2 := by
        by_contra hnot
        exact hsJ ⟨lt_of_not_ge hnot, hst.le⟩
      have hslt : s < t₀ - ρ ^ 2 := lt_of_le_of_ne hle hne
      have hD0 : ∀ x : Vec3,
          ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 := by
        intro x
        apply Finset.sum_eq_zero
        intro i hi
        apply mul_eq_zero.mpr
        right
        apply caccioppoli_spatialPartial_zero_of_not_mem_tsupport hFcont
        intro hz
        exact not_le_of_gt hslt ((hFsupp hz).2.1)
      have hzero : (fun x : Vec3 => gC (x, s)) =ᵐ[volume.restrict Ω]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [] with x
        dsimp [gC]
        rw [hD0 x, mul_zero]
      simpa using (integral_congr_ae hzero)
  have hgcProd : IntegrableOn gC S
      ((volume : Measure Vec3).prod volume) := by
    rw [← volume_parabolicPoint_eq_prod]
    exact hgc
  have houterC : ∫ s in Iio t, ∫ x in Ω, gC (x, s) = 0 := by
    have hzero : (fun s : ℝ => ∫ x in Ω, gC (x, s)) =ᵐ[volume.restrict (Iio t)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hCslice] with s hs
      exact hs
    simpa using (integral_congr_ae hzero)
  have hnestC := caccioppoli_energy_nested_integral_eq (Ω := Ω) (T := Iio t)
    (g := gC) hgcProd
  have hcancelC : ∫ z in S, gC z = 0 := by
    have hprodzero : ∫ z in Ω ×ˢ Iio t, gC z
        ∂((volume : Measure Vec3).prod volume) = 0 := by
      rw [← hnestC]
      exact houterC
    change ∫ z : Vec3 × ℝ in Ω ×ˢ Iio t, gC z
        ∂((volume : Measure Vec3).prod volume) = 0
    exact hprodzero
  have hpoint1 : ∀ z, ENNReal.ofReal |g1 z| ≤
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z| := by
    intro z
    dsimp [g1]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _),
      ENNReal.ofReal_mul (sq_nonneg _),
      ← Real.rpow_natCast (vec3EuclideanNorm (u z)) 2,
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
        (by norm_num)]
    norm_num [Real.rpow_natCast]
  have hpoint2 : ∀ z, ENNReal.ofReal |g2 z| ≤
      ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
    intro z
    have hd := caccioppoli_partial_sum_abs (u := u) (F := F) (z := z)
    have hreal : |g2 z| ≤
        |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) := by
      dsimp [g2]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    calc
      _ ≤ ENNReal.ofReal (|(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (abs_nonneg _),
          ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
        ring
  have hpoint3 : ∀ z, ENNReal.ofReal |g3 z| ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
    intro z
    have hd := caccioppoli_partial_sum_abs (u := u)
      (F := show ParabolicPoint → ℝ from F) (z := z)
    have hd' : |∑ i, u z i * spatialPartial F i z| ≤
        vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
      simpa only using hd
    have hreal : |g3 z| ≤
        2 * |p z| * (vec3EuclideanNorm (u z) *
          ∑ i, |spatialPartial F i z|) := by
      calc
        |g3 z| = 2 * |p z| * |∑ i, u z i * spatialPartial F i z| := by
          simp [g3, abs_mul]
        _ ≤ 2 * |p z| *
              (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) :=
          mul_le_mul_of_nonneg_left hd' (by positivity)
    calc
      _ ≤ ENNReal.ofReal (2 * |p z| * (vec3EuclideanNorm (u z) *
          ∑ i, |spatialPartial F i z|)) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |p z|),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
        norm_num
        ring
  have hpoint4 : ∀ z, ENNReal.ofReal |g4 z| ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f z)) *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (F (show Vec3 × ℝ from z)) := by
    intro z
    have hF0 : 0 ≤ F (show Vec3 × ℝ from z) := by
      simpa only [F] using htest.2 z
    have hreal := caccioppoli_force_abs_le (u := u) (f := f)
      (F := show ParabolicPoint → ℝ from F) hF0 (z := z)
    calc
      _ = ENNReal.ofReal |(2 * (∑ i, f z i * u z i) *
          F (show Vec3 × ℝ from z))| := by rfl
      _ ≤ ENNReal.ofReal (2 * vec3EuclideanNorm (f z) *
          vec3EuclideanNorm (u z) * F (show Vec3 × ℝ from z)) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [g4, abs_of_nonneg hF0] using hreal
      _ = _ := by
        have hfn : 0 ≤ vec3EuclideanNorm (f z) := vec3EuclideanNorm_nonneg _
        have hun : 0 ≤ vec3EuclideanNorm (u z) := vec3EuclideanNorm_nonneg _
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hfn) hun),
          ENNReal.ofReal_mul (mul_nonneg (by norm_num) hfn),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hne1' : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
      (2 : ℝ) * ENNReal.ofReal |timePartial F z +
        ∑ i, spatialSecondPartial F i i z|) ≠ ∞ := by
    dsimp [Q, F]
    exact hne1
  have hne2' : (∫⁻ z in Q, ENNReal.ofReal
      |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
    dsimp [Q, F]
    exact hne2
  have hne3' : (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
      ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
    dsimp [Q, F]
    exact hne3
  have hne4' : (∫⁻ z in Q, (2 : ℝ≥0∞) *
      ENNReal.ofReal (vec3EuclideanNorm (f z)) *
      ENNReal.ofReal (vec3EuclideanNorm (u z)) *
      ENNReal.ofReal (F (show Vec3 × ℝ from z))) ≠ ∞ := by
    dsimp [Q, F]
    exact hne4
  have hterm1' : ∫ z in S, g1 z ≤
      (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
        (2 : ℝ) * ENNReal.ofReal |timePartial F z +
          ∑ i, spatialSecondPartial F i i z|).toReal := by
    exact hterm1.trans (ENNReal.toReal_mono hne1'
      (lintegral_mono (μ := volume.restrict Q) hpoint1))
  have hterm2' : ∫ z in S, g2 z ≤
      (∫⁻ z in Q, ENNReal.ofReal
        |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (∑ i, |spatialPartial F i z|)).toReal := by
    exact hterm2.trans (ENNReal.toReal_mono hne2'
      (lintegral_mono (μ := volume.restrict Q) hpoint2))
  have hterm3' : ∫ z in S, g3 z ≤
      (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)).toReal := by
    exact hterm3.trans (ENNReal.toReal_mono hne3'
      (lintegral_mono (μ := volume.restrict Q) hpoint3))
  have hterm4' : ∫ z in S, g4 z ≤
      (∫⁻ z in Q, (2 : ℝ≥0∞) *
        ENNReal.ofReal (vec3EuclideanNorm (f z)) *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (F (show Vec3 × ℝ from z))).toReal := by
    exact hterm4.trans (ENNReal.toReal_mono hne4'
      (lintegral_mono (μ := volume.restrict Q) hpoint4))
  have hRprod : IntegrableOn
      (fun z : ParabolicPoint => localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
      S ((volume : Measure Vec3).prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    change Integrable (μ := (volume : Measure (Vec3 × ℝ)).restrict S)
      (fun z : Vec3 × ℝ => localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
    exact hRint.mono_measure (Measure.restrict_le_self : volume.restrict S ≤ volume)
  have hnestR := caccioppoli_energy_nested_integral_eq (Ω := Ω) (T := Iio t)
    (g := fun z : ParabolicPoint => localEnergyRhs u p f
      (backwardHeat_cutoff
        (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z) hRprod
  have hR_eq : ∫ z in S,
      localEnergyRhs u p f
        (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z =
      ∫ z in S, (g1 z + g2 z + g3 z + g4 z) := by
    calc
      _ = ∫ z in S, (g1 z + g2 z + g3 z + g4 z) + gC z := by
        apply integral_congr_ae
        filter_upwards [] with z
        change localEnergyRhs u p f F z =
          (g1 z + g2 z + g3 z + g4 z) + gC z
        have hdec := caccioppoli_localEnergyRhs_decompose
          (u := u) (p := p) (f := f)
          (ψ := show Vec3 × ℝ → ℝ from F) z
        rw [hdec]
        dsimp [gC, g1, g2, g3, g4]
        ring
      _ = (∫ z in S, g1 z + g2 z + g3 z + g4 z) +
          (∫ z in S, gC z) := by
        exact integral_add hsumS.integrable hgc.integrable
      _ = ∫ z in S, (g1 z + g2 z + g3 z + g4 z) := by
        rw [hcancelC, add_zero]
  exact caccioppoli_rhs_integral_sum_bound hR_eq hnestR
    hi1S hi2S hi3S hi4S hterm1' hterm2' hterm3' hterm4'
end CKN
