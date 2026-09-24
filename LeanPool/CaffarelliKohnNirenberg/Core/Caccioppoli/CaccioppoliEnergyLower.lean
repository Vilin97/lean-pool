/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyTerms
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergy
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyLowerIntegrability

/-!
# Caccioppoli Energy Lower

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

theorem caccioppoli_energy_lower_of_raw
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
    (hcc : ∀ w, c w = c (x₀, w.2)) :
    (alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r) ^ 2 ≤
      6000 * (caccioppoli_I1_heat_cutoff_raw (u := u) (x₀ := x₀) (t₀ := t₀)
          (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I2_heat_cutoff_raw (u := u) (c := c) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I3_heat_cutoff_raw (p := p) (v := u) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I4_heat_cutoff_raw (u := u) (f := f) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε) := by
  let S : ℝ :=
    caccioppoli_I1_heat_cutoff_raw (u := u) (x₀ := x₀) (t₀ := t₀)
          (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I2_heat_cutoff_raw (u := u) (c := c) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I3_heat_cutoff_raw (p := p) (v := u) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoli_I4_heat_cutoff_raw (u := u) (f := f) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε
  have hS : 0 ≤ S := by
    dsimp [S, caccioppoli_I1_heat_cutoff_raw,
      caccioppoli_I2_heat_cutoff_raw, caccioppoli_I3_heat_cutoff_raw,
      caccioppoli_I4_heat_cutoff_raw]
    positivity
  have hvelocity := caccioppoli_velocity_integral_ne_top hsol hρ hsub
  have hraw := caccioppoli_rhs_terms_bound hsol hρ hε hr hscale hεr
    hsub hfuture hA hcm hcenter hcc hvelocity
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr
    hsub hfuture
  have henergy := caccioppoli_local_energy_ae hsol htest.1 htest.2
  have hgradInt := caccioppoli_gradient_integrable_on_cylinder hsol hρ hsub
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ r
  let T : Set ℝ := Ioc (t₀ - r ^ 2) t₀
  have hB : vec3Ball x₀ r ⊆ Ω := by
    intro x hx
    have hz : (x, t₀) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨(mem_vec3Ball.mp hx).le.trans
        (hscale.trans (half_le_self hρ.le)),
        ⟨sub_le_self _ (sq_nonneg ρ), le_rfl⟩⟩
    exact (hsub hz).1
  have hTsub : T ⊆ I := by
    intro t ht
    change t₀ - r ^ 2 < t ∧ t ≤ t₀ at ht
    exact (hsub (show (x₀, t) ∈ closure (parabolicCylinder x₀ t₀ ρ) from by
      rw [closure_parabolicCylinder hρ]
      have hrho : r ≤ ρ := hscale.trans (half_le_self hρ.le)
      have hrr : r ^ 2 ≤ ρ ^ 2 := (sq_le_sq₀ hr.le hρ.le).2 hrho
      have hx0 : vec3EuclideanNorm (x₀ - x₀) ≤ ρ := by
        rw [sub_self, vec3EuclideanNorm_zero]
        exact hρ.le
      change vec3EuclideanNorm (x₀ - x₀) ≤ ρ ∧
        t₀ - ρ ^ 2 ≤ t ∧ t ≤ t₀
      exact ⟨hx0, ⟨(sub_le_sub_left hrr t₀).trans ht.1.le, ht.2⟩⟩)).2
  have henergyT : ∀ᵐ t ∂volume.restrict T,
      (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 *
        backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
          x₀ t₀ r (x, t)) +
        2 * ∫ s in Iio t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) *
            backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
              x₀ t₀ r (x, s) ≤ S := by
    have hae := ae_restrict_of_ae_restrict_of_subset hTsub henergy
    have hmem : ∀ᵐ t ∂volume.restrict T, t ∈ T :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hae, hmem] with t ht htT
    exact ht.trans (hraw t htT.2)
  let F : ParabolicPoint → ℝ :=
    backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r
  have henergyTF : ∀ᵐ t ∂volume.restrict T,
      (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t)) +
        2 * ∫ s in Iio t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s) ≤ S := by
    simpa only [F] using henergyT
  have hEint := suitableWeakSolution_energy_integrable hsol htest.1 htest.2
  have hEprod : Integrable (fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (u z)) ^ 2 * F z)
    ((volume : Measure Vec3).prod volume) := by
    have h := hEint.2.2
    change Integrable (fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (u z)) ^ 2 *
      backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
          x₀ t₀ r z) (volume : Measure (Vec3 × ℝ)) at h
    rw [MeasureTheory.Measure.volume_eq_prod Vec3 ℝ] at h
    simpa only [F] using h
  have hDprod : Integrable (fun z : Vec3 × ℝ =>
      spatialGradientSq u Du z * F z)
      ((volume : Measure Vec3).prod volume) := by
    have h := hEint.1
    change Integrable (fun z : Vec3 × ℝ =>
      spatialGradientSq u Du z *
        backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
          x₀ t₀ r z) (volume : Measure (Vec3 × ℝ)) at h
    rw [MeasureTheory.Measure.volume_eq_prod Vec3 ℝ] at h
    simpa only [F] using h
  have hΩI : (volume.restrict Ω).prod (volume.restrict I) ≤
      (volume : Measure Vec3).prod volume := by
    exact Measure.prod_mono (Measure.restrict_le_self) (Measure.restrict_le_self)
  have hEtimeI : ∀ᵐ t ∂volume.restrict I,
      Integrable (fun x : Vec3 =>
        (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t))
        (volume.restrict Ω) := by
    have h := hEprod.mono_measure hΩI
    exact h.prod_left_ae
  have hDtimeI : ∀ᵐ t ∂volume.restrict I,
      Integrable (fun x : Vec3 =>
        spatialGradientSq u Du (x, t) * F (x, t))
        (volume.restrict Ω) := by
    have h := hDprod.mono_measure hΩI
    exact h.prod_left_ae
  have hEtimeT := ae_restrict_of_ae_restrict_of_subset hTsub hEtimeI
  have hDtimeT := ae_restrict_of_ae_restrict_of_subset hTsub hDtimeI
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hB' : vec3Ball x₀ r ⊆ Ω' := by
    intro x hx
    have hxρ : x ∈ vec3Ball x₀ ρ := by
      exact (mem_vec3Ball.mp hx).trans_le
        (hscale.trans (half_le_self hρ.le))
    have htρ : t₀ - ρ ^ 2 < t₀ := by
      exact sub_lt_self _ (sq_pos_of_pos hρ)
    exact (hcyl (show (x, t₀) ∈ parabolicCylinder x₀ t₀ ρ from
      ⟨hxρ, ⟨htρ, le_rfl⟩⟩)).1
  have hT' : T ⊆ J := by
    intro t ht
    change t₀ - r ^ 2 < t ∧ t ≤ t₀ at ht
    have hxρ : x₀ ∈ vec3Ball x₀ ρ := by
      simp [vec3EuclideanNorm_zero, hρ]
    have hrho : r ≤ ρ := hscale.trans (half_le_self hρ.le)
    have hrr : r ^ 2 ≤ ρ ^ 2 := (sq_le_sq₀ hr.le hρ.le).2 hrho
    exact (hcyl (show (x₀, t) ∈ parabolicCylinder x₀ t₀ ρ from
      ⟨hxρ, ⟨(sub_le_sub_left hrr t₀).trans_lt ht.1, ht.2⟩⟩)).2
  have hslices := ae_restrict_of_ae_restrict_of_subset hT'
    (slice_memLp_ae_of_sws hsol hbox)
  have hgood : ∀ᵐ t ∂volume.restrict T,
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω') := hslices
  have hu_int : ∀ᵐ t ∂volume.restrict T,
      IntegrableOn (fun x : Vec3 => (vec3EuclideanNorm (u (x, t))) ^ (2 : ℕ))
        (vec3Ball x₀ r) volume := by
    filter_upwards [hgood] with t ht
    exact caccioppoli_u_sq_integrable_of_memLp
      (ht.1.mono_measure (Measure.restrict_mono_set volume hB'))
  have hdu_int : ∀ᵐ t ∂volume.restrict T,
      IntegrableOn (fun x : Vec3 => spatialGradientSq u Du (x, t))
        (vec3Ball x₀ r) volume := by
    filter_upwards [hgood] with t ht
    have h := caccioppoli_gradient_sq_integrable_of_memLp
      (ht.2.mono_measure (Measure.restrict_mono_set volume hB'))
    simpa only [spatialGradientSq] using h
  have hEae : ∀ᵐ t ∂volume.restrict T,
      (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal ((vec3EuclideanNorm (u (x, t))) ^ 2)) ≤
        ENNReal.ofReal (2000 * r * S) := by
    have hTmem : ∀ᵐ t ∂volume.restrict T, t ∈ T :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [henergyTF, hEtimeT, hu_int, hTmem] with t ht hEt hu htT
    change t₀ - r ^ 2 < t ∧ t ≤ t₀ at htT
    have hEtB : IntegrableOn
        (fun x : Vec3 => (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t))
        (vec3Ball x₀ r) volume :=
      hEt.mono_measure (Measure.restrict_mono_set volume hB)
    have hleft : (∫ x in vec3Ball x₀ r,
        (1 / (2000 * r)) * (vec3EuclideanNorm (u (x, t))) ^ 2) ≤
        ∫ x in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t) := by
      refine setIntegral_mono_on (hu.const_mul _) hEtB
        (vec3Ball_measurable x₀ r) ?_
      intro x hx
      have hxQ : (x, t) ∈ parabolicCylinder x₀ t₀ r :=
        ⟨hx, htT.1, htT.2⟩
      have hxhalf : x ∈ vec3Ball x₀ (ρ / 2) := by
        exact hx.trans_le hscale
      have htupper : t ≤ t₀ + ε / 2 := by
        calc
          t ≤ t₀ := htT.2
          _ ≤ t₀ + ε / 2 := le_add_of_nonneg_right (half_pos hε).le
      have hη := caccioppoli_heat_cutoff_eq_one_on x₀ t₀ ρ ε r
        hρ hε hr hscale (z := (x, t)) hxhalf ⟨htT.1, htupper⟩
      have htime : t - t₀ < r ^ 2 := by
        exact lt_of_le_of_lt (sub_nonpos.mpr htT.2) (sq_pos_of_pos hr)
      have hψ := centeredBackwardHeatTest_lower_on_cylinder hr hxQ
      have hlow : 1 / (2000 * r) ≤ F (x, t) := by
        unfold F backwardHeat_cutoff
        simp only [ite_eq_left htime, hη, one_mul]
        simpa only [centeredBackwardHeatTest] using hψ
      have hnonneg : 0 ≤ (vec3EuclideanNorm (u (x, t))) ^ 2 := by positivity
      simpa only [F, mul_comm] using mul_le_mul_of_nonneg_left hlow hnonneg
    have hnonnegD : 0 ≤ ∫ s in Iio t, ∫ x in Ω,
        spatialGradientSq u Du (x, s) * F (x, s) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with s
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact mul_nonneg (by
        unfold spatialGradientSq
        positivity) (htest.2 (x, s))
    have hupper : (∫ x in Ω,
        (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t)) ≤ S := by
      exact (le_add_of_nonneg_right (mul_nonneg (by norm_num) hnonnegD)).trans ht
    have hΩB : (∫ x in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t)) ≤
        ∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t) := by
      apply setIntegral_mono_set hEt
      · filter_upwards [] with x
        exact mul_nonneg (by positivity) (htest.2 (x, t))
      · exact Filter.Eventually.of_forall hB
    have hU : ∫ x in vec3Ball x₀ r,
        (vec3EuclideanNorm (u (x, t))) ^ 2 ≤ 2000 * r * S := by
      calc
        _ = (2000 * r) * (∫ x in vec3Ball x₀ r,
            (1 / (2000 * r)) * (vec3EuclideanNorm (u (x, t))) ^ 2) := by
              rw [integral_const_mul]
              field_simp [hr.ne']
        _ ≤ (2000 * r) * (∫ x in vec3Ball x₀ r,
            (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t)) := by
              exact mul_le_mul_of_nonneg_left hleft (by positivity)
        _ ≤ (2000 * r) * S := mul_le_mul_of_nonneg_left
          (hΩB.trans hupper) (by positivity)
        _ = 2000 * r * S := by ring
    have htop : (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal ((vec3EuclideanNorm (u (x, t))) ^ 2)) ≠ ∞ := by
      apply (lintegral_ofReal_ne_top_iff_integrable
        hu.aestronglyMeasurable (Filter.Eventually.of_forall (fun x =>
          sq_nonneg (vec3EuclideanNorm (u (x, t)))))).2
      exact hu
    apply (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mp
    rw [← setIntegral_eq_toReal_setLIntegral_of_nonneg hu
      (Filter.Eventually.of_forall (fun x =>
        sq_nonneg (vec3EuclideanNorm (u (x, t)))))]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2000 * r * S)]
    exact hU
  have hrho : r ≤ ρ := hscale.trans (half_le_self hρ.le)
  have hQr : IntegrableOn (fun z => spatialGradientSq u Du z)
      (parabolicCylinder x₀ t₀ r) volume :=
    hgradInt.mono_set (parabolicCylinder_mono hr.le hrho)
  have hDprodBT : Integrable (fun z : Vec3 × ℝ => spatialGradientSq u Du z)
      ((volume.restrict (vec3Ball x₀ r)).prod (volume.restrict T)) := by
    have h := hQr
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod] at h
    change Integrable (fun z : Vec3 × ℝ => spatialGradientSq u Du z)
      (((volume : Measure Vec3).prod volume).restrict
        (vec3Ball x₀ r ×ˢ T)) at h
    rw [← Measure.prod_restrict] at h
    simpa only using h
  have hDtimeB : Integrable (fun t => ∫ x in vec3Ball x₀ r,
      spatialGradientSq u Du (x, t)) (volume.restrict T) :=
    hDprodBT.integral_prod_right
  have hRprodT : Integrable (fun z : Vec3 × ℝ =>
      spatialGradientSq u Du z * F z)
      ((volume.restrict Ω).prod (volume.restrict T)) := by
    apply hDprod.mono_measure
    exact Measure.prod_mono (Measure.restrict_le_self) (Measure.restrict_le_self)
  have hRtime : Integrable (fun t => ∫ x in Ω,
      spatialGradientSq u Du (x, t) * F (x, t)) (volume.restrict T) :=
    hRprodT.integral_prod_right
  have hRprodAll : Integrable (fun z : Vec3 × ℝ =>
      spatialGradientSq u Du z * F z)
      ((volume.restrict Ω).prod (volume : Measure ℝ)) := by
    apply hDprod.mono_measure
    exact Measure.prod_mono (Measure.restrict_le_self) le_rfl
  have hRtimeAll : Integrable (fun t => ∫ x in Ω,
      spatialGradientSq u Du (x, t) * F (x, t)) (volume : Measure ℝ) :=
    hRprodAll.integral_prod_right
  have hGae : ∀ᵐ t ∂volume.restrict T,
      (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in vec3Ball x₀ r,
        spatialGradientSq u Du (x, s)) ≤ 1000 * r * S := by
    have hTmem : ∀ᵐ t ∂volume.restrict T, t ∈ T :=
      ae_restrict_mem measurableSet_Ioc
    have hDgood : ∀ᵐ s ∂volume.restrict T,
        IntegrableOn (fun x : Vec3 => spatialGradientSq u Du (x, s))
            (vec3Ball x₀ r) volume := hdu_int
    have hRgood : ∀ᵐ s ∂volume.restrict T,
        IntegrableOn (fun x : Vec3 => spatialGradientSq u Du (x, s) * F (x, s))
            Ω volume := hDtimeT
    filter_upwards [henergyTF, hTmem] with t ht htT
    have htT' : t₀ - r ^ 2 < t ∧ t ≤ t₀ := by
      change t₀ - r ^ 2 < t ∧ t ≤ t₀ at htT
      exact htT
    have hIntT : Ioc (t₀ - r ^ 2) t ⊆ T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans htT'.2⟩
    have hDint : IntegrableOn (fun s => ∫ x in vec3Ball x₀ r,
        spatialGradientSq u Du (x, s)) (Ioc (t₀ - r ^ 2) t) volume :=
      hDtimeB.mono_measure (Measure.restrict_mono_set volume hIntT)
    have hRint : IntegrableOn (fun s => ∫ x in Ω,
        spatialGradientSq u Du (x, s) * F (x, s))
        (Ioc (t₀ - r ^ 2) t) volume :=
      hRtime.mono_measure (Measure.restrict_mono_set volume hIntT)
    have hpoint : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - r ^ 2) t),
        (∫ x in vec3Ball x₀ r, spatialGradientSq u Du (x, s)) ≤
          2000 * r * (∫ x in Ω,
            spatialGradientSq u Du (x, s) * F (x, s)) := by
      have hDgood' := ae_restrict_of_ae_restrict_of_subset hIntT hDgood
      have hRgood' := ae_restrict_of_ae_restrict_of_subset hIntT hRgood
      have hIntmem : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - r ^ 2) t),
          s ∈ Ioc (t₀ - r ^ 2) t := ae_restrict_mem measurableSet_Ioc
      filter_upwards [hDgood', hRgood', hIntmem] with s hsD hsR hs
      have hlocal : (∫ x in vec3Ball x₀ r,
          (1 / (2000 * r)) * spatialGradientSq u Du (x, s)) ≤
          ∫ x in vec3Ball x₀ r,
            spatialGradientSq u Du (x, s) * F (x, s) := by
        refine setIntegral_mono_on (hsD.const_mul _)
          (hsR.mono_set hB)
          (vec3Ball_measurable x₀ r) ?_
        intro x hx
        have hxQ : (x, s) ∈ parabolicCylinder x₀ t₀ r :=
          ⟨hx, hs.1, hs.2.trans htT'.2⟩
        have hlow : 1 / (2000 * r) ≤ F (x, s) := by
          have hxhalf : x ∈ vec3Ball x₀ (ρ / 2) := hx.trans_le hscale
          have hη := caccioppoli_heat_cutoff_eq_one_on x₀ t₀ ρ ε r
            hρ hε hr hscale (z := (x, s)) hxhalf
            ⟨hs.1, le_trans (hs.2.trans htT'.2) (le_add_of_nonneg_right (half_pos hε).le)⟩
          have htime : s - t₀ < r ^ 2 :=
            lt_of_le_of_lt (sub_nonpos.mpr (hs.2.trans htT'.2)) (sq_pos_of_pos hr)
          unfold F backwardHeat_cutoff
          simp only [ite_eq_left htime, hη, one_mul]
          simpa only [centeredBackwardHeatTest] using
            centeredBackwardHeatTest_lower_on_cylinder hr hxQ
        have hDnonneg : 0 ≤ spatialGradientSq u Du (x, s) := by
          unfold spatialGradientSq
          exact Finset.sum_nonneg (fun i _ =>
            Finset.sum_nonneg (fun j _ => sq_nonneg _))
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlow hDnonneg
      have hΩlocal : (∫ x in vec3Ball x₀ r,
          spatialGradientSq u Du (x, s) * F (x, s)) ≤
          ∫ x in Ω, spatialGradientSq u Du (x, s) * F (x, s) := by
        apply setIntegral_mono_set hsR
        · filter_upwards [] with x
          exact mul_nonneg (by unfold spatialGradientSq; positivity)
            (htest.2 (x, s))
        · exact Filter.Eventually.of_forall hB
      calc
        _ = (2000 * r) * (∫ x in vec3Ball x₀ r,
            (1 / (2000 * r)) * spatialGradientSq u Du (x, s)) := by
              rw [integral_const_mul]
              field_simp [hr.ne']
        _ ≤ (2000 * r) * (∫ x in Ω,
            spatialGradientSq u Du (x, s) * F (x, s)) :=
          mul_le_mul_of_nonneg_left (hlocal.trans hΩlocal) (by positivity)
    have hprefix := integral_mono_ae hDint
      (hRint.const_mul (2000 * r)) hpoint
    have hprefix' : (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in vec3Ball x₀ r,
        spatialGradientSq u Du (x, s)) ≤
        2000 * r * (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s)) := by
      simpa only [integral_const_mul] using hprefix
    have hprefixR : (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s)) ≤
        ∫ s in Iio t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s) := by
      calc
        _ ≤ ∫ s in Iic t, ∫ x in Ω,
            spatialGradientSq u Du (x, s) * F (x, s) := by
          have hRintIic : IntegrableOn (fun s => ∫ x in Ω,
              spatialGradientSq u Du (x, s) * F (x, s)) (Iic t) volume :=
            hRtimeAll.integrableOn.mono_set (subset_univ _)
          apply setIntegral_mono_set (s := Ioc (t₀ - r ^ 2) t)
            (t := Iic t) hRintIic
          · filter_upwards [] with s
            apply integral_nonneg_of_ae
            filter_upwards [] with x
            have hDnonneg : 0 ≤ spatialGradientSq u Du (x, s) := by
              unfold spatialGradientSq
              exact Finset.sum_nonneg (fun i _ =>
                Finset.sum_nonneg (fun j _ => sq_nonneg _))
            exact mul_nonneg hDnonneg (htest.2 (x, s))
          · exact Filter.Eventually.of_forall (fun s hs => hs.2)
        _ = ∫ s in Iio t, ∫ x in Ω,
            spatialGradientSq u Du (x, s) * F (x, s) :=
          integral_Iic_eq_integral_Iio
    have hnonnegE : 0 ≤ ∫ x in Ω,
        (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact mul_nonneg (by positivity) (htest.2 (x, t))
    have henergy_prefix : 2 * (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s)) ≤ S := by
        calc
          2 * _ ≤ 2 * (∫ s in Iio t, ∫ x in Ω,
              spatialGradientSq u Du (x, s) * F (x, s)) := by
                exact mul_le_mul_of_nonneg_left hprefixR (by norm_num)
          _ ≤ (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * F (x, t)) +
              2 * (∫ s in Iio t, ∫ x in Ω,
                spatialGradientSq u Du (x, s) * F (x, s)) :=
            le_add_of_nonneg_left hnonnegE
          _ ≤ S := ht
    have hweighted : (∫ s in Ioc (t₀ - r ^ 2) t, ∫ x in Ω,
          spatialGradientSq u Du (x, s) * F (x, s)) ≤ S / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa only [mul_comm] using henergy_prefix
    have hleft := hprefix'
    calc
        _ ≤ 2000 * r * (S / 2) := hleft.trans
          (mul_le_mul_of_nonneg_left hweighted (by positivity))
      _ = 1000 * r * S := by ring
  let g : ℝ → ℝ := fun s => ∫ x in vec3Ball x₀ r,
    spatialGradientSq u Du (x, s)
  have hgint : IntegrableOn g T volume := by
    change Integrable g (volume.restrict T)
    simpa only [g] using hDtimeB
  have hgnonneg : ∀ᵐ s ∂volume.restrict T, 0 ≤ g s := by
    filter_upwards [] with s
    dsimp only [g]
    apply integral_nonneg_of_ae
    filter_upwards [] with x
    unfold spatialGradientSq
    positivity
  let upper : ℕ → ℝ := fun n => t₀ - r ^ 2 / ((n : ℝ) + 2)
  let A : ℕ → Set ℝ := fun n => Ioc (t₀ - r ^ 2) (upper n)
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact measurableSet_Ioc
  have hAmono : Monotone A := by
    intro m n hmn s hs
    have hden : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hmn 2
    have hfrac : r ^ 2 / ((n : ℝ) + 2) ≤ r ^ 2 / ((m : ℝ) + 2) := by
      gcongr
    have hupper : upper m ≤ upper n := by
      dsimp only [upper]
      exact sub_le_sub_left hfrac t₀
    exact ⟨hs.1, hs.2.trans hupper⟩
  have hAunion : ⋃ n, A n = Ioo (t₀ - r ^ 2) t₀ := by
    ext s
    constructor
    · intro hs
      rcases mem_iUnion.mp hs with ⟨n, hs⟩
      have hpos : 0 < r ^ 2 / ((n : ℝ) + 2) := by positivity
      exact ⟨hs.1, lt_of_le_of_lt hs.2 (by
        dsimp only [upper]
        exact sub_lt_self _ hpos)⟩
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (div_pos (sub_pos.mpr hs.2) (sq_pos_of_pos hr))
      have hfrac : r ^ 2 / ((n : ℝ) + 2) < t₀ - s := by
        have hstep : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
          exact one_div_le_one_div_of_le (by positivity) (by norm_num)
        calc
          r ^ 2 / ((n : ℝ) + 2) ≤ r ^ 2 / ((n : ℝ) + 1) := by
            exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (by norm_num)
          _ = r ^ 2 * (1 / ((n : ℝ) + 1)) := by ring
          _ < r ^ 2 * ((t₀ - s) / r ^ 2) := by
            exact mul_lt_mul_of_pos_left hn (sq_pos_of_pos hr)
          _ = t₀ - s := by field_simp [hr.ne']
      apply mem_iUnion.mpr
      refine ⟨n, hs.1, ?_⟩
      dsimp only [upper]
      exact le_sub_comm.mp hfrac.le
  have hAint : IntegrableOn g (⋃ n, A n) volume := by
    rw [hAunion]
    exact hgint.mono_set (fun s hs => ⟨hs.1, hs.2.le⟩)
  have hAn : ∀ n, (∫ s in A n, g s) ≤ 1000 * r * S := by
    intro n
    let D : Set ℝ := Ioc (upper n) t₀
    have hDsub : D ⊆ T := by
      intro s hs
      have hfraclt : r ^ 2 / ((n : ℝ) + 2) < r ^ 2 := by
        exact div_lt_self (sq_pos_of_pos hr)
          (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
            (le_add_of_nonneg_left (Nat.cast_nonneg n)))
      have hlower : t₀ - r ^ 2 < upper n := by
        dsimp only [upper]
        exact sub_lt_sub_left hfraclt t₀
      exact ⟨hlower.trans hs.1, hs.2⟩
    have hDmeasure : volume D ≠ 0 := by
      rw [Real.volume_Ioc]
      apply (ENNReal.ofReal_pos.mpr _).ne'
      dsimp only [D, upper]
      have hpos : 0 < r ^ 2 / ((n : ℝ) + 2) := by positivity
      exact sub_pos.mpr (sub_lt_self _ hpos)
    have hbound : ∀ᵐ t ∂volume.restrict T,
        (∫ s in Ioc (t₀ - r ^ 2) t, g s) ≤ 1000 * r * S := by
      simpa only [g] using hGae
    have hboundD := ae_restrict_of_ae_restrict_of_subset hDsub hbound
    obtain ⟨t, htD, htbound⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hDmeasure hboundD
    have hAt_sub : Ioc (t₀ - r ^ 2) t ⊆ T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans htD.2⟩
    have hAtint : IntegrableOn g (Ioc (t₀ - r ^ 2) t) volume :=
      hgint.mono_set hAt_sub
    have hAtnonneg : 0 ≤ᵐ[volume.restrict (Ioc (t₀ - r ^ 2) t)] g :=
      ae_restrict_of_ae_restrict_of_subset hAt_sub hgnonneg
    have hAsub : A n ⊆ Ioc (t₀ - r ^ 2) t := by
      intro s hs
      exact ⟨hs.1, hs.2.trans htD.1.le⟩
    exact (setIntegral_mono_set hAtint hAtnonneg
      (Filter.Eventually.of_forall hAsub)).trans htbound
  have hAlim := tendsto_setIntegral_of_monotone (f := g)
    hAmeas hAmono hAint
  have hIunion : (∫ s in ⋃ n, A n, g s) ≤ 1000 * r * S :=
    le_of_tendsto hAlim (Filter.Eventually.of_forall hAn)
  have hIoo : (∫ s in Ioo (t₀ - r ^ 2) t₀, g s) ≤ 1000 * r * S := by
    simpa only [hAunion] using hIunion
  have hGfull : (∫ s in T, g s) ≤ 1000 * r * S := by
    simpa only [T, integral_Ioc_eq_integral_Ioo] using hIoo
  have hDrect : IntegrableOn (fun z => spatialGradientSq u Du z)
      (vec3Ball x₀ r ×ˢ T) ((volume : Measure Vec3).prod volume) := by
    change Integrable (fun z => spatialGradientSq u Du z)
      ((volume.prod volume).restrict (vec3Ball x₀ r ×ˢ T))
    rw [← Measure.prod_restrict]
    exact hDprodBT
  have hGreal : (∫ z in Q, spatialGradientSq u Du z) ≤ 1000 * r * S := by
    calc
      (∫ z in Q, spatialGradientSq u Du z) = ∫ s in T, g s := by
        change (∫ z in (vec3Ball x₀ r ×ˢ T), spatialGradientSq u Du z) = _
        exact (caccioppoli_nested_integral_eq hDrect).symm
      _ ≤ 1000 * r * S := hGfull
  have hDnonnegQ : 0 ≤ᵐ[volume.restrict Q]
      (fun z => spatialGradientSq u Du z) := by
    filter_upwards [] with z
    unfold spatialGradientSq
    positivity
  have hGconv : (∫ z in Q, spatialGradientSq u Du z) =
      (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)).toReal :=
    setIntegral_eq_toReal_setLIntegral_of_nonneg hQr hDnonnegQ
  have hGtop : (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hQr.aestronglyMeasurable
      hDnonnegQ).2 hQr
  have hCnonneg : 0 ≤ 1000 * r * S := by positivity
  have hGtoReal : (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)).toReal ≤
      1000 * r * S := by
    rw [← hGconv]
    exact hGreal
  have hG : (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)) ≤
      ENNReal.ofReal (1000 * r * S) := by
    apply (ENNReal.toReal_le_toReal hGtop ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hCnonneg] using hGtoReal
  simpa only [S] using caccioppoli_lower_from_slice_bounds hr hS hEae hG

end CKN
