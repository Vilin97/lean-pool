/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWS
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.TimeHolder

/-!
# Pk Bounds P7 Solution

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

theorem eLpNorm'_prod_three_halves
    {P : Vec3 × ℝ → ℝ} {B : Set Vec3} {T : Set ℝ}
    (hP : AEStronglyMeasurable P
      (volume.restrict (B ×ˢ T)))
    {D : ℝ → ℝ≥0∞}
    (hD : ∀ᵐ s ∂volume.restrict T,
      eLpNorm' (fun x : Vec3 => P (x, s)) (15 : ℝ) volume ≤ D s) :
    eLpNorm' P (3 / 2 : ℝ) (volume.restrict (B ×ˢ T)) ≤
      (∫⁻ s in T, (D s * volume B ^ (3 / 5 : ℝ)) ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) := by
  have hP' : AEStronglyMeasurable P
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict B T]
    exact hP
  have hPs : ∀ᵐ s ∂volume.restrict T,
      AEStronglyMeasurable (fun x : Vec3 => P (x, s)) (volume.restrict B) :=
    hP'.prodMk_right
  have hpoint : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in B, ‖P (x, s)‖ₑ ^ (3 / 2 : ℝ)) ≤
        (D s * volume B ^ (3 / 5 : ℝ)) ^ (3 / 2 : ℝ) := by
    filter_upwards [hD, hPs] with s hs hms
    have hlow := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
      (f := fun x : Vec3 => P (x, s)) (μ := volume.restrict B)
      (p := (3 / 2 : ℝ)) (q := (15 : ℝ)) (by norm_num) (by norm_num) hms
    have hhigh : eLpNorm' (fun x : Vec3 => P (x, s)) (15 : ℝ)
        (volume.restrict B) ≤ eLpNorm' (fun x : Vec3 => P (x, s)) (15 : ℝ) volume :=
      eLpNorm'_mono_measure (fun x : Vec3 => P (x, s))
        Measure.restrict_le_self (by norm_num)
    have hlow' : eLpNorm' (fun x : Vec3 => P (x, s)) (3 / 2 : ℝ)
        (volume.restrict B) ≤ D s * volume B ^ (3 / 5 : ℝ) := by
      calc
        _ ≤ eLpNorm' (fun x : Vec3 => P (x, s)) (15 : ℝ) volume *
            (volume.restrict B) Set.univ ^ (1 / (3 / 2 : ℝ) - 1 / (15 : ℝ)) :=
          hlow.trans (mul_le_mul_of_nonneg_right hhigh (by positivity))
        _ ≤ D s * (volume.restrict B) Set.univ ^
              (1 / (3 / 2 : ℝ) - 1 / (15 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hs (by positivity)
        _ = D s * volume B ^ (3 / 5 : ℝ) := by
          simp only [Measure.restrict_apply_univ]
          congr 1
          norm_num
    rw [eLpNorm'_eq_lintegral_enorm] at hlow'
    have hpow := ENNReal.rpow_le_rpow hlow' (by norm_num : (0 : ℝ) ≤ 3 / 2)
    simpa only [← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ (by norm_num : (3 / 2 : ℝ) ≠ 0), ENNReal.rpow_one] using hpow
  rw [eLpNorm'_eq_lintegral_enorm]
  rw [show volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) by
    rw [Measure.prod_restrict B T, MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
  rw [MeasureTheory.lintegral_prod _ (hP'.enorm.pow_const (3 / 2 : ℝ))]
  rw [MeasureTheory.lintegral_lintegral_swap
    (hP'.enorm.pow_const (3 / 2 : ℝ))]
  have hmon := lintegral_mono_ae hpoint
  simpa only [show (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) by norm_num] using
    (ENNReal.rpow_le_rpow hmon (by norm_num : (0 : ℝ) ≤ 2 / 3))

private theorem component_aestronglyMeasurable
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {g : α → Vec3} (hg : AEStronglyMeasurable g μ) (j : Fin 3) :
    AEStronglyMeasurable (fun x => g x j) μ := by
  obtain ⟨g', hg', hgg'⟩ := hg
  have hg'' : StronglyMeasurable (fun x => g' x j) :=
    (Continuous.comp_stronglyMeasurable
      (ContinuousLinearMap.continuous
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)) hg')
  exact ⟨fun x => g' x j, hg'', hgg'.mono fun x hx => by simp [hx]
    ⟩

private theorem vec3_norm_le_euclidean (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg v)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j))
    (Finset.mem_univ i)

private theorem sws_force_norm_integral_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono ?_)
    (sws_force_integral_lt_top hsol (z := (x₀, t₀)) (r := ρ) hρ hsub)
  intro w
  change ‖f w‖ₑ ^ q ≤ ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q
  rw [← ofReal_norm]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (vec3_norm_le_euclidean (f w)))
    (by linarith only [hsol.2.2.2.1])

private theorem source_eLpNorm_five_halves_le
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3} {q ρ s : ℝ}
    (hq : 5 / 2 < q) (hηbound : ∀ y, |η y| ≤ 1)
    (hηsupp : tsupport η ⊆ vec3Ball (x₀ : Vec3) ρ)
    (hf : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hI : (∫⁻ y in vec3Ball x₀ ρ, ‖f (y, s)‖ₑ ^ q) < ⊤)
    (j : Fin 3)
    (hsource : AEStronglyMeasurable
      (fun y : Vec3 => η y * f (y, s) j) volume) :
    eLpNorm' (fun y : Vec3 => η y * f (y, s) j) (5 / 2 : ℝ) volume ≤
      eLpNorm' (fun y : Vec3 => f (y, s)) q
          (volume.restrict (vec3Ball x₀ ρ)) *
        volume (vec3Ball x₀ ρ) ^ (2 / 5 - 1 / q : ℝ) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  let g : Vec3 → ℝ := fun y => η y * f (y, s) j
  have hfq : eLpNorm' (fun y : Vec3 => f (y, s)) q
      (volume.restrict B) < ⊤ := by
    rw [eLpNorm'_eq_lintegral_enorm]
    have hq0 : 0 < q := by linarith only [hq]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ne_of_lt (by simpa [B] using hI))
  have hfB : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict B) := by simpa [B] using hf
  have hcomp : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
      (volume.restrict B) := by
    obtain ⟨g', hg', hfg'⟩ := hfB
    have hg'' : StronglyMeasurable (fun y : Vec3 => g' y j) :=
      (Continuous.comp_stronglyMeasurable
        (ContinuousLinearMap.continuous
          (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)) hg')
    exact ⟨fun y => g' y j, hg'', hfg'.mono fun y hy => by simp [hy]
      ⟩
  have hcomp_le : ∀ᵐ y ∂volume.restrict B,
      ‖f (y, s) j‖ ≤ ‖f (y, s)‖ := by
    filter_upwards [] with y
    exact norm_le_pi_norm _ _
  have hlow := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
    (f := fun y : Vec3 => f (y, s) j) (μ := volume.restrict B)
    (p := (5 / 2 : ℝ)) (q := q) (by norm_num) (by linarith only [hq]) hcomp
  have hcompq : eLpNorm' (fun y : Vec3 => f (y, s) j) q
      (volume.restrict B) ≤ eLpNorm' (fun y : Vec3 => f (y, s)) q
        (volume.restrict B) := by
    exact eLpNorm'_mono_ae (by linarith only [hq]) hcomp_le
  have hlow' : eLpNorm' (fun y : Vec3 => f (y, s) j) (5 / 2 : ℝ)
      (volume.restrict B) ≤ eLpNorm' (fun y : Vec3 => f (y, s)) q
        (volume.restrict B) * volume B ^ (2 / 5 - 1 / q : ℝ) := by
    calc
      _ ≤ eLpNorm' (fun y : Vec3 => f (y, s) j) q (volume.restrict B) *
          (volume.restrict B) Set.univ ^ (1 / (5 / 2 : ℝ) - 1 / q) := hlow
      _ ≤ _ := mul_le_mul_of_nonneg_right hcompq (by positivity)
      _ = _ := by
        simp only [Measure.restrict_apply_univ]
        congr 1
        norm_num
  have hzero : ∀ y ∉ B, g y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport η := fun hyt => hy (hηsupp hyt)
    have hηzero : η y = 0 := image_eq_zero_of_notMem_tsupport hy'
    simp [g, hηzero]
  have hsource_meas : AEStronglyMeasurable g volume := by
    simpa [g] using hsource
  have hsource_norm : eLpNorm' g (5 / 2 : ℝ) volume ≤
      eLpNorm' (fun y : Vec3 => f (y, s)) q (volume.restrict B) *
        volume B ^ (2 / 5 - 1 / q : ℝ) := by
    rw [eLpNorm'_eq_lintegral_enorm]
    have hfull : (∫⁻ y, ‖g y‖ₑ ^ (5 / 2 : ℝ)) =
        ∫⁻ y in B, ‖g y‖ₑ ^ (5 / 2 : ℝ) := by
      rw [← lintegral_indicator (vec3Ball_measurable x₀ ρ)]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ B
      · have hy' : y ∈ vec3Ball x₀ ρ := by simpa [B] using hy
        rw [indicator_of_mem hy']
      · rw [indicator_of_notMem hy]
        rw [hzero y hy]
        simp
    rw [hfull]
    have hInt : (∫⁻ y in B, ‖g y‖ₑ ^ (5 / 2 : ℝ)) ≤
        ∫⁻ y in B, ‖f (y, s) j‖ₑ ^ (5 / 2 : ℝ) := by
      apply lintegral_mono
      intro y
      have habs : |η y * f (y, s) j| ≤ |f (y, s) j| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hηbound y)
      have hbase : ‖g y‖ₑ ≤ ‖f (y, s) j‖ₑ := by
        simpa only [g, ← ofReal_norm, Real.norm_eq_abs] using
          (ENNReal.ofReal_le_ofReal habs)
      exact ENNReal.rpow_le_rpow hbase (by norm_num)
    have hpow := ENNReal.rpow_le_rpow hInt (by norm_num : (0 : ℝ) ≤ 2 / 5)
    calc
      (∫⁻ y in B, ‖g y‖ₑ ^ (5 / 2 : ℝ)) ^ (1 / (5 / 2 : ℝ)) ≤
          (∫⁻ y in B, ‖f (y, s) j‖ₑ ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
        convert hpow using 1
        all_goals norm_num
      _ = eLpNorm' (fun y : Vec3 => f (y, s) j) (5 / 2 : ℝ)
          (volume.restrict B) := by
        rw [eLpNorm'_eq_lintegral_enorm]
        norm_num
      _ ≤ _ := hlow'
  simpa [g, B] using hsource_norm

private theorem sws_force_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      AEStronglyMeasurable (fun x : Vec3 => f (x, s))
          (volume.restrict (vec3Ball x₀ ρ)) ∧
        (∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q) < ⊤ := by
  have hΩ : IsOpen Ω := hsol.1
  have hIopen : IsOpen I := hsol.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ :=
    exists_localBox_of_closure_subset hΩ hIopen hρ hsub
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hB : B ⊆ Ω' := by
    intro y hy
    have hz : (y, t₀) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by nlinarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hz).1
  have hT : T ⊆ J := by
    intro s hs
    have hs' : s ∈ Ioc (t₀ - ρ ^ 2) t₀ := by simpa [T] using hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs'⟩
    exact (hcyl hz).2
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.1
  have hfprod' : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hfglobal
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod'.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB)
        (Measure.restrict_mono_set volume hT))
  have hFpow : AEMeasurable
      (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ q)
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod.enorm.pow_const q
  have hFtime : AEMeasurable (fun s : ℝ =>
      ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) (volume.restrict T) :=
    hFpow.lintegral_prod_left'
  have htotal : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) =
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
    have hprod : (∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q) =
        ∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q := by
      rw [show volume.restrict (B ×ˢ T) =
          (volume.restrict B).prod (volume.restrict T) by
        rw [Measure.prod_restrict B T,
          MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
      rw [MeasureTheory.lintegral_prod _ hFpow]
      rw [MeasureTheory.lintegral_lintegral_swap hFpow]
    calc
      _ = ∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q := hprod.symm
      _ = ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
        rw [parabolicCylinder, MeasureTheory.Measure.volume_eq_prod Vec3 ℝ,
          volume_parabolicPoint_eq_prod]
        rfl
  have htotal_lt : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) < ⊤ := by
    rw [htotal]
    exact sws_force_norm_integral_lt_top hsol hρ hsub
  have hIae : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) < ⊤ :=
    ae_lt_top' hFtime (ne_of_lt htotal_lt)
  filter_upwards [hfprod.prodMk_right, hIae] with s hfs hIf
  exact ⟨hfs, hIf⟩

private theorem p7_slice_source_data
    {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {V : Set Vec3}
    {q ρ s : ℝ} {x₀ : Vec3}
    (hq : 5 / 2 < q) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) (hηbound : ∀ y, |η y| ≤ 1)
    (hηmeas : AEStronglyMeasurable η volume)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hfs : Integrable (fun x : Vec3 => f (x, s))
      (volume.restrict V))
    (hfB : AEStronglyMeasurable (fun x : Vec3 => f (x, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hI : (∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q) < ⊤) :
    ∀ j, AEStronglyMeasurable (fun y => η y * f (y, s) j) volume ∧
      AEStronglyMeasurable
      (fun x => pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j) x) volume ∧
      (∫⁻ y, ENNReal.ofReal |η y * f (y, s) j| ^ (5 / 2 : ℝ)) < ∞ := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hηmeasV : AEStronglyMeasurable η (volume.restrict V) :=
    hηmeas.mono_measure Measure.restrict_le_self
  have hsourceInt : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume := by
    intro j
    have hfc : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) :=
      component_aestronglyMeasurable hfs.aestronglyMeasurable j
    have hfcint : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfcint.mul_bdd hηmeasV
      (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hηbound y))
    have hmul' : Integrable (fun y : Vec3 => η y * f (y, s) j)
        (volume.restrict V) := by simpa [mul_comm] using hmul
    have hmulOn : IntegrableOn (fun y : Vec3 => η y * f (y, s) j) V volume := hmul'
    have hsourceV : tsupport (fun y : Vec3 => η y * f (y, s) j) ⊆ V :=
      (tsupport_mul_subset_left (f := η)
        (g := fun y : Vec3 => f (y, s) j)).trans hηV
    exact decomposition_full_of_on_sws hmulOn hsourceV
  have hsourceSupp : ∀ j, HasCompactSupport
      (fun y : Vec3 => η y * f (y, s) j) := by
    intro j
    change HasCompactSupport (η * (fun y : Vec3 => f (y, s) j))
    exact hηc.mul_right
  have hsource : ∀ j, AEStronglyMeasurable
      (fun y => η y * f (y, s) j) volume := fun j =>
    (hsourceInt j).aestronglyMeasurable
  have hpotential : ∀ j, AEStronglyMeasurable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) volume := by
    intro j
    exact (pressureNewtonianDerivativePotential_locallyIntegrable j
      (hsourceInt j) (hsourceSupp j)).aestronglyMeasurable
  intro j
  refine ⟨hsource j, hpotential j, ?_⟩
  have hnorm := source_eLpNorm_five_halves_le
    (x₀ := x₀) hq hηbound hηsupport (by simpa [B] using hfB)
      (by simpa [B] using hI) j (hsource j)
  have hqnorm : eLpNorm' (fun y : Vec3 => f (y, s)) q
      (volume.restrict B) < ⊤ := by
    rw [eLpNorm'_eq_lintegral_enorm]
    simpa [B] using
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt hI))
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hexp : 0 ≤ 2 / 5 - 1 / q := by
    have hqle : 1 / q ≤ (2 / 5 : ℝ) := by
      apply (div_le_iff₀ hqpos).2
      nlinarith only [hq]
    linarith only [hqle]
  have hright : eLpNorm' (fun y : Vec3 => f (y, s)) q
      (volume.restrict B) * volume B ^ (2 / 5 - 1 / q : ℝ) < ⊤ :=
    ENNReal.mul_lt_top hqnorm
      (ENNReal.rpow_lt_top_of_nonneg hexp
        (ne_of_lt (volume_vec3Ball_lt_top (x := x₀) (r := ρ))))
  have hnormtop : eLpNorm' (fun y : Vec3 => η y * f (y, s) j)
      (5 / 2 : ℝ) volume < ⊤ := hnorm.trans_lt hright
  have hmem : MemLp (fun y : Vec3 => η y * f (y, s) j)
      (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
    rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofReal_ne_top]
    · rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 2)]
      exact hnormtop
    · exact hsource j
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ENNReal.ofReal (5 / 2 : ℝ)) (by norm_num) ENNReal.ofReal_ne_top
    hmem.eLpNorm_lt_top
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 2),
    ← ofReal_norm, Real.norm_eq_abs]
    using hlt

theorem sws_p7_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} {x₀ : Vec3} {t₀ ρ : ℝ}
    (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hηbound : ∀ y, |η y| ≤ 1)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hηmeas : AEStronglyMeasurable η volume) :
    ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      AEStronglyMeasurable (fun x : Vec3 => f (x, s))
          (volume.restrict (vec3Ball x₀ ρ)) ∧
        (∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q) < ⊤ ∧
        (∀ j, AEStronglyMeasurable
            (fun y => η y * f (y, s) j) volume ∧
          AEStronglyMeasurable
            (fun x => pressureNewtonianDerivativePotential j
              (fun y => η y * f (y, s) j) x) volume ∧
          (∫⁻ y, ENNReal.ofReal |η y * f (y, s) j| ^ (5 / 2 : ℝ)) < ∞) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hforceData := sws_force_slice_data hsol hρ hsub
  have hT_I : T ⊆ I := by
    intro s hs
    have hs' : s ∈ Ioc (t₀ - ρ ^ 2) t₀ := by simpa [T] using hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs'⟩
    exact (hsub (subset_closure hz)).2
  obtain ⟨V, hVopen, hηV, -, hVcompact, hVΩ, hslice⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  have hsliceT : ∀ᵐ s ∂volume.restrict T,
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict V) ∧
      Integrable (fun x : Vec3 => p (x, s)) (volume.restrict V) ∧
      Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V) :=
    (MeasureTheory.ae_mono (Measure.restrict_mono_set volume hT_I)) hslice
  filter_upwards [hforceData, hsliceT] with s ⟨hfs, hIf⟩ hdata
  have hsources := p7_slice_source_data
    (f := f) (η := η) (V := V) (q := q) (ρ := ρ)
    (x₀ := x₀) (s := s) hsol.2.2.2.1 hηc hηV hηbound hηmeas hηsupport
    hdata.2.2 hfs hIf
  exact ⟨hfs, hIf, hsources⟩

theorem force_time_norm_bound
    {H : ℝ → ℝ≥0∞} {T : Set ℝ} {q A : ℝ}
    (hq : 0 < q) (hA : 0 ≤ A)
    (hHae : ∀ᵐ s ∂volume.restrict T, H s < ⊤)
    (hglobal : (∫⁻ s in T, H s) ≤ ENNReal.ofReal (A ^ q)) :
    eLpNorm' (fun s => (H s).toReal ^ (1 / q)) q
        (volume.restrict T) ≤ ENNReal.ofReal A := by
  let g : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q)
  have hpow : ∀ᵐ s ∂volume.restrict T,
      ‖g s‖ₑ ^ q = H s := by
    filter_upwards [hHae] with s hs
    have hmul : (1 / q) * q = (1 : ℝ) := by
      field_simp
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _) hq.le]
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hmul, Real.rpow_one,
      ENNReal.ofReal_toReal hs.ne]
  have hlin : (∫⁻ s in T, ‖g s‖ₑ ^ q) = ∫⁻ s in T, H s := by
    apply lintegral_congr_ae
    exact hpow
  have hnorm : eLpNorm' g q (volume.restrict T) ≤ ENNReal.ofReal A := by
    rw [eLpNorm'_eq_lintegral_enorm, hlin]
    calc
      (∫⁻ s in T, H s) ^ (1 / q) ≤
          (ENNReal.ofReal (A ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hglobal (by positivity)
      _ = ENNReal.ofReal A := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hA hq.le,
          ← ENNReal.rpow_mul]
        rw [show q * (1 / q) = (1 : ℝ) by field_simp]
        simp
  simpa [g] using hnorm

theorem ennreal_rpow_eq_ofReal_toReal_rpow
    {a : ℝ≥0∞} {q : ℝ} (ha : a ≠ ⊤) (hq : 0 < q) :
    a ^ (1 / q : ℝ) = ENNReal.ofReal (a.toReal ^ (1 / q : ℝ)) := by
  rw [← ENNReal.ofReal_toReal ha]
  rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
  simp

theorem sws_force_time_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    AEMeasurable
        (fun s : ℝ => ∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q)
        (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)) ∧
      (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀,
          ∫⁻ x in vec3Ball x₀ ρ, ‖f (x, s)‖ₑ ^ q) ≤
        ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f (x₀, t₀) ρ) ^ q) := by
  have hΩ : IsOpen Ω := hsol.1
  have hIopen : IsOpen I := hsol.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ :=
    exists_localBox_of_closure_subset hΩ hIopen hρ hsub
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hB : B ⊆ Ω' := by
    intro y hy
    have hz : (y, t₀) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by nlinarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hz).1
  have hT : T ⊆ J := by
    intro s hs
    have hs' : s ∈ Ioc (t₀ - ρ ^ 2) t₀ := by simpa [T] using hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs'⟩
    exact (hcyl hz).2
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.1
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hfprod' : AEStronglyMeasurable f
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hfglobal
    exact hfprod'.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB)
        (Measure.restrict_mono_set volume hT))
  have hFpow : AEMeasurable
      (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ q)
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod.enorm.pow_const q
  have hFtime : AEMeasurable (fun s : ℝ =>
      ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) (volume.restrict T) :=
    hFpow.lintegral_prod_left'
  have htotal : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) =
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
    have hprod : (∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q) =
        ∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q := by
      rw [show volume.restrict (B ×ˢ T) =
          (volume.restrict B).prod (volume.restrict T) by
        rw [Measure.prod_restrict B T,
          MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
      rw [MeasureTheory.lintegral_prod _ hFpow]
      rw [MeasureTheory.lintegral_lintegral_swap hFpow]
    calc
      _ = ∫⁻ w in B ×ˢ T, ‖f w‖ₑ ^ q := hprod.symm
      _ = ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q := by
        rw [parabolicCylinder, MeasureTheory.Measure.volume_eq_prod Vec3 ℝ,
          volume_parabolicPoint_eq_prod]
        rfl
  have hforce : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f (x₀, t₀) ρ) ^ q) :=
    sws_lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow hsol
      (x₀, t₀) hρ hsub
  have hglobal : (∫⁻ s in T, ∫⁻ x in B, ‖f (x, s)‖ₑ ^ q) ≤
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f (x₀, t₀) ρ) ^ q) := by
    rw [htotal]
    calc
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ, ‖f w‖ₑ ^ q) ≤
          ∫⁻ w in parabolicCylinder x₀ t₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
        apply lintegral_mono
        intro w
        change ‖f w‖ₑ ^ q ≤
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q
        rw [← ofReal_norm]
        exact ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (vec3_norm_le_euclidean (f w)))
          (by linarith only [hsol.2.2.2.1])
      _ = _ := hforce
  exact ⟨hFtime, by simpa [B, T] using hglobal⟩

theorem pressureP7_eLpNorm15_le_slice_holder
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3} {q ρ s : ℝ}
    (hq : 5 / 2 < q) (hηbound : ∀ y, |η y| ≤ 1)
    (hηsupp : tsupport η ⊆ vec3Ball x₀ ρ)
    (hf : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hI : (∫⁻ y in vec3Ball x₀ ρ, ‖f (y, s)‖ₑ ^ q) < ⊤)
    (hsource : ∀ j, AEStronglyMeasurable
      (fun y : Vec3 => η y * f (y, s) j) volume)
    (hpotential : ∀ j, AEStronglyMeasurable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) volume)
    (hfinite : ∀ j, (∫⁻ y, ENNReal.ofReal
      |η y * f (y, s) j| ^ (5 / 2 : ℝ)) < ∞) :
    eLpNorm' (pressureP7 η f s) (15 : ℝ) volume ≤
      3 * (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant) *
        eLpNorm' (fun y : Vec3 => f (y, s)) q
          (volume.restrict (vec3Ball x₀ ρ)) *
        volume (vec3Ball x₀ ρ) ^ (2 / 5 - 1 / q : ℝ) := by
  have hHLS := pressureP7_eLpNorm15_le_hls_of_aestronglyMeasurable
    (η := η) (f := f) (s := s) hsource hpotential hfinite
  have hsource_le : ∀ j, (∫⁻ y, ENNReal.ofReal
      |η y * f (y, s) j| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≤
      eLpNorm' (fun y : Vec3 => f (y, s)) q
          (volume.restrict (vec3Ball x₀ ρ)) *
        volume (vec3Ball x₀ ρ) ^ (2 / 5 - 1 / q : ℝ) := by
    intro j
    have h := source_eLpNorm_five_halves_le hq hηbound hηsupp hf hI j
      (hsource j)
    rw [eLpNorm'_eq_lintegral_enorm] at h
    have heq : (∫⁻ y, ‖η y * f (y, s) j‖ₑ ^ (5 / 2 : ℝ)) =
        ∫⁻ y, ENNReal.ofReal |η y * f (y, s) j| ^ (5 / 2 : ℝ) := by
      apply lintegral_congr
      intro y
      rw [← ofReal_norm, Real.norm_eq_abs]
    rw [heq] at h
    simpa only [Real.norm_eq_abs, show (1 / (5 / 2 : ℝ)) = (2 / 5 : ℝ) by norm_num]
      using h
  have hsum : ∑ j : Fin 3, (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant) *
      (∫⁻ y, ENNReal.ofReal |η y * f (y, s) j| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≤
      ∑ j : Fin 3, (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant) *
        (eLpNorm' (fun y : Vec3 => f (y, s)) q
          (volume.restrict (vec3Ball x₀ ρ)) *
          volume (vec3Ball x₀ ρ) ^ (2 / 5 - 1 / q : ℝ)) := by
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hsource_le j) (by positivity)
  calc
    _ ≤ ∑ j : Fin 3, (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant) *
        (∫⁻ y, ENNReal.ofReal |η y * f (y, s) j| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := hHLS
    _ ≤ _ := hsum
    _ = _ := by simp; ring

end CKN
