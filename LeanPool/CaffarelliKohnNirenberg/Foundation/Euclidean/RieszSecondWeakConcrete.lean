/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakExterior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondBadPart
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior

/-!
# Riesz Second Weak Concrete

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Heat

private lemma rieszSecond_kernel_continuousOn_off_zero (i j : Fin 3) :
    ContinuousOn (rieszSecondKernel i j) {z : Vec3 | z ≠ 0} := by
  intro z hz
  exact (rieszSecondKernel_differentiableAt hz i j).continuousAt.continuousWithinAt

private lemma vec3_euclidean_norm_le_sqrt_three_concrete (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  exact _root_.CKN.Foundation.Euclidean.vec3_euclidean_norm_le_sqrt_three v

private lemma cube_star_sep_for_concrete {Q : DyadicIndex}
    {x : Vec3} (hx : x ∈ (rieszSecondCubeStar Q)ᶜ) :
    ∀ y ∈ dyadicCubeSet Q,
      Real.sqrt 3 * (dyadicScale Q.scale / 2) ≤
        vec3EuclideanNorm (x - y) := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let s : ℝ := dyadicScale Q.scale / 2
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (dyadicScale_pos _) (by norm_num)
  have htri : ∀ u v : Vec3,
      vec3EuclideanNorm (u + v) ≤ vec3EuclideanNorm u + vec3EuclideanNorm v := by
    intro u v
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
    exact norm_add_le _ _
  have hxstar : 2 * Real.sqrt 3 * s <
      vec3EuclideanNorm (x - c) := by
    exact lt_of_not_ge (by simpa [rieszSecondCubeStar, c, s] using hx)
  intro y hy
  have hyc : vec3EuclideanNorm (y - c) ≤ Real.sqrt 3 * s := by
    simpa [c, s] using
      (vec3_euclidean_norm_le_sqrt_three_concrete
        (y - dyadicCubeCenter Q.scale Q.corner)).trans
        (mul_le_mul_of_nonneg_left
          (by
            apply (pi_norm_le_iff_of_nonneg (by positivity)).2
            intro k
            have hy' := (mem_dyadicCube.mp hy) k
            change |y k - dyadicCubeCenter Q.scale Q.corner k| ≤
              dyadicScale Q.scale / 2
            dsimp [dyadicCubeCenter]
            rw [abs_le]
            constructor <;> nlinarith only [hy'.1, hy'.2,
              dyadicScale_pos Q.scale])
          (Real.sqrt_nonneg 3))
  have htri' : vec3EuclideanNorm (x - c) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (y - c) := by
    have heq : x - c = (x - y) + (y - c) := by abel
    rw [heq]
    exact htri _ _
  dsimp [c, s] at hxstar hyc htri' ⊢
  linarith only [hxstar, hyc, htri']

private lemma rieszSecond_bad_term_integrable
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level) (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    (Q : {Q // Q ∈ D.cubes}) {x : Vec3}
    (hx : x ∈ (rieszSecondCubeStar Q.1)ᶜ) :
    IntegrableOn (fun y => rieszSecondKernel i j (x - y) *
      dyadicBadPart F Q.1 y) (dyadicCubeSet Q.1) volume := by
  let b : Vec3 → ℝ := dyadicBadPart F Q.1
  let S : Set Vec3 := dyadicCubeSet Q.1
  let δ : ℝ := Real.sqrt 3 * (dyadicScale Q.1.scale / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos (Real.sqrt_pos.2 (by norm_num))
      (div_pos (dyadicScale_pos _) (by norm_num))
  have hsep : ∀ y ∈ S, δ ≤ vec3EuclideanNorm (x - y) := by
    intro y hy
    simpa [δ, S] using cube_star_sep_for_concrete hx y hy
  have hzero : ∀ y ∉ S, b y = 0 := by
    intro y hy
    exact Set.indicator_of_notMem hy _
  have hvol : volume S ≠ ∞ := by
    dsimp [S]
    change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hvol
  have hbS : IntegrableOn b S volume :=
    MemLp.integrable (by norm_num)
      ((dyadic_bad_part_memLp_two D hF₂ Q).mono_measure
        Measure.restrict_le_self)
  have hb : Integrable b volume :=
    hbS.integrable_of_forall_notMem_eq_zero hzero
  have hbound : ∀ y ∈ S,
      ‖rieszSecondKernel i j (x - y)‖ ≤
        4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ := by
    intro y hy
    have hnorm := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
    have hnorm' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
      simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hnorm
    have hspace : δ / 3 ≤ ‖x - y‖ := by
      linarith only [hsep y hy, hnorm']
    have hne : x - y ≠ 0 := by
      intro hzero'
      rw [hzero'] at hspace
      simp only [norm_zero] at hspace
      exact (not_lt_of_ge hspace) (by positivity)
    have hpow := inv_pow_le_inv_pow_of_le (by positivity : 0 < δ / 3)
      hspace 3
    have hcoef : 0 ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
    rw [Real.norm_eq_abs]
    calc
      |rieszSecondKernel i j (x - y)| ≤
          4 * (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 3)⁻¹ := by
        simpa [rieszSecondKernel] using
          newtonianKernel_spatialDeriv_second_size_bound hne i j
      _ ≤ 4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow hcoef
  have h := integrable_smul_kernel_shift
    (K := rieszSecondKernel i j) (g := b) (A := S) (x := x)
    (rieszSecond_kernel_continuousOn_off_zero i j) hb hzero hbound
  have hOn : IntegrableOn
      (fun y => b y • rieszSecondKernel i j (x - y)) S volume :=
    h.integrableOn
  have hEq : (fun y => b y • rieszSecondKernel i j (x - y)) =ᵐ[
      volume.restrict S] (fun y => rieszSecondKernel i j (x - y) * b y) := by
    filter_upwards [ae_restrict_mem (dyadicCube_measurable Q.1.scale Q.1.corner)]
      with y hy
    simp only [smul_eq_mul]
    ring
  change Integrable
    (fun y => rieszSecondKernel i j (x - y) *
      dyadicBadPart F Q.1 y)
    (volume.restrict (dyadicCubeSet Q.1))
  simpa [b, S, smul_eq_mul] using hOn.congr hEq

private lemma rieszSecond_bad_joint_measurable
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level) (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    (Q : {Q // Q ∈ D.cubes}) :
    AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(rieszSecondKernel i j (z.1 - z.2) -
        rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
          dyadicBadPart F Q.1 z.2|)
      ((volume.restrict (rieszSecondCubeStar Q.1)ᶜ).prod
        (volume.restrict (dyadicCubeSet Q.1))) := by
  let b : Vec3 → ℝ := dyadicBadPart F Q.1
  let E : Set Vec3 := (rieszSecondCubeStar Q.1)ᶜ
  let S : Set Vec3 := dyadicCubeSet Q.1
  have hK : Measurable (rieszSecondKernel i j) :=
    rieszSecondKernel_measurable i j
  have hK₁ : AEMeasurable (fun z : Vec3 × Vec3 =>
      rieszSecondKernel i j (z.1 - z.2)) (volume.prod volume) :=
    (hK.comp (measurable_fst.sub measurable_snd)).aemeasurable
  have hK₂ : AEMeasurable (fun z : Vec3 × Vec3 =>
      rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.1.scale Q.1.corner))
      (volume.prod volume) :=
    (hK.comp (measurable_fst.sub measurable_const)).aemeasurable
  have hb : AEMeasurable b volume :=
    (dyadic_bad_part_memLp_two D hF₂ Q).aestronglyMeasurable.aemeasurable
  have hb₂ : AEMeasurable (fun z : Vec3 × Vec3 => b z.2)
      (volume.prod volume) :=
    hb.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hglobal : AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(rieszSecondKernel i j (z.1 - z.2) -
        rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
          b z.2|) (volume.prod volume) := by
    exact ((hK₁.sub hK₂).mul hb₂).norm.ennreal_ofReal
  rw [Measure.prod_restrict]
  exact hglobal.mono_measure Measure.restrict_le_self

private lemma rieszSecond_bad_joint_swap_measurable
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level) (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    (Q : {Q // Q ∈ D.cubes}) :
    AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(rieszSecondKernel i j (z.2 - z.1) -
        rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
          dyadicBadPart F Q.1 z.1|)
      ((volume.restrict (dyadicCubeSet Q.1)).prod
        (volume.restrict (rieszSecondCubeStar Q.1)ᶜ)) := by
  let b : Vec3 → ℝ := dyadicBadPart F Q.1
  let E : Set Vec3 := (rieszSecondCubeStar Q.1)ᶜ
  let S : Set Vec3 := dyadicCubeSet Q.1
  have hK : Measurable (rieszSecondKernel i j) :=
    rieszSecondKernel_measurable i j
  have hK₁ : AEMeasurable (fun z : Vec3 × Vec3 =>
      rieszSecondKernel i j (z.2 - z.1)) (volume.prod volume) :=
    (hK.comp (measurable_snd.sub measurable_fst)).aemeasurable
  have hK₂ : AEMeasurable (fun z : Vec3 × Vec3 =>
      rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.1.scale Q.1.corner))
      (volume.prod volume) :=
    (hK.comp (measurable_snd.sub measurable_const)).aemeasurable
  have hb : AEMeasurable b volume :=
    (dyadic_bad_part_memLp_two D hF₂ Q).aestronglyMeasurable.aemeasurable
  have hb₁ : AEMeasurable (fun z : Vec3 × Vec3 => b z.1)
      (volume.prod volume) :=
    hb.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))
  have hglobal : AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(rieszSecondKernel i j (z.2 - z.1) -
        rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
          b z.1|) (volume.prod volume) := by
    exact ((hK₁.sub hK₂).mul hb₁).norm.ennreal_ofReal
  rw [Measure.prod_restrict]
  exact hglobal.mono_measure Measure.restrict_le_self

theorem rieszSecond_bad_cube_data
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level) (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    ∀ Q : {Q // Q ∈ D.cubes},
      IntegrableOn (dyadicBadPart F Q.1) (dyadicCubeSet Q.1) volume ∧
      (∀ x ∈ (rieszSecondCubeStar Q.1)ᶜ,
        IntegrableOn (fun y => rieszSecondKernel i j (x - y) *
          dyadicBadPart F Q.1 y) (dyadicCubeSet Q.1) volume) ∧
      AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.1 - z.2) -
          rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
            dyadicBadPart F Q.1 z.2|)
        ((volume.restrict (rieszSecondCubeStar Q.1)ᶜ).prod
          (volume.restrict (dyadicCubeSet Q.1))) ∧
      AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.2 - z.1) -
          rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
            dyadicBadPart F Q.1 z.1|)
        ((volume.restrict (dyadicCubeSet Q.1)).prod
          (volume.restrict (rieszSecondCubeStar Q.1)ᶜ)) := by
  intro Q
  have hSvol : volume (dyadicCubeSet Q.1) ≠ ∞ := by
    change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure (volume.restrict (dyadicCubeSet Q.1)) :=
    isFiniteMeasure_restrict.mpr hSvol
  have hb : IntegrableOn (dyadicBadPart F Q.1) (dyadicCubeSet Q.1) volume :=
    MemLp.integrable (by norm_num)
      ((dyadic_bad_part_memLp_two D hF₂ Q).mono_measure
        Measure.restrict_le_self)
  exact ⟨hb, by intro x hx; exact rieszSecond_bad_term_integrable D hF₂ Q hx,
    rieszSecond_bad_joint_measurable D hF₂ Q,
    rieszSecond_bad_joint_swap_measurable D hF₂ Q⟩

theorem rieszSecond_bad_cube_kernel_bridge
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level) (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |∫ y, rieszSecondPressureKernel i j (x - y) *
          dyadicBadPart F Q.1 y|) ≤
        ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          ∫⁻ y in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 y| := by
  intro Q
  have hdata := rieszSecond_bad_cube_data (i := i) (j := j) D hF₂ Q
  have hbridge := rieszSecond_bad_cube_bridge_of_kernel
    (K := rieszSecondKernel i j) (b := dyadicBadPart F Q.1) (Q := Q.1)
    (C₂ := rieszSecondKernelC₂) rieszSecondKernelC₂_nonneg
    (rieszSecondKernel_measurable i j)
    (fun x hx => rieszSecondKernel_differentiableAt hx i j)
    (fun x hx => rieszSecondKernel_fderiv_bound hx i j)
    (D.bad_part_mean Q.2) hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  have heq : ∀ x : Vec3,
      (∫ y, rieszSecondPressureKernel i j (x - y) *
        dyadicBadPart F Q.1 y) =
      ∫ y in dyadicCubeSet Q.1,
        rieszSecondPressureKernel i j (x - y) *
          dyadicBadPart F Q.1 y := by
    intro x
    calc
      (∫ y, rieszSecondPressureKernel i j (x - y) *
          dyadicBadPart F Q.1 y) =
          ∫ y, (dyadicCubeSet Q.1).indicator
            (fun y => rieszSecondPressureKernel i j (x - y) *
              dyadicBadPart F Q.1 y) y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ dyadicCubeSet Q.1
        · simp only [Set.indicator_of_mem hy]
        · simp only [Set.indicator_of_notMem hy]
          simp [dyadicBadPart, hy]
      _ = ∫ y in dyadicCubeSet Q.1,
          rieszSecondPressureKernel i j (x - y) *
            dyadicBadPart F Q.1 y :=
        integral_indicator (dyadicCube_measurable Q.1.scale Q.1.corner)
  have hneg : ∀ x : Vec3,
      (∫ y in dyadicCubeSet Q.1,
        rieszSecondPressureKernel i j (x - y) *
          dyadicBadPart F Q.1 y) =
      -(∫ y in dyadicCubeSet Q.1,
        rieszSecondKernel i j (x - y) *
          dyadicBadPart F Q.1 y) := by
    intro x
    have hEq : (fun y => rieszSecondPressureKernel i j (x - y) *
        dyadicBadPart F Q.1 y) =ᵐ[volume.restrict (dyadicCubeSet Q.1)]
        (fun y => -(rieszSecondKernel i j (x - y) *
          dyadicBadPart F Q.1 y)) := by
      filter_upwards [] with y
      simp only [rieszSecondPressureKernel, rieszSecondKernel]
      ring
    calc
      (∫ y in dyadicCubeSet Q.1,
          rieszSecondPressureKernel i j (x - y) *
            dyadicBadPart F Q.1 y) =
          ∫ y in dyadicCubeSet Q.1,
            -(rieszSecondKernel i j (x - y) *
              dyadicBadPart F Q.1 y) :=
        integral_congr_ae hEq
      _ = -(∫ y in dyadicCubeSet Q.1,
          rieszSecondKernel i j (x - y) *
            dyadicBadPart F Q.1 y) := by rw [integral_neg]
  calc
    (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |∫ y, rieszSecondPressureKernel i j (x - y) *
          dyadicBadPart F Q.1 y|) =
        ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
          ENNReal.ofReal |∫ y in dyadicCubeSet Q.1,
            rieszSecondKernel i j (x - y) *
              dyadicBadPart F Q.1 y| := by
      apply lintegral_congr
      intro x
      rw [heq x, hneg x, abs_neg]
    _ ≤ _ := by
      exact hbridge

end CKN.Foundation.Euclidean
