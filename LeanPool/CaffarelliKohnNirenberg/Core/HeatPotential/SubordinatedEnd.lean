/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedAssembly

/-!
# Subordinated End

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
lemma heatPotential_series_representation_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z q : ParabolicPoint} {r P θ₀ θ₁ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i))
    (hδ₀ : 0 < 2 - 5 / θ₀) (hδ₁ : 0 < 1 - 5 / θ₁)
    (hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    heatPotential F G q =
        heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ∑' j : ℕ, heatPotentialShellValue F G
            (heatPotentialFarShellSet z r j) q ∧
      Summable (fun j : ℕ => heatPotentialShellValue F G
        (heatPotentialFarShellSet z r j) q) := by
  have hcover := heatPotential_near_far_cover (z := z) hr
  have hdST : ∀ j : ℕ, Disjoint (heatPotentialNearSet z r)
      (heatPotentialFarShellSet z r j) := heatPotential_near_far_disjoint hr
  have hdT := heatPotential_far_shells_pairwise_disjoint (z := z) hr
  have hInt := heatPotential_kernel_integrable_on_split hr hP hPθ₀ hPθ₁
    hF hG hNF hNG hSupportF hSupportG hδ₀ hδ₁ hq
  have hFsplit := heatPotential_integral_near_far_split hcover hdST hdT hInt.1
  have hGsplit : ∀ i : Fin 3,
      ∫ v, heatPotentialSpatialKernel i q v * G i v =
        (∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i q v * G i v) +
          ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i q v * G i v := by
    intro i
    exact heatPotential_integral_near_far_split hcover hdST hdT (hInt.2 i)
  have hsumF : HasSum (fun j : ℕ =>
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel q v * F v)
      (∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
        heatPotentialKernel q v * F v) := by
    apply MeasureTheory.hasSum_integral_iUnion
      (fun j => measurableSet_heatPotentialFarShellSet z r j) hdT
    exact (hInt.1).mono_set subset_union_right
  have hsumG : ∀ i : Fin 3, HasSum (fun j : ℕ =>
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i q v * G i v)
      (∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i q v * G i v) := by
    intro i
    apply MeasureTheory.hasSum_integral_iUnion
      (fun j => measurableSet_heatPotentialFarShellSet z r j) hdT
    exact (hInt.2 i).mono_set subset_union_right
  let g : Fin 3 → ℕ → ℝ := fun i j =>
    ∫ v in heatPotentialFarShellSet z r j,
      heatPotentialSpatialKernel i q v * G i v
  let gU : Fin 3 → ℝ := fun i =>
    ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
      heatPotentialSpatialKernel i q v * G i v
  have hsumG' : ∀ i : Fin 3, HasSum (g i)
      (gU i) := by
    intro i
    simpa [g, gU] using hsumG i
  have hsumGfin : HasSum (fun j : ℕ => ∑ i : Fin 3, g i j)
      (∑ i : Fin 3, gU i) := by
    classical
    have hsumFin : ∀ s : Finset (Fin 3), HasSum (fun j : ℕ =>
        Finset.sum s (fun i => g i j))
        (Finset.sum s gU) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hadd := (hsumG' i).add ih
          simpa [Finset.sum_insert hi, add_comm, add_left_comm, add_assoc] using hadd
    simpa using hsumFin Finset.univ
  have hsumShell : HasSum (fun j : ℕ =>
      heatPotentialShellValue F G (heatPotentialFarShellSet z r j) q)
      ((∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
          heatPotentialKernel q v * F v) +
        ∑ i : Fin 3, ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
          heatPotentialSpatialKernel i q v * G i v) := by
    have hadd := hsumF.add hsumGfin
    simpa only [heatPotentialShellValue, g, gU] using hadd
  have hcomm : (∑' j : ℕ, ∑ i : Fin 3, g i j) =
      ∑ i : Fin 3, ∑' j : ℕ, g i j := by
    rw [hsumGfin.tsum_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hsumG' i).tsum_eq.symm
  constructor
  · unfold heatPotential
    calc
      (∫ v, heatPotentialKernel q v * F v) +
          ∑ i, ∫ v, heatPotentialSpatialKernel i q v * G i v =
          ((∫ v in heatPotentialNearSet z r,
            heatPotentialKernel q v * F v) +
            ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialKernel q v * F v) +
          ∑ i, ((∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i q v * G i v) +
            ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i q v * G i v) := by
            rw [hFsplit]
            apply congrArg₂ (· + ·) rfl
            apply Finset.sum_congr rfl
            intro i hi
            rw [hGsplit i]
      _ = heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ((∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
              heatPotentialKernel q v * F v) +
            ∑ i, ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i q v * G i v) := by
            simp only [heatPotentialShellValue]
            rw [← hsumF.tsum_eq, ← hsumGfin.tsum_eq, hcomm]
            simp_rw [Finset.sum_add_distrib]
            simp only [g]
            ring_nf
      _ = heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ∑' j : ℕ, heatPotentialShellValue F G
            (heatPotentialFarShellSet z r j) q := by
            rw [← hsumShell.tsum_eq]
  · exact hsumShell.summable

lemma heatPotential_pairwise_oscillation_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z p p' : ParabolicPoint} {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i))
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let Cnear : ℝ :=
      2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
    let A : ℕ → ℝ := fun j =>
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₀)) * BF) +
      ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₁)) * BG i)
    |heatPotential F G p - heatPotential F G p'| ≤
      Cnear * r ^ γ + ∑' j : ℕ, A j := by
  have hδ₀ : 0 < 2 - 5 / θ₀ := by
    rw [heat_morrey_theta_zero_identity hθ₀]
    exact hγ
  have hδ₁ : 0 < 1 - 5 / θ₁ := by
    rw [heat_morrey_theta_one_identity hθ₁]
    exact hγ
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let A : ℕ → ℝ := fun j =>
    (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₀)) * BF) +
    ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
        (5 * (1 - 1 / θ₁)) * BG i)
  have hprofile := heatPotential_far_shell_profile_of_morrey
    (F := F) (G := G) hr hγ hθ₀ hθ₁ hP hPθ₀ hPθ₁ hNF hNG
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    simpa [A, BF, BG, V] using hprofile.1
  have hAj : ∀ j : ℕ, A j ≤
      ((1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
        ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
          120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i) *
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    simpa [A, BF, BG, V] using hprofile.2
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  have hC : 0 ≤ C := by
    dsimp [C, BF, BG, V]
    positivity
  have hq0 : 0 ≤ (2 : ℝ) ^ (γ - 1) := by positivity
  have hq1 : (2 : ℝ) ^ (γ - 1) < 1 :=
    heat_morrey_geometric_ratio_lt_one hγ1
  have hgeo : Summable (fun j : ℕ =>
      (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) := by
    rw [show (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
        (fun j : ℕ => ((2 : ℝ) ^ (γ - 1)) ^ j) by
          funext j
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring]
    exact summable_geometric_of_lt_one hq0 hq1
  have hg : Summable (fun j : ℕ => C * r ^ γ *
      (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) :=
    hgeo.mul_left (C * r ^ γ)
  have hAsum : Summable A := by
    apply Summable.of_norm_bounded hg
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hA j)]
    exact (hAj j).trans_eq (by ring)
  have hnear := heatPotential_near_oscillation_bound_of_morrey
    (F := F) (G := G) (z := z) (p := p) (p' := p') hr hγ hθ₀ hθ₁
      hP hPθ₀ hPθ₁ hF hG hNF hNG hp hp'
  have hfar : ∀ j : ℕ,
      |heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p -
          heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p'| ≤ A j := by
    intro j
    simpa [A, BF, BG, V] using
      (heatPotential_far_shell_value_bound_of_morrey
        (F := F) (G := G) (z := z) (p := p) (p' := p') hr hγ hθ₀ hθ₁
          hP hPθ₀ hPθ₁ hF hG hNF hNG hp hp') j
  have hrep : ∀ q : ParabolicPoint,
      q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      heatPotential F G q =
        heatPotentialShellValue F G (heatPotentialNearSet z r) q +
          ∑' j : ℕ, heatPotentialShellValue F G
            (heatPotentialFarShellSet z r j) q ∧
      Summable (fun j : ℕ => heatPotentialShellValue F G
        (heatPotentialFarShellSet z r j) q) := by
    intro q hq
    exact heatPotential_series_representation_of_morrey
      hr hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG hδ₀ hδ₁ hq
  have hbound := heatPotential_series_difference_bound
    (p := p) (p' := p') (n := fun q =>
      heatPotentialShellValue F G (heatPotentialNearSet z r) q)
    (hsplitp := (hrep p hp).1) (hsplitp' := (hrep p' hp').1)
    (hsump := (hrep p hp).2) (hsump' := (hrep p' hp').2)
    (hnear := by
      simpa [heatPotentialShellValue, Cnear, BF, BG, V] using hnear)
    hAsum hfar
  convert hbound using 1
  simp only [A, BF, BG, V]
  congr 1
  · ring_nf

lemma heatPotential_aemeasurable_of_sources
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume)
    (hG : ∀ i : Fin 3, AEMeasurable (G i) volume) :
    AEMeasurable (heatPotential F G) volume := by
  have hk : Measurable
      (fun qv : ParabolicPoint × ParabolicPoint =>
        heatPotentialKernel qv.1 qv.2) := by
    unfold heatPotentialKernel pointSub heatKernelPlus
    apply Measurable.ite
      (measurableSet_Ioi.preimage
        ((measurable_snd.comp measurable_fst).sub
          (measurable_snd.comp measurable_snd)))
    · unfold heatKernel
      apply Measurable.ite
        (measurableSet_Ioi.preimage
          ((measurable_snd.comp measurable_fst).sub
            (measurable_snd.comp measurable_snd)))
      · fun_prop
      · exact measurable_const
    · exact measurable_const
  have hFprod : AEMeasurable
      (fun qv : ParabolicPoint × ParabolicPoint => F qv.2)
      (volume.prod volume) := hF.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hscalar : AEMeasurable
      (fun q : ParabolicPoint => ∫ v, heatPotentialKernel q v * F v)
      volume := by
    have hs := (hk.aestronglyMeasurable.mul hFprod.aestronglyMeasurable)
      |>.integral_prod_right'
    convert hs.aemeasurable using 1
  have hspatial : ∀ i : Fin 3, AEMeasurable
      (fun q : ParabolicPoint =>
        ∫ v, heatPotentialSpatialKernel i q v * G i v) volume := by
    intro i
    have hki : Measurable
        (fun qv : ParabolicPoint × ParabolicPoint =>
          heatPotentialSpatialKernel i qv.1 qv.2) := by
      unfold heatPotentialSpatialKernel heatKernelSpaceDerivative
      apply Measurable.ite
        (measurableSet_Ioi.preimage
          ((measurable_snd.comp measurable_fst).sub
            (measurable_snd.comp measurable_snd)))
      · have hheat : Measurable
            (fun qv : ParabolicPoint × ParabolicPoint =>
              heatKernel (qv.1.1 - qv.2.1) (qv.1.2 - qv.2.2)) := by
          unfold heatKernel
          apply Measurable.ite
            (measurableSet_Ioi.preimage
              ((measurable_snd.comp measurable_fst).sub
                (measurable_snd.comp measurable_snd)))
          · fun_prop
          · exact measurable_const
        have hcoef : Measurable
            (fun qv : ParabolicPoint × ParabolicPoint =>
              -(qv.1.1 - qv.2.1) i /
                (2 * (qv.1.2 - qv.2.2))) := by
          fun_prop
        exact hcoef.mul hheat
      · exact measurable_const
    have hGi : AEMeasurable
        (fun qv : ParabolicPoint × ParabolicPoint => G i qv.2)
        (volume.prod volume) := (hG i).comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
    have hs := (hki.aestronglyMeasurable.mul hGi.aestronglyMeasurable)
      |>.integral_prod_right'
    convert hs.aemeasurable using 1
  have hsum : AEMeasurable
      (fun q : ParabolicPoint => ∑ i : Fin 3,
        ∫ v, heatPotentialSpatialKernel i q v * G i v) volume := by
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => hspatial i)
  exact hscalar.add hsum

lemma heatPotential_local_data_of_pairwise
    {h : ParabolicPoint → ℝ} {z : ParabolicPoint} {r p K : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (_ : 0 ≤ K)
    (hAEM : AEMeasurable h volume)
    (hpair : ∀ w ∈ @Metric.closedBall ParabolicPoint
        parabolicPseudoMetricSpace z r,
      ∀ w' ∈ @Metric.closedBall ParabolicPoint
        parabolicPseudoMetricSpace z r,
        |h w - h w'| ≤ K) :
    IntegrableOn h (@Metric.closedBall ParabolicPoint
        parabolicPseudoMetricSpace z r) volume ∧
      IntegrableOn
        (fun q => |h q - ⨍ x in @Metric.closedBall ParabolicPoint
          parabolicPseudoMetricSpace z r, h x| ^ p)
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
        volume := by
  let B : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  let C : ℝ := K
  have hBpos : 0 < volume B := by
    dsimp [B]
    exact parabolicBall_closedBall_pos hr
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact parabolicBall_closedBall_top hr
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_closedBall
  have hzB : z ∈ B := by
    simpa [B] using hr.le
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hpoint : ∀ w ∈ B, |h w - h z| ≤ C := by
    intro w hw
    simpa [C] using hpair w (by simpa [B] using hw) z
      (by simpa [B] using hzB)
  have hbound : ∀ w ∈ B, |h w| ≤ |h z| + C := by
    intro w hw
    calc
      |h w| ≤ |h w - h z| + |h z| := by
        simpa [sub_eq_add_neg, add_comm] using abs_add_le (h w - h z) (h z)
      _ ≤ C + |h z| := add_le_add (hpoint w hw) (le_refl _)
      _ = |h z| + C := by ring
  have hint : IntegrableOn h B volume := by
    apply IntegrableOn.of_bound hBtop hAEM.aestronglyMeasurable.restrict
      (|h z| + C)
    filter_upwards [MeasureTheory.ae_restrict_mem hB] with w hw
    simpa [Real.norm_eq_abs] using hbound w hw
  let c : ℝ := ⨍ x in B, h x
  have hpointc : ∀ w ∈ B, |h w - c| ≤ C := by
    intro w hw
    have hconst : IntegrableOn (fun _ : ParabolicPoint => h w) B volume :=
      integrableOn_const hBtop.ne
    have hsub : IntegrableOn (fun v => h w - h v) B volume := hconst.sub hint
    have havgsub : (⨍ v in B, h w - h v) = h w - ⨍ v in B, h v := by
      rw [show (fun v => h w - h v) = (fun v => h w) - h by
        funext v
        rfl,
        MeasureTheory.setAverage_sub hconst hint,
        MeasureTheory.setAverage_const hBpos.ne' hBtop.ne]
    have havgnorm := Integration.setAverage_norm_le volume B
      (fun v => h w - h v)
    rw [havgsub] at havgnorm
    have havgabs : |h w - ⨍ v in B, h v| ≤
        ⨍ v in B, |h w - h v| := by
      simpa only [Real.norm_eq_abs] using havgnorm
    have hmono : (⨍ v in B, |h w - h v|) ≤ C := by
      calc
        (⨍ v in B, |h w - h v|) ≤ ⨍ v in B, C := by
          apply Integration.setAverage_mono_of_ae hsub.norm
            (integrableOn_const hBtop.ne)
          filter_upwards [MeasureTheory.ae_restrict_mem hB] with v hv
          exact hpair w (by simpa [B] using hw) v (by simpa [B] using hv)
        _ = C := MeasureTheory.setAverage_const hBpos.ne' hBtop.ne _
    simpa [c] using havgabs.trans hmono
  have hpowae : AEMeasurable (fun q => |h q - c| ^ p) volume := by
    have hsubae : AEMeasurable (fun q => h q - c) volume :=
      hAEM.sub aemeasurable_const
    exact (Real.continuous_rpow_const hp0).measurable.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable hsubae)
  have hfp : IntegrableOn (fun q => |h q - c| ^ p) B volume := by
    apply IntegrableOn.of_bound hBtop hpowae.aestronglyMeasurable.restrict
      (C ^ p)
    filter_upwards [MeasureTheory.ae_restrict_mem hB] with q hq
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
      (Real.rpow_le_rpow (abs_nonneg _) (hpointc q hq) hp0)
  refine ⟨hint, ?_⟩
  simpa [B, c] using hfp

/-!
# Explicit subordinated heat potentials

The paper writes the pressure part as a degree-one multiplier applied to the
forward heat kernel.  The explicit dictionary used here is

* `∂ₖ W₊` is `heatPotentialSpatialKernel k`;
* `σ(D) W₊` is represented by
  `subordinatedHeatPotentialKernel j l m`, whose value is
  `-∫ s in Ioi t, ∂ₘ∂ⱼ∂ₗ W(x,s)`.

Thus the coordinate branch is the kernel already used by `heatPotential`,
while the pressure branch is a finite collection of the explicit kernels
`K^m_jl`.  The multiplier symbol itself is not used as an additional
assumption.
-/










end CKN.Core.HeatPotential
