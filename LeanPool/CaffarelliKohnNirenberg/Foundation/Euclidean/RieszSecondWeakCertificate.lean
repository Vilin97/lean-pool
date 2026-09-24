/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakConcrete
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondExterior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Input
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RestrictedCZInterpolation

/-!
# Riesz Second Weak Certificate

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

private lemma rieszSecond_concrete_exterior
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {b : Vec3 → ℝ} (hb₂ : MemLp b (2 : ℝ≥0∞) volume)
    {A U : Set Vec3} (hU : IsOpen U) (hbA : ∀ y ∉ A, b y = 0)
    (hAb : Bornology.IsBounded A) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A,
      δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondL2MeasurableOperator hL2 (MemLp.toLp b hb₂) =ᵐ[
        volume.restrict U]
      (fun x => ∫ y, rieszSecondPressureKernel i j (x - y) * b y) := by
  have h := rieszSecondL2_exterior_representation hL2 hb₂ hU hbA hAb hδ hsep
  simpa only [rieszSecondPressureKernel, rieszSecondKernel, Pi.neg_apply] using h

lemma rieszSecond_concrete_bad_bridge
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (hL2 : RieszSecondL2Input i j) (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x|) ≤
      ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
        ∫⁻ y in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 y| := by
  intro Q
  have hExterior : ∀ {b : Vec3 → ℝ} (hb₂ : MemLp b (2 : ℝ≥0∞) volume)
      {A U : Set Vec3}, IsOpen U → (∀ y ∉ A, b y = 0)
      → Bornology.IsBounded A → {δ : ℝ} → 0 < δ
      → (∀ x ∈ U, ∀ y ∈ A,
        δ ≤ vec3EuclideanNorm (x - y)) →
      rieszSecondL2MeasurableOperator hL2 (MemLp.toLp b hb₂) =ᵐ[
        volume.restrict U]
        (fun x => ∫ y, rieszSecondPressureKernel i j (x - y) * b y) := by
    intro b hb₂ A U hU hbA hAb δ hδ hsep
    exact rieszSecond_concrete_exterior hL2 hb₂ hU hbA hAb hδ hsep
  exact (rieszSecond_exterior_operator_bad_bridge hL2 D hF₂ hExterior
    (rieszSecond_bad_cube_kernel_bridge D hF₂)) Q

lemma rieszSecond_concrete_bad_additivity
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (hL2 : RieszSecondL2Input i j) (D : CZDecomposition F level)
    (hF : Integrable F volume) (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
        rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicGoodPart F D.cubes)
            (dyadic_good_part_memLp_two D hF₂)) x) =
        (tsum (fun Q : {Q // Q ∈ D.cubes} =>
          rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (dyadicBadPart F Q.1)
              (dyadic_bad_part_memLp_two D hF₂ Q)) x))) ∧
    (∀ᵐ x ∂(volume.restrict
      (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      Summable (fun Q : {Q // Q ∈ D.cubes} =>
        |rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x|)) := by
  exact rieszSecond_countable_bad_additivity hL2 D hF hF₂
    ENNReal.ofReal_ne_top (rieszSecond_concrete_bad_bridge hL2 D hF₂)

/-- Concrete Calderón–Zygmund certificate for the second-Riesz L² operator. -/
def rieszSecondL2CzCertificate
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (hL2 : RieszSecondL2Input i j) (_hFmeas : Measurable F)
    (hFint : Integrable F volume)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (hlevel : 0 < level) :
    RieszSecondL2CZCertificate hL2 F hF₂ level := by
  apply rieszSecondL2CzCertificateOfInterfaces hL2 hFint hF₂ hlevel
  intro D
  obtain ⟨hEq, hsum⟩ := rieszSecond_concrete_bad_additivity
    hL2 D hFint hF₂
  have hbridge := rieszSecond_concrete_bad_bridge hL2 D hF₂
  let Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ := fun Q =>
    rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp (dyadicBadPart F Q.1)
        (dyadic_bad_part_memLp_two D hF₂ Q))
  refine ⟨Tbad, ?_, ?_, ?_⟩
  · simpa only [Tbad] using hEq
  · intro Q
    exact (rieszSecondL2MeasurableOperator_measurable hL2 _).norm.aemeasurable
      |>.ennreal_ofReal.mono_measure Measure.restrict_le_self
  · intro Q
    exact hbridge Q

theorem rieszSecondL2_weak_type :
    ∀ (i j : Fin 3) (f : Vec3 → ℝ), Measurable f → Integrable f volume →
      MemLp f (2 : ℝ≥0∞) volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator
          (rieszSecondL2Input i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l := by
  intro i j f hf hfi hf₂ l hl
  exact rieszSecondL2_restricted_weak_type (rieszSecondL2Input i j)
    (fun hfm hfin hmem hlevel =>
      rieszSecondL2CzCertificate (rieszSecondL2Input i j)
        hfm hfin hmem hlevel)
    f hf hfi hf₂ l hl

theorem rieszSecondL2_interpolation_threeHalves
    {i j : Fin 3} {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    ∫⁻ x, absE (rieszSecondL2RawOperator
      (rieszSecondL2Input i j) f) x ^ ((3 : ℝ) / 2) ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant
        rieszSecondWeakTypeConstant 1 ((3 : ℝ) / 2)) *
        ∫⁻ x, absE f x ^ ((3 : ℝ) / 2) := by
  exact CKN.Core.Endgame.raw_rieszSecond_interpolation_of_weak_ae
    (rieszSecondL2Input i j) (fun g hg hgi hg₂ l hl =>
      rieszSecondL2_weak_type i j g hg hgi hg₂ l hl)
    (by
      unfold rieszSecondWeakTypeConstant
      have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
      positivity)
    (by norm_num) (by norm_num) hf hf₂

theorem rieszSecondL2_interpolation_sixFifths
    {i j : Fin 3} {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    ∫⁻ x, absE (rieszSecondL2RawOperator
      (rieszSecondL2Input i j) f) x ^ ((6 : ℝ) / 5) ≤
      ENNReal.ofReal (rieszSecondInterpolationConstant
        rieszSecondWeakTypeConstant 1 ((6 : ℝ) / 5)) *
        ∫⁻ x, absE f x ^ ((6 : ℝ) / 5) := by
  exact CKN.Core.Endgame.raw_rieszSecond_interpolation_of_weak_ae
    (rieszSecondL2Input i j) (fun g hg hgi hg₂ l hl =>
      rieszSecondL2_weak_type i j g hg hgi hg₂ l hl)
    (by
      unfold rieszSecondWeakTypeConstant
      have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
      positivity)
    (by norm_num) (by norm_num) hf hf₂

end CKN.Foundation.Euclidean
