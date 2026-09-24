/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorRepresentative
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Interior Regularity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

private lemma euclidean_ball_isOpen {x₀ : Vec3} {ρ : ℝ} (_ : 0 < ρ) :
    IsOpen (euclideanBall x₀ ρ) := by
  change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

lemma mollify_memLp_of_memLp
    {g : Vec3 → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hg : MemLp g p volume) {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollify g ε hε) p volume := by
  rw [memLp_iff]
  have hyoung := young_convolution_nonneg_integral_one_of_aemeasurable
    (p := p) hp hp_top (mollifier_nonneg hε)
    (integrable_of_integral_eq_one (mollifier_integral_one hε))
    (mollifier_integral_one hε)
    (mollifier_contDiff hε (n := 0)).continuous.measurable
    hg.aestronglyMeasurable.aemeasurable
  simpa only [mollify] using hyoung.trans_lt hg.eLpNorm_lt_top

lemma lpNorm_restrict_mono
    {U A : Set Vec3} (hAsub : A ⊆ U) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U)) :
    lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) ≤
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
  rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
  exact ENNReal.toReal_mono hf.eLpNorm_lt_top.ne
    (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hAsub))

private lemma integrable_mul_annulus_kernel
    {A : Set Vec3} (hAmeas : MeasurableSet A)
    [IsFiniteMeasure (volume.restrict A)] {f k : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A))
    (hk : MemLp k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A))
    {C : ℝ} (hC : 0 ≤ C)
    (hk_bound : ∀ y ∈ A, |k y| ≤ C)
    (hk_zero : ∀ y, y ∉ A → k y = 0) :
    Integrable (fun y => f y * k y) volume := by
  have hf_int : Integrable f (volume.restrict A) := hf.integrable (by norm_num)
  have hCf : Integrable (fun y => C * |f y|) (volume.restrict A) := by
    simpa only [Real.norm_eq_abs] using hf_int.norm.const_mul C
  have hprod_int : Integrable (fun y => f y * k y)
      (volume.restrict A) := by
    refine hCf.mono (hf.aestronglyMeasurable.mul hk.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hAmeas] with y hy
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      |f y| * |k y| ≤ |f y| * C :=
        mul_le_mul_of_nonneg_left (hk_bound y hy) (abs_nonneg _)
      _ = |C| * |(|f y|)| := by
        rw [abs_of_nonneg hC, abs_of_nonneg (abs_nonneg _)]
        ring
  have hind : Integrable (A.indicator (fun y => f y * k y)) volume :=
    (integrable_indicator_iff hAmeas).2 hprod_int
  apply hind.congr
  filter_upwards [] with y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy, hk_zero y hy]

private lemma weak_rep_source_integral_bound
    {h : Vec3 → ℝ} {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    |∫ y, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y)| ≤
      weakHarmonicInteriorSourceConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  let A : Set Vec3 := cutoffAnnulus x₀ ρ
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact cutoffAnnulus_measurable hρ
  have hAsub : A ⊆ euclideanBall x₀ ρ := by
    dsimp [A]
    exact weak_annulus_subset_outer hρ
  let _ : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (weak_annulus_isFinite hρ)
  have hmemA := hmem.mono_measure (Measure.restrict_mono_set volume hAsub)
  let k : Vec3 → ℝ := fun y => newtonianKernel (x - y) *
    CKN.spatialLaplacian (eta x₀ hρ) y
  have hkcont : ContinuousOn k A := by
    dsimp [k]
    exact weak_source_kernel_continuousOn hρ hx
  have hkbound : ∀ y ∈ A, |k y| ≤
      weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
    intro y hy
    exact weak_source_kernel_bound hρ hx (by simpa [A] using hy)
  have hk : MemLp k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
    exact memLp_of_continuousOn_bound hAmeas hkcont
      _ hkbound _
  have hklp := weak_lp_kernel_bound hρ hAmeas hkcont
    weakHarmonicInteriorSourceConstant_nonneg (fun y hy => by
      exact hkbound y hy)
  have hbound := integral_mul_memLp_bound_on hAmeas hmemA hk
    (fun y hy => by
      dsimp [k]
      exact weak_source_kernel_zero_off_annulus hρ (by simpa [A] using hy))
  calc
    |∫ y, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y)| ≤
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
          lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
      simpa only [k] using hbound
    _ ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) *
        (weakHarmonicInteriorSourceConstant *
          (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹) := by
      calc
        _ ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) *
              lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
          mul_le_mul_of_nonneg_right (lpNorm_restrict_mono hAsub hmem)
            lpNorm_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hklp lpNorm_nonneg
    _ = _ := by ring

private lemma weak_rep_cutoff_integral_bound
    {h : Vec3 → ℝ} {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) (i : Fin 3)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    |∫ y, h y * CKN.spatialDeriv
        (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      weakHarmonicInteriorCutoffConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  let A : Set Vec3 := cutoffAnnulus x₀ ρ
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact cutoffAnnulus_measurable hρ
  have hAsub : A ⊆ euclideanBall x₀ ρ := by
    dsimp [A]
    exact weak_annulus_subset_outer hρ
  let _ : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (weak_annulus_isFinite hρ)
  have hmemA := hmem.mono_measure (Measure.restrict_mono_set volume hAsub)
  let k : Vec3 → ℝ := fun y => CKN.spatialDeriv
    (kernelCutoffDerivative x x₀ hρ i) i y
  have hkcont : ContinuousOn k A := by
    dsimp [k]
    exact weak_cutoff_kernel_continuousOn hρ hx i
  have hkbound : ∀ y ∈ A, |k y| ≤
      weakHarmonicInteriorCutoffConstant * (ρ ^ 3)⁻¹ := by
    intro y hy
    exact weak_cutoff_kernel_bound hρ hx (by simpa [A] using hy) i
  have hk : MemLp k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
    exact memLp_of_continuousOn_bound hAmeas hkcont
      _ hkbound _
  have hklp := weak_lp_kernel_bound hρ hAmeas hkcont
    weakHarmonicInteriorCutoffConstant_nonneg (fun y hy => by
      exact hkbound y hy)
  have hbound := integral_mul_memLp_bound_on hAmeas hmemA hk
    (fun y hy => by
      dsimp [k]
      exact weak_cutoff_kernel_zero_off_annulus hρ hx
        (by simpa [A] using hy) i)
  calc
    |∫ y, h y * CKN.spatialDeriv
        (kernelCutoffDerivative x x₀ hρ i) i y| ≤
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
          lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
      simpa only [k] using hbound
    _ ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) *
        (weakHarmonicInteriorCutoffConstant *
          (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹) := by
      calc
        _ ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) *
              lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
          mul_le_mul_of_nonneg_right (lpNorm_restrict_mono hAsub hmem)
            lpNorm_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hklp lpNorm_nonneg
    _ = _ := by ring

lemma weak_rep_sub_eq
    {f g : Vec3 → ℝ} {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    weakHarmonicInteriorRepresentative f x₀ hρ x -
        weakHarmonicInteriorRepresentative g x₀ hρ x =
      weakHarmonicInteriorRepresentative (fun y => f y - g y) x₀ hρ x := by
  let A : Set Vec3 := cutoffAnnulus x₀ ρ
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact cutoffAnnulus_measurable hρ
  have hAsub : A ⊆ euclideanBall x₀ ρ := by
    dsimp [A]
    exact weak_annulus_subset_outer hρ
  let _ : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (weak_annulus_isFinite hρ)
  have hfA := hf.mono_measure (Measure.restrict_mono_set volume hAsub)
  have hgA := hg.mono_measure (Measure.restrict_mono_set volume hAsub)
  let k₀ : Vec3 → ℝ := fun y => newtonianKernel (x - y) *
    CKN.spatialLaplacian (eta x₀ hρ) y
  have hk₀cont : ContinuousOn k₀ A := by
    dsimp [k₀]
    exact weak_source_kernel_continuousOn hρ hx
  have hk₀bound : ∀ y ∈ A, |k₀ y| ≤
      weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
    intro y hy
    exact weak_source_kernel_bound hρ hx (by simpa [A] using hy)
  have hk₀ : MemLp k₀ (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
    memLp_of_continuousOn_bound hAmeas hk₀cont _ hk₀bound _
  have hC₀ : 0 ≤ weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ :=
    mul_nonneg weakHarmonicInteriorSourceConstant_nonneg (by positivity)
  have hfi₀ := integrable_mul_annulus_kernel hAmeas hfA hk₀
    hC₀
    (fun y hy => hk₀bound y hy)
    (fun y hy => weak_source_kernel_zero_off_annulus hρ (by simpa [A] using hy))
  have hgi₀ := integrable_mul_annulus_kernel hAmeas hgA hk₀
    hC₀
    (fun y hy => hk₀bound y hy)
    (fun y hy => weak_source_kernel_zero_off_annulus hρ (by simpa [A] using hy))
  have hfi₀' : Integrable (fun y => newtonianKernel (x - y) *
      (f y * CKN.spatialLaplacian (eta x₀ hρ) y)) volume := by
    exact hfi₀.congr (Eventually.of_forall (fun y => by dsimp [k₀]; ring))
  have hgi₀' : Integrable (fun y => newtonianKernel (x - y) *
      (g y * CKN.spatialLaplacian (eta x₀ hρ) y)) volume := by
    exact hgi₀.congr (Eventually.of_forall (fun y => by dsimp [k₀]; ring))
  have hsource :
      (∫ y, newtonianKernel (x - y) *
          (f y * CKN.spatialLaplacian (eta x₀ hρ) y)) -
        ∫ y, newtonianKernel (x - y) *
          (g y * CKN.spatialLaplacian (eta x₀ hρ) y) =
      ∫ y, newtonianKernel (x - y) *
          ((f y - g y) * CKN.spatialLaplacian (eta x₀ hρ) y) := by
    rw [← integral_sub hfi₀' hgi₀']
    congr 1
    funext y
    ring
  have hcutoff : ∀ i : Fin 3,
      (∫ y, f y * CKN.spatialDeriv
          (kernelCutoffDerivative x x₀ hρ i) i y) -
        ∫ y, g y * CKN.spatialDeriv
          (kernelCutoffDerivative x x₀ hρ i) i y =
      ∫ y, (f y - g y) * CKN.spatialDeriv
          (kernelCutoffDerivative x x₀ hρ i) i y := by
    intro i
    let ki : Vec3 → ℝ := fun y => CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y
    have hkicont : ContinuousOn ki A := by
      dsimp [ki]
      exact weak_cutoff_kernel_continuousOn hρ hx i
    have hkibound : ∀ y ∈ A, |ki y| ≤
        weakHarmonicInteriorCutoffConstant * (ρ ^ 3)⁻¹ := by
      intro y hy
      exact weak_cutoff_kernel_bound hρ hx (by simpa [A] using hy) i
    have hki : MemLp ki (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
      memLp_of_continuousOn_bound hAmeas hkicont _ hkibound _
    have hCi : 0 ≤ weakHarmonicInteriorCutoffConstant * (ρ ^ 3)⁻¹ :=
      mul_nonneg weakHarmonicInteriorCutoffConstant_nonneg (by positivity)
    have hfi := integrable_mul_annulus_kernel hAmeas hfA hki
      hCi
      (fun y hy => hkibound y hy)
      (fun y hy => weak_cutoff_kernel_zero_off_annulus hρ hx
        (by simpa [A] using hy) i)
    have hgi := integrable_mul_annulus_kernel hAmeas hgA hki
      hCi
      (fun y hy => hkibound y hy)
      (fun y hy => weak_cutoff_kernel_zero_off_annulus hρ hx
        (by simpa [A] using hy) i)
    have hfi' : Integrable (fun y => f y * ki y) volume := hfi
    have hgi' : Integrable (fun y => g y * ki y) volume := hgi
    rw [← integral_sub hfi' hgi']
    congr 1
    funext y
    dsimp [ki]
    ring
  let If : Fin 3 → ℝ := fun i => ∫ y, f y * CKN.spatialDeriv
    (kernelCutoffDerivative x x₀ hρ i) i y
  let Ig : Fin 3 → ℝ := fun i => ∫ y, g y * CKN.spatialDeriv
    (kernelCutoffDerivative x x₀ hρ i) i y
  let Id : Fin 3 → ℝ := fun i => ∫ y, (f y - g y) * CKN.spatialDeriv
    (kernelCutoffDerivative x x₀ hρ i) i y
  have hsum : (∑ i : Fin 3, If i) - ∑ i : Fin 3, Ig i =
      ∑ i : Fin 3, Id i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hcutoff i
  simp only [weakHarmonicInteriorRepresentative]
  dsimp [If, Ig, Id] at hsum ⊢
  calc
    ((-∫ y : Vec3, newtonianKernel (x - y) *
          (f y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3, f y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) -
        ((-∫ y : Vec3, newtonianKernel (x - y) *
          (g y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3, g y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) =
      -((∫ y : Vec3, newtonianKernel (x - y) *
          (f y * CKN.spatialLaplacian (eta x₀ hρ) y)) -
        (∫ y : Vec3, newtonianKernel (x - y) *
          (g y * CKN.spatialLaplacian (eta x₀ hρ) y))) +
        2 * ((∑ i : Fin 3, If i) - ∑ i : Fin 3, Ig i) := by
          simp only [If, Ig]
          ring
    _ = -(∫ y : Vec3, newtonianKernel (x - y) *
          ((f y - g y) * CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3, (f y - g y) *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y := by
      rw [hsource, hsum]

lemma approximation_scale_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 < ρ / (12 * ((n : ℝ) + 1)) := by
  positivity

lemma approximation_scale_le {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ρ / (12 * ((n : ℝ) + 1)) ≤ ρ / 12 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn0]
  apply (div_le_div_iff₀ (by positivity : 0 < 12 * ((n : ℝ) + 1))
    (by positivity : 0 < (12 : ℝ))).2
  nlinarith only [hρ, hn]

lemma approximation_scale_tendsto {ρ : ℝ} (_ : 0 < ρ) :
    Tendsto (fun n : ℕ => ρ / (12 * ((n : ℝ) + 1))) atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (b - 1)]
      with n hn
    linarith only [hn]
  have hden : Tendsto (fun n : ℕ => 12 * ((n : ℝ) + 1)) atTop atTop := by
    simpa [mul_comm] using
      hn.atTop_mul_const (show (0 : ℝ) < 12 by norm_num)
  exact tendsto_const_nhds.div_atTop hden

lemma closedBall_subset_euclideanBall
    {x₀ y : Vec3} {ρ ε : ℝ} (hρ : 0 < ρ) (_ : 0 < ε)
    (hy : y ∈ euclideanBall x₀ (3 * ρ / 4)) (hε_le : ε ≤ ρ / 12) :
    Metric.closedBall y ε ⊆ euclideanBall x₀ ρ := by
  intro z hz
  have hz' : ‖z - y‖ ≤ ε := by
    rw [← dist_eq_norm]
    exact (Metric.mem_closedBall.mp hz)
  have hy' : vec3EuclideanNorm (y - x₀) < 3 * ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
  have htri : vec3EuclideanNorm (z - x₀) ≤
      vec3EuclideanNorm (z - y) + vec3EuclideanNorm (y - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (z - x₀)‖ =
          ‖WithLp.toLp 2 ((z - y) + (y - x₀))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (z - y)‖ +
          ‖WithLp.toLp 2 (y - x₀)‖ := norm_add_le _ _
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (z - y)
  have hthree' : vec3EuclideanNorm (z - y) ≤ 3 * ‖z - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  have hfinal : vec3EuclideanNorm (z - x₀) < ρ := by
    nlinarith only [htri, hthree', hz', hy', hε_le, hρ]
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hfinal

private theorem weak_harmonic_interior_representative_bound_internal
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      |weakHarmonicInteriorRepresentative h x₀ hρ x| ≤
        weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := by
  intro x hx
  have hsource := weak_rep_source_integral_bound hρ hx hmem
  have hcutoff : ∀ i : Fin 3, |∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      weakHarmonicInteriorCutoffConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro i
    exact weak_rep_cutoff_integral_bound hρ hx i hmem
  have hsum : |2 * ∑ i : Fin 3, ∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      6 * weakHarmonicInteriorCutoffConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    let I : Fin 3 → ℝ := fun i => ∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y
    change 2 * |∑ i : Fin 3, I i| ≤ _
    have habs : |∑ i : Fin 3, I i| ≤ ∑ i : Fin 3, |I i| := by
      simpa only [Fin.sum_univ_three] using
        (Finset.abs_sum_le_sum_abs I (Finset.univ : Finset (Fin 3)))
    calc
      2 * |∑ i : Fin 3, I i| ≤ 2 * ∑ i : Fin 3, |I i| :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * ∑ i : Fin 3,
          (weakHarmonicInteriorCutoffConstant *
            (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (2 : ℝ))
        apply Finset.sum_le_sum
        intro i hi
        exact hcutoff i
      _ = _ := by simp; ring
  rw [weakHarmonicInteriorRepresentative]
  have hsource_eq : (∫ y : Vec3, newtonianKernel (x - y) *
        (h y * CKN.spatialLaplacian (eta x₀ hρ) y)) =
      ∫ y : Vec3, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y) := by
    congr 1
    funext y
    ring
  rw [hsource_eq]
  calc
    |(-∫ y : Vec3, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y| ≤
        |∫ y, h y * (newtonianKernel (x - y) *
          CKN.spatialLaplacian (eta x₀ hρ) y)| +
        |2 * ∑ i : Fin 3, ∫ y, h y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y| := by
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
      rw [show weakHarmonicInteriorSupConstant =
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
          (weakHarmonicInteriorSourceConstant +
            6 * weakHarmonicInteriorCutoffConstant) by rfl]
      exact (add_le_add hsource hsum).trans_eq (by ring)

theorem weakly_harmonic_interior_representative_ae
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))]
      (fun x => weakHarmonicInteriorRepresentative
        ((euclideanBall x₀ ρ).indicator h) x₀ hρ x) := by
  let U : Set Vec3 := euclideanBall x₀ ρ
  let I : Set Vec3 := euclideanBall x₀ (ρ / 2)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact euclidean_ball_isOpen hρ
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hIopen : IsOpen I := by
    dsimp [I]
    exact euclidean_ball_isOpen (by positivity)
  have hImeas : MeasurableSet I := hIopen.measurableSet
  let g : Vec3 → ℝ := U.indicator h
  have hgmem : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    dsimp [g]
    exact (memLp_indicator_iff_restrict hUmeas).2 hmem
  let ε : ℕ → ℝ := fun n => ρ / (12 * ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    exact approximation_scale_pos hρ n
  have hεle : ∀ n, ε n ≤ ρ / 12 := by
    intro n
    exact approximation_scale_le hρ n
  have hεtendsto : Tendsto ε atTop (nhds 0) := by
    exact approximation_scale_tendsto hρ
  let fn : ℕ → Vec3 → ℝ := fun n => mollify g (ε n) (hεpos n)
  have hfnmem : ∀ n, MemLp (fn n) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro n
    dsimp [fn]
    exact mollify_memLp_of_memLp (by norm_num) (by norm_num) hgmem (hεpos n)
  have hdiffmem : ∀ n, MemLp (fun y => fn n y - g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro n
    exact (hfnmem n).sub hgmem
  have hconv : Tendsto
      (fun n => eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (nhds 0) := by
    dsimp [fn]
    exact tendsto_eLpNorm_sub_zero_mollify (p := ENNReal.ofReal (3 / 2 : ℝ))
      (by norm_num) (by norm_num) hgmem hεtendsto hεpos
  have hfn_harm : ∀ n y, y ∈ euclideanBall x₀ (3 * ρ / 4) →
      CKN.spatialLaplacian (fn n) y = 0 := by
    intro n y hy
    apply weaklyHarmonicOn_mollify_spatialLaplacian_eq_zero hUmeas hmem hweak
    exact closedBall_subset_euclideanBall hρ (hεpos n) hy (hεle n)
  have hrepn : ∀ n x, x ∈ I →
      fn n x = weakHarmonicInteriorRepresentative (fn n) x₀ hρ x := by
    intro n x hx
    have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
      exact hx'.trans (by nlinarith only [hρ])
    have hrep := smooth_harmonic_annular_representation_on_outer
      (CKN.mollify_contDiff (hεpos n)
        (hgmem.locallyIntegrable (by norm_num))) hρ (hfn_harm n) hxinner
    simpa only [fn, weakHarmonicInteriorRepresentative] using hrep
  have hUsub : I ⊆ U := by
    intro x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hgun : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
    exact hgmem.mono_measure Measure.restrict_le_self
  have hfnU : ∀ n, MemLp (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict U) := by
    intro n
    exact (hfnmem n).mono_measure Measure.restrict_le_self
  have hbound : ∀ n x, x ∈ I →
      dist (fn n x)
          (weakHarmonicInteriorRepresentative g x₀ hρ x) ≤
        weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          (eLpNorm (fun y => fn n y - g y)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal := by
    intro n x hx
    have hdiffU := (hfnU n).sub hgun
    have hrepdiff := weak_rep_sub_eq hρ hx (hfnU n) hgun
    have hdiffU_lp : lpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) ≤
        (eLpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal := by
      exact ENNReal.toReal_mono (hdiffmem n).eLpNorm_lt_top.ne
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    have hrepbound := weak_harmonic_interior_representative_bound_internal
      hρ hdiffU x hx
    have hC : 0 ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ := by
      dsimp [weakHarmonicInteriorSupConstant]
      exact mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hval : |weakHarmonicInteriorRepresentative (fun y => fn n y - g y)
        x₀ hρ x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm (fun y => fn n y - g y)
            (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := hrepbound
    rw [← hrepdiff] at hval
    rw [← hrepn n x hx] at hval
    exact hval.trans (mul_le_mul_of_nonneg_left hdiffU_lp hC)
  have hC : 0 ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ := by
    dsimp [weakHarmonicInteriorSupConstant]
    exact mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)
  have hconv_real : Tendsto
      (fun n => (eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) atTop (nhds 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hdiffmem n).eLpNorm_ne_top)).mpr hconv
  have huniform : TendstoUniformlyOn fn
      (fun x => weakHarmonicInteriorRepresentative g x₀ hρ x)
      atTop I := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hprod : Tendsto
        (fun n => weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          (eLpNorm (fun y => fn n y - g y)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal)
        atTop (nhds 0) :=
      by
        have hD : Tendsto
            (fun _ : ℕ => weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹)
            atTop (nhds (weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹)) :=
          tendsto_const_nhds
        simpa only [mul_zero] using hD.mul hconv_real
    filter_upwards [hprod.eventually (gt_mem_nhds hδ)] with n hn x hx
    rw [dist_comm]
    exact (hbound n x hx).trans_lt hn
  have hmeasure : TendstoInMeasure volume fn atTop g := by
    exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hnae⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [ae_restrict_of_ae hnae, ae_restrict_mem hImeas] with x hx hxI
  have hxU : x ∈ U := hUsub hxI
  have hlim_g : Tendsto (fun i => fn (ns i) x) atTop (𝓝 (g x)) := hx
  have hlim_H : Tendsto (fun i => fn (ns i) x) atTop
      (𝓝 (weakHarmonicInteriorRepresentative g x₀ hρ x)) :=
    by
      simpa only [Function.comp_def] using
        (huniform.tendsto_at hxI).comp hns.tendsto_atTop
  have hgx : g x = h x := by simp [g, hxU]
  exact tendsto_nhds_unique (by simpa [hgx] using hlim_g) hlim_H

theorem weak_harmonic_interior_representative_bound
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      |weakHarmonicInteriorRepresentative h x₀ hρ x| ≤
        weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := by
  intro x hx
  have hsource := weak_rep_source_integral_bound hρ hx hmem
  have hcutoff : ∀ i : Fin 3, |∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      weakHarmonicInteriorCutoffConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro i
    exact weak_rep_cutoff_integral_bound hρ hx i hmem
  have hsum : |2 * ∑ i : Fin 3, ∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      6 * weakHarmonicInteriorCutoffConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    let I : Fin 3 → ℝ := fun i => ∫ y, h y * CKN.spatialDeriv
      (kernelCutoffDerivative x x₀ hρ i) i y
    change 2 * |∑ i : Fin 3, I i| ≤ _
    have habs : |∑ i : Fin 3, I i| ≤ ∑ i : Fin 3, |I i| := by
      simpa only [Fin.sum_univ_three] using
        (Finset.abs_sum_le_sum_abs I (Finset.univ : Finset (Fin 3)))
    calc
      2 * |∑ i : Fin 3, I i| ≤ 2 * ∑ i : Fin 3, |I i| :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * ∑ i : Fin 3,
          (weakHarmonicInteriorCutoffConstant *
            (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (2 : ℝ))
        apply Finset.sum_le_sum
        intro i hi
        exact hcutoff i
      _ = _ := by simp; ring
  rw [weakHarmonicInteriorRepresentative]
  have hsource_eq : (∫ y : Vec3, newtonianKernel (x - y) *
        (h y * CKN.spatialLaplacian (eta x₀ hρ) y)) =
      ∫ y : Vec3, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y) := by
    congr 1
    funext y
    ring
  rw [hsource_eq]
  calc
    |(-∫ y : Vec3, h y * (newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y)) +
        2 * ∑ i : Fin 3, ∫ y : Vec3,
          h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y| ≤
        |∫ y, h y * (newtonianKernel (x - y) *
          CKN.spatialLaplacian (eta x₀ hρ) y)| +
        |2 * ∑ i : Fin 3, ∫ y, h y *
          CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y| := by
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
      rw [show weakHarmonicInteriorSupConstant =
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
          (weakHarmonicInteriorSourceConstant +
            6 * weakHarmonicInteriorCutoffConstant) by rfl]
      exact (add_le_add hsource hsum).trans_eq (by ring)

end CKN.Foundation.Heat
