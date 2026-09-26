/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HLS
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# Pk Bounds P7

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

/-! The HLS input for one derivative potential.  The pointwise domination
hypothesis is the kernel comparison used when the pressure potential is
defined from an integrable compactly supported slice. -/

private lemma pressure_derivative_kernel_enorm_le {i : Fin 3} {x y : Vec3}
    (hxy : x ≠ y) :
    ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hb := CKN.Foundation.Heat.newtonianKernel_spatialDeriv_size_bound hz i
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hpi : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  calc
    ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ =
        ENNReal.ofReal |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
          (x - y)| := by
      simpa only [Real.norm_eq_abs] using
        (ofReal_norm
          (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y))).symm
    _ ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
      ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        (ENNReal.ofReal ‖x - y‖) ^ (-2 : ℝ) := by
      rw [ENNReal.ofReal_mul hpi]
      rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 4 * Real.pi)]
      rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < ‖x - y‖ ^ 2)]
      have hpow : ENNReal.ofReal (‖x - y‖ ^ 2) =
          (ENNReal.ofReal ‖x - y‖) ^ (2 : ℕ) :=
        ENNReal.ofReal_pow hnorm.le 2
      have hinv := congrArg Inv.inv hpow
      rw [hinv, ← ENNReal.rpow_natCast, ENNReal.rpow_neg]
      norm_num
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
      rw [rieszKernelOne, dist_eq_norm]

theorem pressureNewtonianDerivativePotential_enorm_le_rieszPotentialOne
    (i : Fin 3) (g : Vec3 → ℝ) (x : Vec3) :
    ‖pressureNewtonianDerivativePotential i g x‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszPotentialOne g x := by
  have hkernel : ∀ᵐ y ∂volume,
      ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ ≤
        ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    exact pressure_derivative_kernel_enorm_le hy.symm
  have hmain := enorm_integral_le_lintegral_enorm
    (μ := volume)
    (fun y : Vec3 => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
      (x - y) * g y)
  change ‖∫ y, CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
      (x - y) * g y‖ₑ ≤ _
  calc
    ‖∫ y, CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
        (x - y) * g y‖ₑ ≤
        ∫⁻ y, ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
          (x - y) * g y‖ₑ := hmain
    _ ≤ ∫⁻ y, (ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y) *
        ENNReal.ofReal |g y| := by
      apply lintegral_mono_ae
      filter_upwards [hkernel] with y hy
      calc
        ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
            (x - y) * g y‖ₑ =
            ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
              (x - y)‖ₑ * ENNReal.ofReal |g y| := by
          have hg : ENNReal.ofReal |g y| = ‖g y‖ₑ := by
            simpa only [Real.norm_eq_abs] using ofReal_norm (g y)
          rw [hg, ← enorm_mul]
        _ ≤ (ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y) *
            ENNReal.ofReal |g y| :=
          mul_le_mul_of_nonneg_right hy (by positivity)
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszPotentialOne g x := by
      rw [rieszPotentialOne]
      rw [← lintegral_const_mul' (ENNReal.ofReal ((4 * Real.pi)⁻¹))
        _ ENNReal.ofReal_ne_top]
      ac_rfl

theorem pressureNewtonianDerivativePotential_eLpNorm15_le_hls
    {g : Vec3 → ℝ} (i : Fin 3) (hg : Measurable g)
    (hfinite : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞)
    (hzero : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ≠ 0)
    (hgood : ∀ᵐ x ∂volume,
      maximalMajorant g x ≠ 0 ∧ maximalMajorant g x ≠ ∞)
    {K : ℝ}
    (hdom : ∀ᵐ x ∂volume,
      ‖pressureNewtonianDerivativePotential i g x‖ₑ ≤
        ENNReal.ofReal K * rieszPotentialOne g x) :
    eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ)
        volume ≤
      ENNReal.ofReal K * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  have hHLS := rieszPotentialOne_hls_of_good hg hfinite hzero hgood
  have hpow : ∀ᵐ x ∂volume,
      ‖pressureNewtonianDerivativePotential i g x‖ₑ ^ (15 : ℝ) ≤
        (ENNReal.ofReal K * rieszPotentialOne g x) ^ (15 : ℝ) := by
    filter_upwards [hdom] with x hx
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  calc
    eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ)
        volume =
        (∫⁻ x, ‖pressureNewtonianDerivativePotential i g x‖ₑ ^ (15 : ℝ)) ^
          (1 / 15 : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
    _ ≤ (∫⁻ x, (ENNReal.ofReal K * rieszPotentialOne g x) ^ (15 : ℝ)) ^
          (1 / 15 : ℝ) := by
      exact ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) (by norm_num)
    _ = ENNReal.ofReal K *
          (∫⁻ x, rieszPotentialOne g x ^ (15 : ℝ)) ^ (1 / 15 : ℝ) := by
      have heq : (fun x : Vec3 =>
          (ENNReal.ofReal K * rieszPotentialOne g x) ^ (15 : ℝ)) =
          (fun x : Vec3 =>
            (ENNReal.ofReal K) ^ (15 : ℝ) *
              rieszPotentialOne g x ^ (15 : ℝ)) := by
        funext x
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [heq, lintegral_const_mul']
      · rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hHLS
          (show 0 ≤ ENNReal.ofReal K from bot_le))

theorem pressureNewtonianDerivativePotential_eLpNorm15_le_hls_unconditional
    {g : Vec3 → ℝ} (i : Fin 3) (hg : Measurable g)
    (hfinite : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞)
    (hzero : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ≠ 0)
    (hgood : ∀ᵐ x ∂volume,
      maximalMajorant g x ≠ 0 ∧ maximalMajorant g x ≠ ∞) :
    eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ)
        volume ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  apply pressureNewtonianDerivativePotential_eLpNorm15_le_hls i hg hfinite hzero
    hgood
  · exact Eventually.of_forall
      (pressureNewtonianDerivativePotential_enorm_le_rieszPotentialOne i g)

theorem pressureNewtonianDerivativePotential_eLpNorm15_le_hls_of_zero_or_good
    {g : Vec3 → ℝ} (i : Fin 3) (hg : Measurable g)
    (hfinite : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞) :
    eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ)
        volume ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let I : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)
  by_cases hI0 : I = 0
  · have hgzero0 : (fun y : Vec3 => ENNReal.ofReal |g y|) =ᵐ[volume] 0 :=
      ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero (by norm_num)
        (hg.norm.ennreal_ofReal).aemeasurable hI0
    have hgzero : g =ᵐ[volume] 0 := by
      filter_upwards [hgzero0] with y hy
      have habs : |g y| = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp hy
        · exact abs_nonneg _
      exact abs_eq_zero.mp habs
    have hderiv : ∀ x : Vec3, pressureNewtonianDerivativePotential i g x = 0 := by
      intro x
      unfold pressureNewtonianDerivativePotential
      apply integral_eq_zero_of_ae
      filter_upwards [hgzero] with y hy
      simp [hy]
    have hfun : (fun x => pressureNewtonianDerivativePotential i g x) =ᵐ[volume] 0 :=
      Eventually.of_forall hderiv
    have hnorm := eLpNorm'_eq_zero_of_ae_zero (f := fun x =>
      pressureNewtonianDerivativePotential i g x) (by norm_num : (0 : ℝ) < 15) hfun
    simpa [I, hI0] using hnorm.le
  · have htop := ae_lt_top_maximalFunction
      (f := fun y : Vec3 => ENNReal.ofReal |g y|)
      (hg.norm.ennreal_ofReal) (by norm_num) hfinite
    have hgood : ∀ᵐ x ∂volume,
        maximalMajorant g x ≠ 0 ∧ maximalMajorant g x ≠ ∞ := by
      filter_upwards [htop] with x hx
      exact ⟨maximalMajorant_ne_zero_of_integral_ne_zero hg hI0 x,
        ne_of_lt (show maximalMajorant g x < ∞ by
          simpa [maximalMajorant] using hx)⟩
    exact pressureNewtonianDerivativePotential_eLpNorm15_le_hls_unconditional
      i hg hfinite hI0 hgood

theorem pressureP7_eLpNorm15_le_components
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    {A : Fin 3 → ℝ≥0∞}
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) volume)
    (hA : ∀ j, eLpNorm'
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) (15 : ℝ) volume ≤ A j) :
    eLpNorm' (pressureP7 η f s) (15 : ℝ) volume ≤ ∑ j, A j := by
  let F : Fin 3 → Vec3 → ℝ := fun j x =>
    pressureNewtonianDerivativePotential j (fun y => η y * f (y, s) j) x
  change eLpNorm' (-fun x => ∑ j, F j x) (15 : ℝ) volume ≤ _
  rw [eLpNorm'_neg]
  calc
    eLpNorm' (∑ j, F j) (15 : ℝ) volume ≤
        ∑ j, eLpNorm' (F j) (15 : ℝ) volume := by
      exact eLpNorm'_sum_le (q := (15 : ℝ))
        (s := (Finset.univ : Finset (Fin 3)))
        (fun j _hj => by simpa [F] using hmeas j) (by norm_num)
    _ ≤ ∑ j, A j := by
      exact Finset.sum_le_sum (fun j _hj => by simpa [F] using hA j)

theorem pressureP7_eLpNorm15_le_hls_of_aestronglyMeasurable
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hgmeas : ∀ j, AEStronglyMeasurable
      (fun y => η y * f (y, s) j) volume)
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) volume)
    (hfinite : ∀ j, (∫⁻ y, ENNReal.ofReal
      |η y * f (y, s) j| ^ (5 / 2 : ℝ)) < ∞) :
    eLpNorm' (pressureP7 η f s) (15 : ℝ) volume ≤
      ∑ j, ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal
          |η y * f (y, s) j| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  apply pressureP7_eLpNorm15_le_components hmeas
  intro j
  let g : Vec3 → ℝ := fun y => η y * f (y, s) j
  let gm0 : Vec3 →ₘ[volume] ℝ := AEEqFun.mk g (hgmeas j)
  let gm : Vec3 → ℝ := gm0
  have hgae : gm =ᵐ[volume] g := AEEqFun.coeFn_mk g (hgmeas j)
  have hIeq : (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) =
      ∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [hgae] with y hy
    simp [hy]
  have hfinite' : (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) < ∞ := by
    rw [hIeq]
    exact hfinite j
  have hpot_ae : (fun x => pressureNewtonianDerivativePotential j gm x) =ᵐ[volume]
      (fun x => pressureNewtonianDerivativePotential j g x) := by
    filter_upwards [] with x
    unfold pressureNewtonianDerivativePotential
    apply integral_congr_ae
    filter_upwards [hgae] with y hy
    simp [hy]
  have hbound := pressureNewtonianDerivativePotential_eLpNorm15_le_hls_of_zero_or_good
    j gm0.measurable hfinite'
  have hbound' : eLpNorm' (fun x => pressureNewtonianDerivativePotential j g x)
      (15 : ℝ) volume ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
    rw [← eLpNorm'_congr_ae hpot_ae]
    rw [hIeq] at hbound
    simpa [g] using hbound
  simpa [g] using hbound'

/-! Cylinder assembly in the same scale-interface form as the other pressure
terms.  The preceding theorem supplies the fixed-time HLS estimate used to
instantiate `hP₇`; the cylinder step is purely the time/space Hölder algebra. -/

end CKN
