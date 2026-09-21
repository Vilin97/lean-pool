/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectScaleEnergy
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection

/-!
# Projected scale tails for the direct quadratic action

This module instantiates the seven separated annular families with the
actual fixed-scale outputs of an arbitrary retained subcollection `A`. The
smallest-selected-region partition continues to be formed from the ambient
family `S`.
-/

open Function MeasureTheory Set FourierTransform
open scoped ENNReal NNReal ContDiff SchwartzMap ComplexConjugate Convolution

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectProjectedTail

open KrauseLaceyBadScale KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectPositivePairing
open KrauseLaceyQuadraticDirectScaleEnergy
open KrauseLaceyQuadraticAnnularTail
open KrauseLaceyQuadraticSmoothProjection


noncomputable
section

/-- Classical equality for the interval indices of the projected tail. -/
local instance : DecidableEq RealInterval := Classical.decEq _

theorem norm_annularProjectionL2_le
    (j : ℤ) (v : Lp (α := ℝ) ℂ 2 volume) :
    ‖annularProjectionL2 j v‖ ≤ ‖v‖ := by
  have hmult : eLpNorm (annularFourierMultiplier j v) 2 volume ≤
      eLpNorm (⇑(Lp.fourierTransformₗᵢ ℝ ℂ v)) 2 volume := by
    apply eLpNorm_mono_ae (memLp_annularFourierMultiplier j v).aestronglyMeasurable
    filter_upwards with ξ
    unfold annularFourierMultiplier
    rw [norm_mul]
    simpa using mul_le_of_le_one_left (norm_nonneg _)
      (norm_scaledAnnularFrequencyCutoff_le_one j ξ)
  calc
    ‖annularProjectionL2 j v‖ = ‖annularMultiplierL2 j v‖ := by
      exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
    _ = (eLpNorm (annularFourierMultiplier j v) 2 volume).toReal := by
      exact Lp.norm_toLp _ _
    _ ≤ (eLpNorm (⇑(Lp.fourierTransformₗᵢ ℝ ℂ v)) 2 volume).toReal :=
      ENNReal.toReal_mono
        (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v)).eLpNorm_ne_top hmult
    _ = ‖Lp.fourierTransformₗᵢ ℝ ℂ v‖ := by
      let hF₂ := Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v)
      rw [← Lp.norm_toLp (⇑(Lp.fourierTransformₗᵢ ℝ ℂ v)) hF₂]
      rw [Lp.toLp_coeFn]
    _ = ‖v‖ := Lp.norm_fourier_eq v

/-! ## Integrable representatives of annular projections -/

/-- The Schwartz kernel obtained by inverse Fourier transform of the scaled annular cutoff. -/
def scaledAnnularKernelSchwartz (j : ℤ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (scaledAnnularFrequencySchwartz j)

/-- The function underlying the scaled annular Schwartz kernel. -/
def scaledAnnularKernel (j : ℤ) : ℝ → ℂ :=
  scaledAnnularKernelSchwartz j

theorem integrable_scaledAnnularKernel (j : ℤ) :
    Integrable (scaledAnnularKernel j) volume :=
  (scaledAnnularKernelSchwartz j).integrable

theorem fourier_scaledAnnularKernel (j : ℤ) (ξ : ℝ) :
    𝓕 (scaledAnnularKernel j) ξ = scaledAnnularFrequencyCutoff j ξ := by
  change 𝓕 (⇑(scaledAnnularKernelSchwartz j)) ξ = _
  rw [← SchwartzMap.fourier_coe]
  change (𝓕 (𝓕⁻ (scaledAnnularFrequencySchwartz j))) ξ = _
  rw [fourier_fourierInv_eq]
  rfl

/-- A uniform bound for the scaled annular kernel, given by its zeroth Schwartz seminorm. -/
def scaledAnnularKernelBound (j : ℤ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (scaledAnnularKernelSchwartz j)

theorem scaledAnnularKernelBound_nonneg (j : ℤ) :
    0 ≤ scaledAnnularKernelBound j := by
  unfold scaledAnnularKernelBound
  positivity

theorem norm_scaledAnnularKernel_le (j : ℤ) (x : ℝ) :
    ‖scaledAnnularKernel j x‖ ≤ scaledAnnularKernelBound j := by
  exact SchwartzMap.norm_le_seminorm ℂ (scaledAnnularKernelSchwartz j) x

/-- Convolution of an input with the scaled annular kernel. -/
def annularKernelConvolution (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, scaledAnnularKernel j (x - y) * f y

theorem annularKernelConvolution_eq_convolution
    (j : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    annularKernelConvolution j f x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledAnnularKernel j) x := by
  rw [annularKernelConvolution, MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.mul_apply']
  ring

theorem integrable_annularKernelConvolution
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) :
    Integrable (annularKernelConvolution j f) volume := by
  have hconv := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_scaledAnnularKernel j)
  apply hconv.congr
  filter_upwards with x
  exact (annularKernelConvolution_eq_convolution j f x).symm

theorem norm_annularKernelConvolution_le
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) (x : ℝ) :
    ‖annularKernelConvolution j f x‖ ≤
      scaledAnnularKernelBound j * ∫ y, ‖f y‖ := by
  have hrow : Integrable
      (fun y ↦ scaledAnnularKernel j (x - y) * f y) volume := by
    apply hf.bdd_mul
    · exact (scaledAnnularKernelSchwartz j).continuous.comp
        (continuous_const.sub continuous_id) |>.aestronglyMeasurable
    · filter_upwards with y
      exact norm_scaledAnnularKernel_le j (x - y)
  calc
    ‖annularKernelConvolution j f x‖ ≤
        ∫ y, ‖scaledAnnularKernel j (x - y) * f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, scaledAnnularKernelBound j * ‖f y‖ := by
      apply integral_mono hrow.norm
        (hf.norm.const_mul (scaledAnnularKernelBound j))
      intro y
      change ‖scaledAnnularKernel j (x - y) * f y‖ ≤
        scaledAnnularKernelBound j * ‖f y‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_scaledAnnularKernel_le j (x - y)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem memLp_two_annularKernelConvolution
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) :
    MemLp (annularKernelConvolution j f) 2 volume := by
  have hconv := integrable_annularKernelConvolution j hf
  rw [memLp_two_iff_integrable_sq_norm hconv.aestronglyMeasurable]
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖annularKernelConvolution j f x‖ ≤
        scaledAnnularKernelBound j * ∫ y, ‖f y‖ :=
    ae_of_all _ (norm_annularKernelConvolution_le j hf)
  have hbound' : ∀ᵐ x : ℝ ∂volume,
      ‖‖annularKernelConvolution j f x‖‖ ≤
        scaledAnnularKernelBound j * ∫ y, ‖f y‖ := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hx
  have hi := hconv.norm.bdd_mul hconv.norm.aestronglyMeasurable hbound'
  simpa only [pow_two] using hi

theorem fourier_annularKernelConvolution
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    𝓕 (annularKernelConvolution j f) ξ =
      scaledAnnularFrequencyCutoff j ξ * 𝓕 f ξ := by
  rw [show annularKernelConvolution j f =
      f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledAnnularKernel j by
    funext x
    exact annularKernelConvolution_eq_convolution j f x]
  rw [Real.fourier_mul_convolution_eq hf
      (integrable_scaledAnnularKernel j) ξ,
    fourier_scaledAnnularKernel]
  ring

theorem annularProjectionL2_eq_toLp_annularKernelConvolution
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume)
    (hf₂ : MemLp f 2 volume) :
    annularProjectionL2 j (hf₂.toLp f) =
      (memLp_two_annularKernelConvolution j hf).toLp
        (annularKernelConvolution j f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_annularProjectionL2]
  apply Lp.ext
  filter_upwards [
    (memLp_annularFourierMultiplier j (hf₂.toLp f)).coeFn_toLp,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq
      (integrable_annularKernelConvolution j hf)
      (memLp_two_annularKernelConvolution j hf),
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hf hf₂]
      with ξ hmult hconv hfourier
  rw [show (annularMultiplierL2 j (hf₂.toLp f) : ℝ → ℂ) ξ =
      annularFourierMultiplier j (hf₂.toLp f) ξ by
        simpa only [annularMultiplierL2] using hmult]
  rw [hconv, fourier_annularKernelConvolution j hf ξ]
  unfold annularFourierMultiplier
  rw [hfourier]

theorem annularProjectionL2_ae_eq_annularKernelConvolution
    (j : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume)
    (hf₂ : MemLp f 2 volume) :
    annularProjectionL2 j (hf₂.toLp f) =ᵐ[volume]
      annularKernelConvolution j f := by
  rw [annularProjectionL2_eq_toLp_annularKernelConvolution j hf hf₂]
  exact (memLp_two_annularKernelConvolution j hf).coeFn_toLp

/-! ## The actual projected fixed-scale outputs -/

/-- The genuine fixed-scale `L²` outputs, enumerated in one of the seven
residue classes. Both the grouped inputs and their smallest-region
partition are formed from the fixed ambient family `S`; only the output sum
is restricted to `A`. -/
def offsetScaleFamily
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  offsetOutputScaleLp S A scale f (residueScale r n) s

/-- A canonical measurable representative of the smooth annular projection
of the actual fixed-scale output. -/
def projectedOffsetResidueOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) : ℕ → ℝ → ℂ :=
  annularResidueRepresentative r (offsetScaleFamily S A scale f r s)

/-- The genuine fixed-output-scale `L²` representative is also integrable.
This is inherited from the finite sum of the localized `L¹` outputs, not
from any finite-measure support shortcut. -/
theorem integrable_offsetOutputScaleLp_toFun
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    Integrable (fun x ↦ offsetOutputScaleLp S A scale f k s x) volume := by
  have hliteral : Integrable
      (fun x ↦ ∑ I ∈ A.filter (fun I ↦ scale I = k),
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x) volume := by
    apply integrable_finsetSum
    intro I hI
    exact integrable_krauseLaceyLocalizedPiece (scale I) I
      (integrable_offsetGroupedInput S scale f I s)
  exact hliteral.congr (offsetOutputScaleLp_ae_eq S A scale f k s).symm

/-- Every projected actual scale output has an integrable representative.
The proof realizes the multiplier as convolution with its Schwartz inverse
Fourier kernel. -/
theorem integrable_projectedOffsetResidueOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (n : ℕ) :
    Integrable (projectedOffsetResidueOutput S A scale f r s n) volume := by
  let w : Lp ℂ 2 (volume : Measure ℝ) :=
    offsetOutputScaleLp S A scale f (residueScale r n) s
  have hw₁ : Integrable (fun x ↦ w x) volume :=
    integrable_offsetOutputScaleLp_toFun S A scale f (residueScale r n) s
  have hw₂ : MemLp (fun x ↦ w x) 2 volume := Lp.memLp w
  have hconv : Integrable
      (annularKernelConvolution (residueScale r n) (fun x ↦ w x)) volume :=
    integrable_annularKernelConvolution (residueScale r n) hw₁
  apply hconv.congr
  have hae := annularProjectionL2_ae_eq_annularKernelConvolution
    (residueScale r n) hw₁ hw₂
  simpa only [projectedOffsetResidueOutput, annularResidueRepresentative,
    annularResiduePiece, offsetScaleFamily, Lp.toLp_coeFn] using hae.symm

/-- Consequently the finite total required by the concrete annular-tail
theorem is integrable. -/
theorem integrable_projectedOffsetResidueTotal
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    Integrable (finitePieceTotal N
      (projectedOffsetResidueOutput S A scale f r s)) volume := by
  unfold finitePieceTotal
  apply integrable_finsetSum
  intro n hn
  exact integrable_projectedOffsetResidueOutput S A scale f r s n

/-- The fully concrete cardinality-free maximal-tail estimate for one of
the seven residue classes, before replacing projected energies by the
unprojected fixed-scale energies. -/
theorem projectedOffsetResidueTailMax_sq_lintegral_le_projectedSum
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    (∫⁻ x, finitePieceTailMax N
      (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ∑ n ∈ Finset.range N,
          ∫⁻ x, ‖projectedOffsetResidueOutput S A scale f r s n x‖ₑ ^ 2 := by
  exact annularResidueTailMax_sq_lintegral_le_sum r
    (offsetScaleFamily S A scale f r s) N
    (integrable_projectedOffsetResidueTotal S A scale f r s N)

/-! ## Replacement by the concrete fixed-scale energy -/

theorem lintegral_enorm_sq_coe_Lp
    (w : Lp (α := ℝ) ℂ 2 volume) :
    (∫⁻ x, ‖w x‖ₑ ^ 2) = ENNReal.ofReal (‖w‖ ^ 2) := by
  rw [← eLpNorm_two_sq_lintegral _ (Lp.memLp w).aestronglyMeasurable, ← Lp.enorm_def w,
    ENNReal.ofReal_pow (norm_nonneg w), ofReal_norm]

/-- Annular projection is contractive on the square integral. -/
theorem lintegral_enorm_sq_projectedOffsetResidueOutput_le
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (n : ℕ) :
    (∫⁻ x, ‖projectedOffsetResidueOutput S A scale f r s n x‖ₑ ^ 2) ≤
      ENNReal.ofReal
        (‖offsetOutputScaleLp S A scale f (residueScale r n) s‖ ^ 2) := by
  let w : Lp ℂ 2 (volume : Measure ℝ) :=
    offsetOutputScaleLp S A scale f (residueScale r n) s
  change (∫⁻ x, ‖annularProjectionL2 (residueScale r n) w x‖ₑ ^ 2) ≤ _
  rw [lintegral_enorm_sq_coe_Lp]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg (annularProjectionL2 (residueScale r n) w))
    (norm_annularProjectionL2_le (residueScale r n) w) 2

/-- A scale absent from the retained output family gives the zero `L²`
fixed-scale output. -/
theorem offsetOutputScaleLp_eq_zero_of_not_mem_image
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) (hk : k ∉ A.image scale) :
    offsetOutputScaleLp S A scale f k s = 0 := by
  unfold offsetOutputScaleLp
  apply Finset.sum_eq_zero
  intro I hI
  exact (hk (Finset.mem_image.mpr ⟨I, (Finset.mem_filter.mp hI).1,
    (Finset.mem_filter.mp hI).2⟩)).elim

/-- Restricting an injectively enumerated residue class to finitely many
indices cannot have more fixed-scale energy than the complete finite set of
scales occurring in `A`. -/
theorem sum_range_norm_offsetOutputScaleLp_residue_le_allScales
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ‖offsetOutputScaleLp S A scale f (residueScale r n) s‖ ^ 2 ≤
      ∑ k ∈ A.image scale, ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 := by
  classical
  let K := A.image scale
  let T := (Finset.range N).filter (fun n ↦ residueScale r n ∈ K)
  let F : ℤ → ℝ := fun k ↦ ‖offsetOutputScaleLp S A scale f k s‖ ^ 2
  have hzero (n : ℕ) (hn : n ∈ Finset.range N) (hnT : n ∉ T) :
      F (residueScale r n) = 0 := by
    have hnotK : residueScale r n ∉ K := by
      intro hnK
      exact hnT (Finset.mem_filter.mpr ⟨hn, hnK⟩)
    dsimp only [F]
    rw [show offsetOutputScaleLp S A scale f (residueScale r n) s = 0 by
      exact offsetOutputScaleLp_eq_zero_of_not_mem_image S A scale f
        (residueScale r n) s hnotK]
    norm_num
  have hrestrict :
      (∑ n ∈ Finset.range N, F (residueScale r n)) =
        ∑ n ∈ T, F (residueScale r n) := by
    symm
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro n hn hnT
      exact hzero n hn hnT
  have hinj : Set.InjOn (residueScale r) (↑T : Set ℕ) := by
    intro m hm n hn hmn
    unfold residueScale at hmn
    omega
  have himage :
      (∑ n ∈ T, F (residueScale r n)) =
        ∑ k ∈ T.image (residueScale r), F k := by
    symm
    exact Finset.sum_image hinj
  have hsub : T.image (residueScale r) ⊆ K := by
    intro k hk
    obtain ⟨n, hnT, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hnT).2
  calc
    ∑ n ∈ Finset.range N,
        ‖offsetOutputScaleLp S A scale f (residueScale r n) s‖ ^ 2 =
        ∑ n ∈ Finset.range N, F (residueScale r n) := by rfl
    _ = ∑ n ∈ T, F (residueScale r n) := hrestrict
    _ = ∑ k ∈ T.image (residueScale r), F k := himage
    _ ≤ ∑ k ∈ K, F k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hkK hkT
      exact sq_nonneg _
    _ = ∑ k ∈ A.image scale,
        ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 := by rfl

/-- The sum of the projected residue energies is bounded by the genuine
fixed-scale square sum over all scales occurring in `A`. -/
theorem sum_lintegral_projectedOffsetResidueOutput_le_allScales
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ∫⁻ x, ‖projectedOffsetResidueOutput S A scale f r s n x‖ₑ ^ 2) ≤
      ENNReal.ofReal (∑ k ∈ A.image scale,
        ‖offsetOutputScaleLp S A scale f k s‖ ^ 2) := by
  calc
    (∑ n ∈ Finset.range N,
        ∫⁻ x, ‖projectedOffsetResidueOutput S A scale f r s n x‖ₑ ^ 2) ≤
        ∑ n ∈ Finset.range N, ENNReal.ofReal
          (‖offsetOutputScaleLp S A scale f (residueScale r n) s‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact lintegral_enorm_sq_projectedOffsetResidueOutput_le
        S A scale f r s n
    _ = ENNReal.ofReal (∑ n ∈ Finset.range N,
        ‖offsetOutputScaleLp S A scale f (residueScale r n) s‖ ^ 2) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∑ k ∈ A.image scale,
        ‖offsetOutputScaleLp S A scale f k s‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (sum_range_norm_offsetOutputScaleLp_residue_le_allScales
          S A scale f r s N)

/-- The concrete projected maximal tail in each of the seven residue
classes is controlled by the actual all-scale output energy. -/
theorem projectedOffsetResidueTailMax_sq_lintegral_le_allScales
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    (∫⁻ x, finitePieceTailMax N
      (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal (∑ k ∈ A.image scale,
          ‖offsetOutputScaleLp S A scale f k s‖ ^ 2) := by
  exact (projectedOffsetResidueTailMax_sq_lintegral_le_projectedSum
    S A scale f r s N).trans
      (mul_le_mul_of_nonneg_left
        (sum_lintegral_projectedOffsetResidueOutput_le_allScales
          S A scale f r s N) bot_le)

/-- Final root-mass form of the projected maximal-tail estimate. It is
uniform in the retained output subcollection `A ⊆ S`, in the residue class,
and in the finite truncation length. -/
theorem projectedOffsetResidueTailMax_sq_lintegral_le_root_mass
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (r : Fin 7) (N : ℕ) :
    (∫⁻ x, finitePieceTailMax N
      (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖) := by
  refine (projectedOffsetResidueTailMax_sq_lintegral_le_allScales
    S A scale f r s N).trans ?_
  exact mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_le_ofReal
      (sum_norm_offsetOutputScaleLp_sq_le_root_mass hA hlam scale hscale
        f hs hM hmass I₀ hsub hgap)) bot_le

/-- The simultaneous form for all seven separated residue classes. -/
theorem sum_projectedOffsetResidueTailMax_sq_lintegral_le_allScales
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (s : ℤ) (N : ℕ) :
    (∑ r : Fin 7, ∫⁻ x, finitePieceTailMax N
      (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
      7 * ((4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal (∑ k ∈ A.image scale,
          ‖offsetOutputScaleLp S A scale f k s‖ ^ 2)) := by
  calc
    (∑ r : Fin 7, ∫⁻ x, finitePieceTailMax N
        (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
        ∑ _r : Fin 7,
          ((4 + 128 *
            (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
            ENNReal.ofReal (∑ k ∈ A.image scale,
              ‖offsetOutputScaleLp S A scale f k s‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact projectedOffsetResidueTailMax_sq_lintegral_le_allScales
        S A scale f r s N
    _ = _ := by simp

/-- Root-mass closure of the simultaneous seven-residue estimate. -/
theorem sum_projectedOffsetResidueTailMax_sq_lintegral_le_root_mass
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (N : ℕ) :
    (∑ r : Fin 7, ∫⁻ x, finitePieceTailMax N
      (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
      7 * ((4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)) := by
  calc
    (∑ r : Fin 7, ∫⁻ x, finitePieceTailMax N
        (projectedOffsetResidueOutput S A scale f r s) x ^ 2) ≤
        ∑ _r : Fin 7,
          ((4 + 128 *
            (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
            ENNReal.ofReal
              ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                  (2 : ℝ) ^ (-s)) *
                ∫ x in I₀.carrier, ‖f x‖)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact projectedOffsetResidueTailMax_sq_lintegral_le_root_mass
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap r N
    _ = _ := by simp


end
end KrauseLaceyQuadraticDirectProjectedTail
end QuadraticCarleson
