/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveDyadicKernel
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertMaximalWeakOneOne
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertRepresentativeBridge
import Mathlib.Analysis.Fourier.Convolution

/-!
# Concrete smooth frequency cutoffs for the direct quadratic proof

The positive quadratic kernel at physical scale `2^j` has stationary
frequency in the normalized interval `[1/4, 1]`.  We choose a smooth cutoff
which is identically one on the larger interval `[1/8, 2]` and is supported
in `(1/16, 33/16)`.  Its dyadic dilates are exactly disjoint after separating
the scales into seven residue classes.
-/

open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ContDiff SchwartzMap ComplexConjugate Convolution

namespace QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection

open HilbertMaximalWeakOneOne


noncomputable section

/-- A one-sided smooth frequency bump.  The inner ball is `[1/8,2]` and
the outer ball is `(1/16,33/16)`. -/
def annularFrequencyCutoffData : ContDiffBump (17 / 16 : ℝ) :=
  ⟨15 / 16, 1, by norm_num, by norm_num⟩

def annularFrequencyCutoffReal : ℝ → ℝ := annularFrequencyCutoffData

def annularFrequencyCutoff (ξ : ℝ) : ℂ :=
  (annularFrequencyCutoffReal ξ : ℂ)

theorem contDiff_annularFrequencyCutoff :
    ContDiff ℝ ∞ annularFrequencyCutoff := by
  exact Complex.ofRealCLM.contDiff.comp annularFrequencyCutoffData.contDiff

theorem annularFrequencyCutoff_eq_one {ξ : ℝ}
    (hξ : ξ ∈ Icc (1 / 8 : ℝ) 2) :
    annularFrequencyCutoff ξ = 1 := by
  have hmem : ξ ∈ closedBall (17 / 16 : ℝ) (15 / 16) := by
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  have hbump : annularFrequencyCutoffData ξ = 1 :=
    annularFrequencyCutoffData.one_of_mem_closedBall hmem
  change (annularFrequencyCutoffData ξ : ℂ) = 1
  rw [hbump]
  norm_num

theorem annularFrequencyCutoff_eq_zero {ξ : ℝ}
    (hξ : ξ ≤ 1 / 16 ∨ 33 / 16 ≤ ξ) :
    annularFrequencyCutoff ξ = 0 := by
  have hdist : (1 : ℝ) ≤ dist ξ (17 / 16 : ℝ) := by
    rw [Real.dist_eq]
    rcases hξ with hlow | hhigh
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have hbump : annularFrequencyCutoffData ξ = 0 :=
    annularFrequencyCutoffData.zero_of_le_dist hdist
  change (annularFrequencyCutoffData ξ : ℂ) = 0
  rw [hbump]
  norm_num

theorem annularFrequencyCutoff_support_subset :
    Function.support annularFrequencyCutoff ⊆ Ioo (1 / 16 : ℝ) (33 / 16) := by
  intro ξ hξ
  constructor
  · by_contra h
    exact hξ (annularFrequencyCutoff_eq_zero (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hξ (annularFrequencyCutoff_eq_zero (Or.inr (le_of_not_gt h)))

theorem hasCompactSupport_annularFrequencyCutoff :
    HasCompactSupport annularFrequencyCutoff := by
  exact annularFrequencyCutoffData.hasCompactSupport.comp_left rfl

/-- The cutoff at frequency scale `2^j`. -/
def scaledAnnularFrequencyCutoff (j : ℤ) (ξ : ℝ) : ℂ :=
  annularFrequencyCutoff (ξ / (2 : ℝ) ^ j)

/-- The exact open annulus naturally attached to the scaled cutoff. -/
def scaledFrequencyAnnulus (j : ℤ) : Set ℝ :=
  Ioo ((1 / 16 : ℝ) * (2 : ℝ) ^ j)
    ((33 / 16 : ℝ) * (2 : ℝ) ^ j)

theorem scaledAnnularFrequencyCutoff_support_subset (j : ℤ) :
    Function.support (scaledAnnularFrequencyCutoff j) ⊆
      scaledFrequencyAnnulus j := by
  intro ξ hξ
  have hs := annularFrequencyCutoff_support_subset hξ
  have hpow : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  constructor
  · exact (lt_div_iff₀ hpow).mp hs.1
  · exact (div_lt_iff₀ hpow).mp hs.2

theorem contDiff_scaledAnnularFrequencyCutoff (j : ℤ) :
    ContDiff ℝ ∞ (scaledAnnularFrequencyCutoff j) := by
  exact contDiff_annularFrequencyCutoff.comp
    (contDiff_id.div_const ((2 : ℝ) ^ j))

theorem hasCompactSupport_scaledAnnularFrequencyCutoff (j : ℤ) :
    HasCompactSupport (scaledAnnularFrequencyCutoff j) := by
  have hc : ((2 : ℝ) ^ j)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by norm_num))
  change HasCompactSupport (fun x : ℝ ↦
    annularFrequencyCutoff (x / (2 : ℝ) ^ j))
  simpa only [smul_eq_mul, div_eq_inv_mul, mul_comm] using
    hasCompactSupport_annularFrequencyCutoff.comp_smul hc

/-- The concrete annuli are disjoint once their scale indices differ by six.
The numerical inequality behind this is `33 < 2^6`. -/
theorem scaledFrequencyAnnulus_disjoint_of_add_six_le
    {j k : ℤ} (hjk : j + 6 ≤ k) :
    Disjoint (scaledFrequencyAnnulus j) (scaledFrequencyAnnulus k) := by
  rw [Set.disjoint_left]
  intro ξ hξj hξk
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hscale : (64 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := by
    calc
      (64 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 6) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ ≤ (2 : ℝ) ^ k :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk
  have hgap :
      (33 / 16 : ℝ) * (2 : ℝ) ^ j <
        (1 / 16 : ℝ) * (2 : ℝ) ^ k := by
    nlinarith
  exact (not_lt_of_ge (le_of_lt hgap)) (hξk.1.trans hξj.2)

/-- The integer scale in residue class `r mod 7` with nonnegative index `n`. -/
def residueScale (r : Fin 7) (n : ℕ) : ℤ :=
  (r : ℕ) + 7 * (n : ℤ)

/-- Within each of the seven residue classes, the concrete annuli are
pairwise disjoint.  Seven classes leave a one-scale margin beyond the exact
six-scale disjointness threshold, which is used by the low-pass cutoff. -/
theorem pairwiseDisjoint_scaledFrequencyAnnulus_residueScale (r : Fin 7) :
    Pairwise fun m n : ℕ ↦
      Disjoint (scaledFrequencyAnnulus (residueScale r m))
        (scaledFrequencyAnnulus (residueScale r n)) := by
  intro m n hmn
  by_cases hlt : m < n
  · apply scaledFrequencyAnnulus_disjoint_of_add_six_le
    simp only [residueScale]
    omega
  · have hnm : n < m := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hmn.symm
    exact (scaledFrequencyAnnulus_disjoint_of_add_six_le (j := residueScale r n)
      (k := residueScale r m) (by simp only [residueScale]; omega)).symm

/-- The scaled cutoff as a Schwartz multiplier. -/
def scaledAnnularFrequencySchwartz (j : ℤ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_scaledAnnularFrequencyCutoff j).toSchwartzMap
    (contDiff_scaledAnnularFrequencyCutoff j)

@[simp] theorem scaledAnnularFrequencySchwartz_apply (j : ℤ) (ξ : ℝ) :
    scaledAnnularFrequencySchwartz j ξ = scaledAnnularFrequencyCutoff j ξ := rfl

/-- Multiplication by the concrete annular cutoff on the Fourier side. -/
def annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ :=
  fun ξ ↦ scaledAnnularFrequencyCutoff j ξ *
    (Lp.fourierTransformₗᵢ ℝ ℂ v) ξ

theorem aestronglyMeasurable_annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    AEStronglyMeasurable (annularFourierMultiplier j v) volume := by
  exact (contDiff_scaledAnnularFrequencyCutoff j).continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ v))

theorem norm_scaledAnnularFrequencyCutoff_le_one (j : ℤ) (ξ : ℝ) :
    ‖scaledAnnularFrequencyCutoff j ξ‖ ≤ 1 := by
  rw [scaledAnnularFrequencyCutoff, annularFrequencyCutoff,
    annularFrequencyCutoffReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg annularFrequencyCutoffData.nonneg]
  exact annularFrequencyCutoffData.le_one

theorem memLp_annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (annularFourierMultiplier j v) 2 volume := by
  apply MemLp.of_le_mul (c := 1)
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v))
  · exact aestronglyMeasurable_annularFourierMultiplier j v
  · filter_upwards with ξ
    unfold annularFourierMultiplier
    rw [norm_mul, one_mul]
    simpa using mul_le_mul_of_nonneg_right
      (norm_scaledAnnularFrequencyCutoff_le_one j ξ)
      (norm_nonneg ((Lp.fourierTransformₗᵢ ℝ ℂ v) ξ))

/-- The concrete Fourier-side annular multiplier as an `L²` element. -/
def annularMultiplierL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (memLp_annularFourierMultiplier j v).toLp (annularFourierMultiplier j v)

/-- The smooth annular projection, defined by applying the concrete cutoff
on the Fourier side and then inverse Fourier transforming. -/
def annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (annularMultiplierL2 j v)

theorem fourier_annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v) =
      annularMultiplierL2 j v := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

theorem fourier_annularProjectionL2_ae (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v)) ξ) =ᵐ[volume]
      annularFourierMultiplier j v := by
  rw [fourier_annularProjectionL2]
  exact (memLp_annularFourierMultiplier j v).coeFn_toLp

theorem hasFourierSupportIn_annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    KrauseLaceyQuadraticAnnularTail.HasFourierSupportIn
      (annularProjectionL2 j v) (scaledFrequencyAnnulus j) := by
  have hae :
      (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v)) ξ) =ᵐ[volume]
        annularFourierMultiplier j v := by
    rw [fourier_annularProjectionL2]
    exact (memLp_annularFourierMultiplier j v).coeFn_toLp
  filter_upwards [hae] with ξ hξ
  intro hξout
  rw [hξ]
  have hcut : scaledAnnularFrequencyCutoff j ξ = 0 := by
    by_contra hne
    exact hξout (scaledAnnularFrequencyCutoff_support_subset j hne)
  simp [annularFourierMultiplier, hcut]

/-- Projecting arbitrary `L²` pieces at scales in one residue class produces
the exact pairwise Fourier separation needed by the abstract tail theorem. -/
theorem hasPairwiseSeparatedFourierSupport_annularProjection_residueScale
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) :
    KrauseLaceyQuadraticAnnularTail.HasPairwiseSeparatedFourierSupport
      (fun n ↦ annularProjectionL2 (residueScale r n) (v n)) := by
  apply KrauseLaceyQuadraticAnnularTail.hasPairwiseSeparatedFourierSupport_of_disjoint_regions
    (E := fun n ↦ scaledFrequencyAnnulus (residueScale r n))
  · exact pairwiseDisjoint_scaledFrequencyAnnulus_residueScale r
  · exact fun n ↦ hasFourierSupportIn_annularProjectionL2 _ _

/-! ## The boundary low-pass cutoff -/

/-- A smooth low-pass cutoff placed three scales below the first omitted
annulus.  The shift by three is chosen so that the cutoff is one on all
earlier annuli in a seven-residue-class split and zero on the current and
all later annuli. -/
def scaledLowPassCutoff (k : ℤ) (ξ : ℝ) : ℂ :=
  (dyadicCutoff (ξ / (2 : ℝ) ^ (k - 3)) : ℂ)

theorem contDiff_scaledLowPassCutoff (k : ℤ) :
    ContDiff ℝ ∞ (scaledLowPassCutoff k) := by
  exact Complex.ofRealCLM.contDiff.comp
    (dyadicCutoff_smooth.comp (contDiff_id.div_const ((2 : ℝ) ^ (k - 3))))

theorem scaledLowPassCutoff_eq_one_on_earlier_annulus
    {j k : ℤ} (hjk : j + 7 ≤ k) {ξ : ℝ}
    (hξ : ξ ∈ scaledFrequencyAnnulus j) :
    scaledLowPassCutoff k ξ = 1 := by
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hpk : 0 < (2 : ℝ) ^ (k - 3) := zpow_pos (by norm_num) (k - 3)
  have hscale : (16 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (k - 3) := by
    calc
      (16 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 4) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ ≤ (2 : ℝ) ^ (k - 3) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
  have hξpos : 0 < ξ := by
    have hlower : 0 < (1 / 16 : ℝ) * (2 : ℝ) ^ j := mul_pos (by norm_num) hpj
    exact hlower.trans hξ.1
  have hnorm : |ξ / (2 : ℝ) ^ (k - 3)| ≤ 1 / 4 := by
    rw [abs_of_pos (div_pos hξpos hpk)]
    apply (div_le_iff₀ hpk).2
    nlinarith [hξ.2]
  unfold scaledLowPassCutoff
  rw [dyadicCutoff_eq_one hnorm]
  norm_num

theorem scaledLowPassCutoff_eq_zero_on_current_or_later_annulus
    {j k : ℤ} (hkj : k ≤ j) {ξ : ℝ}
    (hξ : ξ ∈ scaledFrequencyAnnulus j) :
    scaledLowPassCutoff k ξ = 0 := by
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hpk : 0 < (2 : ℝ) ^ (k - 3) := zpow_pos (by norm_num) (k - 3)
  have hjm : 0 < (2 : ℝ) ^ (j - 3) := zpow_pos (by norm_num) (j - 3)
  have hscale : (2 : ℝ) ^ (k - 3) ≤ (2 : ℝ) ^ (j - 3) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hjid : (2 : ℝ) ^ j = 8 * (2 : ℝ) ^ (j - 3) := by
    calc
      (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 3) + 3) := by congr 2 <;> omega
      _ = (2 : ℝ) ^ (j - 3) * (2 : ℝ) ^ (3 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 8 * (2 : ℝ) ^ (j - 3) := by norm_num; ring
  have hξpos : 0 < ξ := by
    have hlower : 0 < (1 / 16 : ℝ) * (2 : ℝ) ^ j := mul_pos (by norm_num) hpj
    exact hlower.trans hξ.1
  have hnorm : 1 / 2 ≤ |ξ / (2 : ℝ) ^ (k - 3)| := by
    rw [abs_of_pos (div_pos hξpos hpk)]
    apply (le_div_iff₀ hpk).2
    nlinarith [hξ.1]
  unfold scaledLowPassCutoff
  rw [dyadicCutoff_eq_zero hnorm]
  norm_num

theorem scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_earlier
    {j k : ℤ} (hjk : j + 7 ≤ k) (ξ : ℝ) :
    scaledLowPassCutoff k ξ * scaledAnnularFrequencyCutoff j ξ =
      scaledAnnularFrequencyCutoff j ξ := by
  by_cases hcut : scaledAnnularFrequencyCutoff j ξ = 0
  · simp [hcut]
  · rw [scaledLowPassCutoff_eq_one_on_earlier_annulus hjk
      (scaledAnnularFrequencyCutoff_support_subset j hcut), one_mul]

theorem scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_current_or_later
    {j k : ℤ} (hkj : k ≤ j) (ξ : ℝ) :
    scaledLowPassCutoff k ξ * scaledAnnularFrequencyCutoff j ξ = 0 := by
  by_cases hcut : scaledAnnularFrequencyCutoff j ξ = 0
  · simp [hcut]
  · rw [scaledLowPassCutoff_eq_zero_on_current_or_later_annulus hkj
      (scaledAnnularFrequencyCutoff_support_subset j hcut), zero_mul]

def lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ :=
  fun ξ ↦ scaledLowPassCutoff k ξ *
    (Lp.fourierTransformₗᵢ ℝ ℂ v) ξ

theorem norm_scaledLowPassCutoff_le_one (k : ℤ) (ξ : ℝ) :
    ‖scaledLowPassCutoff k ξ‖ ≤ 1 := by
  rw [scaledLowPassCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dyadicCutoff_nonneg _)]
  exact dyadicCutoff_le_one _

theorem aestronglyMeasurable_lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    AEStronglyMeasurable (lowPassFourierMultiplier k v) volume := by
  exact (contDiff_scaledLowPassCutoff k).continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ v))

theorem memLp_lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (lowPassFourierMultiplier k v) 2 volume := by
  apply MemLp.of_le_mul (c := 1)
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v))
  · exact aestronglyMeasurable_lowPassFourierMultiplier k v
  · filter_upwards with ξ
    unfold lowPassFourierMultiplier
    rw [norm_mul, one_mul]
    simpa using mul_le_mul_of_nonneg_right
      (norm_scaledLowPassCutoff_le_one k ξ)
      (norm_nonneg ((Lp.fourierTransformₗᵢ ℝ ℂ v) ξ))

def lowPassMultiplierL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (memLp_lowPassFourierMultiplier k v).toLp (lowPassFourierMultiplier k v)

/-- The concrete smooth low-pass projection used to recover a prefix from
the total annular sum. -/
def lowPassProjectionL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (lowPassMultiplierL2 k v)

theorem fourier_lowPassProjectionL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (lowPassProjectionL2 k v) =
      lowPassMultiplierL2 k v := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

theorem fourier_lowPassProjectionL2_ae (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (lowPassProjectionL2 k v)) ξ) =ᵐ[volume]
      lowPassFourierMultiplier k v := by
  rw [fourier_lowPassProjectionL2]
  exact (memLp_lowPassFourierMultiplier k v).coeFn_toLp

theorem lowPassProjectionL2_annularProjectionL2_of_earlier
    {j k : ℤ} (hjk : j + 7 ≤ k)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (annularProjectionL2 j v) =
      annularProjectionL2 j v := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (annularProjectionL2 j v)).coeFn_toLp,
    fourier_annularProjectionL2_ae j v] with ξ hlow hann
  have hlow' :
      (lowPassMultiplierL2 k (annularProjectionL2 j v) : ℝ → ℂ) ξ =
        lowPassFourierMultiplier k (annularProjectionL2 j v) ξ := by
    simpa only [lowPassMultiplierL2] using hlow
  rw [hlow']
  unfold lowPassFourierMultiplier
  rw [hann]
  unfold annularFourierMultiplier
  rw [← mul_assoc,
    scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_earlier hjk]

theorem lowPassProjectionL2_annularProjectionL2_of_current_or_later
    {j k : ℤ} (hkj : k ≤ j)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (annularProjectionL2 j v) = 0 := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_zero]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (annularProjectionL2 j v)).coeFn_toLp,
    fourier_annularProjectionL2_ae j v] with ξ hlow hann
  have hlow' :
      (lowPassMultiplierL2 k (annularProjectionL2 j v) : ℝ → ℂ) ξ =
        lowPassFourierMultiplier k (annularProjectionL2 j v) ξ := by
    simpa only [lowPassMultiplierL2] using hlow
  rw [hlow']
  unfold lowPassFourierMultiplier
  rw [hann]
  unfold annularFourierMultiplier
  rw [← mul_assoc,
    scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_current_or_later hkj,
    zero_mul]
  simp

theorem lowPassProjectionL2_add (k : ℤ)
    (v w : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (v + w) =
      lowPassProjectionL2 k v + lowPassProjectionL2 k w := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_add,
    fourier_lowPassProjectionL2, fourier_lowPassProjectionL2]
  apply Lp.ext
  have hFourierAdd :
      (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (v + w) : ℝ → ℂ) ξ) =ᵐ[volume]
        fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ v : ℝ → ℂ) ξ +
          (Lp.fourierTransformₗᵢ ℝ ℂ w : ℝ → ℂ) ξ := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (v + w)).coeFn_toLp,
    (memLp_lowPassFourierMultiplier k v).coeFn_toLp,
    (memLp_lowPassFourierMultiplier k w).coeFn_toLp,
    hFourierAdd,
    Lp.coeFn_add (lowPassMultiplierL2 k v) (lowPassMultiplierL2 k w)]
      with ξ hvw hv hw hFadd hLadd
  rw [show (lowPassMultiplierL2 k (v + w) : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k (v + w) ξ by
        simpa only [lowPassMultiplierL2] using hvw]
  rw [hLadd]
  change lowPassFourierMultiplier k (v + w) ξ =
    (lowPassMultiplierL2 k v : ℝ → ℂ) ξ +
      (lowPassMultiplierL2 k w : ℝ → ℂ) ξ
  rw [show (lowPassMultiplierL2 k v : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k v ξ by
        simpa only [lowPassMultiplierL2] using hv]
  rw [show (lowPassMultiplierL2 k w : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k w ξ by
        simpa only [lowPassMultiplierL2] using hw]
  simp only [lowPassFourierMultiplier, hFadd, mul_add]

theorem lowPassProjectionL2_zero (k : ℤ) :
    lowPassProjectionL2 k (0 : Lp (α := ℝ) ℂ 2 volume) = 0 := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_zero]
  apply Lp.ext
  filter_upwards [(memLp_lowPassFourierMultiplier k 0).coeFn_toLp] with ξ hξ
  rw [show (lowPassMultiplierL2 k 0 : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k 0 ξ by
        simpa only [lowPassMultiplierL2] using hξ]
  simp [lowPassFourierMultiplier]

theorem lowPassProjectionL2_finset_sum
    {ι : Type*} (S : Finset ι) (k : ℤ)
    (v : ι → Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (∑ i ∈ S, v i) =
      ∑ i ∈ S, lowPassProjectionL2 k (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lowPassProjectionL2_zero]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, lowPassProjectionL2_add, ih,
        Finset.sum_insert ha]

/-- The annularly projected piece at the `n`th scale of residue class `r`. -/
def annularResiduePiece (r : Fin 7)
    (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    Lp (α := ℝ) ℂ 2 volume :=
  annularProjectionL2 (residueScale r n) (v n)

theorem lowPassProjectionL2_annularResiduePiece_of_lt
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {m n : ℕ} (hmn : m < n) :
    lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) =
      annularResiduePiece r v m := by
  apply lowPassProjectionL2_annularProjectionL2_of_earlier
  simp only [residueScale]
  omega

theorem lowPassProjectionL2_annularResiduePiece_of_le
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {m n : ℕ} (hnm : n ≤ m) :
    lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) = 0 := by
  apply lowPassProjectionL2_annularProjectionL2_of_current_or_later
  simp only [residueScale]
  omega

/-- Exact prefix recovery in `L²`: the boundary low-pass projection of a
finite total is precisely the sum of the pieces before the boundary index. -/
theorem lowPassProjectionL2_finite_total_eq_prefix
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {n N : ℕ} (hnN : n ≤ N) :
    lowPassProjectionL2 (residueScale r n)
        (∑ m ∈ Finset.range N, annularResiduePiece r v m) =
      ∑ m ∈ Finset.range n, annularResiduePiece r v m := by
  classical
  rw [lowPassProjectionL2_finset_sum]
  calc
    ∑ m ∈ Finset.range N,
        lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) =
        ∑ m ∈ Finset.range N,
          if m < n then annularResiduePiece r v m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmn : m < n
      · rw [if_pos hmn, lowPassProjectionL2_annularResiduePiece_of_lt r v hmn]
      · rw [if_neg hmn,
          lowPassProjectionL2_annularResiduePiece_of_le r v (Nat.le_of_not_gt hmn)]
    _ = ∑ m ∈ Finset.range n, annularResiduePiece r v m := by
      rw [← Finset.sum_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      omega

/-! ## The inverse-Fourier kernel and its maximal majorant -/

def lowPassFrequencyCutoff (ξ : ℝ) : ℂ := (dyadicCutoff ξ : ℂ)

theorem contDiff_lowPassFrequencyCutoff :
    ContDiff ℝ ∞ lowPassFrequencyCutoff := by
  exact Complex.ofRealCLM.contDiff.comp dyadicCutoff_smooth

theorem hasCompactSupport_lowPassFrequencyCutoff :
    HasCompactSupport lowPassFrequencyCutoff := by
  exact dyadicCutoffData.hasCompactSupport.comp_left rfl

def lowPassFrequencySchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_lowPassFrequencyCutoff.toSchwartzMap
    contDiff_lowPassFrequencyCutoff

@[simp] theorem lowPassFrequencySchwartz_apply (ξ : ℝ) :
    lowPassFrequencySchwartz ξ = lowPassFrequencyCutoff ξ := rfl

/-- The fixed physical-space kernel whose Fourier transform is the base
low-pass cutoff. -/
def baseLowPassKernelSchwartz : 𝓢(ℝ, ℂ) :=
  𝓕⁻ lowPassFrequencySchwartz

/-- A concrete uniform quadratic-decay constant for the base Schwartz
kernel. -/
def baseLowPassKernelDecayConstant : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 baseLowPassKernelSchwartz +
    SchwartzMap.seminorm ℂ 2 0 baseLowPassKernelSchwartz

theorem baseLowPassKernelDecayConstant_nonneg :
    0 ≤ baseLowPassKernelDecayConstant := by
  unfold baseLowPassKernelDecayConstant
  positivity

theorem norm_baseLowPassKernelSchwartz_le (x : ℝ) :
    ‖baseLowPassKernelSchwartz x‖ ≤
      baseLowPassKernelDecayConstant / (1 + x ^ 2) := by
  have h0 := SchwartzMap.norm_le_seminorm ℂ baseLowPassKernelSchwartz x
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ
    baseLowPassKernelSchwartz 2 x
  have hden : 0 < 1 + x ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  calc
    ‖baseLowPassKernelSchwartz x‖ * (1 + x ^ 2) =
        ‖baseLowPassKernelSchwartz x‖ +
          ‖x‖ ^ 2 * ‖baseLowPassKernelSchwartz x‖ := by
      rw [Real.norm_eq_abs, sq_abs]
      ring
    _ ≤ SchwartzMap.seminorm ℂ 0 0 baseLowPassKernelSchwartz +
        SchwartzMap.seminorm ℂ 2 0 baseLowPassKernelSchwartz :=
      add_le_add h0 h2
    _ = baseLowPassKernelDecayConstant := rfl

/-- The correctly normalized physical kernel at frequency radius
`R = 2^(k-3)`. -/
def scaledLowPassKernel (k : ℤ) (t : ℝ) : ℂ :=
  (((2 : ℝ) ^ (k - 3) : ℝ) : ℂ) *
    baseLowPassKernelSchwartz ((2 : ℝ) ^ (k - 3) * t)

theorem measurable_scaledLowPassKernel (k : ℤ) :
    Measurable (scaledLowPassKernel k) := by
  exact (baseLowPassKernelSchwartz.continuous.comp
    (continuous_const.mul continuous_id)).measurable.const_mul _

theorem fourier_scaledLowPassKernel (k : ℤ) (ξ : ℝ) :
    𝓕 (scaledLowPassKernel k) ξ = scaledLowPassCutoff k ξ := by
  let R : ℝ := (2 : ℝ) ^ (k - 3)
  have hR : 0 < R := by dsimp [R]; positivity
  let g : ℝ → ℂ := fun u ↦
    Complex.exp (((-2 * Real.pi * u * (ξ / R) : ℝ) : ℂ) * Complex.I) •
      baseLowPassKernelSchwartz u
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ ↦
      Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) •
        scaledLowPassKernel k t) =
      fun t ↦ (R : ℂ) * g (R * t) := by
    funext t
    unfold scaledLowPassKernel g
    simp only [R, smul_eq_mul]
    have hphase :
        (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) =
          (((-2 * Real.pi * ((2 : ℝ) ^ (k - 3) * t) *
            (ξ / (2 : ℝ) ^ (k - 3)) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      norm_cast
      field_simp
    rw [hphase]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hR)]
  rw [Complex.real_smul]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne']
  norm_num
  have hg : (∫ y : ℝ, g y) =
      𝓕 (baseLowPassKernelSchwartz : ℝ → ℂ) (ξ / R) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
  rw [hg]
  rw [← SchwartzMap.fourier_coe]
  have hinv : 𝓕 baseLowPassKernelSchwartz = lowPassFrequencySchwartz := by
    exact fourier_fourierInv_eq lowPassFrequencySchwartz
  rw [hinv]
  rfl

theorem norm_scaledLowPassKernel_le_poisson (k : ℤ) (t : ℝ) :
    ‖scaledLowPassKernel k t‖ ≤
      baseLowPassKernelDecayConstant *
        cotlarPoissonKernel ((2 : ℝ) ^ (-(k - 3))) t := by
  let R : ℝ := (2 : ℝ) ^ (k - 3)
  have hR : 0 < R := by dsimp [R]; positivity
  have hC := baseLowPassKernelDecayConstant_nonneg
  calc
    ‖scaledLowPassKernel k t‖ =
        R * ‖baseLowPassKernelSchwartz (R * t)‖ := by
      simp only [scaledLowPassKernel, R, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ R * (baseLowPassKernelDecayConstant / (1 + (R * t) ^ 2)) :=
      mul_le_mul_of_nonneg_left (norm_baseLowPassKernelSchwartz_le _) hR.le
    _ = baseLowPassKernelDecayConstant * cotlarPoissonKernel R⁻¹ t := by
      unfold cotlarPoissonKernel
      field_simp
      <;> ring
    _ = baseLowPassKernelDecayConstant *
        cotlarPoissonKernel ((2 : ℝ) ^ (-(k - 3))) t := by
      rw [show R⁻¹ = (2 : ℝ) ^ (-(k - 3)) by
        simp only [R, zpow_neg]]

theorem integrable_scaledLowPassKernel (k : ℤ) :
    Integrable (scaledLowPassKernel k) volume := by
  let r : ℝ := (2 : ℝ) ^ (-(k - 3))
  have hr : 0 < r := by dsimp [r]; positivity
  have hdom : Integrable
      (fun t ↦ baseLowPassKernelDecayConstant * cotlarPoissonKernel r t) volume :=
    (HilbertPoissonFourier.integrable_cotlarPoissonKernel hr).const_mul _
  apply Integrable.mono' hdom
    (measurable_scaledLowPassKernel k).aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg baseLowPassKernelDecayConstant_nonneg,
    abs_of_nonneg (cotlarPoissonKernel_nonneg hr.le)] using
      (show ‖scaledLowPassKernel k t‖ ≤
        baseLowPassKernelDecayConstant * cotlarPoissonKernel r t by
          simpa only [r] using norm_scaledLowPassKernel_le_poisson k t)

/-- The inverse-Fourier low-pass kernels, uniformly over every integer
scale, are pointwise dominated by the centered Hardy--Littlewood maximal
operator.  The proof uses the already formalized dyadic-shell majorization
of the Poisson kernel. -/
theorem enorm_scaledLowPassKernel_convolution_le_maximal
    (k : ℤ) {f : ℝ → ℂ} (hf : Measurable f) (x : ℝ) :
    ‖∫ y, scaledLowPassKernel k (x - y) * f y‖ₑ ≤
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let r : ℝ := (2 : ℝ) ^ (-(k - 3))
  have hr : 0 < r := by dsimp [r]; positivity
  have hC := baseLowPassKernelDecayConstant_nonneg
  calc
    ‖∫ y, scaledLowPassKernel k (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖scaledLowPassKernel k (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, (ENNReal.ofReal baseLowPassKernelDecayConstant *
          ENNReal.ofReal (cotlarPoissonKernel r (x - y))) * ‖f y‖ₑ := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [enorm_mul]
      apply mul_le_mul'
      · rw [← ofReal_norm]
        calc
          ENNReal.ofReal ‖scaledLowPassKernel k (x - y)‖ ≤
              ENNReal.ofReal (baseLowPassKernelDecayConstant *
                cotlarPoissonKernel r (x - y)) :=
            ENNReal.ofReal_le_ofReal (by
              simpa only [r] using norm_scaledLowPassKernel_le_poisson k (x - y))
          _ = ENNReal.ofReal baseLowPassKernelDecayConstant *
              ENNReal.ofReal (cotlarPoissonKernel r (x - y)) := by
            rw [ENNReal.ofReal_mul hC]
      · exact le_rfl
    _ = ENNReal.ofReal baseLowPassKernelDecayConstant *
        (∫⁻ y, ENNReal.ofReal (cotlarPoissonKernel r (x - y)) * ‖f y‖ₑ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      ac_rfl
    _ ≤ ENNReal.ofReal baseLowPassKernelDecayConstant *
        (20 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) := by
      apply mul_le_mul' le_rfl
      exact lintegral_ofReal_cotlarPoissonKernel_mul_le_maximal hr hf.enorm x
    _ = (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by ring

def lowPassKernelConvolution (k : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, scaledLowPassKernel k (x - y) * f y

theorem lowPassKernelConvolution_eq_convolution
    (k : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    lowPassKernelConvolution k f x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledLowPassKernel k) x := by
  rw [lowPassKernelConvolution, MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.mul_apply']
  ring

theorem integrable_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) :
    Integrable (lowPassKernelConvolution k f) volume := by
  have hconv := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_scaledLowPassKernel k)
  apply hconv.congr
  filter_upwards with x
  exact (lowPassKernelConvolution_eq_convolution k f x).symm

/-- The centered maximal function of the norm of an `L²` function is itself
an `L²` ENNReal-valued function.  This packages the already proved strong
`L²` maximal inequality for use in convolution estimates. -/
theorem memLp_two_centeredHardyLittlewoodMaximal_enorm
    {f : ℝ → ℂ} (hfmeas : Measurable f) (hf₂ : MemLp f 2 volume) :
    MemLp (centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ)) 2 volume := by
  let M : ℝ → ℝ≥0∞ :=
    centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ)
  have hm := (measurable_centeredHardyLittlewoodMaximal hfmeas.enorm)
  have hinput : (∫⁻ x, ‖f x‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    rw [← eLpNorm_two_sq_lintegral _ hf₂.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hf₂.eLpNorm_lt_top
  have hM : (∫⁻ x, M x ^ 2) < (⊤ : ℝ≥0∞) :=
    (centeredHardyLittlewoodMaximal_sq_lintegral_le hfmeas.enorm).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hinput)
  have hp : eLpNorm M 2 volume ^ 2 < (⊤ : ℝ≥0∞) := by
    rw [eLpNorm_two_sq_lintegral M hm.aestronglyMeasurable]
    simpa only [enorm_eq_self] using hM
  exact (ENNReal.pow_lt_top_iff.mp hp).resolve_right (by norm_num)

theorem memLp_two_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hfmeas : Measurable f)
    (hf : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    MemLp (lowPassKernelConvolution k f) 2 volume := by
  let A : ℝ≥0∞ := 20 * ENNReal.ofReal baseLowPassKernelDecayConstant
  have hAtop : A ≠ (⊤ : ℝ≥0∞) := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  apply (memLp_two_centeredHardyLittlewoodMaximal_enorm hfmeas hf₂).of_enorm_le_mul
    (c := A.toNNReal)
    (integrable_lowPassKernelConvolution k hf).aestronglyMeasurable
  filter_upwards with x
  rw [ENNReal.coe_toNNReal hAtop]
  change ‖lowPassKernelConvolution k f x‖ₑ ≤
    A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x
  exact enorm_scaledLowPassKernel_convolution_le_maximal k hfmeas x

theorem fourier_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    𝓕 (lowPassKernelConvolution k f) ξ =
      scaledLowPassCutoff k ξ * 𝓕 f ξ := by
  rw [show lowPassKernelConvolution k f =
      f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledLowPassKernel k by
    funext x
    exact lowPassKernelConvolution_eq_convolution k f x]
  rw [Real.fourier_mul_convolution_eq hf
      (integrable_scaledLowPassKernel k) ξ,
    fourier_scaledLowPassKernel]
  ring

/-- For an `L¹ ∩ L²` representative, the concrete kernel convolution is
exactly the canonical `L²` low-pass Fourier multiplier.  Both sides are
compared by their canonical `L²` Fourier transforms; the bridge from the
integral Fourier transform is almost-everywhere, as it should be. -/
theorem lowPassProjectionL2_eq_toLp_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hfmeas : Measurable f)
    (hf : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    lowPassProjectionL2 k (hf₂.toLp f) =
      (memLp_two_lowPassKernelConvolution k hfmeas hf hf₂).toLp
        (lowPassKernelConvolution k f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (hf₂.toLp f)).coeFn_toLp,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq
      (integrable_lowPassKernelConvolution k hf)
      (memLp_two_lowPassKernelConvolution k hfmeas hf hf₂),
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hf hf₂]
      with ξ hlow hconv hfourier
  rw [show (lowPassMultiplierL2 k (hf₂.toLp f) : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k (hf₂.toLp f) ξ by
        simpa only [lowPassMultiplierL2] using hlow]
  rw [hconv, fourier_lowPassKernelConvolution k hf ξ]
  unfold lowPassFourierMultiplier
  rw [hfourier]

/-- Canonical measurable representative of the `n`th annular piece in one
of the seven separated residue classes. -/
def annularResidueRepresentative (r : Fin 7)
    (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) : ℝ → ℂ :=
  annularResiduePiece r v n

theorem measurable_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    Measurable (annularResidueRepresentative r v n) :=
  (Lp.stronglyMeasurable (annularResiduePiece r v n)).measurable

theorem memLp_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    MemLp (annularResidueRepresentative r v n) 2 volume :=
  Lp.memLp (annularResiduePiece r v n)

/-- For a finite total of annular pieces which is also integrable, every
prefix is almost everywhere convolution by the concrete boundary low-pass
kernel.  This closes the representative-level bridge without imposing any
pointwise choice on `L²` equivalence classes. -/
theorem annularResiduePrefix_ae_eq_lowPassKernelConvolution
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) {n N : ℕ}
    (hnN : n ≤ N)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    KrauseLaceyQuadraticAnnularTail.finitePiecePrefix
        (annularResidueRepresentative r v) n =ᵐ[volume]
      lowPassKernelConvolution (residueScale r n)
        (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
          (annularResidueRepresentative r v)) := by
  let u : ℕ → ℝ → ℂ := annularResidueRepresentative r v
  have hu₂ : ∀ j, MemLp (u j) 2 volume :=
    fun j ↦ memLp_annularResidueRepresentative r v j
  have htotalMeas : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) :=
    KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
      (fun j _ ↦ measurable_annularResidueRepresentative r v j)
  have htotal₂ : MemLp
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) 2 volume :=
    KrauseLaceyQuadraticAnnularTail.memLp_finitePieceTotal hu₂
  have htotalLp :
      htotal₂.toLp
          (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) =
        ∑ m ∈ Finset.range N, annularResiduePiece r v m := by
    simpa only [u, annularResidueRepresentative, Lp.toLp_coeFn] using
      (KrauseLaceyQuadraticAnnularTail.toLp_finitePieceTotal_eq_sum hu₂)
  have hprojection :
      lowPassProjectionL2 (residueScale r n)
          (∑ m ∈ Finset.range N, annularResiduePiece r v m) =
        (memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u)) := by
    rw [← htotalLp]
    exact lowPassProjectionL2_eq_toLp_lowPassKernelConvolution
      (residueScale r n) htotalMeas htotalInt htotal₂
  have hLp :
      (∑ m ∈ Finset.range n, annularResiduePiece r v m) =
        (memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u)) := by
    rw [← lowPassProjectionL2_finite_total_eq_prefix r v hnN]
    exact hprojection
  have hprefixCoe := Lp.coeFn_finsetSum (Finset.range n)
    (fun m ↦ annularResiduePiece r v m)
  have hLpCoe :
      (⇑(∑ m ∈ Finset.range n, annularResiduePiece r v m) : ℝ → ℂ) =ᵐ[volume]
        ⇑((memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u))) := by
    rw [hLp]
  have hconvCoe :=
    (memLp_two_lowPassKernelConvolution (residueScale r n)
      htotalMeas htotalInt htotal₂).coeFn_toLp
  filter_upwards [hprefixCoe, hLpCoe, hconvCoe] with x hprefix hEq hconv
  unfold KrauseLaceyQuadraticAnnularTail.finitePiecePrefix
  calc
    ∑ j ∈ Finset.range n, annularResidueRepresentative r v j x =
        (∑ j ∈ Finset.range n, annularResiduePiece r v j) x := by
      simpa only [annularResidueRepresentative, Finset.sum_apply] using hprefix.symm
    _ = _ := hEq.trans hconv

/-- Fully instantiated a.e. low-pass prefix control for one separated
residue class.  The only application hypothesis is integrability of the
finite total; its `L²` membership is automatic. -/
theorem hasAELowPassPrefixControl_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (N : ℕ)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    KrauseLaceyQuadraticAnnularTail.HasAELowPassPrefixControl N
      (annularResidueRepresentative r v)
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn
  have htotalMeas : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) :=
    KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
      (fun j _ ↦ measurable_annularResidueRepresentative r v j)
  filter_upwards [annularResiduePrefix_ae_eq_lowPassKernelConvolution
    r v hn htotalInt] with x hx
  rw [hx]
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (residueScale r n) htotalMeas x

/-- Concrete cardinality-free maximal-tail `L²` estimate for one residue
class of annular projections.  Frequency separation, exact low-pass prefix
recovery, the inverse-Fourier convolution identity, and Hardy--Littlewood
control have all been instantiated. -/
theorem annularResidueTailMax_sq_lintegral_le_sum
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (N : ℕ)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    (∫⁻ x, KrauseLaceyQuadraticAnnularTail.finitePieceTailMax N
      (annularResidueRepresentative r v) x ^ 2) ≤
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ∑ j ∈ Finset.range N,
          ∫⁻ x, ‖annularResidueRepresentative r v j x‖ₑ ^ 2 := by
  apply KrauseLaceyQuadraticAnnularTail.finitePieceTailMax_sq_lintegral_le_sum_ae
    (fun j ↦ measurable_annularResidueRepresentative r v j)
    (fun j ↦ memLp_annularResidueRepresentative r v j)
  · simpa only [annularResidueRepresentative, Lp.toLp_coeFn,
      annularResiduePiece] using
      (hasPairwiseSeparatedFourierSupport_annularProjection_residueScale r v)
  · exact hasAELowPassPrefixControl_annularResidueRepresentative
      r v N htotalInt

/-- Once a pointwise prefix is identified with convolution by the concrete
scaled inverse-Fourier kernel, all analytic hypotheses of
`HasLowPassPrefixControl` are discharged.  In particular, no compact-support
fiction is imposed on the Schwartz kernel: the preceding dyadic-shell
argument supplies the uniform constant. -/
theorem hasLowPassPrefixControl_of_scaledLowPassKernel_representation
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ j, Measurable (u j))
    (boundaryScale : ℕ → ℤ)
    (hprefix : ∀ n ≤ N, ∀ x,
      KrauseLaceyQuadraticAnnularTail.finitePiecePrefix u n x =
        ∫ y, scaledLowPassKernel (boundaryScale n) (x - y) *
          KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u y) :
    KrauseLaceyQuadraticAnnularTail.HasLowPassPrefixControl N u
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn x
  rw [hprefix n hn x]
  have htotal : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) := by
    apply KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
    exact fun j _ ↦ hu j
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (boundaryScale n) htotal x

/-- The a.e. representative version of the concrete low-pass adapter.
This is the natural output of `L²` Fourier multiplier identities and is
already sufficient for the maximal-tail `lintegral` theorem. -/
theorem hasAELowPassPrefixControl_of_scaledLowPassKernel_representation
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ j, Measurable (u j))
    (boundaryScale : ℕ → ℤ)
    (hprefix : ∀ n ≤ N,
      KrauseLaceyQuadraticAnnularTail.finitePiecePrefix u n =ᵐ[volume]
        fun x ↦ ∫ y, scaledLowPassKernel (boundaryScale n) (x - y) *
          KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u y) :
    KrauseLaceyQuadraticAnnularTail.HasAELowPassPrefixControl N u
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn
  have htotal : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) := by
    apply KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
    exact fun j _ ↦ hu j
  filter_upwards [hprefix n hn] with x hx
  rw [hx]
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (boundaryScale n) htotal x


end
end QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection
