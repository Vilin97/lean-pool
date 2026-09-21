/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveDyadicKernel

/-!
# Infinite telescoping of the positive-proof dyadic kernel

For a fixed nonzero spatial point, only finitely many of the dyadic pieces
`ψ_{j+r}` with `r ≥ 0` are nonzero. Their infinite sum therefore telescopes
exactly to the high-pass kernel used in the paper's oscillatory reduction.
-/

open Filter Function Set
open scoped Topology BigOperators

namespace QuadraticCarleson


/-- The shrinking dyadic argument in the telescoping numerator tends to
zero. -/
theorem tendsto_dyadicCutoffArgument_add_nat_zero (j : ℤ) (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦ (2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : Tendsto (fun _ : ℕ ↦ (2⁻¹ : ℝ) ^ (j - 1)) atTop
      (𝓝 ((2⁻¹ : ℝ) ^ (j - 1))) := tendsto_const_nhds
  have h := (hc.mul hp).mul_const t
  convert h using 1
  · funext n
    rw [show j + (n : ℤ) - 1 = (j - 1) + (n : ℤ) by ring,
      zpow_add₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0), zpow_natCast]
    norm_num
  · simp

/-- At every nonzero point the positive-height dyadic kernel sequence has
finite support. -/
theorem hasFiniteSupport_dyadicPsi_add_nat (j : ℤ) (t : ℝ) :
    HasFiniteSupport (fun r : ℕ ↦ dyadicPsi (j + (r : ℤ)) t) := by
  have hp : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc : 0 < (2 : ℝ) ^ (j - 3) := zpow_pos (by norm_num) _
  have hscale : Tendsto
      (fun n : ℕ ↦ (2 : ℝ) ^ (j + (n : ℤ) - 3)) atTop atTop := by
    convert hp.const_mul_atTop hc using 1
    funext n
    rw [show j + (n : ℤ) - 3 = (j - 3) + (n : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  have hz : ∀ᶠ n : ℕ in atTop,
      dyadicPsi (j + (n : ℤ)) t = 0 := by
    filter_upwards [hscale.eventually_gt_atTop |t|] with n hn
    exact dyadicPsi_eq_zero_of_abs_le hn.le
  have hzcofinite : {n : ℕ | dyadicPsi (j + (n : ℤ)) t = 0} ∈ cofinite := by
    rw [Nat.cofinite_eq_atTop]
    exact hz
  rw [mem_cofinite] at hzcofinite
  simpa only [HasFiniteSupport, support, ne_eq,
    compl_ofPred] using hzcofinite

theorem summable_dyadicPsi_add_nat (j : ℤ) (t : ℝ) :
    Summable (fun r : ℕ ↦ dyadicPsi (j + (r : ℤ)) t) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_dyadicPsi_add_nat j t)

/-- The infinite positive-height dyadic sum is the exact high-pass part of
`1/t`. -/
theorem hasSum_dyadicPsi_add_nat (j : ℤ) {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun r : ℕ ↦ dyadicPsi (j + (r : ℤ)) t)
      ((1 - dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)) / t) := by
  apply ((summable_dyadicPsi_add_nat j t).hasSum_iff_tendsto_nat).2
  have hcut : Tendsto
      (fun n : ℕ ↦ dyadicCutoff
        ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t))
      atTop (𝓝 1) := by
    have h := dyadicCutoff_smooth.continuous.continuousAt.tendsto.comp
      (tendsto_dyadicCutoffArgument_add_nat_zero j t)
    change Tendsto
      (fun n : ℕ ↦ dyadicCutoff
        ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t))
      atTop (𝓝 (dyadicCutoff 0)) at h
    rw [dyadicCutoff_eq_one (x := (0 : ℝ)) (by norm_num)] at h
    exact h
  have hc : Tendsto
      (fun _ : ℕ ↦ dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)) atTop
      (𝓝 (dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t))) := tendsto_const_nhds
  have hquot := (hcut.sub hc).div_const t
  convert hquot using 1
  · funext n
    rw [sum_dyadicPsi_consecutive j n ht]

theorem tsum_dyadicPsi_add_nat (j : ℤ) {t : ℝ} (ht : t ≠ 0) :
    (∑' r : ℕ, dyadicPsi (j + (r : ℤ)) t) =
      (1 - dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)) / t :=
  (hasSum_dyadicPsi_add_nat j ht).tsum_eq

/-- Specialization to the paper's selected oscillatory scales. -/
theorem hasSum_dyadicPsi_oscillatoryScaleIndex
    (lam : ℝ) (hlam : lam ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun r : ℕ ↦ dyadicPsi (oscillatoryScaleIndex lam r hlam) t)
      ((1 - dyadicCutoff
        ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)) / t) := by
  apply (hasSum_dyadicPsi_add_nat (oscillatoryScaleIndex lam 0 hlam) ht).congr_fun
  intro r
  rw [oscillatoryScaleIndex_eq_add]

/-- The exact high-pass oscillatory kernel obtained after summing all
nonnegative oscillation heights. -/
noncomputable def paperOscillatoryKernel
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) : ℂ :=
  (((1 - dyadicCutoff
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2)

/-- The complementary low-pass kernel omitted by the nonnegative
oscillation heights. -/
noncomputable def paperNonoscillatoryKernel
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) : ℂ :=
  ((dyadicCutoff
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2)

/-- Exact pointwise decomposition of the quadratically modulated Hilbert
kernel into its complementary low-pass and oscillatory pieces. -/
theorem paperNonoscillatoryKernel_add_paperOscillatoryKernel
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    paperNonoscillatoryKernel lam hlam t +
        paperOscillatoryKernel lam hlam t =
      phase (lam * t ^ 2) / (t : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp [paperNonoscillatoryKernel, paperOscillatoryKernel]
  · unfold paperNonoscillatoryKernel paperOscillatoryKernel
    push_cast
    field_simp
    ring

/-- The paper's complex-valued height kernels telescope pointwise to the
high-pass oscillatory kernel. At `t = 0` both sides use their canonical zero
extension. -/
theorem hasSum_selectedDyadicQuadraticKernel
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasSum
      (fun r : ℕ ↦
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) *
          phase (lam * t ^ 2))
      (paperOscillatoryKernel lam hlam t) := by
  by_cases ht : t = 0
  · subst t
    have hz : (fun r : ℕ ↦
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) 0 : ℂ) *
          phase (lam * 0 ^ 2)) = 0 := by
      funext r
      simp [dyadicPsi_zero]
    rw [hz]
    have hkernel : paperOscillatoryKernel lam hlam 0 = 0 := by
      simp [paperOscillatoryKernel,
        dyadicCutoff_eq_one (x := (0 : ℝ)) (by norm_num)]
    rw [hkernel]
    exact (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)
  · have hr := hasSum_dyadicPsi_oscillatoryScaleIndex lam hlam ht
    have hc : HasSum
        (fun r : ℕ ↦ (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ))
        (((1 - dyadicCutoff
          ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)) / t : ℝ) : ℂ) :=
      Complex.hasSum_ofReal.mpr hr
    simpa only [paperOscillatoryKernel] using
      hc.mul_right (phase (lam * t ^ 2))

theorem tsum_selectedDyadicQuadraticKernel
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    (∑' r : ℕ,
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) *
        phase (lam * t ^ 2)) = paperOscillatoryKernel lam hlam t :=
  (hasSum_selectedDyadicQuadraticKernel lam hlam t).tsum_eq

/-- Equivalent form saying that the height series is the full quadratic
Hilbert kernel minus the complementary low-pass kernel. -/
theorem hasSum_selectedDyadicQuadraticKernel_eq_full_sub_low
    (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasSum
      (fun r : ℕ ↦
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) *
          phase (lam * t ^ 2))
      (phase (lam * t ^ 2) / (t : ℂ) -
        paperNonoscillatoryKernel lam hlam t) := by
  convert hasSum_selectedDyadicQuadraticKernel lam hlam t using 1
  apply sub_eq_iff_eq_add.mpr
  calc
    phase (lam * t ^ 2) / (t : ℂ) =
        paperNonoscillatoryKernel lam hlam t +
          paperOscillatoryKernel lam hlam t :=
      (paperNonoscillatoryKernel_add_paperOscillatoryKernel lam hlam t).symm
    _ = paperOscillatoryKernel lam hlam t +
        paperNonoscillatoryKernel lam hlam t := add_comm _ _

end QuadraticCarleson
