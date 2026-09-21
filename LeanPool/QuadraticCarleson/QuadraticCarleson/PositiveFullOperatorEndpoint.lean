/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FullNegativeEndpoint
import LeanPool.QuadraticCarleson.QuadraticCarleson.ExtendedWeakL1Combinators
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseInterface
import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveFullOscillatoryScaling

/-!
# Passage from the oscillatory estimate to the full quadratic operator

The canonical truncation limsup at each modulation is bounded by the genuine
maximal truncation.  Combining this at modulation zero with the established
oscillatory reduction gives a pointwise bound for the paper's full operator.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace PositiveFullOperatorEndpoint

open OscillatoryReduction
open PositiveFullOscillatoryEndpoint PositiveStoppingBadEstimate
open KaltonPaperApplication


/-- The canonical cofinal limsup is no larger than the supremum over every
positive truncation radius. -/
theorem quadraticHilbertL0Limsup_le_maximalTruncation
    (lam : ℝ) (f : L0Infinity) (x : ℝ) :
    quadraticHilbertL0Limsup lam f x ≤
      quadraticHilbertMaximalTruncation lam f x := by
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards with m
  change ENNReal.ofReal ‖quadraticHilbertTrunc lam (principalValueRadius m) f x‖ ≤ _
  unfold quadraticHilbertMaximalTruncation
  simpa only [ofReal_norm] using le_iSup
    (fun ε : {ε : ℝ // 0 < ε} ↦ ‖quadraticHilbertTrunc lam ε f x‖ₑ)
    ⟨principalValueRadius m, principalValueRadius_pos m⟩

/-- The full real-modulation principal-value limsup is pointwise controlled
by the proved oscillatory part, the ordinary Hilbert maximal truncation, and
the elementary Hardy--Littlewood error.  The zero modulation is included. -/
theorem quadraticCarlesonL0_le_oscillatory_add_hilbert_add_maximal
    (f : L0Infinity) (x : ℝ) :
    quadraticCarlesonL0 f x ≤
      paperOscillatoryMaximal f x +
        2 * quadraticHilbertMaximalTruncation 0 f x +
        maximalErrorConstant *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold quadraticCarlesonL0
  apply iSup_le
  intro lam
  by_cases hlam : lam = 0
  · subst lam
    have hzero := quadraticHilbertL0Limsup_le_maximalTruncation 0 f x
    apply hzero.trans
    calc
      quadraticHilbertMaximalTruncation 0 f x ≤
          2 * quadraticHilbertMaximalTruncation 0 f x := by
        simpa only [one_mul] using
          (mul_le_mul' (by norm_num : (1 : ENNReal) ≤ 2)
            (le_refl (quadraticHilbertMaximalTruncation 0 f x)))
      _ ≤ paperOscillatoryMaximal f x +
          2 * quadraticHilbertMaximalTruncation 0 f x :=
        le_add_left le_rfl
      _ ≤ paperOscillatoryMaximal f x +
          2 * quadraticHilbertMaximalTruncation 0 f x +
          maximalErrorConstant *
            centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
        le_add_right le_rfl
  · apply (quadraticHilbertL0Limsup_le_oscillatory lam hlam f x).trans
    gcongr
    exact le_iSup
      (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖paperOscillatoryAction μ.1 μ.2 f x‖ₑ)
      ⟨lam, hlam⟩

noncomputable def maximalErrorConstantReal : ℝ := 8 + 8 * Real.pi

theorem maximalErrorConstantReal_pos : 0 < maximalErrorConstantReal := by
  unfold maximalErrorConstantReal
  positivity

theorem ofReal_maximalErrorConstantReal :
    ENNReal.ofReal maximalErrorConstantReal = maximalErrorConstant := by
  unfold maximalErrorConstantReal maximalErrorConstant
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 8) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

theorem paperLog_one_two_mul_le_two_mul {t : ℝ} (ht : 0 ≤ t) :
    paperLog 1 (2 * t) ≤ 2 * paperLog 1 t := by
  simp only [paperLog_succ, paperLog_zero]
  have hleft : 0 < 10 + 2 * t := by linarith
  have hright : 0 < 10 + t := by linarith
  have hpoly : 10 + 2 * t ≤ (10 + t) ^ 2 := by nlinarith
  calc
    Real.log (10 + 2 * t) ≤ Real.log ((10 + t) ^ 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact hleft
      · exact sq_pos_of_pos hright
      · exact hpoly
    _ = 2 * Real.log (10 + t) := by rw [Real.log_pow]; norm_num

theorem scaled_half_fullOrlicz_lintegral_le
    (f : ℝ → ℂ) :
    (∫⁻ x, ENNReal.ofReal
      ((‖f x‖ / (1 / 2 : ℝ)) * paperLog 1 (‖f x‖ / (1 / 2 : ℝ)))) ≤
      4 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  calc
    _ ≤ ∫⁻ x, 4 * ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal
          ((‖f x‖ / (1 / 2 : ℝ)) * paperLog 1 (‖f x‖ / (1 / 2 : ℝ))) ≤
        4 * ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖)
      rw [show ‖f x‖ / (1 / 2 : ℝ) = 2 * ‖f x‖ by ring,
        show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      have hlog := paperLog_one_two_mul_le_two_mul (norm_nonneg (f x))
      have hlog0 : 0 ≤ paperLog 1 ‖f x‖ := by
        exact PositiveEndpointOptimization.paperLog_nonnegative 1 (norm_nonneg (f x))
      nlinarith [norm_nonneg (f x)]
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

/-- Threshold-one full-operator endpoint, reduced only to a uniform ordinary
Hilbert maximal weak constant.  This is the exact classical input proved in
`HilbertMaximalWeakOneOne`; it is not an assumption about the target operator. -/
theorem quadraticCarlesonL0_levelSet_one_le_orlicz_of_hilbertWeak
    (f : L0Infinity) {CH : ℝ} (hCH : 0 ≤ CH)
    (hH : HasExtendedWeakL1Bound volume
      (CH * (∫⁻ x, ‖f x‖ₑ).toReal)
      (quadraticHilbertMaximalTruncation 0 f)) :
    volume {x | 1 < quadraticCarlesonL0 f x} ≤
      (4 * fullOscillatoryEndpointConstant + 8 * ENNReal.ofReal CH +
        16 * ENNReal.ofReal maximalErrorConstantReal) *
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  let O := paperOscillatoryMaximal f
  let H := quadraticHilbertMaximalTruncation 0 f
  let M := centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ)
  let J := ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖)
  let D := maximalErrorConstantReal
  have hD : 0 < D := maximalErrorConstantReal_pos
  have hquarterD : ENNReal.ofReal D * ENNReal.ofReal (1 / (4 * D)) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    field_simp
  have htwoeight : (2 : ENNReal) * ENNReal.ofReal (1 / 8 : ℝ) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hthresholds : ENNReal.ofReal (1 / 2 : ℝ) +
      2 * ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
    rw [htwoeight, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hsub : {x | 1 < quadraticCarlesonL0 f x} ⊆
      {x | ENNReal.ofReal (1 / 2 : ℝ) < O x} ∪
        ({x | ENNReal.ofReal (1 / 8 : ℝ) < H x} ∪
          {x | ENNReal.ofReal (1 / (4 * D)) < M x}) := by
    intro x hx
    by_cases hO : ENNReal.ofReal (1 / 2 : ℝ) < O x
    · exact Or.inl hO
    apply Or.inr
    by_cases hHilb : ENNReal.ofReal (1 / 8 : ℝ) < H x
    · exact Or.inl hHilb
    apply Or.inr
    by_contra hMax
    have hp := quadraticCarlesonL0_le_oscillatory_add_hilbert_add_maximal f x
    have hbound : O x + 2 * H x + maximalErrorConstant * M x ≤ 1 := by
      rw [← ofReal_maximalErrorConstantReal]
      calc
        O x + 2 * H x + ENNReal.ofReal D * M x ≤
            ENNReal.ofReal (1 / 2 : ℝ) +
              2 * ENNReal.ofReal (1 / 8 : ℝ) +
              ENNReal.ofReal D * ENNReal.ofReal (1 / (4 * D)) := by
          gcongr
          · exact le_of_not_gt hO
          · exact le_of_not_gt hHilb
          · exact le_of_not_gt hMax
        _ = 1 := by rw [hquarterD]; exact hthresholds
    exact hx.not_ge (hp.trans hbound)
  have hOset : volume {x | ENNReal.ofReal (1 / 2 : ℝ) < O x} ≤
      (4 * fullOscillatoryEndpointConstant) * J := by
    have h := paperOscillatoryMaximal_levelSet_le_scaled_orlicz
      f.measurable_toFun f.integrable (by norm_num : (0 : ℝ) < 1 / 2)
    apply h.trans
    exact (mul_le_mul' le_rfl (scaled_half_fullOrlicz_lintegral_le f)).trans_eq
      (by ring)
  have hmass_ne : (∫⁻ x, ‖f x‖ₑ) ≠ ∞ := f.integrable.hasFiniteIntegral.ne
  have hHset : volume {x | ENNReal.ofReal (1 / 8 : ℝ) < H x} ≤
      8 * ENNReal.ofReal CH * (∫⁻ x, ‖f x‖ₑ) := by
    have h := hH.2 (1 / 8) (by norm_num)
    have height : (8 : ENNReal) * ENNReal.ofReal (1 / 8 : ℝ) = 1 := by
      rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    calc
      volume {x | ENNReal.ofReal (1 / 8 : ℝ) < H x} =
          8 * (ENNReal.ofReal (1 / 8 : ℝ) *
            volume {x | ENNReal.ofReal (1 / 8 : ℝ) < H x}) := by
        rw [← mul_assoc, height, one_mul]
      _ ≤ 8 * ENNReal.ofReal
          (CH * (∫⁻ x, ‖f x‖ₑ).toReal) := mul_le_mul' le_rfl h
      _ = 8 * ENNReal.ofReal CH * (∫⁻ x, ‖f x‖ₑ) := by
        rw [ENNReal.ofReal_mul hCH, ENNReal.ofReal_toReal hmass_ne]
        ring
  have hMweak := centeredHardyLittlewoodMaximal_weak_bound
    (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal (1 / (4 * D)))
  have hMset : volume {x | ENNReal.ofReal (1 / (4 * D)) < M x} ≤
      16 * ENNReal.ofReal D * (∫⁻ x, ‖f x‖ₑ) := by
    have hfourD : ENNReal.ofReal (4 * D) * ENNReal.ofReal (1 / (4 * D)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * D)]
      have hreal : (4 * D) * (1 / (4 * D)) = 1 := by field_simp
      rw [hreal]
      norm_num
    calc
      volume {x | ENNReal.ofReal (1 / (4 * D)) < M x} =
          ENNReal.ofReal (4 * D) *
            (ENNReal.ofReal (1 / (4 * D)) *
              volume {x | ENNReal.ofReal (1 / (4 * D)) < M x}) := by
        rw [← mul_assoc, hfourD, one_mul]
      _ ≤ ENNReal.ofReal (4 * D) * (4 * ∫⁻ x, ‖f x‖ₑ) :=
        mul_le_mul' le_rfl hMweak
      _ = 16 * ENNReal.ofReal D * (∫⁻ x, ‖f x‖ₑ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        ring
  calc
    volume {x | 1 < quadraticCarlesonL0 f x} ≤
        volume {x | ENNReal.ofReal (1 / 2 : ℝ) < O x} +
          (volume {x | ENNReal.ofReal (1 / 8 : ℝ) < H x} +
            volume {x | ENNReal.ofReal (1 / (4 * D)) < M x}) :=
      (measure_mono hsub).trans (measure_union_le _ _ |>.trans
        (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ (4 * fullOscillatoryEndpointConstant) * J +
        (8 * ENNReal.ofReal CH * (∫⁻ x, ‖f x‖ₑ) +
          16 * ENNReal.ofReal D * (∫⁻ x, ‖f x‖ₑ)) :=
      add_le_add hOset (add_le_add hHset hMset)
    _ ≤ (4 * fullOscillatoryEndpointConstant) * J +
        (8 * ENNReal.ofReal CH * J + 16 * ENNReal.ofReal D * J) := by
      exact add_le_add le_rfl (add_le_add
        (mul_le_mul' le_rfl (lintegral_norm_le_full_orlicz f))
        (mul_le_mul' le_rfl (lintegral_norm_le_full_orlicz f)))
    _ = _ := by ring

theorem quadraticHilbertL0TruncNorm_smul
    (lam : ℝ) (c : ℂ) (f : L0Infinity) (m : ℕ) (x : ℝ) :
    quadraticHilbertL0TruncNorm lam (L0Infinity.smul c f) m x =
      ‖c‖ₑ * quadraticHilbertL0TruncNorm lam f m x := by
  have hs := quadraticHilbertTrunc_smul lam (principalValueRadius_pos m) c f x
  change quadraticHilbertTrunc lam (principalValueRadius m) (L0Infinity.smul c f) x =
    c * quadraticHilbertTrunc lam (principalValueRadius m) f x at hs
  unfold quadraticHilbertL0TruncNorm
  rw [hs, norm_mul,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]

theorem quadraticHilbertL0Limsup_smul
    (lam : ℝ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    quadraticHilbertL0Limsup lam (L0Infinity.smul c f) x =
      ‖c‖ₑ * quadraticHilbertL0Limsup lam f x := by
  unfold quadraticHilbertL0Limsup
  simp_rw [quadraticHilbertL0TruncNorm_smul]
  exact ENNReal.limsup_const_mul_of_ne_top (by finiteness)

theorem quadraticCarlesonL0_smul
    (c : ℂ) (f : L0Infinity) (x : ℝ) :
    quadraticCarlesonL0 (L0Infinity.smul c f) x =
      ‖c‖ₑ * quadraticCarlesonL0 f x := by
  unfold quadraticCarlesonL0
  simp_rw [quadraticHilbertL0Limsup_smul]
  exact (ENNReal.mul_iSup _ _).symm

noncomputable def normalizedL0Input (α : ℝ) (f : L0Infinity) : L0Infinity :=
  L0Infinity.smul (α : ℂ)⁻¹ f

@[simp] theorem normalizedL0Input_apply (α : ℝ) (f : L0Infinity) (x : ℝ) :
    normalizedL0Input α f x = normalizedOscillatoryInput α f x := rfl

theorem norm_normalizedL0Input {α : ℝ} (hα : 0 < α)
    (f : L0Infinity) (x : ℝ) :
    ‖normalizedL0Input α f x‖ = ‖f x‖ / α :=
  norm_normalizedOscillatoryInput hα f x

theorem quadraticCarlesonL0_normalizedInput
    {α : ℝ} (hα : 0 < α) (f : L0Infinity) (x : ℝ) :
    quadraticCarlesonL0 (normalizedL0Input α f) x =
      quadraticCarlesonL0 f x / ENNReal.ofReal α := by
  unfold normalizedL0Input
  rw [quadraticCarlesonL0_smul]
  have hc : ‖(α : ℂ)⁻¹‖ₑ = (ENNReal.ofReal α)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
      ENNReal.ofReal_inv_of_pos hα]
  rw [hc, div_eq_mul_inv, mul_comm]

theorem quadraticCarlesonL0_levelSet_eq_normalized
    {α : ℝ} (hα : 0 < α) (f : L0Infinity) :
    {x | ENNReal.ofReal α < quadraticCarlesonL0 f x} =
      {x | 1 < quadraticCarlesonL0 (normalizedL0Input α f) x} := by
  ext x
  change ENNReal.ofReal α < quadraticCarlesonL0 f x ↔
    1 < quadraticCarlesonL0 (normalizedL0Input α f) x
  rw [quadraticCarlesonL0_normalizedInput hα]
  simpa only [one_mul] using (ENNReal.lt_div_iff_mul_lt
    (a := quadraticCarlesonL0 f x) (b := ENNReal.ofReal α) (c := 1)
    (Or.inl (ENNReal.ofReal_pos.mpr hα).ne') (Or.inl ENNReal.ofReal_ne_top)).symm

/-- Uniform form of exactly the classical ordinary Hilbert maximal theorem.
It is separated so the eventual Cotlar proof can discharge it once and all
positive endpoint statements can consume it without restating assumptions. -/
def HasUniformZeroHilbertMaximalWeakBound (CH : ℝ) : Prop :=
  0 ≤ CH ∧ ∀ (g : ℝ → ℂ), Measurable g → Integrable g →
    HasExtendedWeakL1Bound volume
      (CH * (∫⁻ x, ‖g x‖ₑ).toReal)
      (quadraticHilbertMaximalTruncation 0 g)

/-- The paper's arbitrary-threshold full `L log₁ L` estimate, conditional
only on the exact uniform ordinary Hilbert maximal theorem. -/
theorem quadraticCarlesonL0_levelSet_le_scaled_orlicz_of_hilbertWeak
    {CH : ℝ} (hH : HasUniformZeroHilbertMaximalWeakBound CH)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < quadraticCarlesonL0 f x} ≤
      (4 * fullOscillatoryEndpointConstant + 8 * ENNReal.ofReal CH +
        16 * ENNReal.ofReal maximalErrorConstantReal) *
      ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  let g := normalizedL0Input α f
  have hgmeas : Measurable (g : ℝ → ℂ) := g.measurable_toFun
  have hgint : Integrable (g : ℝ → ℂ) := g.integrable
  have h := quadraticCarlesonL0_levelSet_one_le_orlicz_of_hilbertWeak
    g hH.1 (hH.2 g hgmeas hgint)
  rw [← quadraticCarlesonL0_levelSet_eq_normalized hα f] at h
  have hnorm (x : ℝ) : ‖g x‖ = ‖f x‖ / α := by
    exact norm_normalizedL0Input hα f x
  simpa only [hnorm] using h


end PositiveFullOperatorEndpoint
end QuadraticCarleson
