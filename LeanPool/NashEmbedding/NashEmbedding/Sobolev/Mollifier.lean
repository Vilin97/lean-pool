/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.RiemannSum
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.IntegrationByParts

/-!
# Mollifier existence, rescale technicalities, and Bridge Lemma 1

Smooth compactly supported infrastructure on ℝⁿ:

## Main contents

* `mollifier_exists` — there exists `ψ ∈ C^∞_c(ℝⁿ; ℝ)` with
  `ψ ≥ 0`, `∫ ψ = 1`, and `supp(ψ) ⊂ (-π, π)ⁿ`.
* `rescale_hasCompactSupport`, `rescale_contDiff`,
  `rescale_support_in_cube` — `rescale n φ ε` preserves compact
  support, smoothness, and the cube-support condition.
* `ftRn_at_zero` — `ftRn n φ 0 = ∫ φ`.
* `cinfty_rapidDecay` (Bridge Lemma 1) — for `φ ∈ C^∞_c(ℝⁿ; ℂ)`,
  `FTRapidDecay n φ` holds.
* `convDistrib_memSobolevDistrib` — `convDistrib n φ u ∈ H^s_*` whenever
  `φ` is integrable and `u ∈ H^s_*`.
-/

open scoped BigOperators ContDiff
open Complex Real MeasureTheory

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Mollifier existence -/

/-
There exists `ψ ∈ C^∞_c(ℝⁿ; ℝ)` with `ψ ≥ 0`, `∫ ψ = 1`, and
    `supp(ψ) ⊂ (-π, π)ⁿ`.
-/
lemma mollifier_exists (hn : 0 < n) :
    ∃ ψ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ∞ ψ ∧
      HasCompactSupport ψ ∧
      Integrable ψ ∧
      (∀ x, 0 ≤ ψ x) ∧
      (∀ x, ψ x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi) ∧
      ∫ x, ψ x = 1 := by
  -- Let's choose the bump function $b$ from the provided solution.
  obtain ⟨b, hb⟩ : ∃ b : ((Fin n) → ℝ) → ℝ,
    (ContDiff ℝ ∞ b) ∧
    HasCompactSupport b ∧
    (∀ x, 0 ≤ b x) ∧
    (∫ x, b x) > 0 ∧
    (∀ x, b x ≠ 0 → (∀ j, |x j| < Real.pi)) := by
      -- Use `ContDiffBump` to construct a smooth bump function on ℝⁿ.
      obtain ⟨b, hb⟩ : ∃ b : ContDiffBump (0 : (Fin n) → ℝ), b.rOut < Real.pi := by
        refine' ⟨ _, _ ⟩;
        constructor;
        exact one_half_pos;
        exact show ( 1 / 2 : ℝ ) < 1 by norm_num;
        linarith [ Real.pi_gt_three ];
      refine' ⟨ fun x => b x, _, _, _, _, _ ⟩;
      · exact ContDiffBump.contDiff b;
      · exact b.hasCompactSupport;
      · exact fun x => ContDiffBump.nonneg b;
      · exact ContDiffBump.integral_pos b;
      · intro x hx j;
        have := b.support_eq;
        exact lt_of_le_of_lt ( by simpa using ( norm_le_pi_norm x j ) ) ( lt_of_lt_of_le (
            mem_ball_zero_iff.mp ( this.subset hx ) ) hb.le );
  refine' ⟨ fun x => b x / ( ∫ x, b x ), _, _, _, _, _, _ ⟩ <;> simp_all +decide [
      MeasureTheory.integral_div ];
  · exact hb.1.div_const _;
  · rw [ hasCompactSupport_iff_eventuallyEq ] at *;
    filter_upwards [ hb.2.1 ] with x hx using by simp +decide [ hx, hb.2.2.2.1.ne' ] ;
  · exact MeasureTheory.Integrable.div_const ( by exact ( by contrapose! hb; simp_all +decide [
      MeasureTheory.integral_undef ] ) ) _;
  · exact fun x => div_nonneg ( hb.2.2.1 x ) hb.2.2.2.1.le;
  · linarith

/-! ## Rescale technicalities -/

/-
`rescale` preserves compact support.
-/
lemma rescale_hasCompactSupport {φ : (Fin n → ℝ) → ℂ}
    (hsupp : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (rescale n φ ε) := by
  have h_support_rescale : HasCompactSupport (fun x => φ (ε⁻¹ • x)) := by
    convert hsupp.comp_smul ( inv_ne_zero hε.ne' ) using 1;
  rw [ hasCompactSupport_iff_eventuallyEq ] at *;
  filter_upwards [ h_support_rescale ] with x hx using by simp [ rescale, hx ];

/-
`rescale` preserves smoothness.
-/
lemma rescale_contDiff {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (ε : ℝ) :
    ContDiff ℝ ∞ (rescale n φ ε) := by
  exact contDiff_const.mul ( hsmooth.comp ( contDiff_const_smul ε⁻¹ ) )

/-
If `supp(φ) ⊂ (-π,π)ⁿ` and `0 < ε ≤ 1`, then
    `supp(rescale n φ ε) ⊂ (-π,π)ⁿ`.
-/
lemma rescale_support_in_cube {φ : (Fin n → ℝ) → ℂ}
    (hsupp : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ x, rescale n φ ε x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi := by
  -- If rescale n φ ε x is not zero, then φ (ε⁻¹ • x) must be non-zero.
  intro x hx
  have h_phi_nonzero : φ (ε⁻¹ • x) ≠ 0 := by
    exact fun h => hx <| by unfold rescale; aesop;
  intro j; specialize hsupp ( ε⁻¹ • x ) h_phi_nonzero j; simp_all +decide [ abs_mul, abs_inv ] ;
  rw [ abs_of_pos hε ] at hsupp ; nlinarith [ inv_mul_cancel₀ ( ne_of_gt hε ), Real.pi_gt_three,
      abs_nonneg ( x j ) ]

/-
`ftRn n φ 0 = ∫ y, φ y`.
-/
lemma ftRn_at_zero (φ : (Fin n → ℝ) → ℂ) :
    ftRn n φ 0 = ∫ y, φ y := by
  exact MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall fun x => by simp +decide [
      ftRn ] )

/-! ## Bridge Lemma 1: `C^∞_c ⟹ FTRapidDecay`

The statement and proof now live in `NashEmbedding/Sobolev/IntegrationByParts.lean`
alongside the `ftRn`-side IBP infrastructure it depends on. Downstream
callers still see `NashEmbedding.Sobolev.cinfty_rapidDecay` through this file's
transitive re-export. -/

/-! ## `MemSobolevDistrib` closure for `convDistrib` -/

/-
The convolution distribution `convDistrib n φ u` preserves `MemSobolevDistrib`
    when `φ` is integrable.
-/
lemma convDistrib_memSobolevDistrib {φ : (Fin n → ℝ) → ℂ} (hφ : Integrable φ)
    {s : ℝ} {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u) :
    MemSobolevDistrib n s (convDistrib n φ u) := by
  exact memSobolevDistrib_convDistrib φ hφ hu

end NashEmbedding.Sobolev

end
