/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.CanonicalPairing
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact kernel corrections

This file extends summable errors on the canonical Hilbert-kernel basis to a compact ambient
operator whose symplectic adjoint is also compact.
-/


namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic
open scoped ENNReal NNReal Topology lp BigOperators

private def l2Basis (n : ℕ) : CanonicalL2 :=
  lp.single 2 n 1

private def kernelCoefficient (n : ℕ) :
    StrongDual ℝ CanonicalRealKaltonPeck :=
  ((ContinuousLinearMap.apply ℝ ℝ) (canonicalSecondBasisVector n)).comp
    canonicalKaltonSwansonForm.toDual.toContinuousLinearMap

private lemma kernelCoefficient_apply (n : ℕ)
    (z : CanonicalRealKaltonPeck) :
    kernelCoefficient n z =
      canonicalKaltonSwansonForm.toDual z
        (canonicalSecondBasisVector n) := by
  rfl

private lemma inclusion_l2Basis (n : ℕ) :
    canonicalL2Inclusion (l2Basis n) = canonicalFirstBasisVector n := by
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [canonicalL2Inclusion_coordinates, (canonicalBasisCoordinates n).1]
  apply Prod.ext
  · funext k
    simp [l2Basis, standardBasisSequence, lp.single_apply, Pi.single_apply]
  · rfl

private lemma quotient_secondBasis (n : ℕ) :
    canonicalL2Quotient (canonicalSecondBasisVector n) = l2Basis n := by
  apply Subtype.ext
  funext k
  rw [canonicalL2Quotient_apply]
  change standardBasisSequence n k = l2Basis n k
  simp [standardBasisSequence, l2Basis, lp.single_apply, Pi.single_apply]

private lemma kernelCoefficient_firstBasis (n m : ℕ) :
    kernelCoefficient n (canonicalFirstBasisVector m) =
      if n = m then 1 else 0 := by
  rw [← inclusion_l2Basis, kernelCoefficient_apply,
    Symplectic.canonicalKaltonSwansonForm_inclusion_left,
    quotient_secondBasis]
  dsimp only [l2Basis]
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

private def kernelCorrectionTerm
    (e : ℕ → CanonicalRealKaltonPeck) (n : ℕ) :
    CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
  (kernelCoefficient n).smulRight (e n)

private def kernelCorrectionAdjointTerm
    (e : ℕ → CanonicalRealKaltonPeck) (n : ℕ) :
    CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
  (canonicalKaltonSwansonForm.toDual (e n)).smulRight
    (canonicalSecondBasisVector n)

private lemma adjoint_kernelCorrectionTerm
    (e : ℕ → CanonicalRealKaltonPeck) (n : ℕ) :
    canonicalKaltonSwansonForm.adjoint (kernelCorrectionTerm e n) =
      kernelCorrectionAdjointTerm e n := by
  apply ContinuousLinearMap.ext
  intro y
  apply canonicalKaltonSwansonForm.toDual.injective
  apply ContinuousLinearMap.ext
  intro x
  rw [Forms.adjoint_apply]
  change
    canonicalKaltonSwansonForm.toDual
        y (kernelCoefficient n x • e n) =
      canonicalKaltonSwansonForm.toDual
        (canonicalKaltonSwansonForm.toDual (e n) y •
          canonicalSecondBasisVector n) x
  simp only [map_smul, smul_apply, kernelCoefficient_apply]
  have hskew (a b : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual a b =
        -canonicalKaltonSwansonForm.toDual b a := by
    have h := canonicalKaltonSwansonForm.alternating (a + b)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  rw [hskew y (e n), hskew (canonicalSecondBasisVector n) x]
  ring

private lemma evaluation_opNorm_le (z : CanonicalRealKaltonPeck) :
    ‖(ContinuousLinearMap.apply ℝ ℝ) z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro f
  simpa only [ContinuousLinearMap.apply_apply, mul_comm] using
    f.le_opNorm z

private lemma kernelCoefficient_norm_le (n : ℕ) :
    ‖kernelCoefficient n‖ ≤
      ‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ *
        ‖canonicalSecondBasisVector n‖ := by
  calc
    ‖kernelCoefficient n‖ ≤
        ‖(ContinuousLinearMap.apply ℝ ℝ)
            (canonicalSecondBasisVector n)‖ *
          ‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖canonicalSecondBasisVector n‖ *
          ‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ := by
      gcongr
      exact evaluation_opNorm_le _
    _ = ‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ *
          ‖canonicalSecondBasisVector n‖ := mul_comm _ _

private lemma rankOne_isCompact
    (f : StrongDual ℝ CanonicalRealKaltonPeck)
    (z : CanonicalRealKaltonPeck) :
    IsCompactOperator (f.smulRight z) := by
  have hf : IsCompactOperator f :=
    isCompactOperator_of_locallyCompactSpace_dom f
  change IsCompactOperator
    (fun x => (ContinuousLinearMap.toSpanSingleton ℝ z) (f x))
  exact hf.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ z)

private theorem exists_uniform_secondBasis_norm :
    ∃ D : ℝ, 0 < D ∧ ∀ n, ‖canonicalSecondBasisVector n‖ ≤ D := by
  obtain ⟨c, D, hc, hD, hmodel⟩ :=
    canonicalRealKaltonPeckPresentation.norm_equivalent
  refine ⟨D, hD, fun n => ?_⟩
  apply (hmodel (canonicalSecondBasisVector n)).2.trans_eq
  rw [(canonicalBasisCoordinates n).2]
  have hl2 : l2Norm (standardBasisSequence n) = 1 := by
    rw [l2Norm, tsum_eq_single n]
    · simp [standardBasisSequence]
    · intro k hk
      simp [standardBasisSequence, hk]
  have hcentral : centralizer (standardBasisSequence n) = 0 := by
    funext k
    by_cases hk : k = n
    · simp [centralizer, standardBasisSequence, hk, hl2]
    · simp [centralizer, standardBasisSequence, hk]
  rw [kaltonPeckQuasiNorm, hcentral, hl2]
  simp [l2Norm]

private lemma kernelCorrectionTerm_summable
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    Summable (kernelCorrectionTerm e) := by
  obtain ⟨D, hD, hsecond⟩ := exists_uniform_secondBasis_norm
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg (kernelCorrectionTerm e n))
    (fun n => ?_)
    (he.mul_left
      (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ * D))
  calc
    ‖kernelCorrectionTerm e n‖ =
        ‖kernelCoefficient n‖ * ‖e n‖ := by
      simp [kernelCorrectionTerm]
    _ ≤ (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ *
          ‖canonicalSecondBasisVector n‖) * ‖e n‖ := by
      exact mul_le_mul_of_nonneg_right
        (kernelCoefficient_norm_le n) (norm_nonneg _)
    _ ≤ (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ * D) *
          ‖e n‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsecond n)
        (norm_nonneg
          canonicalKaltonSwansonForm.toDual.toContinuousLinearMap)

private lemma kernelCorrectionAdjointTerm_summable
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    Summable (kernelCorrectionAdjointTerm e) := by
  obtain ⟨D, hD, hsecond⟩ := exists_uniform_secondBasis_norm
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg (kernelCorrectionAdjointTerm e n))
    (fun n => ?_)
    (he.mul_left
      (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ * D))
  calc
    ‖kernelCorrectionAdjointTerm e n‖ =
        ‖canonicalKaltonSwansonForm.toDual (e n)‖ *
          ‖canonicalSecondBasisVector n‖ := by
      simp [kernelCorrectionAdjointTerm]
    _ ≤
        (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ *
          ‖e n‖) *
          ‖canonicalSecondBasisVector n‖ := by
      gcongr
      exact
        canonicalKaltonSwansonForm.toDual.toContinuousLinearMap.le_opNorm
          (e n)
    _ ≤
        (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ *
          ‖e n‖) * D := by
      exact mul_le_mul_of_nonneg_left (hsecond n) (by positivity)
    _ =
        (‖canonicalKaltonSwansonForm.toDual.toContinuousLinearMap‖ * D) *
          ‖e n‖ := by
      ring

private def kernelCorrection
    (e : ℕ → CanonicalRealKaltonPeck) :
    CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
  ∑' n, kernelCorrectionTerm e n

private def kernelCorrectionAdjoint
    (e : ℕ → CanonicalRealKaltonPeck) :
    CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
  ∑' n, kernelCorrectionAdjointTerm e n

private lemma kernelCorrection_isCompact
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    IsCompactOperator (kernelCorrection e) := by
  have hs := kernelCorrectionTerm_summable e he
  apply isCompactOperator_of_tendsto hs.hasSum.tendsto_sum_nat
  filter_upwards []
  intro N
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact isCompactOperator_zero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (rankOne_isCompact _ _)

private lemma kernelCorrectionAdjoint_isCompact
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    IsCompactOperator (kernelCorrectionAdjoint e) := by
  have hs := kernelCorrectionAdjointTerm_summable e he
  apply isCompactOperator_of_tendsto hs.hasSum.tendsto_sum_nat
  filter_upwards []
  intro N
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact isCompactOperator_zero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (rankOne_isCompact _ _)

private lemma adjoint_kernelCorrection
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    canonicalKaltonSwansonForm.adjoint (kernelCorrection e) =
      kernelCorrectionAdjoint e := by
  apply ContinuousLinearMap.ext
  intro x
  apply canonicalKaltonSwansonForm.toDual.injective
  apply ContinuousLinearMap.ext
  intro y
  rw [Forms.adjoint_apply]
  have hs := kernelCorrectionTerm_summable e he
  have hsAdj := kernelCorrectionAdjointTerm_summable e he
  have hleft :=
    hs.hasSum.map
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck) y)
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck) y).continuous
  have hright :=
    hsAdj.hasSum.map
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck) x)
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck) x).continuous
  change
    canonicalKaltonSwansonForm.toDual x
        ((∑' n, kernelCorrectionTerm e n) y) =
      canonicalKaltonSwansonForm.toDual
        ((∑' n, kernelCorrectionAdjointTerm e n) x) y
  have hleft' :
      HasSum (fun n => kernelCorrectionTerm e n y)
        ((∑' n, kernelCorrectionTerm e n) y) := by
    apply HasSum.congr_fun hleft
    intro n
    rfl
  have hright' :
      HasSum (fun n => kernelCorrectionAdjointTerm e n x)
        ((∑' n, kernelCorrectionAdjointTerm e n) x) := by
    apply HasSum.congr_fun hright
    intro n
    rfl
  rw [← hleft'.tsum_eq, ← hright'.tsum_eq]
  let fy : StrongDual ℝ CanonicalRealKaltonPeck :=
    ((ContinuousLinearMap.apply ℝ ℝ) y).comp
      canonicalKaltonSwansonForm.toDual.toContinuousLinearMap
  change
    canonicalKaltonSwansonForm.toDual x
        (∑' n, kernelCorrectionTerm e n y) =
      fy (∑' n, kernelCorrectionAdjointTerm e n x)
  rw [(canonicalKaltonSwansonForm.toDual x).map_tsum hleft'.summable,
    fy.map_tsum hright'.summable]
  apply tsum_congr
  intro n
  rw [← Forms.adjoint_apply, adjoint_kernelCorrectionTerm]
  rfl

private lemma kernelCorrection_firstBasis
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) (m : ℕ) :
    kernelCorrection e (canonicalFirstBasisVector m) = e m := by
  have hs := kernelCorrectionTerm_summable e he
  have happ :=
    hs.hasSum.map
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck)
        (canonicalFirstBasisVector m))
      ((ContinuousLinearMap.apply ℝ CanonicalRealKaltonPeck)
        (canonicalFirstBasisVector m)).continuous
  have happ' :
      HasSum
        (fun n =>
          kernelCorrectionTerm e n (canonicalFirstBasisVector m))
        ((∑' n, kernelCorrectionTerm e n)
          (canonicalFirstBasisVector m)) := by
    apply HasSum.congr_fun happ
    intro n
    rfl
  rw [show kernelCorrection e = ∑' n, kernelCorrectionTerm e n by rfl,
    ← happ'.tsum_eq]
  change
    ∑' n, kernelCoefficient n (canonicalFirstBasisVector m) • e n =
      e m
  have hsingle :
      (fun n => kernelCoefficient n (canonicalFirstBasisVector m) • e n) =
        fun n => if n = m then e m else 0 := by
    funext n
    rw [kernelCoefficient_firstBasis]
    by_cases hnm : n = m <;> simp [hnm]
  rw [hsingle, tsum_ite_eq]

/-- A summable error sequence on the canonical kernel extends to a compact ambient
operator whose symplectic adjoint is compact as well. -/
theorem exists_compact_biadjoint_kernelCorrection
    (e : ℕ → CanonicalRealKaltonPeck)
    (he : Summable fun n => ‖e n‖) :
    ∃ K : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
      IsCompactOperator K ∧
      IsCompactOperator (canonicalKaltonSwansonForm.adjoint K) ∧
      ∀ n, K (canonicalFirstBasisVector n) = e n := by
  refine ⟨kernelCorrection e, kernelCorrection_isCompact e he, ?_, ?_⟩
  · rw [adjoint_kernelCorrection e he]
    exact kernelCorrectionAdjoint_isCompact e he
  · exact kernelCorrection_firstBasis e he

end

end KaltonPeck.Support.GraphFredholm

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
