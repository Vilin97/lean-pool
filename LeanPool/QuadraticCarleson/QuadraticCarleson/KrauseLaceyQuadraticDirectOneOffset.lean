/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectExceptionalPairing
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectLowPairing

/-!
# One-offset closure for the direct quadratic proof

This module combines the checked low and high estimates for the regular
output subcollection at one fixed offset.  Exceptional outputs and finite
offset summation are kept as subsequent, separate steps.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectOneOffset

open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectExceptionalPairing
open KrauseLaceyQuadraticDirectLowPairing
open KrauseLaceyQuadraticDirectThresholdClosure
open KrauseLaceyStoppingRecursion


noncomputable section

/-- The regular output subcollection at one offset is controlled by the sum
of the direct quadratic low estimate and the positive high estimate. -/
theorem lintegral_directRegular_offsetTailMaximalOn_le_low_add_high
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ S, scale I < N)
    (g : L0Infinity) {p V : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    let A := directRegularIntervals S g p
      (directQuadraticExceptionalThreshold p n)
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x * ‖g x‖ₑ) ≤
      (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
          directQuadraticDelta n ^ (p - 1) * V) := by
  dsimp only
  let A := directRegularIntervals S g p
    (directQuadraticExceptionalThreshold p n)
  let a := directQuadraticLowThreshold n
  have hA : A ⊆ S := by
    intro I hI
    exact (mem_directRegularIntervals_iff.mp hI).1
  have hboundA : ∀ I ∈ A, scale I < N := by
    intro I hI
    exact hbound I (hA hI)
  have ha : 0 < a := Real.rpow_pos_of_pos (directQuadraticDelta_pos n) _
  have hlowMeas : AEMeasurable (fun x ↦
      offsetTailMaximalOn S A scale (f : ℝ → ℂ) ell₀ (n : ℤ) x *
        ‖interpolationLow g a x‖ₑ) volume :=
    (measurable_offsetTailMaximalOn S A scale
      f.measurable_toFun ell₀ (n : ℤ)).aemeasurable.mul
        (KrauseLaceyBadScale.integrable_interpolationLow_local g.measurable_toFun
          g.integrable_finiteSparseProof a).aestronglyMeasurable.enorm
  have hnorm (x : ℝ) :
      ‖g x‖ₑ = ‖interpolationLow g a x‖ₑ +
        ‖interpolationHigh g a x‖ₑ := by
    by_cases hx : ‖g x‖ ≤ a
    · simp [interpolationLow, interpolationHigh, hx, not_lt.mpr hx]
    · simp [interpolationLow, interpolationHigh, hx, lt_of_not_ge hx]
  have hlow :
      (∫⁻ x, offsetTailMaximalOn S A scale
          (f : ℝ → ℂ) ell₀ (n : ℤ) x *
            ‖interpolationLow g a x‖ₑ) ≤
        (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) := by
    simpa only [A, a] using
      lintegral_offsetTailMaximalOn_interpolationLow_le_directQuadratic_of_nonnegative_scales
        hA hlam scale hscale hscaleNonneg f n hM hmass I₀ hsub ell₀ N
          hboundA g hp hp2 hV hroot hgp
  have hgpInt : Integrable (fun x ↦ ‖g x‖ ^ p) :=
    KrauseLaceyQuadraticDirectExceptionalPairing.L0Infinity.integrable_norm_rpow_direct
      g (lt_trans zero_lt_one hp)
  have hhigh0 :=
    lintegral_regular_offsetTailMaximalOn_interpolationHigh_le_directQuadratic
      n hp hgpInt hlam scale hscale f ell₀ I₀ hsub
  have hcoeff :
      0 ≤ 8 * positiveDyadicAmplitudeBound *
        directQuadraticDelta n ^ (p - 1) :=
    mul_nonneg
      (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
      (Real.rpow_nonneg (directQuadraticDelta_pos n).le _)
  have hhigh :
      (∫⁻ x, offsetTailMaximalOn S A scale
          (f : ℝ → ℂ) ell₀ (n : ℤ) x *
            ‖interpolationHigh g a x‖ₑ) ≤
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
          directQuadraticDelta n ^ (p - 1) * V) := by
    apply hhigh0.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hroot hcoeff
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x * ‖g x‖ₑ) =
      (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x *
          ‖interpolationLow g a x‖ₑ) +
        ∫⁻ x, offsetTailMaximalOn S A scale
          (f : ℝ → ℂ) ell₀ (n : ℤ) x *
            ‖interpolationHigh g a x‖ₑ := by
      simp_rw [hnorm, mul_add]
      exact lintegral_add_left' hlowMeas _
    _ ≤ (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
          directQuadraticDelta n ^ (p - 1) * V) := add_le_add hlow hhigh

/-- The complete regular/exceptional decomposition at one fixed offset.
The first two terms are the regular low/high bounds, while the final term is
the packing bound for the exceptional output family. -/
theorem lintegral_offsetTailMaximalOn_le_oneOffset_directQuadratic
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ S, scale I < N)
    (g : L0Infinity) {p V F G : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V)
    (hgpRoot : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ Q ∈ directMaximalExceptionalIntervals S g p
        (directQuadraticExceptionalThreshold p n),
      intervalL1Average f Q ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G) :
    (∫⁻ x, offsetTailMaximalOn S S scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x * ‖g x‖ₑ) ≤
      ((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
          directQuadraticDelta n ^ (p - 1) * V)) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F *
          (directQuadraticDelta n ^ (p - 1) * V)) := by
  let Λ := directQuadraticExceptionalThreshold p n
  have hE : AEMeasurable (fun x ↦ offsetTailMaximalOn S
      (directExceptionalIntervals S g p Λ) scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x * ‖g x‖ₑ) volume :=
    ((measurable_offsetTailMaximalOn S
      (directExceptionalIntervals S g p Λ) scale
        f.measurable_toFun ell₀ (n : ℤ)).mul
      g.measurable_toFun.enorm).aemeasurable
  have hsplit :=
    lintegral_offsetTailMaximalOn_directRegular_exceptional_le
      S scale (f : ℝ → ℂ) (g : ℝ → ℂ) p Λ ell₀ (n : ℤ) hE
  have hregular :=
    lintegral_directRegular_offsetTailMaximalOn_le_low_add_high
      hlam scale hscale hscaleNonneg f n hM hmass I₀ hsub ell₀ N hbound
        g hp hp2 hV hroot hgp
  have hgpInt : Integrable (fun x ↦ ‖g x‖ ^ p) :=
    KrauseLaceyQuadraticDirectExceptionalPairing.L0Infinity.integrable_norm_rpow_direct
      g (lt_trans zero_lt_one hp)
  have hexception :=
    lintegral_exceptional_offsetTailMaximalOn_le_directQuadratic
      n hgpInt hlam scale hscale f (s := (n : ℤ)) (Int.ofNat_nonneg n)
        ell₀ I₀ hsub hgpRoot hF hG hfavg hgavg
  exact hsplit.trans (add_le_add hregular hexception)

/-- Integrating the exact finite offset reconstruction costs only the sum of
the individual offset pairings. -/
theorem lintegral_localizedTailMaximal_le_sum_offsetPairings
    {S : Finset RealInterval} (scale : RealInterval → ℤ)
    (f g : L0Infinity) (ell₀ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2)) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      ∑ s ∈ (offsetSet S scale).filter (fun s ↦ 0 ≤ s),
        ∫⁻ x, offsetTailMaximal S scale (f : ℝ → ℂ) ell₀ s x * ‖g x‖ₑ := by
  let O := (offsetSet S scale).filter (fun s ↦ 0 ≤ s)
  have hmeas : ∀ s ∈ O, AEMeasurable (fun x ↦
      offsetTailMaximal S scale (f : ℝ → ℂ) ell₀ s x * ‖g x‖ₑ) volume := by
    intro s hs
    exact ((measurable_offsetTailMaximalOn S S scale
      f.measurable_toFun ell₀ s).mul g.measurable_toFun.enorm).aemeasurable
  calc
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        ∫⁻ x, (∑ s ∈ O, offsetTailMaximal S scale
          (f : ℝ → ℂ) ell₀ s x) * ‖g x‖ₑ := by
      apply lintegral_mono
      intro x
      exact mul_le_mul'
        (localizedTailMaximal_le_sum_offsetTailMaximal
          scale f ell₀ hlam hscale x) le_rfl
    _ = ∫⁻ x, ∑ s ∈ O,
        offsetTailMaximal S scale (f : ℝ → ℂ) ell₀ s x * ‖g x‖ₑ := by
      congr 1
      funext x
      simp only [Finset.sum_mul]
    _ = ∑ s ∈ O,
        ∫⁻ x, offsetTailMaximal S scale
          (f : ℝ → ℂ) ell₀ s x * ‖g x‖ₑ :=
      lintegral_finsetSum' O hmeas

/-- Finite offset reconstruction with the complete direct quadratic estimate
inserted at every nonnegative offset. -/
theorem lintegral_localizedTailMaximal_le_sum_oneOffset_directQuadratic
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ S, scale I < N)
    (g : L0Infinity) {p V F G : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V)
    (hgpRoot : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ I ∈ S, intervalL1Average f I ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      ∑ s ∈ (offsetSet S scale).filter (fun s ↦ 0 ≤ s),
        (((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal
              (directQuadraticDelta s.toNat ^ (p - 1) * V) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
            directQuadraticDelta s.toNat ^ (p - 1) * V)) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F *
            (directQuadraticDelta s.toNat ^ (p - 1) * V))) := by
  let O := (offsetSet S scale).filter (fun s ↦ 0 ≤ s)
  apply (lintegral_localizedTailMaximal_le_sum_offsetPairings
    scale f g ell₀ hlam hscale).trans
  apply Finset.sum_le_sum
  intro s hs
  have hs0 : 0 ≤ s := (Finset.mem_filter.mp hs).2
  have hcast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
  simpa only [hcast, offsetTailMaximalOn_self] using
    (lintegral_offsetTailMaximalOn_le_oneOffset_directQuadratic
      hlam scale hscale hscaleNonneg f s.toNat hM hmass I₀ hsub ell₀ N
        hbound g hp hp2 hV hroot hgp hgpRoot hF hG
        (fun Q hQ ↦ hfavg Q
          (directMaximalExceptionalIntervals_subset S g p
            (directQuadraticExceptionalThreshold p s.toNat) hQ))
        hgavg)

/-- The common real mass-decay term in the offset estimates sums to the
paper's `20 * p'` geometric-series factor. -/
theorem sum_ofReal_directQuadraticDelta_rpow_mul_le
    {p V : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (O : Finset ℤ) (hO : ∀ s ∈ O, 0 ≤ s) :
    (∑ s ∈ O, ENNReal.ofReal
      (directQuadraticDelta s.toNat ^ (p - 1) * V)) ≤
        ENNReal.ofReal (20 * holderConjugate p * V) := by
  have hterm (s : ℤ) :
      0 ≤ directQuadraticDelta s.toNat ^ (p - 1) * V :=
    mul_nonneg
      (Real.rpow_nonneg (directQuadraticDelta_pos s.toNat).le _) hV
  have hgeom :=
    finite_int_directQuadraticDecayRatio_sum_le_twenty_mul_holderConjugate
      hp hp2 O hO
  calc
    (∑ s ∈ O, ENNReal.ofReal
        (directQuadraticDelta s.toNat ^ (p - 1) * V)) =
        ENNReal.ofReal (∑ s ∈ O,
          directQuadraticDelta s.toNat ^ (p - 1) * V) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun s _ ↦ hterm s)]
    _ = ENNReal.ofReal
        ((∑ s ∈ O, directQuadraticDecayRatio p ^ s.toNat) * V) := by
      congr 1
      simp_rw [directQuadraticDelta_rpow_eq_decayRatio_pow]
      rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (20 * holderConjugate p * V) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hgeom hV

/-- The reconstructed localized maximal-tail pairing, with all offsets summed
and the geometric series replaced by the paper's `20 * p'` bound. -/
theorem lintegral_localizedTailMaximal_le_directQuadratic_geometric
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ S, scale I < N)
    (g : L0Infinity) {p V F G : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V)
    (hgpRoot : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ I ∈ S, intervalL1Average f I ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      ((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F)) *
        ENNReal.ofReal (20 * holderConjugate p * V) := by
  let O := (offsetSet S scale).filter (fun s ↦ 0 ≤ s)
  let K : ℝ≥0∞ := (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ)
  let B : ℝ := 8 * positiveDyadicAmplitudeBound
  let C : ℝ := B * G * F
  let D : ℤ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal
    (directQuadraticDelta s.toNat ^ (p - 1) * V)
  have hB : 0 ≤ B :=
    mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hB hG) hF
  have hfinite :=
    lintegral_localizedTailMaximal_le_sum_oneOffset_directQuadratic
      hlam scale hscale hscaleNonneg f hM hmass I₀ hsub ell₀ N hbound
        g hp hp2 hV hroot hgp hgpRoot hF hG hfavg hgavg
  have hterm (s : ℤ) :
      (((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) * D s +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
            directQuadraticDelta s.toNat ^ (p - 1) * V)) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F *
          (directQuadraticDelta s.toNat ^ (p - 1) * V))) =
        (K + ENNReal.ofReal B + ENNReal.ofReal C) * D s := by
    have hsecond :
        8 * positiveDyadicAmplitudeBound *
            directQuadraticDelta s.toNat ^ (p - 1) * V =
          B * (directQuadraticDelta s.toNat ^ (p - 1) * V) := by
      simp only [B]
      ring
    have hthird :
        8 * positiveDyadicAmplitudeBound * G * F *
            (directQuadraticDelta s.toNat ^ (p - 1) * V) =
          C * (directQuadraticDelta s.toNat ^ (p - 1) * V) := by
      simp only [C, B]
    rw [hsecond, hthird, ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hC]
    simp only [K, D]
    ring
  have hdecay :
      (∑ s ∈ O, D s) ≤ ENNReal.ofReal (20 * holderConjugate p * V) := by
    exact sum_ofReal_directQuadraticDelta_rpow_mul_le hp hp2 hV O
      (fun s hs ↦ (Finset.mem_filter.mp hs).2)
  calc
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        ∑ s ∈ O,
          (((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) * D s +
            ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
              directQuadraticDelta s.toNat ^ (p - 1) * V)) +
            ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F *
              (directQuadraticDelta s.toNat ^ (p - 1) * V))) := by
      simpa only [O, D] using hfinite
    _ = (K + ENNReal.ofReal B + ENNReal.ofReal C) * ∑ s ∈ O, D s := by
      simp_rw [hterm]
      rw [Finset.mul_sum]
    _ ≤ (K + ENNReal.ofReal B + ENNReal.ofReal C) *
        ENNReal.ofReal (20 * holderConjugate p * V) :=
      mul_le_mul' le_rfl hdecay
    _ = ((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F)) *
        ENNReal.ofReal (20 * holderConjugate p * V) := by
      simp only [K, B, C]


end
end KrauseLaceyQuadraticDirectOneOffset
end QuadraticCarleson
