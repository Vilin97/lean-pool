/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectTailProjection
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectThresholdPairing

/-!
# Low-truncation pairing for the direct quadratic tail

This module joins the checked direct-tail `L²` estimate to the scalar Holder
interface. Constant normalization is deliberately kept separate from this
analytic step.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectLowPairing

open KrauseLaceyBadScale
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectTailProjection
open KrauseLaceyQuadraticProjectionRemainder
open KrauseLaceyQuadraticSmoothProjection


noncomputable
section

/-- The scale-independent extended-nonnegative energy constant obtained by
factoring the common spatial mass and dyadic decay out of the direct-tail
estimate. -/
def directQuadraticTailEnergyConstant (M : ℝ) : ℝ≥0∞ :=
  1372 *
    ((4 + 128 *
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal (432 * positiveDyadicAmplitudeBound ^ 2 * M) +
      ENNReal.ofReal
        ((2 * (Real.pi * projectionRemainderConstant) *
          Real.sqrt (3 * M)) ^ 2 * 8))

/-- Exact extraction of the common `t * V` factor from the explicit
projected-plus-remainder energy. -/
theorem directQuadraticTailEnergy_eq_constant_mul
    {M t V : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t) (hV : 0 ≤ V) :
    1372 *
      ((4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
          ENNReal.ofReal
            ((432 * positiveDyadicAmplitudeBound ^ 2 * M * t) * V) +
        ENNReal.ofReal
          ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
            Real.sqrt (8 * t) * Real.sqrt V) ^ 2)) =
      directQuadraticTailEnergyConstant M * ENNReal.ofReal (t * V) := by
  have hcoeffB :
      0 ≤ 432 * positiveDyadicAmplitudeBound ^ 2 * M :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM
  have hB :
      ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M * t) * V) =
        ENNReal.ofReal (432 * positiveDyadicAmplitudeBound ^ 2 * M) *
          ENNReal.ofReal (t * V) := by
    rw [show (432 * positiveDyadicAmplitudeBound ^ 2 * M * t) * V =
      (432 * positiveDyadicAmplitudeBound ^ 2 * M) * (t * V) by ring,
      ENNReal.ofReal_mul hcoeffB]
  have h8t : 0 ≤ 8 * t := mul_nonneg (by norm_num) ht
  have hrealC :
      (2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
          Real.sqrt (8 * t) * Real.sqrt V) ^ 2 =
        ((2 * (Real.pi * projectionRemainderConstant) *
          Real.sqrt (3 * M)) ^ 2 * 8) * (t * V) := by
    calc
      (2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
          Real.sqrt (8 * t) * Real.sqrt V) ^ 2 =
        (2 * (Real.pi * projectionRemainderConstant) *
          Real.sqrt (3 * M)) ^ 2 *
            (Real.sqrt (8 * t)) ^ 2 * (Real.sqrt V) ^ 2 := by ring
      _ = (2 * (Real.pi * projectionRemainderConstant) *
          Real.sqrt (3 * M)) ^ 2 * (8 * t) * V := by
        rw [Real.sq_sqrt h8t, Real.sq_sqrt hV]
      _ = ((2 * (Real.pi * projectionRemainderConstant) *
          Real.sqrt (3 * M)) ^ 2 * 8) * (t * V) := by ring
  have hcoeffC :
      0 ≤ (2 * (Real.pi * projectionRemainderConstant) *
        Real.sqrt (3 * M)) ^ 2 * 8 :=
    mul_nonneg (sq_nonneg _) (by norm_num)
  have hC :
      ENNReal.ofReal
          ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
            Real.sqrt (8 * t) * Real.sqrt V) ^ 2) =
        ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M)) ^ 2 * 8) *
          ENNReal.ofReal (t * V) := by
    rw [hrealC, ENNReal.ofReal_mul hcoeffC]
  rw [hB, hC]
  unfold directQuadraticTailEnergyConstant
  ring

/-- The genuine direct-tail `L²` estimate with its scale-independent
constant and its exact dyadic/root-mass factor separated. -/
theorem eLpNorm_offsetTailMaximalOn_le_factored
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
    (ell₀ : ℤ) (N : ℕ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    eLpNorm (offsetTailMaximalOn S A scale
      (f : ℝ → ℂ) ell₀ s) 2 volume ≤
      (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal
          ((2 : ℝ) ^ (-s) * ∫ x in I₀.carrier, ‖f x‖)) ^ (1 / 2 : ℝ) := by
  have ht : 0 ≤ (2 : ℝ) ^ (-s) := zpow_nonneg (by norm_num) _
  have hV : 0 ≤ ∫ x in I₀.carrier, ‖f x‖ := integral_nonneg fun _ ↦ norm_nonneg _
  calc
    eLpNorm (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ s) 2 volume ≤
      (1372 *
        ((4 + 128 *
          (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
            ENNReal.ofReal
              ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                  (2 : ℝ) ^ (-s)) *
                ∫ x in I₀.carrier, ‖f x‖) +
          ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M) * Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
                Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2))) ^
        (1 / 2 : ℝ) :=
      eLpNorm_offsetTailMaximalOn_le_root
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap ell₀ N hnonneg hbound
    _ = (directQuadraticTailEnergyConstant M *
          ENNReal.ofReal
            ((2 : ℝ) ^ (-s) * ∫ x in I₀.carrier, ‖f x‖)) ^
        (1 / 2 : ℝ) := by
      rw [directQuadraticTailEnergy_eq_constant_mul hM ht hV]
    _ = (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal
          ((2 : ℝ) ^ (-s) * ∫ x in I₀.carrier, ‖f x‖)) ^ (1 / 2 : ℝ) :=
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

/-- The factored direct-tail estimate for an arbitrary output subcollection.
The former frequency-radius premise is discharged by deleting the outputs
whose grouped input is identically zero. -/
theorem eLpNorm_offsetTailMaximalOn_le_factored_of_nonnegative_scales
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ A, scale I < N) :
    eLpNorm (offsetTailMaximalOn S A scale
      (f : ℝ → ℂ) ell₀ s) 2 volume ≤
      (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal
          ((2 : ℝ) ^ (-s) * ∫ x in I₀.carrier, ‖f x‖)) ^ (1 / 2 : ℝ) := by
  let R := relevantOffsetOutputs A scale s
  have hR : R ⊆ S := by
    intro I hI
    exact hA (mem_relevantOffsetOutputs_iff.mp hI).1
  have hgap : ∀ k ∈ R.image scale,
      ∀ I ∈ R.filter (fun I ↦ scale I = k),
        0 ≤ scale I + 2 - s := by
    intro k hk I hI
    exact (mem_relevantOffsetOutputs_iff.mp
      (Finset.mem_filter.mp hI).1).2
  have hnonneg : ∀ I ∈ R, 0 ≤ scale I := by
    intro I hI
    exact hscaleNonneg I (hR hI)
  have hboundR : ∀ I ∈ R, scale I < N := by
    intro I hI
    exact hbound I (mem_relevantOffsetOutputs_iff.mp hI).1
  have h := eLpNorm_offsetTailMaximalOn_le_factored
    hR hlam scale hscale f hs hM hmass I₀ hsub hgap ell₀ N hnonneg hboundR
  rw [offsetTailMaximalOn_relevantOffsetOutputs
    hscaleNonneg (f : ℝ → ℂ) ell₀ s] at h
  exact h

/-- The square root of the integer dyadic scale factor is exactly the
paper's real scale parameter `directQuadraticDelta`. -/
theorem ennreal_dyadic_mass_rpow_half_eq_delta
    (n : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    (ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ)) * V)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (directQuadraticDelta n * Real.sqrt V) := by
  have ht : 0 ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_nonneg (by norm_num) _
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ht hV) (by norm_num)]
  congr 1
  rw [Real.mul_rpow ht hV, Real.sqrt_eq_rpow]
  congr 1
  unfold directQuadraticDelta
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- Low-truncation Holder with a fixed extended-nonnegative constant in
front of the normalized `L²` estimate. -/
theorem lintegral_pairing_interpolationLow_ennreal_le_normalized_mul
    {U : ℝ → ℝ≥0∞} {g : ℝ → ℂ} (hUmeas : AEMeasurable U volume)
    (hg : Measurable g) (hgi : Integrable g) {C : ℝ≥0∞}
    {a p delta V : ℝ} (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2)
    (hdelta : 0 ≤ delta) (hV : 0 ≤ V)
    (hU : eLpNorm U 2 volume ≤
      C * ENNReal.ofReal (delta * Real.sqrt V))
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    (∫⁻ x, U x * ‖interpolationLow g a x‖ₑ) ≤
      C * ENNReal.ofReal (delta * a ^ (1 - p / 2) * V) := by
  have halg :
      ENNReal.ofReal (delta * Real.sqrt V) *
          (ENNReal.ofReal (a ^ (2 - p)) * ENNReal.ofReal V) ^
            (1 / 2 : ℝ) =
        ENNReal.ofReal (delta * a ^ (1 - p / 2) * V) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le (2 - p))]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ha.le _) hV)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_mul (mul_nonneg hdelta (Real.sqrt_nonneg V))]
    rw [show delta * Real.sqrt V * (a ^ (2 - p) * V) ^ (1 / 2 : ℝ) =
      delta * (Real.sqrt V * (a ^ (2 - p) * V) ^ (1 / 2 : ℝ)) by ring]
    rw [KrauseLaceyBadScale.sqrt_mul_rpow_mul_sqrt ha hV]
    congr 1
    ring
  calc
    (∫⁻ x, U x * ‖interpolationLow g a x‖ₑ) ≤
        eLpNorm U 2 volume *
          (ENNReal.ofReal (a ^ (2 - p)) *
            ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) :=
      KrauseLaceyBadScale.lintegral_pairing_interpolationLow_ennreal_le
        hUmeas hg hgi ha hp hp2
    _ ≤ (C * ENNReal.ofReal (delta * Real.sqrt V)) *
        (ENNReal.ofReal (a ^ (2 - p)) * ENNReal.ofReal V) ^
          (1 / 2 : ℝ) := by
      apply mul_le_mul' hU
      apply ENNReal.rpow_le_rpow
      · exact mul_le_mul' le_rfl hgp
      norm_num
    _ = C * ENNReal.ofReal (delta * a ^ (1 - p / 2) * V) := by
      rw [mul_assoc, halg]

/-- The low half of the author's direct fixed-offset argument for the
genuine localized maximal tail, at `A = delta⁻²`. -/
theorem lintegral_offsetTailMaximalOn_interpolationLow_le_directQuadratic
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k),
        0 ≤ scale I + 2 - (n : ℤ))
    (ell₀ : ℤ) (N : ℕ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N)
    (g : L0Infinity) {p V : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x *
          ‖interpolationLow g (directQuadraticLowThreshold n) x‖ₑ) ≤
      (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) := by
  let C : ℝ≥0∞ := (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ)
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast n.zero_le
  have ht : 0 ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_nonneg (by norm_num) _
  have hscaleMass :
      ENNReal.ofReal
          ((2 : ℝ) ^ (-(n : ℤ)) * ∫ x in I₀.carrier, ‖f x‖) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ)) * V) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hroot ht
  have hU :
      eLpNorm (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ)) 2 volume ≤
        C * ENNReal.ofReal (directQuadraticDelta n * Real.sqrt V) := by
    calc
      eLpNorm (offsetTailMaximalOn S A scale
          (f : ℝ → ℂ) ell₀ (n : ℤ)) 2 volume ≤
        C *
          (ENNReal.ofReal
            ((2 : ℝ) ^ (-(n : ℤ)) *
              ∫ x in I₀.carrier, ‖f x‖)) ^ (1 / 2 : ℝ) :=
        eLpNorm_offsetTailMaximalOn_le_factored
          hA hlam scale hscale f hn0 hM hmass I₀ hsub hgap ell₀ N
            hnonneg hbound
      _ ≤ C *
          (ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ)) * V)) ^
            (1 / 2 : ℝ) := by
        apply mul_le_mul' le_rfl
        exact ENNReal.rpow_le_rpow hscaleMass (by norm_num)
      _ = C * ENNReal.ofReal
          (directQuadraticDelta n * Real.sqrt V) := by
        rw [ennreal_dyadic_mass_rpow_half_eq_delta n hV]
  have ha : 0 < directQuadraticLowThreshold n :=
    Real.rpow_pos_of_pos (directQuadraticDelta_pos n) _
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x *
          ‖interpolationLow g (directQuadraticLowThreshold n) x‖ₑ) ≤
      C * ENNReal.ofReal
        (directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2) * V) :=
      lintegral_pairing_interpolationLow_ennreal_le_normalized_mul
        (measurable_offsetTailMaximalOn S A scale
          f.measurable_toFun ell₀ (n : ℤ)).aemeasurable
        g.measurable_toFun g.integrable_finiteSparseProof ha
        (lt_trans zero_lt_one hp) hp2 (directQuadraticDelta_pos n).le hV hU hgp
    _ = (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) := by
      dsimp only [C]
      rw [show directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2) * V =
        (directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2)) * V by ring,
        directQuadratic_low_threshold_identity]

/-- The same paper-facing low estimate with no per-offset gap premise. It is
the form used when summing over the arbitrary finite set `offsetSet`. -/
theorem lintegral_offsetTailMaximalOn_interpolationLow_le_directQuadratic_of_nonnegative_scales
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ A, scale I < N)
    (g : L0Infinity) {p V : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgp : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ≤ ENNReal.ofReal V) :
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x *
          ‖interpolationLow g (directQuadraticLowThreshold n) x‖ₑ) ≤
      (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) := by
  let C : ℝ≥0∞ := (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ)
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast n.zero_le
  have ht : 0 ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_nonneg (by norm_num) _
  have hscaleMass :
      ENNReal.ofReal
          ((2 : ℝ) ^ (-(n : ℤ)) * ∫ x in I₀.carrier, ‖f x‖) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ)) * V) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hroot ht
  have hU :
      eLpNorm (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ)) 2 volume ≤
        C * ENNReal.ofReal (directQuadraticDelta n * Real.sqrt V) := by
    calc
      eLpNorm (offsetTailMaximalOn S A scale
          (f : ℝ → ℂ) ell₀ (n : ℤ)) 2 volume ≤
        C *
          (ENNReal.ofReal
            ((2 : ℝ) ^ (-(n : ℤ)) *
              ∫ x in I₀.carrier, ‖f x‖)) ^ (1 / 2 : ℝ) :=
        eLpNorm_offsetTailMaximalOn_le_factored_of_nonnegative_scales
          hA hlam scale hscale hscaleNonneg f hn0 hM hmass I₀ hsub ell₀ N hbound
      _ ≤ C *
          (ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ)) * V)) ^
            (1 / 2 : ℝ) := by
        apply mul_le_mul' le_rfl
        exact ENNReal.rpow_le_rpow hscaleMass (by norm_num)
      _ = C * ENNReal.ofReal
          (directQuadraticDelta n * Real.sqrt V) := by
        rw [ennreal_dyadic_mass_rpow_half_eq_delta n hV]
  have ha : 0 < directQuadraticLowThreshold n :=
    Real.rpow_pos_of_pos (directQuadraticDelta_pos n) _
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ (n : ℤ) x *
          ‖interpolationLow g (directQuadraticLowThreshold n) x‖ₑ) ≤
      C * ENNReal.ofReal
        (directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2) * V) :=
      lintegral_pairing_interpolationLow_ennreal_le_normalized_mul
        (measurable_offsetTailMaximalOn S A scale
          f.measurable_toFun ell₀ (n : ℤ)).aemeasurable
        g.measurable_toFun g.integrable_finiteSparseProof ha
        (lt_trans zero_lt_one hp) hp2 (directQuadraticDelta_pos n).le hV hU hgp
    _ = (directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (directQuadraticDelta n ^ (p - 1) * V) := by
      dsimp only [C]
      rw [show directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2) * V =
        (directQuadraticDelta n *
          directQuadraticLowThreshold n ^ (1 - p / 2)) * V by ring,
        directQuadratic_low_threshold_identity]

/-- The genuine direct localized tail paired with the low truncation of the
testing function. The right side is exactly the square root of the checked
projected-plus-remainder energy times the standard low-truncation factor. -/
theorem lintegral_offsetTailMaximalOn_interpolationLow_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f g : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (ell₀ : ℤ) (N : ℕ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N)
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (hp2 : p ≤ 2) :
    let B : ℝ≥0∞ :=
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)
    let C : ℝ≥0∞ := ENNReal.ofReal
      ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)
    (∫⁻ x, offsetTailMaximalOn S A scale (f : ℝ → ℂ) ell₀ s x *
        ‖interpolationLow g a x‖ₑ) ≤
      (1372 * (B + C)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) := by
  dsimp only
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale (f : ℝ → ℂ) ell₀ s x *
        ‖interpolationLow g a x‖ₑ) ≤
      eLpNorm (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ s) 2 volume *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) :=
      lintegral_pairing_interpolationLow_ennreal_le
        (measurable_offsetTailMaximalOn S A scale
          f.measurable_toFun ell₀ s).aemeasurable
        g.measurable_toFun g.integrable_finiteSparseProof ha hp hp2
    _ ≤ (1372 *
        ((4 + 128 *
          (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
          ENNReal.ofReal
            ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                (2 : ℝ) ^ (-s)) *
              ∫ x in I₀.carrier, ‖f x‖) +
          ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M) * Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
                Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2))) ^
          (1 / 2 : ℝ) *
        (ENNReal.ofReal (a ^ (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) := by
      apply mul_le_mul' _ le_rfl
      exact eLpNorm_offsetTailMaximalOn_le_root
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap ell₀ N hnonneg hbound


end
end KrauseLaceyQuadraticDirectLowPairing
end QuadraticCarleson
