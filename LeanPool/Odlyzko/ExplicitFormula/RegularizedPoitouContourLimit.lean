/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouEstimateLimit
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouSubtractedContour
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Regularized Poitou Contour Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A regularized subtracted horizontal vanishing used in the Odlyzko-bound argument. -/
def RegularizedSubtractedHorizontalVanishing
    (y δ b : ℝ) : Prop :=
  ∃ T : ℕ → ℝ,
    Tendsto T atTop atTop ∧
    (∀ n, 0 < T n ∧
      ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-(T n)) (T n),
        (z.re = 1 - b ∨ z.re = b ∨
          z.im = -(T n) ∨ z.im = T n) →
          poleClearedCompletedDedekindZetaContinuation K z ≠ 0) ∧
    Tendsto
      (fun n ↦
        horizontalIntegral
            (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
              (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
                completedZetaPoleLogDeriv s))
            (1 - b) b (-(T n)) -
          horizontalIntegral
            (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
              (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
                completedZetaPoleLogDeriv s))
            (1 - b) b (T n))
      atTop (𝓝 0)

theorem regularizedRightVerticalLowerBound_of_horizontalVanishing
    {y δ b : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) (hb : 1 < b)
    (hvanish : RegularizedSubtractedHorizontalVanishing K y δ b) :
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (b + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (b + t * I) -
            completedZetaPoleLogDeriv (b + t * I))).re := by
  obtain ⟨T, hT, hboundary, hhorizontal⟩ := hvanish
  let q : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (b + t * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (b + t * I) -
        completedZetaPoleLogDeriv (b + t * I))
  let H : ℕ → ℂ := fun n ↦
    horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (1 - b) b (-(T n)) -
      horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (1 - b) b (T n)
  let V : ℕ → ℂ := fun n ↦ ∫ t : ℝ in -(T n)..T n, q t
  let R : ℂ := ∫ t : ℝ, q t
  have hq : Integrable q :=
    integrable_poitouTransform_regularized_mul_logDeriv_sub_poles
      K hδ y hb
  have hV : Tendsto V atTop (𝓝 R) := by
    exact intervalIntegral_tendsto_integral hq
      ((tendsto_neg_atBot_iff).2 hT) hT
  have hH : Tendsto H atTop (𝓝 0) := hhorizontal
  have hfinite :
      ∀ n, -4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
        (H n + 2 * (I * V n)).im := by
    intro n
    have h :=
      regularizedPoitou_subtracted_centeredRectangle_im_lowerBound
        K hy hδ hb (hboundary n).1 (hboundary n).2
    simpa only [H, V, q, verticalSegmentIntegral, smul_eq_mul,
      ofReal_ofNat, mul_assoc] using h
  have hcomplex :
      Tendsto (fun n ↦ H n + 2 * (I * V n))
        atTop (𝓝 (2 * (I * R))) := by
    simpa only [zero_add] using
      hH.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul hV))
  have him :
      Tendsto (fun n ↦ (H n + 2 * (I * V n)).im)
        atTop (𝓝 ((2 * (I * R)).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  have hlim :
      -4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
        (2 * (I * R)).im :=
    ge_of_tendsto him (Filter.Eventually.of_forall hfinite)
  change
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤ R.re
  have hvalue : (2 * (I * R)).im = 2 * R.re := by simp
  grind

theorem regularizedRightVerticalLowerBound_of_forall_horizontalVanishing
    {y b : ℝ} (hy : y ≠ 0) (hb : 1 < b)
    (hvanish : ∀ δ : ℝ, 0 < δ →
      RegularizedSubtractedHorizontalVanishing K y δ b) :
    RegularizedRightVerticalLowerBound K y b := by
  intro δ hδ
  exact regularizedRightVerticalLowerBound_of_horizontalVanishing
    K hy hδ hb (hvanish δ hδ)

end NumberField.Odlyzko
