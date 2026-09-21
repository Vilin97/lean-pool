/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PrincipalValueDistribution
import Mathlib.MeasureTheory.Group.Integral

/-!
# Symmetric truncations of the principal-value distribution

The direct cancelled pairing defining `p.v. (1 / x)` is the limit of the
ordinary integrals over `{x | ε < |x|}` as `ε → 0+`. The proof first removes
the constant term on a symmetric annulus using the measure-preserving
change of variables `x ↦ -x`. The remaining error is the integral of the
bounded cancelled integrand over `[-ε, ε]`, yielding an explicit bound by
`2 * ε` times the first derivative Schwartz seminorm.
-/

open MeasureTheory Set Filter
open scoped SchwartzMap Topology

namespace QuadraticCarleson

private theorem symmetricAnnulus_constant_integral (ε : ℝ) (c : ℂ) :
    (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, c / (x : ℂ)) = 0 := by
  let s : Set ℝ := {x : ℝ | ε < |x| ∧ |x| < 1}
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const continuous_abs).measurableSet.inter
      (isOpen_lt continuous_abs continuous_const).measurableSet
  let F : ℝ → ℂ := s.indicator (fun x ↦ c / (x : ℂ))
  have hodd : (fun x ↦ F (-x)) = fun x ↦ -F x := by
    funext x
    simp only [F, s, Set.indicator, Set.mem_ofPred_eq, abs_neg, Complex.ofReal_neg,
      div_neg]
    split_ifs <;> simp
  rw [← integral_indicator hs]
  change (∫ x : ℝ, F x) = 0
  apply self_eq_neg.mp
  calc
    (∫ x : ℝ, F x) = ∫ x : ℝ, F (-x) := (integral_neg_eq_self F volume).symm
    _ = -(∫ x : ℝ, F x) := by rw [hodd, integral_neg]

/-- The constant term cancels on the symmetric annulus, leaving the
regularized near integral and the unmodified far integral. -/
theorem principalValueTruncation_eq_near_add_far {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ε < 1) (f : 𝓢(ℝ, ℂ)) :
    principalValueTruncation ε f =
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, principalValueNearIntegrand f x) +
        ∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ) := by
  let a : Set ℝ := {x : ℝ | ε < |x| ∧ |x| < 1}
  have horig : IntegrableOn (fun x : ℝ ↦ f x / (x : ℂ)) a :=
    (integrableOn_schwartz_div_id hε f).mono_set (fun _ hx ↦ hx.1)
  have hnear : IntegrableOn (principalValueNearIntegrand f) a :=
    (integrableOn_principalValueNearIntegrand f).mono_set
      (fun _ hx ↦ abs_lt.mp hx.2)
  have hcancel : (∫ x in a, f x / (x : ℂ)) =
      ∫ x in a, principalValueNearIntegrand f x := by
    apply sub_eq_zero.mp
    rw [← integral_sub horig hnear]
    calc
      (∫ x in a, f x / (x : ℂ) - principalValueNearIntegrand f x) =
          ∫ x in a, f 0 / (x : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [principalValueNearIntegrand, sub_div]
        ring
      _ = 0 := symmetricAnnulus_constant_integral ε (f 0)
  have hset : {x : ℝ | ε < |x|} = a ∪ {x : ℝ | 1 ≤ |x|} := by
    ext x
    constructor
    · intro hx
      rcases lt_or_ge |x| 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (hx | hx)
      · exact hx.1
      · exact hε₁.trans_le hx
  have hd : Disjoint a {x : ℝ | 1 ≤ |x|} :=
    Set.disjoint_left.mpr (fun _ hx hy ↦ (not_le_of_gt hx.2) hy)
  rw [principalValueTruncation, hset,
    setIntegral_union hd (isClosed_le continuous_const continuous_abs).measurableSet
      horig (integrableOn_principalValueFarIntegrand f), hcancel]

/-- The exact truncation error is the cancelled near integrand integrated
over the deleted symmetric interval. -/
theorem principalValuePairing_sub_truncation {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ε < 1) (f : 𝓢(ℝ, ℂ)) :
    principalValuePairing f - principalValueTruncation ε f =
      ∫ x in Icc (-ε) ε, principalValueNearIntegrand f x := by
  let a : Set ℝ := {x : ℝ | ε < |x| ∧ |x| < 1}
  have hasub : a ⊆ Ioo (-1 : ℝ) 1 := fun _ hx ↦ abs_lt.mp hx.2
  have hcsub : Icc (-ε) ε ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (by linarith) hx.1, hx.2.trans_lt hε₁⟩
  have hset : Ioo (-1 : ℝ) 1 = a ∪ Icc (-ε) ε := by
    ext x
    constructor
    · intro hx
      by_cases ha : ε < |x|
      · exact Or.inl ⟨ha, abs_lt.mpr hx⟩
      · exact Or.inr (abs_le.mp (le_of_not_gt ha))
    · rintro (hx | hx)
      · exact hasub hx
      · exact hcsub hx
  have hd : Disjoint a (Icc (-ε) ε) :=
    Set.disjoint_left.mpr (fun _ hx hy ↦ (not_le_of_gt hx.1) (abs_le.mpr hy))
  have hsplit := setIntegral_union hd measurableSet_Icc
    ((integrableOn_principalValueNearIntegrand f).mono_set hasub)
    ((integrableOn_principalValueNearIntegrand f).mono_set hcsub)
  rw [← hset] at hsplit
  rw [principalValueTruncation_eq_near_add_far hε hε₁,
    principalValuePairing, hsplit]
  change _ + _ + _ - (_ + _) = _
  ring

/-- A quantitative bound for the symmetric principal-value truncation
error, in terms of the first derivative Schwartz seminorm. -/
theorem norm_principalValueTruncation_sub_pairing_le {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ε < 1) (f : 𝓢(ℝ, ℂ)) :
    ‖principalValueTruncation ε f - principalValuePairing f‖ ≤
      2 * ε * SchwartzMap.seminorm ℂ 0 1 f := by
  rw [norm_sub_rev, principalValuePairing_sub_truncation hε hε₁]
  calc
    ‖∫ x in Icc (-ε) ε, principalValueNearIntegrand f x‖ ≤
        SchwartzMap.seminorm ℂ 0 1 f * volume.real (Icc (-ε) ε) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
        (fun x _ ↦ norm_principalValueNearIntegrand_le f x)
    _ = 2 * ε * SchwartzMap.seminorm ℂ 0 1 f := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring

/-- Parissis's direct cancelled pairing is precisely the principal-value
limit of ordinary integrals with symmetric positive truncation radii. -/
theorem tendsto_principalValueTruncation (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ ↦ principalValueTruncation ε f) (𝓝[>] 0)
      (𝓝 (principalValuePairing f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g := fun ε ↦ 2 * ε * SchwartzMap.seminorm ℂ 0 1 f)
    (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with ε hε hε₁
    exact norm_principalValueTruncation_sub_pairing_le hε hε₁ f
  · have hzero : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero, zero_mul] using
      (hzero.const_mul 2).mul_const (SchwartzMap.seminorm ℂ 0 1 f)

end QuadraticCarleson
