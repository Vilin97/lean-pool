/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! # RelativeError: averaging the transport duality bound

The analytic part of the low-mode trace argument is isolated here. The
remaining flow/Piola work must supply the pointwise duality inequality and its
two Cauchy--Schwarz bounds. -/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace AVenhance.Infra.Section5.RelativeError

theorem TraceAveraging.intervalIntegral_f_le_sqrt_length_mul_l2
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..t, f s) ≤
      Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) := by
  let I : Set ℝ := Set.Ioc (0 : ℝ) t
  have hsubset : I ⊆ Set.Icc (0 : ℝ) t := by
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) t) := hf.mono (by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 ht1⟩)
  have hfI : IntegrableOn f I := by
    exact (hfIcc.integrableOn_compact isCompact_Icc).mono_set hsubset
  have hf2I : IntegrableOn (fun x => f x ^ 2) I := by
    exact ((hfIcc.pow 2).integrableOn_compact isCompact_Icc).mono_set hsubset
  have honeI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I := by
    exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set hsubset
  have honeSqI : IntegrableOn (fun x : ℝ => (1 : ℝ) ^ 2) I := by
    simpa using honeI
  have hprodI : IntegrableOn (fun x => f x * 1) I := by
    simpa using hfI
  have hcs := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
    (μ := volume.restrict I) (f := f) (g := fun _ : ℝ => (1 : ℝ))
    hf2I honeSqI hprodI
  have hcsSimple :
      (∫ x in I, f x) ≤
        Real.sqrt (∫ x in I, f x ^ 2) * Real.sqrt (∫ x in I, (1 : ℝ)) := by
    simpa using hcs
  have hfconv :
      (∫ x in I, f x) = (∫ s in (0 : ℝ)..t, f s) := by
    dsimp [I]
    exact (intervalIntegral.integral_of_le ht0).symm
  have hsqconv :
      (∫ x in I, f x ^ 2) = (∫ s in (0 : ℝ)..t, f s ^ 2) := by
    dsimp [I]
    exact (intervalIntegral.integral_of_le ht0).symm
  have honeconv : (∫ x in I, (1 : ℝ)) = t := by
    calc
      (∫ x in I, (1 : ℝ)) =
          (∫ s in (0 : ℝ)..t, (1 : ℝ)) :=
        (intervalIntegral.integral_of_le ht0).symm
      _ = t := by simp [intervalIntegral.integral_const]
  have hcs' :
      (∫ s in (0 : ℝ)..t, f s) ≤
        Real.sqrt (∫ s in (0 : ℝ)..t, f s ^ 2) * Real.sqrt t := by
    rw [← hfconv, ← hsqconv, ← honeconv]
    exact hcsSimple
  have hG : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume 0 1 :=
    (hf.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hleft : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume 0 t :=
    hG.mono_set (by
      rw [Set.uIcc_of_le ht0, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_right ht1)
  have hright : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume t 1 :=
    hG.mono_set (by
      rw [Set.uIcc_of_le ht1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_left ht0)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hrest : 0 ≤ (∫ s in t..1, f s ^ 2) :=
    intervalIntegral.integral_nonneg ht1 (fun s hs => sq_nonneg (f s))
  have hsqmono :
      (∫ s in (0 : ℝ)..t, f s ^ 2) ≤
        (∫ s in (0 : ℝ)..1, f s ^ 2) := by
    rw [← hadd]
    linarith
  calc
    (∫ s in (0 : ℝ)..t, f s) ≤
        Real.sqrt (∫ s in (0 : ℝ)..t, f s ^ 2) * Real.sqrt t := hcs'
    _ ≤ Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) * Real.sqrt t := by
      exact mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hsqmono) (Real.sqrt_nonneg _)
    _ = Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) := by ring

/-- Average the transport-duality inequality on the short interval whose
length is (ν K²)⁻¹. The two displayed square-root integral bounds are the
Cauchy--Schwarz inputs on [0,T] and [0,t]. -/
theorem lowModeTrace_from_transportDuality_average
    {ν K T G S : ℝ} {f : ℝ → ℝ}
    (hν : 0 < ν) (hK : 0 < K) (hT : 0 < T) (hTle : T ≤ 1)
    (hTdef : T = (ν * K ^ 2)⁻¹)
    (_hS : 0 ≤ S)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (haverage : (∫ t in (0 : ℝ)..T, f t) ≤ Real.sqrt T * S)
    (hprefix : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, f s) ≤ Real.sqrt T * S)
    (hdual : ∀ t ∈ Set.Icc (0 : ℝ) T,
      G ≤ Real.exp 1 * f t +
        Real.exp 1 * ν * K ^ 2 * (∫ s in (0 : ℝ)..t, f s)) :
    G ≤ 2 * Real.exp 1 * K * Real.sqrt ν * S := by
  have hrootT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hrootν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hcoeff :
      Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S) =
        Real.exp 1 * K * Real.sqrt ν * S := by
    have hrootSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
    have hfactor : ν * K ^ 2 * Real.sqrt T = K * Real.sqrt ν := by
      have hsquare :
          (ν * K ^ 2 * Real.sqrt T) ^ 2 = (K * Real.sqrt ν) ^ 2 := by
        rw [mul_pow, hrootSq]
        rw [hTdef]
        field_simp [ne_of_gt (mul_pos hν (sq_pos_of_pos hK))]
        rw [Real.sq_sqrt hν.le]
      have hleft : 0 ≤ ν * K ^ 2 * Real.sqrt T := by positivity
      have hright : 0 ≤ K * Real.sqrt ν := by positivity
      exact (sq_eq_sq₀ hleft hright).mp hsquare
    calc
      Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S) =
          Real.exp 1 * (ν * K ^ 2 * Real.sqrt T) * S := by ring
      _ = Real.exp 1 * K * Real.sqrt ν * S := by rw [hfactor]; ring
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      G ≤ Real.exp 1 * f t +
        Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S) := by
    calc
      G ≤ Real.exp 1 * f t +
          Real.exp 1 * ν * K ^ 2 * (∫ s in (0 : ℝ)..t, f s) := hdual t ht
      _ ≤ _ := by
        have hprefix' := hprefix t ht
        have hnonneg : 0 ≤ Real.exp 1 * ν * K ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hprefix' hnonneg]
  have hfT : ContinuousOn f (Set.Icc (0 : ℝ) T) := hf.mono (by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hTle⟩)
  have hfInt : IntervalIntegrable f volume 0 T :=
    hfT.intervalIntegrable_of_Icc (le_of_lt hT)
  have hRhsInt : IntervalIntegrable
      (fun t => Real.exp 1 * f t +
        Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S)) volume 0 T := by
    exact (hfInt.const_mul (Real.exp 1)).add intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := T)
    hT.le intervalIntegrable_const hRhsInt hpoint
  have hint' :
      T * G ≤ Real.exp 1 * (∫ t in (0 : ℝ)..T, f t) +
        T * (Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S)) := by
    rw [intervalIntegral.integral_add (hfInt.const_mul (Real.exp 1))
      intervalIntegrable_const] at hint
    simp only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    nlinarith [hint]
  have hupper :
      Real.exp 1 * (∫ t in (0 : ℝ)..T, f t) +
        T * (Real.exp 1 * ν * K ^ 2 * (Real.sqrt T * S)) ≤
      Real.exp 1 * (Real.sqrt T * S) +
        T * (Real.exp 1 * K * Real.sqrt ν * S) := by
    have hexp : 0 ≤ Real.exp 1 := Real.exp_nonneg _
    have hfirst := mul_le_mul_of_nonneg_left haverage hexp
    rw [hcoeff]
    exact add_le_add hfirst le_rfl
  have hbound :
      T * G ≤ Real.exp 1 * (Real.sqrt T * S) +
        T * (Real.exp 1 * K * Real.sqrt ν * S) :=
    hint'.trans hupper
  have hrootRelation : (Real.sqrt T)⁻¹ = K * Real.sqrt ν := by
    calc
      (Real.sqrt T)⁻¹ =
          (Real.sqrt ((ν * K ^ 2)⁻¹))⁻¹ := by rw [hTdef]
      _ = Real.sqrt (ν * K ^ 2) := by rw [Real.sqrt_inv, inv_inv]
      _ = Real.sqrt ν * Real.sqrt (K ^ 2) := Real.sqrt_mul hν.le _
      _ = K * Real.sqrt ν := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hK]
        ring
  have hdiv : G ≤
      (Real.exp 1 * (Real.sqrt T * S) +
        T * (Real.exp 1 * K * Real.sqrt ν * S)) / T := by
    apply (le_div_iff₀ hT).2
    simpa [mul_comm] using hbound
  have hfirst :
      Real.exp 1 * (Real.sqrt T * S) / T =
        Real.exp 1 * K * Real.sqrt ν * S := by
    have hratio : Real.sqrt T / T = (Real.sqrt T)⁻¹ := by
      field_simp [ne_of_gt hT, ne_of_gt hrootT]
      nlinarith [Real.sq_sqrt hT.le]
    calc
      Real.exp 1 * (Real.sqrt T * S) / T =
          Real.exp 1 * S * (Real.sqrt T / T) := by ring
      _ = Real.exp 1 * S * (Real.sqrt T)⁻¹ := by rw [hratio]
      _ = Real.exp 1 * K * Real.sqrt ν * S := by rw [hrootRelation]; ring
  have hfinal :
      (Real.exp 1 * (Real.sqrt T * S) +
        T * (Real.exp 1 * K * Real.sqrt ν * S)) / T =
        2 * Real.exp 1 * K * Real.sqrt ν * S := by
    rw [add_div, hfirst]
    field_simp [ne_of_gt hT]
    ring
  rw [hfinal] at hdiv
  exact hdiv

/-- Cauchy--Schwarz supplies both segment bounds needed by the averaged
transport-duality estimate from the full time-interval L² norm. -/
theorem lowModeTrace_from_transportDuality
    {ν K T G : ℝ} {f : ℝ → ℝ}
    (hν : 0 < ν) (hK : 0 < K) (hT : 0 < T) (hTle : T ≤ 1)
    (hTdef : T = (ν * K ^ 2)⁻¹)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hdual : ∀ t ∈ Set.Icc (0 : ℝ) T,
      G ≤ Real.exp 1 * f t +
        Real.exp 1 * ν * K ^ 2 * (∫ s in (0 : ℝ)..t, f s)) :
    G ≤ 2 * Real.exp 1 * K * Real.sqrt ν *
      Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) := by
  let S : ℝ := Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have haverage :
      (∫ t in (0 : ℝ)..T, f t) ≤ Real.sqrt T * S := by
    have h := TraceAveraging.intervalIntegral_f_le_sqrt_length_mul_l2 hf
      (le_of_lt hT) hTle
    simpa [S] using h
  have hprefix : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, f s) ≤ Real.sqrt T * S := by
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hTle
    have h := TraceAveraging.intervalIntegral_f_le_sqrt_length_mul_l2 hf ht.1 ht1
    have hroot : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
    have hrootS := mul_le_mul_of_nonneg_right hroot hS
    simpa [S, mul_comm] using h.trans hrootS
  exact lowModeTrace_from_transportDuality_average
    hν hK hT hTle hTdef hS hf haverage hprefix hdual

end AVenhance.Infra.Section5.RelativeError

end
