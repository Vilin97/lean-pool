/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Actual integration of uniformly L²-bounded parameter families.
The result is proved directly on raw jointly measurable representatives,
without assuming a pre-existing Bochner path in the L² space. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace EulerLpParameterIntegral

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integral_norm_sq_eq (μ : Measure α) (f : α → E) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) = (eLpNorm f 2 μ).toReal^2 := by
  have he := EulerLpBochnerRealization.norm_sq_eq_integral (hf.toLp f)
  rw [Lp.norm_toLp] at he
  apply Eq.trans _ he.symm
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Bochner Cauchy--Schwarz against the constant function one. -/
theorem norm_integral_sq_le (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → E) (hf : MemLp f 2 ν) :
    ‖∫ s, f s ∂ν‖^2 ≤ ν.real univ*(∫ s, ‖f s‖^2 ∂ν) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hn : MemLp (fun s => ‖f s‖) (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hf.norm
  have ho : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) ν := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Eventually.of_forall (fun s => norm_nonneg (f s)))
    (Eventually.of_forall (fun _ => show (0 : ℝ) ≤ 1 by norm_num)) hn ho
  have hi : (∫ s, ‖f s‖ ∂ν) ≤
      Real.sqrt (∫ s, ‖f s‖^2 ∂ν)*Real.sqrt (ν.real univ) := by
    simpa only [mul_one, Real.rpow_two, Real.one_rpow, integral_const,
      smul_eq_mul, Real.sqrt_eq_rpow, one_pow] using h
  have hb := (norm_integral_le_integral_norm f).trans hi
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow,
    Real.sq_sqrt (integral_nonneg (fun s => sq_nonneg ‖f s‖)),
    Real.sq_sqrt (measureReal_nonneg : 0 ≤ ν.real univ), mul_comm] using hs

/-- The integral of a raw family with uniform L² bound C has L² bound
`measure(parameter space) * C`.  This applies to time integration on a
finite interval and to periodic parameter averaging. -/
theorem integral_memLp_and_bound
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure β) [SFinite μ]
    (f : α × β → E) (hf : AEStronglyMeasurable f (ν.prod μ))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ s ∂ν, MemLp (fun x => f (s, x)) 2 μ ∧
      (eLpNorm (fun x => f (s, x)) 2 μ).toReal ≤ C) :
    MemLp (fun x => ∫ s, f (s,x) ∂ν) 2 μ ∧
      (eLpNorm (fun x => ∫ s, f (s,x) ∂ν) 2 μ).toReal ≤ ν.real univ*C := by
  have hsq : AEStronglyMeasurable (fun p => ‖f p‖^2) (ν.prod μ) := hf.norm.pow 2
  have houterBound : ∀ᵐ s ∂ν, (∫ x, ‖f (s,x)‖^2 ∂μ) ≤ C^2 := by
    filter_upwards [hbound] with s hs
    rw [integral_norm_sq_eq μ _ hs.1]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hs.2 2
  have houter : Integrable (fun s => ∫ x, ‖f (s,x)‖^2 ∂μ) ν := by
    apply (integrable_const (C^2)).mono' hsq.integral_prod_right'
    filter_upwards [houterBound] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg ‖f (s,x)‖))]
    exact hs
  have hprod : Integrable (fun p => ‖f p‖^2) (ν.prod μ) := by
    apply (integrable_prod_iff hsq).2
    constructor
    · filter_upwards [hbound] with s hs
      exact (memLp_two_iff_integrable_sq_norm hs.1.aestronglyMeasurable).1 hs.1
    · simpa only [norm_pow, norm_norm] using houter
  have htime : ∀ᵐ x ∂μ, MemLp (fun s => f (s,x)) 2 ν := by
    filter_upwards [hprod.prod_left_ae, hf.prodMk_right] with x hi hm
    exact (memLp_two_iff_integrable_sq_norm hm).2 hi
  have hg : AEStronglyMeasurable (fun x => ∫ s, f (s,x) ∂ν) μ :=
    hf.prod_swap.integral_prod_right'
  have hdom : ∀ᵐ x ∂μ, ‖∫ s, f (s,x) ∂ν‖^2 ≤
      ν.real univ*(∫ s, ‖f (s,x)‖^2 ∂ν) := by
    filter_upwards [htime] with x hx
    exact norm_integral_sq_le ν _ hx
  have hright : Integrable (fun x => ν.real univ*(∫ s, ‖f (s,x)‖^2 ∂ν)) μ :=
    hprod.integral_prod_right.const_mul _
  have hg2 : Integrable (fun x => ‖∫ s, f (s,x) ∂ν‖^2) μ := by
    apply hright.mono' (hg.norm.pow 2)
    filter_upwards [hdom] with x hx
    simpa only [Pi.pow_apply, norm_pow, norm_norm] using hx
  have hgLp : MemLp (fun x => ∫ s, f (s,x) ∂ν) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hg).2 hg2
  refine ⟨hgLp,?_⟩
  have hfinal : (eLpNorm (fun x => ∫ s, f (s,x) ∂ν) 2 μ).toReal^2 ≤
      (ν.real univ*C)^2 := by
    calc
      _ = ∫ x, ‖∫ s, f (s,x) ∂ν‖^2 ∂μ := (integral_norm_sq_eq μ _ hgLp).symm
      _ ≤ ∫ x, ν.real univ*(∫ s, ‖f (s,x)‖^2 ∂ν) ∂μ := integral_mono_ae hg2 hright hdom
      _ = ν.real univ*(∫ s, ∫ x, ‖f (s,x)‖^2 ∂μ ∂ν) := by
        rw [integral_const_mul]
        exact congrArg (fun r => ν.real univ*r) (integral_integral_swap hprod).symm
      _ ≤ ν.real univ*(∫ _ : α, C^2 ∂ν) :=
        mul_le_mul_of_nonneg_left (integral_mono_ae houter (integrable_const _) houterBound)
          measureReal_nonneg
      _ = _ := by rw [integral_const]; simp only [smul_eq_mul]; ring
  exact (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg measureReal_nonneg hC)).mp hfinal

theorem intervalIntegral_memLp_and_bound
    (T : ℝ) (hT : 0 ≤ T) (μ : Measure β) [SFinite μ]
    (f : ℝ × β → E)
    (hf : AEStronglyMeasurable f ((volume.restrict (Icc 0 T)).prod μ))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ s ∂volume.restrict (Icc 0 T), MemLp (fun x => f (s, x)) 2 μ ∧
      (eLpNorm (fun x => f (s, x)) 2 μ).toReal ≤ C) :
    MemLp (fun x => ∫ s in 0..T, f (s,x)) 2 μ ∧
      (eLpNorm (fun x => ∫ s in 0..T, f (s,x)) 2 μ).toReal ≤ T*C := by
  have he := integral_memLp_and_bound (volume.restrict (Icc 0 T)) μ f hf C hC hbound
  have hfun : (fun x => ∫ s in 0..T, f (s,x)) =
      (fun x => ∫ s in Icc 0 T, f (s,x)) := by
    funext x
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  have hmass : (volume.restrict (Icc 0 T)).real univ = T := by
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.toReal_ofReal hT]
  rw [hmass] at he
  rw [hfun]
  exact he

end EulerLpParameterIntegral
