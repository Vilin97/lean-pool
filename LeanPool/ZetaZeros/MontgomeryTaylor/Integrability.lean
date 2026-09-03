/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.MontgomeryTaylor.TestFunction

/-!
# Interval-integrability of the integrands

Side conditions only: `f_0` against the linear, `max` and shifted-`max` kernels must be
interval-integrable, and the outer integral needs a continuous integrand.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- `extremalTest` is interval-integrable on any interval. -/
lemma extremalTest_intervalIntegrable_gen (p q : ℝ) :
    IntervalIntegrable extremalTest MeasureTheory.volume p q := by
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  apply extremalTest_integrableOn
  rw [Set.uIcc_eq_union]
  exact lt_of_le_of_lt (measure_union_le _ _)
    (by exact ENNReal.add_lt_top.mpr ⟨measure_Icc_lt_top, measure_Icc_lt_top⟩)

/-- `(β + t) · f₀ β` and `max(β+t, 0) · f₀ β` are interval-integrable on any interval. -/
lemma linTest_intervalIntegrable (t p q : ℝ) :
    IntervalIntegrable (fun β => (β + t) * extremalTest β) MeasureTheory.volume p q :=
  (extremalTest_intervalIntegrable_gen p q).continuousOn_mul
    (by fun_prop : ContinuousOn (fun β => β + t) (Set.uIcc p q))

lemma maxTest_intervalIntegrable (t p q : ℝ) :
    IntervalIntegrable (fun β => max (β + t) 0 * extremalTest β) MeasureTheory.volume p q :=
  (extremalTest_intervalIntegrable_gen p q).continuousOn_mul
    (by fun_prop : ContinuousOn (fun β => max (β + t) 0) (Set.uIcc p q))

/-- `max(c - v, 0) · f₀ v` is interval-integrable in `v` on any interval. -/
lemma maxSubTest_intervalIntegrable (c p q : ℝ) :
    IntervalIntegrable (fun v => max (c - v) 0 * extremalTest v) MeasureTheory.volume p q :=
  (extremalTest_intervalIntegrable_gen p q).continuousOn_mul
    (by fun_prop : ContinuousOn (fun v => max (c - v) 0) (Set.uIcc p q))

/-- For a jointly continuous kernel `K`, the outer integrand
    `t ↦ f₀ t · ∫ v in -1/2..1/2, K t v · f₀ v` is interval-integrable on `[-1/2,1/2]`. -/
lemma outer_intervalIntegrable (K : ℝ → ℝ → ℝ) (hK : Continuous (Function.uncurry K)) :
    IntervalIntegrable
      (fun t => extremalTest t * ∫ v in (-(1:ℝ)/2)..(1/2), K t v * extremalTest v)
      MeasureTheory.volume (-(1:ℝ)/2) (1/2) := by
  apply ContinuousOn.intervalIntegrable
  apply extremalTest_continuousOn.mul
  -- rewrite the inner kernel to the continuous cos-form on [-1/2,1/2]
  have hcont : Continuous (fun t => ∫ v in (-(1:ℝ)/2)..(1/2),
      K t v * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hK.comp (continuous_fst.prodMk continuous_snd)).mul (by fun_prop)
  apply ContinuousOn.congr hcont.continuousOn
  intro t _
  apply intervalIntegral.integral_congr
  intro v hv
  simp only
  rw [extremalTest_eqOn_uIcc hv]

end ZetaZeros
