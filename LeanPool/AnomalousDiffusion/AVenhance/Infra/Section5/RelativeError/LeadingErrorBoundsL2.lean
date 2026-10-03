/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeVectorTriangle

/-! # `L²((0,1)×𝕋²)` bookkeeping for the leading-error estimate

Elementary measure-theoretic facts used to turn pointwise bounds on the remainder fields of
`e.grad.tildetheta.again` into `spaceTimeGradNormSq` bounds: integrability of functions continuous
on `[0,∞) × ℝ²` over the time cell, the scalar `L²` triangle inequality, and the comparison
`‖F‖_{L²} ≤ 2 ‖B‖_{L²}` when every component of `F` is dominated by a continuous `B`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- Compact closure of the time cell. -/
def LeadingErrorBoundsL2.closedTimeCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem LeadingErrorBoundsL2.isCompact_closedTimeCell : IsCompact
    LeadingErrorBoundsL2.closedTimeCell :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

theorem LeadingErrorBoundsL2.timeCube_subset_closedTimeCell : timeCube ⊆
    LeadingErrorBoundsL2.closedTimeCell :=
  Set.prod_mono Set.Ioo_subset_Icc_self (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)

theorem LeadingErrorBoundsL2.closedTimeCell_subset :
    LeadingErrorBoundsL2.closedTimeCell ⊆ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) :=
  fun _ hp => ⟨hp.1.1, trivial⟩

/-- Functions continuous on `[0,∞) × ℝ²` are integrable on the time cell. -/
theorem integrable_timeCube_of_continuousOn {f : ℝ × Vec 2 → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Integrable f (volume.restrict timeCube) :=
  ((hf.mono LeadingErrorBoundsL2.closedTimeCell_subset).integrableOn_compact
      LeadingErrorBoundsL2.isCompact_closedTimeCell).mono_set
    LeadingErrorBoundsL2.timeCube_subset_closedTimeCell

theorem measurableSet_timeCube : MeasurableSet timeCube :=
  measurableSet_Ioo.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)

theorem vecNormSq_nonneg_of_vec2 (v : Vec 2) : 0 ≤ vecNormSq v := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

theorem LeadingErrorBoundsL2.vecNormSq_embed (a : ℝ) : vecNormSq (![a, 0] : Vec 2) = a ^ 2 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two, sq]

theorem LeadingErrorBoundsL2.embed_add (a b : ℝ) : (![a, 0] : Vec 2) + ![b, 0] = ![a + b, 0] := by
  ext i
  fin_cases i <;> simp

/-- Scalar `L²` triangle inequality on the time cell. -/
theorem sqrt_setIntegral_sq_add_le {f g : ℝ × Vec 2 → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Real.sqrt (∫ p in timeCube, (f p + g p) ^ 2) ≤
      Real.sqrt (∫ p in timeCube, f p ^ 2) + Real.sqrt (∫ p in timeCube, g p ^ 2) := by
  have hf2 : ContinuousOn (fun p => f p ^ 2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hf.pow 2
  have hg2 : ContinuousOn (fun p => g p ^ 2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hg.pow 2
  have key := relative_vector_integral_L2_add (μ := volume.restrict timeCube)
    (f := fun p => (![f p, 0] : Vec 2)) (g := fun p => (![g p, 0] : Vec 2))
    (by simpa only [LeadingErrorBoundsL2.vecNormSq_embed] using
        integrable_timeCube_of_continuousOn hf2)
    (by simpa only [LeadingErrorBoundsL2.vecNormSq_embed] using
        integrable_timeCube_of_continuousOn hg2)
    (by
      have := integrable_timeCube_of_continuousOn (hf.mul hg)
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [vecDot, Fin.sum_univ_two])
  simpa only [LeadingErrorBoundsL2.embed_add, LeadingErrorBoundsL2.vecNormSq_embed] using key

theorem sqrt_setIntegral_sq_const_mul {c : ℝ} (hc : 0 ≤ c) (f : ℝ × Vec 2 → ℝ) :
    Real.sqrt (∫ p in timeCube, (c * f p) ^ 2) = c * Real.sqrt (∫ p in timeCube, f p ^ 2) := by
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

end AVenhance.Infra.Section5.RelativeError
