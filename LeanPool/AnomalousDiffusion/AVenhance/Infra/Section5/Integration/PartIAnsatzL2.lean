/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.IndyStepDownPartI

/-! # `L²(𝕋²)` bookkeeping for the ansatz estimate `e.tildethetam.to.Tm`

Elementary facts about the `l2NormSq` for continuous functions: the square of a continuous
function is integrable on the unit cube, pointwise domination by a continuous function
dominates `l2NormSq`, scaling by a nonnegative constant, and the triangle inequality for
`|f| + |g|`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- The square of a continuous function is integrable on the unit cube. -/
theorem integrableOn_sq_unitCube_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn (fun x => f x ^ 2) unitCube := by
  have hbase := (memL2On_unitCube_of_continuous hf).integrable_norm_rpow (by norm_num)
    (by norm_num)
  change Integrable (fun x => f x ^ 2) (volume.restrict unitCube)
  convert hbase using 1
  norm_num [Real.norm_eq_abs, sq_abs, Real.rpow_natCast]

/-- Pointwise domination by a continuous function dominates the `L²` norm. -/
theorem sqrt_l2NormSq_le_of_abs_le {f g : Vec 2 → ℝ} (hg : Continuous g)
    (h : ∀ x, |f x| ≤ g x) :
    Real.sqrt (l2NormSq f) ≤ Real.sqrt (l2NormSq g) := by
  refine Real.sqrt_le_sqrt ?_
  unfold l2NormSq
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (integrableOn_sq_unitCube_of_continuous hg) (Filter.Eventually.of_forall fun x => ?_)
  change f x ^ 2 ≤ g x ^ 2
  rw [← sq_abs (f x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2

theorem sqrt_l2NormSq_const_mul {c : ℝ} (hc : 0 ≤ c) (f : Vec 2 → ℝ) :
    Real.sqrt (l2NormSq (fun x => c * f x)) = c * Real.sqrt (l2NormSq f) := by
  unfold l2NormSq
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem l2NormSq_abs (f : Vec 2 → ℝ) : l2NormSq (fun x => |f x|) = l2NormSq f := by
  simp [l2NormSq, sq_abs]

/-- Triangle inequality for `|f| + |g|` with continuous `f, g`. -/
theorem sqrt_l2NormSq_abs_add_le {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Real.sqrt (l2NormSq (fun x => |f x| + |g x|)) ≤
      Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) := by
  have h := Infra.Section5.sqrt_l2NormSq_add_le
    (memL2On_unitCube_of_continuous hf.abs) (memL2On_unitCube_of_continuous hg.abs)
  rwa [l2NormSq_abs, l2NormSq_abs] at h

/-- Triangle inequality for continuous `f, g`. -/
theorem sqrt_l2NormSq_add_le_of_continuous {f g : Vec 2 → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    Real.sqrt (l2NormSq (fun x => f x + g x)) ≤
      Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) :=
  Infra.Section5.sqrt_l2NormSq_add_le (memL2On_unitCube_of_continuous hf)
    (memL2On_unitCube_of_continuous hg)

end AVenhance.Infra.Section5.Integration
