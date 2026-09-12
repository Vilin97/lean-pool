/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
A jointly measurable field which represents an actual Bochner L² family belongs
to the product L² space, with exactly the same norm.  This realizes nested
space/angle or time/space estimates without changing any derivative constants.
-/

@[expose] public section


noncomputable section

namespace EulerLpBochnerRealization

open MeasureTheory Filter
open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

theorem norm_sq_eq_integral (u : Lp E 2 μ) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp u)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _)]
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

theorem fiber_integral (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) :
    (fun x => ∫ y, ‖f (x,y)‖^2 ∂ν) =ᵐ[μ] fun x => ‖w x‖^2 := by
  filter_upwards [hrep] with x hx
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]

variable [SFinite ν]

theorem field_memLp (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) :
    MemLp f 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm hf).2
  apply (integrable_prod_iff (hf.norm.pow 2)).2
  constructor
  · filter_upwards [hrep] with x hx
    have hm : MemLp (fun y => f (x,y)) 2 ν := (memLp_congr_ae hx).1 (Lp.memLp (w x))
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  · have ho : Integrable (fun x => ‖w x‖^2) μ :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).1 (Lp.memLp w)
    apply ho.congr
    filter_upwards [fiber_integral w f hrep] with x hx
    change ‖w x‖^2 = ∫ y, ‖‖f (x,y)‖^2‖ ∂ν
    simpa only [norm_pow, norm_norm] using hx.symm

/-- The genuine product-space representative of the given nested L² element. -/
def realization (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) : Lp E 2 (μ.prod ν) :=
  (field_memLp w f hf hrep).toLp f

theorem realization_ae (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) :
    (realization w f hf hrep : α × β → E) =ᵐ[μ.prod ν] f :=
  (field_memLp w f hf hrep).coeFn_toLp

variable [SFinite μ]

/-- Fubini preserves the exact L² norm, with no angle or dimension factor. -/
theorem realization_norm (w : Lp (Lp E 2 ν) 2 μ) (f : α × β → E)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (w x : β → E) =ᵐ[ν] fun y => f (x, y)) :
    ‖realization w f hf hrep‖ = ‖w‖ := by
  have he : ‖realization w f hf hrep‖^2 = ‖w‖^2 := by
    rw [norm_sq_eq_integral]
    calc
      _ = ∫ z, ‖f z‖^2 ∂μ.prod ν := by
        apply integral_congr_ae
        filter_upwards [realization_ae w f hf hrep] with z hz
        rw [hz]
      _ = ∫ x, ∫ y, ‖f (x,y)‖^2 ∂ν ∂μ :=
        integral_prod _ ((memLp_two_iff_integrable_sq_norm hf).1 (field_memLp w f hf hrep))
      _ = ∫ x, ‖w x‖^2 ∂μ := integral_congr_ae (fiber_integral w f hrep)
      _ = _ := (norm_sq_eq_integral w).symm
  nlinarith [norm_nonneg (realization w f hf hrep), norm_nonneg w]

end EulerLpBochnerRealization
