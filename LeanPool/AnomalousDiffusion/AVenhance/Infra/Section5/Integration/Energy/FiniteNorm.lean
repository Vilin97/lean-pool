/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools

/-! # Consequences of `timeHMinusOneNorm f ≠ ⊤`

With measurability of `t ↦ ‖f t‖_{HDot⁻¹}` on `(0,1)`, finiteness of the time norm gives: the norm
    is
finite for a.e. `t ∈ (0,1)`, its square is integrable, and the real square of
`(timeHMinusOneNorm f).toReal` is the integral of the squares. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance AVenhance.Infra.Section5

section

variable {f : ℝ → Vec 2 → ℝ}

theorem FiniteNorm.lintegral_ne_top_of_timeNorm (hfin : timeHMinusOneNorm f ≠ ⊤) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ^ 2 ≠ ⊤ := by
  intro h
  apply hfin
  unfold timeHMinusOneNorm
  rw [h]
  exact ENNReal.top_rpow_of_pos (by norm_num)

theorem FiniteNorm.aemeasurable_sq
    (hm : AEMeasurable (fun t => hMinusOneNorm (f t)) (volume.restrict (Set.Ioo (0 : ℝ) 1))) :
    AEMeasurable (fun t => hMinusOneNorm (f t) ^ 2) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  hm.pow_const 2

/-- Almost every slice has finite `HDot⁻¹` norm. -/
theorem ae_hMinusOneNorm_ne_top
    (hm : AEMeasurable (fun t => hMinusOneNorm (f t)) (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hfin : timeHMinusOneNorm f ≠ ⊤) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), hMinusOneNorm (f t) ≠ ⊤ := by
  have h := ae_lt_top' (FiniteNorm.aemeasurable_sq hm) (FiniteNorm.lintegral_ne_top_of_timeNorm
      hfin)
  filter_upwards [h] with t ht hT
  rw [hT] at ht
  simp at ht

/-- The squared real norms are integrable on `(0,1)`. -/
theorem integrable_toReal_sq
    (hm : AEMeasurable (fun t => hMinusOneNorm (f t)) (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hfin : timeHMinusOneNorm f ≠ ⊤) :
    Integrable (fun t => (hMinusOneNorm (f t)).toReal ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have h := integrable_toReal_of_lintegral_ne_top (FiniteNorm.aemeasurable_sq hm)
    (FiniteNorm.lintegral_ne_top_of_timeNorm hfin)
  simpa [ENNReal.toReal_pow] using h

/-- `(timeHMinusOneNorm f).toReal ^ 2` is the integral of the squared real norms. -/
theorem integral_toReal_sq_eq
    (hm : AEMeasurable (fun t => hMinusOneNorm (f t)) (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hfin : timeHMinusOneNorm f ≠ ⊤) :
    (timeHMinusOneNorm f).toReal ^ 2 =
      ∫ t in Set.Ioo (0 : ℝ) 1, (hMinusOneNorm (f t)).toReal ^ 2 := by
  have hint := integral_toReal (FiniteNorm.aemeasurable_sq hm)
    (ae_lt_top' (FiniteNorm.aemeasurable_sq hm) (FiniteNorm.lintegral_ne_top_of_timeNorm hfin))
  simp only [ENNReal.toReal_pow] at hint
  rw [hint]
  unfold timeHMinusOneNorm
  rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt ENNReal.toReal_nonneg

end

end AVenhance.Infra.Section5.Integration.Energy

end
