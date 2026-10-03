/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Inequality
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Abstract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.FiniteNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy

/-! # The integrated energy inequality for `w = u - v`

For `t ∈ [0,1]`:
`∫ w(t)² + κ ∫₀ᵗ ∫ |∇w|² ≤ ∫ w(0)² + κ⁻¹ ‖f‖²_{L²(0,1;HDot⁻¹)}`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Section5 AVenhance.Infra.Classical

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

/-- Slice energy gradient `∫ |∇u(s) - ∇v(s)|²` over the unit cube. -/
def errGrad (u v : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCube, vecNormSq (spaceGrad (u s) x - spaceGrad (v s) x)

theorem errGrad_nonneg (u v : ℝ → Vec 2 → ℝ) (s : ℝ) : 0 ≤ errGrad u v s :=
  integral_nonneg fun _ => vecNormSq_nonneg _

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

namespace ForcedSetup

/-- The error gradient is jointly continuous on `[0,∞) × ℝ²`. -/
theorem errGrad_jointContinuousOn (S : ForcedSetup φ κ θ₀ u v) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2 - spaceGrad (v p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  (spaceGrad_continuousOn_one S.hu1).sub (spaceGrad_continuousOn_one S.hv1)

theorem errGrad_continuousOn (S : ForcedSetup φ κ θ₀ u v) :
    ContinuousOn (errGrad u v) (Set.Icc (0 : ℝ) 1) := by
  have hV : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2 - spaceGrad (v p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    S.errGrad_jointContinuousOn.mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)
  exact LeftToShow.continuousOn_integral_unitCube
    (h := fun s x => vecNormSq (spaceGrad (u s) x - spaceGrad (v s) x))
    (LeftToShow.continuous_vecNormSq_two.comp_continuousOn hV)

theorem errGrad_eq (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 ≤ t) :
    errGrad u v t = gradNormSq (spaceGrad fun y => u t y - v t y) := by
  have h := smooth_spaceGrad_sub (classicalSmooth_slice_nonneg S.hu.1 ht) (S.hvs t ht)
  unfold errGrad gradNormSq
  rw [h]

/-- Continuity of the error energy on `[0,1]`. -/
theorem errEnergy_continuousOn (S : ForcedSetup φ κ θ₀ u v) :
    ContinuousOn (fun t => ∫ x in unitCell 2, (u t x - v t x) ^ 2) (Set.Icc (0 : ℝ) 1) := by
  have hJ : ContinuousOn (fun p : ℝ × Vec 2 => (u p.1 p.2 - v p.1 p.2) ^ 2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    ((S.hw1.continuousOn).pow 2).mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)
  have h := LeftToShow.continuousOn_integral_unitCube
    (h := fun t x => (u t x - v t x) ^ 2) hJ
  refine h.congr fun t _ => ?_
  exact integral_unitCell_eq_unitCube _

/-- Continuity of the energy rate on `(0,∞)`. -/
theorem energyRate_continuousOn (S : ForcedSetup φ κ θ₀ u v) :
    ContinuousOn (fun t => ∫ x in unitCell 2,
      2 * (u t x - v t x) * deriv (fun s => u s x - v s x) t) (Set.Ioi (0 : ℝ)) := by
  have hW := S.hw1Open
  have hJ : ContinuousOn (Function.uncurry fun t x =>
      2 * (u t x - v t x) * deriv (fun s => u s x - v s x) t)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℝ × Vec 2 => 2 * (u p.1 p.2 - v p.1 p.2) *
        fderiv ℝ (Function.uncurry fun t x => u t x - v t x) p ((1 : ℝ), (0 : Vec 2)))
        classicalPositiveTimeDomain :=
      (continuousOn_const.mul hW.continuousOn).mul (continuousOn_timePartial_one hW)
    refine h1.congr ?_
    rintro ⟨s, x⟩ hp
    have hs : 0 < s := hp.1
    simp only [Function.uncurry]
    rw [deriv_timeSection_eq hW hs x]
  exact continuousOn_integral_unitCell_Ioi (H := fun t x =>
    2 * (u t x - v t x) * deriv (fun s => u s x - v s x) t) hJ

end ForcedSetup

/-- The integrated forced energy inequality. -/
theorem integrated_energy_bound (S : ForcedSetup φ κ θ₀ u v)
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x in unitCell 2, (u t x - v t x) ^ 2) + κ * ∫ s in (0 : ℝ)..t, errGrad u v s ≤
        (∫ x in unitCell 2, (u 0 x - v 0 x) ^ 2) +
          (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal ^ 2 / κ := by
  intro t ht
  set f : ℝ → Vec 2 → ℝ := fun s x => advDiffOp (streamVel φ) κ v s x with hf
  have hfc : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) :=
    S.forcing_continuousOn.mono (Set.prod_mono Set.Ioo_subset_Ioi_self le_rfl)
  have hm := aemeasurable_hMinusOneNorm_of_continuousOn hfc
  have hgint := Energy.integrable_toReal_sq hm hfin
  have hae := Energy.ae_hMinusOneNorm_ne_top hm hfin
  have hF2 := Energy.integral_toReal_sq_eq hm hfin
  set g : ℝ → ℝ := fun s => (hMinusOneNorm (f s)).toReal ^ 2 with hg
  have hG := S.errGrad_continuousOn
  have hGint : IntegrableOn (errGrad u v) (Set.Ioo 0 1) :=
    (hG.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  set h : ℝ → ℝ := fun s => g s / κ - κ * errGrad u v s with hh
  have hhint : IntegrableOn h (Set.Ioo 0 1) :=
    (hgint.div_const κ).sub' (hGint.const_mul κ)
  have hineq : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (∫ x in unitCell 2, 2 * (u s x - v s x) * deriv (fun r => u r x - v r x) s) ≤ h s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hae] with s hs hsfin
    have := S.energy_inequality hs.1 hsfin
    rw [← S.errGrad_eq hs.1.le] at this
    simp only [hh, hg, hf]
    have hκ := S.hκ
    rw [le_sub_iff_add_le]
    linarith
  have hEd : ∀ s, 0 < s → HasDerivAt (fun r => ∫ x in unitCell 2, (u r x - v r x) ^ 2)
      (∫ x in unitCell 2, 2 * (u s x - v s x) * deriv (fun r => u r x - v r x) s) s :=
    fun s hs => energy_hasDerivAt_one (g := fun r x => u r x - v r x) S.hw1 hs
  have hmain := sub_le_integral_of_deriv_le_ae S.errEnergy_continuousOn hEd
    S.energyRate_continuousOn hhint hineq t ht
  -- integrate `h`
  have hgI : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hgint).mono_set
      (Set.Ioc_subset_Ioc le_rfl ht.2)
  have hGI : IntervalIntegrable (errGrad u v) volume 0 t :=
    (hG.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hsplit : ∫ s in (0 : ℝ)..t, h s =
      (∫ s in (0 : ℝ)..t, g s) / κ - κ * ∫ s in (0 : ℝ)..t, errGrad u v s := by
    simp only [hh]
    rw [intervalIntegral.integral_sub (hgI.div_const κ) (hGI.const_mul κ),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  have hgnn : ∀ s, 0 ≤ g s := fun s => sq_nonneg _
  have hgmono : ∫ s in (0 : ℝ)..t, g s ≤ ∫ s in (0 : ℝ)..1, g s := by
    have h1I : IntervalIntegrable g volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 hgint
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall hgnn) h1I
  have hg1 : ∫ s in (0 : ℝ)..1, g s =
      (timeHMinusOneNorm f).toReal ^ 2 := by
    rw [hF2, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hκ := S.hκ
  have hdiv : (∫ s in (0 : ℝ)..t, g s) / κ ≤ (timeHMinusOneNorm f).toReal ^ 2 / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le
    linarith
  rw [hsplit] at hmain
  linarith

end AVenhance.Infra.Section5.Integration.Energy

end
