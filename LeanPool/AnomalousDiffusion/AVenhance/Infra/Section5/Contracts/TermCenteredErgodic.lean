/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.SpaceErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound.Centered

/-! # One centered ergodic component

The centered Appendix C estimate (`centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow`,
§8 (27)) specialised to a continuous fast factor with a uniform sup bound `Gm`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

/-- The absolute constant of the centered App C estimate (dimension two). -/
def sdCd : ℝ :=
  1 + 64 * (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) + 1024 * ((2 : ℝ) + 1)

theorem sdCd_pos : 0 < sdCd := by
  unfold sdCd
  have : 0 ≤ (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by
    unfold ergodicFourierWeight
    positivity) _
  positivity

theorem sd_cellAverage_sq_sqrt_le {g : Vec 2 → ℝ} (hg : Continuous g) {Gm : ℝ}
    (hGm : ∀ y, |g y| ≤ Gm) :
    (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) ≤ Gm := by
  have hG0 : 0 ≤ Gm := (abs_nonneg _).trans (hGm 0)
  have h1 : cellAverage (fun x => |g x| ^ 2) ≤ Gm ^ 2 :=
    LeftToShow.cellAverage_le_of_forall_le (fun x => by
      have := hGm x
      exact pow_le_pow_left₀ (abs_nonneg _) this 2) (by fun_prop)
  calc (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (Gm ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by
        rw [cellAverage_eq_unitCellIntegral]
        exact integral_nonneg fun x => by positivity) h1 (by norm_num)
    _ = Gm := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hG0]

/-- The two centering operators (unit-cube integral versus torus average) agree. -/
theorem sd_centerCell_eq (h : Vec 2 → ℝ) :
    Integration.centerCell h = Infra.Ergodic.centerCell h := by
  funext x
  unfold Integration.centerCell Infra.Ergodic.centerCell
  rw [← LeftToShow.spaceAvg_eq_cellAverage]
  rfl

/-- **One component** of the centered ergodic estimate, with the fast factor bounded by `Gm`. -/
theorem sd_component_bound {N : ℕ} (hN : 0 < N)
    (X : PeriodicVolumePreservingDiffeomorphism 2)
    {f g : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : IsZPeriodic f)
    {Cf r Gm : ℝ} (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hder : HasCoordinateAnalyticL2Bounds (fun x => (f (X.toFun x) : ℂ)) Cf r)
    (hg : Continuous g) (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ))
    (hnear : FlowDerivativeNearIdentity X) (hgmean : cellAverage g = 0)
    (hGm : ∀ y, |g y| ≤ Gm) :
    hMinusOneNorm (Integration.centerCell (fun x => f x * g (X.invFun x))) ≤
      ENNReal.ofReal (3 * (2 : ℝ) ^ 2 *
        (sdCd / (N : ℝ) * (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) * Gm +
          sdCd * Cf * Gm * Real.exp (-r * (N : ℝ) / 4096))) := by
  have hG0 : 0 ≤ Gm := (abs_nonneg _).trans (hGm 0)
  have hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec 2)) :=
    (hg.abs.pow 2).locallyIntegrable
  have h := centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow hN X hf hper Cf r hCf hr
    hder hg.locallyIntegrable hg2 hfast hNr hnear hgmean
  rw [sd_centerCell_eq]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hGa := sd_cellAverage_sq_sqrt_le hg hGm
  have hF0 : 0 ≤ (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by
    rw [cellAverage_eq_unitCellIntegral]
    exact integral_nonneg fun x => by positivity) _
  have hE0 := (Real.exp_pos (-r * (N : ℝ) / 4096)).le
  have hC := sdCd_pos
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold sdCd at hC ⊢
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · gcongr
  · gcongr

theorem sd_memL2On_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) : MemL2On unitCube f := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

/-- The centered `HDot⁻¹` norm of a finite sum of continuous functions is at most the sum of the
centered norms (centering and the sum commute; the homogeneous seminorm is subadditive). -/
theorem sd_centered_finset_sum_bound {ι : Type*} (s : Finset ι) (h : ι → Vec 2 → ℝ)
    (B : ι → ℝ≥0∞) (hc : ∀ i ∈ s, Continuous (h i))
    (hb : ∀ i ∈ s, hMinusOneNorm (Integration.centerCell (h i)) ≤ B i) :
    hMinusOneNorm (Integration.centerCell (fun x => ∑ i ∈ s, h i x)) ≤ ∑ i ∈ s, B i := by
  have hsumc : Continuous (fun x => ∑ i ∈ s, h i x) := continuous_finsetSum s hc
  have hL2 : MemL2On unitCube (fun x => ∑ i ∈ s, h i x) := sd_memL2On_of_continuous hsumc
  have hli : ∀ i ∈ s, LocallyIntegrable (h i) (volume : Measure (Vec 2)) := fun i hi =>
    (hc i hi).locallyIntegrable
  rw [sd_centerCell_eq, centered_hMinusOneNorm_eq_ergodic hL2 hsumc.locallyIntegrable]
  refine (homogeneousHMinusOneNorm_finset_sum_le s h hli).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hLi : MemL2On unitCube (h i) := sd_memL2On_of_continuous (hc i hi)
  rw [← centered_hMinusOneNorm_eq_ergodic hLi (hli i hi), ← sd_centerCell_eq]
  exact hb i hi

end AVenhance.Infra.Section5.Contracts
end
