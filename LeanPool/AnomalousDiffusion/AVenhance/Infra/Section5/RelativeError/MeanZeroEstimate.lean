/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.MeanZeroEnergy

/-!# RelativeError: mean-zero data are controlled by total dissipation

The slice Poincare inequality is averaged against the exact classical energy
identity.  This avoids requiring a derivative at the initial time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

theorem MeanZeroEstimate.interval_energy_average_bound
    {E G : ℝ → ℝ} {κ Cₚ E₀ : ℝ}
    (hκ : 0 ≤ κ)
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (hGnonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t)
    (henergy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      E t + 2 * κ * (∫ s in (0 : ℝ)..t, G s) = E₀)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, E t ≤ Cₚ * G t) :
    E₀ ≤ (Cₚ + 2 * κ) * (∫ s in (0 : ℝ)..1, G s) := by
  have hGint : IntervalIntegrable G volume 0 1 :=
    hG.intervalIntegrable_of_Icc (by norm_num)
  have hDmono (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, G s) ≤ (∫ s in (0 : ℝ)..1, G s) := by
    have hsubLeft : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_right ht.2
    have hsubRight : Set.uIcc t 1 ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le ht.2, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_left ht.1
    have hleft : IntervalIntegrable G volume 0 t := hGint.mono_set hsubLeft
    have hright : IntervalIntegrable G volume t 1 := hGint.mono_set hsubRight
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    have hrestnonneg : 0 ≤ ∫ s in t..1, G s :=
      intervalIntegral.integral_nonneg ht.2 (fun s hs =>
        hGnonneg s ⟨le_trans ht.1 hs.1, hs.2⟩)
    calc
      (∫ s in (0 : ℝ)..t, G s) ≤
          (∫ s in (0 : ℝ)..t, G s) + ∫ s in t..1, G s := by linarith
      _ = ∫ s in (0 : ℝ)..1, G s := hadd
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      E₀ ≤ Cₚ * G t + 2 * κ * (∫ s in (0 : ℝ)..1, G s) := by
    have hEid := henergy t ht
    have hPoincare := hP t ht
    have hD := hDmono t ht
    have h2κ : 0 ≤ 2 * κ := mul_nonneg (by norm_num) hκ
    have hκD := mul_le_mul_of_nonneg_left hD h2κ
    nlinarith only [hEid, hPoincare, hκD]
  have hRhsInt : IntervalIntegrable
      (fun t => Cₚ * G t + 2 * κ * (∫ s in (0 : ℝ)..1, G s)) volume 0 1 := by
    refine IntervalIntegrable.add ?_ ?_
    · exact hGint.const_mul Cₚ
    · exact intervalIntegrable_const
  have haverage := intervalIntegral.integral_mono_on zero_le_one
    intervalIntegrable_const hRhsInt hpoint
  calc
    E₀ = ∫ t in (0 : ℝ)..1, E₀ := by simp
    _ ≤ ∫ t in (0 : ℝ)..1,
        (Cₚ * G t + 2 * κ * (∫ s in (0 : ℝ)..1, G s)) := haverage
    _ = (Cₚ + 2 * κ) * (∫ s in (0 : ℝ)..1, G s) := by
      rw [intervalIntegral.integral_add (hGint.const_mul Cₚ)
        intervalIntegrable_const, intervalIntegral.integral_const_mul]
      simp [intervalIntegral.integral_const]
      ring

/-- Mean-zero smooth classical data have initial squared norm bounded by the
time-integrated gradient energy, uniformly for diffusivity at most one. -/
theorem classical_meanZero_initial_energy_le
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hmean : ∫ x in unitCube, g x = 0) :
    l2NormSq g ≤ 3 * (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := by
  let E : ℝ → ℝ := fun t => ∫ x in unitCell 2, (u t x) ^ 2
  let G : ℝ → ℝ := classicalCellGradientEnergy u
  have hgradJoint := LeftToShow.spaceGrad_continuousOn hsol.1
  have hgradEnergyJoint :
      ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (spaceGrad (u p.1) p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    apply LeftToShow.continuous_vecNormSq_two.comp_continuousOn
    exact hgradJoint.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨hs.1, trivial⟩)
  have hGcontCube :
      ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x))
        (Set.Icc (0 : ℝ) 1) :=
    LeftToShow.continuousOn_integral_unitCube hgradEnergyJoint
  have hcellCube : G =
      (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) := by
    funext t
    exact Infra.Torus.integral_unitCell_eq_unitCube _
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    rw [hcellCube]
    exact hGcontCube
  have hGnonneg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ G t := by
    simp only [G, classicalCellGradientEnergy]
    exact integral_nonneg (fun x => vecNormSq_nonneg _)
  have henergy (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      E t + 2 * κ * (∫ s in (0 : ℝ)..t, G s) = l2NormSq g := by
    by_cases hzero : t = 0
    · subst t
      have hcellg : (∫ x in unitCell 2, g x ^ 2) = l2NormSq g := by
        rw [Infra.Torus.integral_unitCell_eq_unitCube]
        rfl
      have hzeroEnergy : E 0 = l2NormSq g := by
        change (∫ x in unitCell 2, (u 0 x) ^ 2) = _
        calc
          (∫ x in unitCell 2, (u 0 x) ^ 2) =
              ∫ x in unitCell 2, g x ^ 2 := by
                apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
                intro x hx
                change (u 0 x) ^ 2 = g x ^ 2
                rw [hsol.2.2.1 x]
          _ = l2NormSq g := hcellg
      rw [hzeroEnergy]
      simp [G]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
      have ht1 : t ≤ 1 := ht.2
      have hId := classical_solution_energy_identity hb hdiv hsol htpos ht1
      have hcellg : (∫ x in unitCell 2, g x ^ 2) = l2NormSq g := by
        rw [Infra.Torus.integral_unitCell_eq_unitCube]
        rfl
      calc
        E t + 2 * κ * (∫ s in (0 : ℝ)..t, G s) =
            (∫ x in unitCell 2, (u t x) ^ 2) +
              2 * κ * (∫ s in (0 : ℝ)..t, classicalCellGradientEnergy u s) := by
              rfl
        _ = ∫ x in unitCell 2, g x ^ 2 := hId
        _ = l2NormSq g := hcellg
  have hP (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : E t ≤ (4 * Real.pi ^ 2)⁻¹ * G t := by
    have hper := hsol.2.1 t ht.1
    have hmeanT : ∫ x in unitCube, u t x = 0 := by
      have hcellMean : ∫ x in unitCell 2, u t x = ∫ x in unitCell 2, g x :=
        classical_solution_mean_preserved hb hdiv hsol ht
      have hgcell : ∫ x in unitCell 2, g x = 0 := by
        rw [Infra.Torus.integral_unitCell_eq_unitCube]
        exact hmean
      calc
        ∫ x in unitCube, u t x = ∫ x in unitCell 2, u t x :=
          (Infra.Torus.integral_unitCell_eq_unitCube _).symm
        _ = 0 := hcellMean.trans hgcell
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
      classicalSmooth_slice_nonneg hsol.1 ht.1
    have hPtorus := Infra.Torus.l2NormSq_le_fourierPoincare
      (hslice.of_le (by norm_num)) hper hmeanT
    change (∫ x in unitCube, (u t x) ^ 2) ≤
      (4 * Real.pi ^ 2)⁻¹ * (∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) at hPtorus
    calc
      E t = ∫ x in unitCell 2, (u t x) ^ 2 := rfl
      _ = ∫ x in unitCube, (u t x) ^ 2 :=
        Infra.Torus.integral_unitCell_eq_unitCube _
      _ ≤ (4 * Real.pi ^ 2)⁻¹ *
          (∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) := hPtorus
      _ = (4 * Real.pi ^ 2)⁻¹ * G t := by
          change (4 * Real.pi ^ 2)⁻¹ *
              (∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) =
            (4 * Real.pi ^ 2)⁻¹ *
              (∫ x in unitCell 2, vecNormSq (spaceGrad (u t) x))
          rw [Infra.Torus.integral_unitCell_eq_unitCube]
  have haverage := MeanZeroEstimate.interval_energy_average_bound hκ.le
    hGcont hGnonneg henergy hP
  have hlambda : (4 * Real.pi ^ 2)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : 0 < 4 * Real.pi ^ 2)).2
    nlinarith [Real.pi_gt_three]
  have hCoeff : (4 * Real.pi ^ 2)⁻¹ + 2 * κ ≤ 3 := by
    nlinarith [hlambda, hκ1]
  exact haverage.trans (mul_le_mul_of_nonneg_right hCoeff
    (intervalIntegral.integral_nonneg zero_le_one (fun t ht => hGnonneg t ht)))

/-- Norm form of the mean-zero dissipation estimate, with
`S = sqrt κ * ‖∇u‖_{L²((0,1)×cell)}`. -/
theorem classical_meanZero_initial_l2_le
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hmean : ∫ x in unitCube, g x = 0) :
    Real.sqrt (l2NormSq g) ≤ Real.sqrt 3 * (Real.sqrt κ)⁻¹ *
      (Real.sqrt κ * Real.sqrt
        (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) := by
  have hsq := classical_meanZero_initial_energy_le hb hdiv hsol hκ hκ1 hmean
  have hDnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t :=
    intervalIntegral.integral_nonneg zero_le_one (fun t ht =>
      integral_nonneg (fun x => vecNormSq_nonneg _))
  have hroot := Real.sqrt_le_sqrt hsq
  have hsplit : Real.sqrt (3 *
      (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) =
      Real.sqrt 3 * Real.sqrt
        (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) :=
    Real.sqrt_mul (by norm_num) _
  have hbase : Real.sqrt (l2NormSq g) ≤ Real.sqrt 3 * Real.sqrt
      (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := by
    simpa [hsplit] using hroot
  have hκroot : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  calc
    Real.sqrt (l2NormSq g) ≤ Real.sqrt 3 * Real.sqrt
        (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := hbase
    _ = Real.sqrt 3 * (Real.sqrt κ)⁻¹ * (Real.sqrt κ * Real.sqrt
        (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) := by
      field_simp [ne_of_gt hκroot]

end AVenhance.Infra.Section5.RelativeError

end
