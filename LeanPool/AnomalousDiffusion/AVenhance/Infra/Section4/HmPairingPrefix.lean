/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourcePairing

/-! Full-cell time-L² data restrict to every prefix, so the scalar and flux
pairing Cauchy estimates can be applied uniformly to moving half-cell base points. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section4

theorem HmPairingPrefix.hm_prefix_measure_le_full {a b t : ℝ} (ht : t ≤ b) :
    volume.restrict (Set.Ioc a t) ≤ volume.restrict (Set.Ioc a b) := by
  exact Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl

theorem HmPairingPrefix.hm_Ioc_measure_le {a b A B : ℝ}
    (hAa : A ≤ a) (hbB : b ≤ B) :
    volume.restrict (Set.Ioc a b) ≤ volume.restrict (Set.Ioc A B) := by
  exact Measure.restrict_mono (Set.Ioc_subset_Ioc hAa hbB) le_rfl

/-- Restrict an L² time-slice datum from the whole positive-time interval to a
smaller closed cell, retaining both its norm and integrability bounds. -/
theorem hm_time_l2_data_restrict
    {g : ℝ → ℝ} {A B a b Q : ℝ} (hAa : A ≤ a) (hbB : b ≤ B)
    (hNorm : MemLp g 2 (volume.restrict (Set.Ioc A B)))
    (hSq : ∫ t in Set.Ioc A B, g t ^ 2 ≤ Q ^ 2)
    (hInt : Integrable g (volume.restrict (Set.Ioc A B))) :
    MemLp g 2 (volume.restrict (Set.Ioc a b)) ∧
      (∫ t in Set.Ioc a b, g t ^ 2 ≤ Q ^ 2) ∧
      Integrable g (volume.restrict (Set.Ioc a b)) := by
  let hμ := HmPairingPrefix.hm_Ioc_measure_le hAa hbB
  have hSqInt := hNorm.integrable_sq
  have hSq' : ∫ t in Set.Ioc a b, g t ^ 2 ≤ Q ^ 2 := by
    calc
      _ ≤ ∫ t in Set.Ioc A B, g t ^ 2 :=
        integral_mono_measure hμ
          (Filter.Eventually.of_forall fun t => sq_nonneg _)
          hSqInt
      _ ≤ Q ^ 2 := hSq
  exact ⟨hNorm.mono_measure hμ, hSq', hInt.mono_measure hμ⟩

/-- Convert an integrable spatial energy function into the time-L² datum of
its spatial norm. The separate measurability hypothesis is the Fubini
interface for the slice norm. -/
theorem hm_time_slice_l2_data_of_spatial_energy
    {G : ℝ → Vec 2 → ℝ} {a b Q : ℝ}
    (hMeas : AEStronglyMeasurable
      (fun t => Real.sqrt (AVenhance.l2NormSq (G t)))
      (volume.restrict (Set.Ioc a b)))
    (hEnergyInt : Integrable
      (fun t => AVenhance.l2NormSq (G t))
      (volume.restrict (Set.Ioc a b)))
    (hEnergy : ∫ t in Set.Ioc a b, AVenhance.l2NormSq (G t) ≤ Q ^ 2) :
    MemLp (fun t => Real.sqrt (AVenhance.l2NormSq (G t))) 2
        (volume.restrict (Set.Ioc a b)) ∧
      (∫ t in Set.Ioc a b,
        (Real.sqrt (AVenhance.l2NormSq (G t))) ^ 2 ≤ Q ^ 2) ∧
      Integrable (fun t => Real.sqrt (AVenhance.l2NormSq (G t)))
        (volume.restrict (Set.Ioc a b)) := by
  have hrootNonneg (t : ℝ) : 0 ≤ AVenhance.l2NormSq (G t) :=
    integral_nonneg fun x => sq_nonneg _
  have hsqInt : Integrable
      (fun t => (Real.sqrt (AVenhance.l2NormSq (G t))) ^ 2)
      (volume.restrict (Set.Ioc a b)) := by
    apply (integrable_congr (Filter.Eventually.of_forall fun t =>
      Real.sq_sqrt (hrootNonneg t))).2
    exact hEnergyInt
  have hmem := (memLp_two_iff_integrable_sq hMeas).2 hsqInt
  refine ⟨hmem, ?_, ?_⟩
  · calc
      _ = ∫ t in Set.Ioc a b, AVenhance.l2NormSq (G t) := by
        apply integral_congr_ae
        filter_upwards with t
        exact Real.sq_sqrt (hrootNonneg t)
      _ ≤ Q ^ 2 := hEnergy
  · exact hmem.integrable (by norm_num)

/-- Cauchy--Schwarz for a prefix measured from any base point in a full cell.
The interval orientation is immaterial, and the exact distance from the
base point is retained. -/
theorem hm_regular_pairing_integral_bound_of_full_cell_l2
    {F G : ℝ → Vec 2 → ℝ} {a b c s H Q : ℝ}
    (hc : c ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hFbound : ∀ r ∈ Set.Icc a b,
      Real.sqrt (AVenhance.l2NormSq (F r)) ≤ H)
    (hFcont : ∀ r ∈ Set.Icc a b, Continuous (F r))
    (hGcont : ∀ r ∈ Set.Icc a b, Continuous (G r))
    (hGnorm : MemLp (fun r => Real.sqrt (AVenhance.l2NormSq (G r))) 2
      (volume.restrict (Set.Ioc a b)))
    (hGsq : ∫ r in Set.Ioc a b,
      (Real.sqrt (AVenhance.l2NormSq (G r))) ^ 2 ≤ Q ^ 2)
    (hGint : Integrable
      (fun r => Real.sqrt (AVenhance.l2NormSq (G r)))
      (volume.restrict (Set.Ioc a b)))
    (hPairInt : Integrable
      (fun r => |hmRegularPairing (F := F) (G := G) r|)
      (volume.restrict (Set.Ioc a b))) :
    |∫ r in c..s, hmRegularPairing (F := F) (G := G) r| ≤
      Real.sqrt |s - c| * Q * H := by
  let u := min c s
  let v := max c s
  have huv : u ≤ v := min_le_max
  have hu : u ∈ Set.Icc a b := by
    exact ⟨le_min hc.1 hs.1,
      le_trans (min_le_left c s) hc.2⟩
  have hv : v ∈ Set.Icc a b := by
    exact ⟨le_trans hc.1 (le_max_left c s),
      max_le_iff.mpr ⟨hc.2, hs.2⟩⟩
  have hμ : volume.restrict (Set.Ioc u v) ≤ volume.restrict (Set.Ioc a b) := by
    apply Measure.restrict_mono
    · exact Set.Ioc_subset_Ioc (le_trans hu.1 le_rfl) hv.2
    · exact le_rfl
  have hnorm := hGnorm.mono_measure hμ
  have hsqInt := hGnorm.integrable_sq
  have hsq : ∫ r in Set.Ioc u v,
      (Real.sqrt (AVenhance.l2NormSq (G r))) ^ 2 ≤ Q ^ 2 := by
    calc
      _ ≤ ∫ r in Set.Ioc a b,
          (Real.sqrt (AVenhance.l2NormSq (G r))) ^ 2 :=
        integral_mono_measure hμ
          (Filter.Eventually.of_forall fun r => sq_nonneg _)
          hsqInt
      _ ≤ Q ^ 2 := hGsq
  have hbound := hm_regular_pairing_interval_bound_of_l2
    (a := u) (b := v) (H := H) (Q := Q) huv hH hQ
    (fun r hr => hFbound r ⟨le_trans hu.1 hr.1.le, le_trans hr.2 hv.2⟩)
    (fun r hr => hFcont r ⟨le_trans hu.1 hr.1.le, le_trans hr.2 hv.2⟩)
    (fun r hr => hGcont r ⟨le_trans hu.1 hr.1.le, le_trans hr.2 hv.2⟩) hnorm hsq
    (hGint.mono_measure hμ) (hPairInt.mono_measure hμ)
  by_cases hcs : c ≤ s
  · simpa [u, v, min_eq_left hcs, max_eq_right hcs,
      abs_of_nonneg (sub_nonneg.mpr hcs)] using hbound
  · have hsc : s ≤ c := le_of_not_ge hcs
    have hbound' :
        |∫ r in s..c, hmRegularPairing (F := F) (G := G) r| ≤
          Real.sqrt (c - s) * Q * H := by
      simpa [u, v, min_eq_right hsc, max_eq_left hsc] using hbound
    rw [intervalIntegral.integral_symm]
    simpa [abs_of_nonpos (sub_nonpos.mpr hsc)] using hbound'

/-- Flux-pairing Cauchy--Schwarz on a subinterval of a full cell, with an
arbitrary base point and either orientation. -/
theorem hm_flux_pairing_integral_bound_of_full_cell_l2
    {F : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {a b c s QF QV : ℝ}
    (hc : c ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b)
    (hQF : 0 ≤ QF) (hQV : 0 ≤ QV)
    (hGradCont : ∀ r ∈ Set.Icc a b, Continuous (AVenhance.spaceGrad (F r)))
    (hVcont : ∀ r ∈ Set.Icc a b, Continuous (V r))
    (hFnorm : MemLp (fun r => Real.sqrt (AVenhance.gradNormSq (fun x =>
      AVenhance.spaceGrad (F r) x))) 2 (volume.restrict (Set.Ioc a b)))
    (hVnorm : MemLp (fun r => Real.sqrt (AVenhance.gradNormSq (V r))) 2
      (volume.restrict (Set.Ioc a b)))
    (hFsq : ∫ r in Set.Ioc a b,
      (Real.sqrt (AVenhance.gradNormSq (fun x => AVenhance.spaceGrad (F r) x))) ^ 2
        ≤ QF ^ 2)
    (hVsq : ∫ r in Set.Ioc a b,
      (Real.sqrt (AVenhance.gradNormSq (V r))) ^ 2 ≤ QV ^ 2)
    (hPairInt : Integrable
      (fun r => |hmFluxPairing (F := F) (V := V) r|)
      (volume.restrict (Set.Ioc a b))) :
    |∫ r in c..s, hmFluxPairing (F := F) (V := V) r| ≤ QF * QV := by
  let u := min c s
  let v := max c s
  have huv : u ≤ v := min_le_max
  have hu : u ∈ Set.Icc a b := by
    exact ⟨le_min hc.1 hs.1,
      le_trans (min_le_left c s) hc.2⟩
  have hv : v ∈ Set.Icc a b := by
    exact ⟨le_trans hc.1 (le_max_left c s),
      max_le_iff.mpr ⟨hc.2, hs.2⟩⟩
  have hμ : volume.restrict (Set.Ioc u v) ≤ volume.restrict (Set.Ioc a b) := by
    apply Measure.restrict_mono
    · exact Set.Ioc_subset_Ioc (le_trans hu.1 le_rfl) hv.2
    · exact le_rfl
  have hFnorm' := hFnorm.mono_measure hμ
  have hVnorm' := hVnorm.mono_measure hμ
  have hFsquareInt := hFnorm.integrable_sq
  have hVsquareInt := hVnorm.integrable_sq
  have hFsquare : ∫ r in Set.Ioc u v,
      (Real.sqrt (AVenhance.gradNormSq (fun x => AVenhance.spaceGrad (F r) x))) ^ 2
        ≤ QF ^ 2 := by
    calc
      _ ≤ ∫ r in Set.Ioc a b,
          (Real.sqrt (AVenhance.gradNormSq (fun x => AVenhance.spaceGrad (F r) x))) ^ 2 :=
        integral_mono_measure hμ
          (Filter.Eventually.of_forall fun r => sq_nonneg _)
          hFsquareInt
      _ ≤ QF ^ 2 := hFsq
  have hVsquare : ∫ r in Set.Ioc u v,
      (Real.sqrt (AVenhance.gradNormSq (V r))) ^ 2 ≤ QV ^ 2 := by
    calc
      _ ≤ ∫ r in Set.Ioc a b,
          (Real.sqrt (AVenhance.gradNormSq (V r))) ^ 2 :=
        integral_mono_measure hμ
          (Filter.Eventually.of_forall fun r => sq_nonneg _)
          hVsquareInt
      _ ≤ QV ^ 2 := hVsq
  have hbound := hm_flux_pairing_interval_bound_of_l2
    (a := u) (b := v) huv hQF hQV
    (fun r hr => hGradCont r ⟨le_trans hu.1 hr.1.le, le_trans hr.2 hv.2⟩)
    (fun r hr => hVcont r ⟨le_trans hu.1 hr.1.le, le_trans hr.2 hv.2⟩)
    hFnorm' hVnorm' hFsquare hVsquare
    (hPairInt.mono_measure hμ)
  by_cases hcs : c ≤ s
  · simpa [u, v, min_eq_left hcs, max_eq_right hcs] using hbound
  · have hsc : s ≤ c := le_of_not_ge hcs
    have hbound' :
        |∫ r in s..c, hmFluxPairing (F := F) (V := V) r| ≤ QF * QV := by
      simpa [u, v, min_eq_right hsc, max_eq_left hsc] using hbound
    rw [intervalIntegral.integral_symm]
    simpa only [abs_neg] using hbound'

end AVenhance.Infra.Section4

end
