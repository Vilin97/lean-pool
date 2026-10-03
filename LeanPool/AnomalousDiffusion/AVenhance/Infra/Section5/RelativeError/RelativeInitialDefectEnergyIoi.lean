/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIEnergyIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.IndyStepDownPartI

/-! The comparison's initial defect is measured from the right against the
actual datum. No value or regularity of the comparison at zero is consumed. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- A classical solution approaches its actual datum in L2 from the right. -/
theorem relative_classical_initial_L2_tendsto {b : ℝ → Vec 2 → Vec 2}
    {κ : ℝ} {g : Vec 2 → ℝ} {u f : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol b κ f g u)
    :
    Tendsto (fun s => Real.sqrt (l2NormSq (fun x => u s x - g x)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg : Continuous g := by
    have h0 := AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hu.1
      (t := 0) (le_refl 0)
    have he : u 0 = g := funext hu.2.2.1
    simpa only [he] using h0.continuous
  have hc : ContinuousOn (fun p : ℝ × Vec 2 => u p.1 p.2 - g p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (Vec 2))) :=
    hu.1.continuousOn.sub (hg.comp continuous_snd).continuousOn
  have hnorm := (relative_initial_norm_continuous (F := fun s x => u s x - g x) hc
      1).continuousWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  have hlim := (hnorm.mono Ioc_subset_Icc_self).tendsto
  rw [nhdsWithin_Ioc_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)] at hlim
  have hz : (fun x => u 0 x - g x) = fun _ => (0 : ℝ) := by
    funext x
    rw [hu.2.2.1 x, sub_self]
  change Tendsto _ _ (𝓝 (Real.sqrt (l2NormSq (fun x => u 0 x - g x)))) at hlim
  rw [hz] at hlim
  simpa [l2NormSq] using hlim

end AVenhance.Infra.Section5.RelativeError
