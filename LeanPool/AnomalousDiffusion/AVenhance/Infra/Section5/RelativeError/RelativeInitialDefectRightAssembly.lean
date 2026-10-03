/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEnergyIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeSecondLast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity

/-! The oscillatory corrector has a legitimate right trace. Combining this
trace with a positive-time Hm bound supplies the relative initial leaf. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
open AVenhance.Infra.Section5.LeftToShow
open scoped Topology ContDiff
namespace AVenhance.Infra.Section5.RelativeError

/-- Conditional assembly of the right-limit defect. The Hm hypothesis is an
eventual positive-time bound, and no Hm value at zero appears. -/
theorem relative_initial_defect_from_right_Hm_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ ν : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hp : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κ ν g θprev T)
    {B D : ℝ}
    (hCorrector : Real.sqrt (l2NormSq (fun x =>
      ∑' k : ℤ, ansatzSummand I hΦ m κ (T (Nstar β)) k 0 x)) ≤ B)
    (hHm : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤ D) :
    ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κ (T (Nstar β)) s x - g x)) ≤
        B + D + η := by
  let U := T (Nstar β)
  let C := fun s x => ∑' k : ℤ, ansatzSummand I hΦ m κ U k s x
  have hsol := tIterates_classicalSol hT
  have hCcont : ContinuousOn (fun p : ℝ × Vec 2 => C p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ) :=
    (ansatz_series_contDiffOn_two I hΦ m κ hsol.1).continuousOn
  have hc := (relative_initial_norm_continuous (F := C) hCcont 1).continuousWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  have hclim := (hc.mono Ioc_subset_Icc_self).tendsto
  rw [nhdsWithin_Ioc_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)] at hclim
  have hUlim := relative_classical_initial_L2_tendsto hsol
  have hg : Continuous g := by
    have he : U 0 = g := funext hsol.2.2.1
    simpa only [← he] using
      (AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hsol.1 (t := 0) le_rfl).continuous
  intro η hη
  have hsmall := hUlim.eventually (eventually_lt_nhds (half_pos hη))
  have hcorr := hclim.eventually (eventually_lt_nhds
    (lt_add_of_pos_right (Real.sqrt (l2NormSq (C 0))) (half_pos hη)))
  filter_upwards [hHm, hsmall, hcorr, self_mem_nhdsWithin] with s hs hu hc hspos
  have hUs := (AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hsol.1 hspos.le).continuous
  have hH := (Hm_slice_contDiff_pos I hΦ hm hκ hp hT hspos).continuous
  have hCorrs : Continuous (C s) := hCcont.comp_continuous
    (show Continuous (fun x : Vec 2 => (s, x)) from by fun_prop)
    (fun x => ⟨show 0 ≤ s from (show 0 < s from hspos).le, mem_univ x⟩)
  have h1 := sqrt_l2NormSq_add_le (memL2On_unitCube_of_continuous (hUs.sub hg))
    (memL2On_unitCube_of_continuous hCorrs)
  have h2 := sqrt_l2NormSq_add_le
    (memL2On_unitCube_of_continuous ((hUs.sub hg).add hCorrs))
    (memL2On_unitCube_of_continuous hH)
  change Real.sqrt (l2NormSq (fun x => (U s x - g x) + C s x)) ≤
    Real.sqrt (l2NormSq (fun x => U s x - g x)) + Real.sqrt (l2NormSq (C s)) at h1
  have he : (fun x => ((U s x - g x) + C s x) + I.Hm hΦ m κ U s x) =
      fun x => I.ansatz hΦ m κ U s x - g x := by
    funext x
    rw [ansatz_eq_summand]
    dsimp [C]
    ring
  change Real.sqrt (l2NormSq (fun x => ((U s x - g x) + C s x) +
      I.Hm hΦ m κ U s x)) ≤
      Real.sqrt (l2NormSq (fun x => (U s x - g x) + C s x)) +
        Real.sqrt (l2NormSq (I.Hm hΦ m κ U s)) at h2
  rw [he] at h2
  change Real.sqrt (l2NormSq (C 0)) ≤ B at hCorrector
  change Real.sqrt (l2NormSq (fun x => U s x - g x)) < η / 2 at hu
  change Real.sqrt (l2NormSq (C s)) < Real.sqrt (l2NormSq (C 0)) + η / 2 at hc
  change Real.sqrt (l2NormSq (I.Hm hΦ m κ U s)) ≤ D at hs
  change Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κ U s x - g x)) ≤ _
  linarith only [h1, h2, hu, hc, hs, hCorrector]

end AVenhance.Infra.Section5.RelativeError
