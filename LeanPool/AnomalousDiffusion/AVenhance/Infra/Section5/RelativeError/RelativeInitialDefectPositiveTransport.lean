/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectTransport

/-! Backward transport on positive windows. No continuity at zero is needed
when the source integral is uniformly bounded on every such window. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance AVenhance.Infra.Ergodic Transport

/-- Backward FTC and compact maximum absorption control every positive slice.
The source primitive is bounded on `[t,b]`, so the argument never uses time zero. -/
theorem relative_initial_backward_transport_integrated_pos
    {F source : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, IsZ2Periodic (F t))
    (hSourcePer : ∀ t, IsZ2Periodic (source t))
    (hComp : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 ((X p.1).toFun p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 => source p.1 ((X p.1).toFun p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => F s ((X s).toFun x)) (source t ((X t).toFun x)) t)
    {b D : ℝ} (hb : 0 < b) (hD : 0 ≤ D) (hzero : F b = 0)
    (hSourceIntegral : ∀ t ∈ Ioc (0 : ℝ) b,
      (∫ s in t..b, Real.sqrt (l2NormSq (source s))) ≤ D) :
    ∀ t ∈ Ioc (0 : ℝ) b, Real.sqrt (l2NormSq (F t)) ≤ 2 * D := by
  intro a ha
  let f := fun t => Real.sqrt (l2NormSq (F t))
  have hc := hm_transported_norm_continuous_of_joint (F := F) X hFper hComp
    (b := b) ha.1
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨a, le_rfl, ha.2⟩) hc
  let H := f t₀
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hBound : ∀ t ∈ Icc a b, f t ≤ H := fun _ ht => hmax ht
  have hFTC : ∀ t ∈ Icc a b, f t ^ 2 ≤ 2 * D * H := by
    intro t ht
    have htpos : 0 < t := ha.1.trans_le ht.1
    have hsub : uIcc b t ⊆ Icc a b := by
      rw [uIcc_of_ge ht.2]
      exact Icc_subset_Icc ht.1 le_rfl
    have hint : |∫ s in b..t, Real.sqrt (l2NormSq (source s))| ≤ D := by
      rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg ht.2 fun _ _ => Real.sqrt_nonneg _)]
      exact hSourceIntegral t ⟨htpos, ht.2⟩
    exact hm_transported_energy_ftc_integrated X hFper hSourcePer hComp hSourceComp
      hMaterial hb htpos hH hzero (fun s hs => hBound s (hsub hs)) hint
  have h := hm_transport_cell_sup_le_of_continuous (f := f) (H := H)
    (cell := Icc a b) (L := 1) (D := D) (fun _ _ => Real.sqrt_nonneg _)
    (by simpa using hD) (by simpa only [mul_one, one_mul] using hFTC)
    ⟨t₀, ht₀, rfl, fun s hs => hmax hs⟩ a ⟨le_rfl, ha.2⟩
  simpa only [mul_one] using h

/-- Time Cauchy--Schwarz on a positive subwindow, with an abstract source
amplitude. No source trace at zero is assumed. -/
theorem relative_initial_source_L1_of_positive_L2 {t b D : ℝ}
    (ht : 0 < t) (htb : t ≤ b) (hD : 0 ≤ D) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc t b))
    (hquad : (∫ s in t..b, g s ^ 2) ≤ D ^ 2) :
    (∫ s in t..b, g s) ≤ Real.sqrt b * D := by
  have hgu : ContinuousOn g (uIcc t b) := by rwa [uIcc_of_le htb]
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc t b) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc t b)).intervalIntegrable.1
  have hcs := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
    (μ := volume.restrict (Ioc t b)) (f := fun _ => (1 : ℝ)) (g := g)
    (by simpa only [one_pow, IntegrableOn] using h1)
    (hgu.pow 2).intervalIntegrable.1
    (by simpa only [one_mul, IntegrableOn] using hgu.intervalIntegrable.1)
  have hs := (Real.sqrt_le_sqrt hquad).trans_eq (Real.sqrt_sq hD)
  rw [intervalIntegral.integral_of_le htb] at hs ⊢
  simp only [one_pow, one_mul] at hcs
  have hv : (∫ _s in Ioc t b, (1 : ℝ)) = b - t := by simp [htb]
  rw [hv] at hcs
  have htime := Real.sqrt_le_sqrt (sub_le_self b ht.le)
  exact hcs.trans (mul_le_mul htime hs (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end AVenhance.Infra.Section5.RelativeError
