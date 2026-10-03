/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectPositiveTransport

/-! Positive-time transport estimates ignore the arbitrary extension at
nonpositive times, including its value at zero. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance AVenhance.Infra.Ergodic

/-- All periodicity premises are positive-time premises. Zeroing the unused
nonpositive slices lets the existing transport FTC apply without constraining
the original extension. -/
theorem relative_initial_backward_transport_of_positive_data
    {F source : ℝ → Vec 2 → ℝ}
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (F t))
    (hSourcePer : ∀ t, 0 < t → IsZ2Periodic (source t))
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
  let FP := fun t x => if 0 < t then F t x else 0
  let SP := fun t x => if 0 < t then source t x else 0
  have hf : ∀ t, IsZ2Periodic (FP t) := by
    intro t n x
    dsimp [FP]
    split_ifs with ht
    · exact hFper t ht n x
    · rfl
  have hs : ∀ t, IsZ2Periodic (SP t) := by
    intro t n x
    dsimp [SP]
    split_ifs with ht
    · exact hSourcePer t ht n x
    · rfl
  have hfc : ContinuousOn (fun p : ℝ × Vec 2 => FP p.1 ((X p.1).toFun p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))) := by
    apply hComp.congr
    intro p hp
    simp only [FP, ite_eq_left (show 0 < p.1 from hp.1)]
  have hsc : ContinuousOn (fun p : ℝ × Vec 2 => SP p.1 ((X p.1).toFun p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))) := by
    apply hSourceComp.congr
    intro p hp
    simp only [SP, ite_eq_left (show 0 < p.1 from hp.1)]
  have hm : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => FP s ((X s).toFun x)) (SP t ((X t).toFun x)) t := by
    intro t ht x
    have he : (fun s => FP s ((X s).toFun x)) =ᶠ[𝓝 t]
        (fun s => F s ((X s).toFun x)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp only [FP, ite_eq_left (show 0 < s from hs)]
    simpa only [SP, ite_eq_left ht] using (hMaterial t ht x).congr_of_eventuallyEq he
  have hz : FP b = 0 := by
    funext x
    simp only [FP, ite_eq_left hb, hzero, Pi.zero_apply]
  have hi : ∀ t ∈ Ioc (0 : ℝ) b,
      (∫ s in t..b, Real.sqrt (l2NormSq (SP s))) ≤ D := by
    intro t ht
    have he : (∫ s in t..b, Real.sqrt (l2NormSq (SP s))) =
        ∫ s in t..b, Real.sqrt (l2NormSq (source s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.2] at hs
      have hsp : 0 < s := ht.1.trans_le hs.1
      simp only [SP, ite_eq_left hsp]
    rw [he]
    exact hSourceIntegral t ht
  intro t ht
  have h := relative_initial_backward_transport_integrated_pos X hf hs hfc hsc hm
    hb hD hz hi t ht
  simpa only [FP, ite_eq_left (show 0 < t from ht.1)] using h

end AVenhance.Infra.Section5.RelativeError
