/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTBoundedRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRemainderGlobal

/-! # Morrey control from almost-everywhere remainder slice bounds

An almost-everywhere spatial bound is sufficient for the measurable
remainder selected by weak derivative uniqueness. A bounded representative
satisfies the pointwise consumer and preserves the original Morrey class.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- A finite temporal majorant controls the original measurable remainder
in Morrey space even when the spatial bound initially holds only almost
everywhere on each time slice. -/
theorem pressure_remainder_indicator_morrey_lt_top_of_ae_slice_bound
    {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {H : ParabolicPoint → ℝ} (hH : Measurable H)
    {M : ℝ → ℝ≥0∞} (hM : AEMeasurable M volume)
    {A : Set ParabolicPoint} {B : Set Vec3}
    (hA : MeasurableSet A) (hAB : ∀ w ∈ A, w.1 ∈ B)
    (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (hbound : ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ A → ‖H (x, s)‖ₑ ≤ M s)
    (hMfinite : (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ (A.indicator H) < ⊤ := by
  obtain ⟨H', hm, heq, hb⟩ := exists_measurable_spatially_bounded_representative hH hM hA hbound
  have hN := pressure_remainder_indicator_morreyNorm_lt_top hκlo hκhi hA hAB
    hm.aemeasurable hM hB hBfinite
    (hb.mono (fun _ hs x _hx => hs x)) hMfinite
  apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6 / 5) ?_).trans_lt hN
  filter_upwards [(ae_restrict_iff' hA).mp heq] with w hw
  by_cases ha : w ∈ A
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hw ha]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- A bound on a measurable product carrier, expressed with restricted
space and time measures, has the full-time implication form needed by the
remainder Morrey estimate. -/
theorem ae_spatial_bound_on_product_of_restricted_slices
    {H : ParabolicPoint → ℝ} {M : ℝ → ℝ≥0∞} {B : Set Vec3} {J : Set ℝ}
    (hB : MeasurableSet B) (hJ : MeasurableSet J)
    (hbound : ∀ᵐ s ∂volume.restrict J, ∀ᵐ x ∂volume.restrict B, ‖H (x, s)‖ₑ ≤ M s) :
    ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ B ×ˢ J → ‖H (x, s)‖ₑ ≤ M s := by
  filter_upwards [(ae_restrict_iff' hJ).mp hbound] with s hs
  by_cases hsJ : s ∈ J
  · filter_upwards [(ae_restrict_iff' hB).mp (hs hsJ)] with x hx
    exact fun h => hx h.1
  · exact Eventually.of_forall fun _ h => (hsJ h.2).elim

end CKN.Core.Step4
