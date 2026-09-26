/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedSelection

/-! # Representatives with pointwise spatial slice bounds

A jointly measurable field with an almost-everywhere spatial bound can be
changed on a null set to obey that bound at every spatial point on almost
every time slice. This preserves its value on the prescribed carrier.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- A measurable representative can satisfy a temporal bound at every spatial
point, while remaining almost everywhere equal to the original field on its
measurable carrier. -/
theorem exists_measurable_spatially_bounded_representative
    {H : ParabolicPoint → ℝ} (hH : Measurable H)
    {M : ℝ → ℝ≥0∞} (hM : AEMeasurable M volume)
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    (hbound : ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ S → ‖H (x, s)‖ₑ ≤ M s) :
    ∃ H' : ParabolicPoint → ℝ, Measurable H' ∧ H' =ᵐ[volume.restrict S] H ∧
      ∀ᵐ s ∂volume, ∀ x : Vec3, ‖H' (x, s)‖ₑ ≤ M s := by
  let M₀ := hM.mk M
  let E : Set ParabolicPoint := {w | ‖H w‖ₑ ≤ M₀ w.2}
  have hm : Measurable M₀ := hM.measurable_mk
  have hE : MeasurableSet E := measurableSet_le hH.enorm (hm.comp measurable_snd)
  let H' := E.indicator H
  have hm' : Measurable H' := hH.indicator hE
  have hb (x : Vec3) (s : ℝ) : ‖H' (x, s)‖ₑ ≤ M₀ s := by
    change ‖E.indicator H (show ParabolicPoint from (x, s))‖ₑ ≤ M₀ s
    by_cases he : (x, s) ∈ E
    · rw [Set.indicator_of_mem (α := ParabolicPoint) he]
      exact he
    · rw [Set.indicator_of_notMem (α := ParabolicPoint) he, enorm_zero]
      exact bot_le
  have hslice : ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ S → H' (x, s) = H (x, s) := by
    filter_upwards [hbound, hM.ae_eq_mk] with s hs he
    filter_upwards [hs] with x hx
    intro hxS
    apply Set.indicator_of_mem
    change ‖H (x, s)‖ₑ ≤ M₀ s
    exact (hx hxS).trans_eq he
  have hsetP : MeasurableSet {w : ParabolicPoint | w ∈ S → H' w = H w} := by
    have he : {w : ParabolicPoint | w ∈ S → H' w = H w} = Sᶜ ∪ {w | H' w = H w} := by
      ext w
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [he]
    exact hS.compl.union (measurableSet_eq_fun hm' hH)
  have hset : MeasurableSet {w : Vec3 × ℝ | w ∈ S → H' w = H w} := hsetP
  have hfull : ∀ᵐ w ∂(volume : Measure (Vec3 × ℝ)), w ∈ S → H' w = H w := by
    rw [volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hset).mpr ((Measure.ae_ae_comm hset).mpr hslice)
  refine ⟨H', hm', (ae_restrict_iff' hS).mpr hfull, ?_⟩
  filter_upwards [hM.ae_eq_mk] with s hs
  intro x
  rw [hs]
  exact hb x s

end CKN.Core.Step4
