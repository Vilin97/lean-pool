/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection

/-! # Jointly measurable representatives of global slice derivatives

Spatial mollification constructs a representative from joint measurability
and local integrability of almost every slice. No time-integrability bound
on the derivative is needed for this selection.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN

/-- Global slice derivatives have a jointly measurable representative,
uniquely identified with every locally integrable weak derivative on each
good slice. -/
theorem exists_measurable_global_slice_derivative (k : Fin 3)
    {p : Vec3 × ℝ → ℝ} (hp : Measurable p)
    (hploc : ∀ᵐ t ∂volume, LocallyIntegrable (fun x => p (x, t)) volume)
    (hslice : ∀ᵐ t ∂volume, ∃ g : Vec3 → ℝ,
      LocallyIntegrable g volume ∧ HasWeakPartialDerivOn univ k (fun x => p (x, t)) g) :
    ∃ D : Vec3 × ℝ → ℝ, Measurable D ∧
      ∀ᵐ t ∂volume, ∀ g : Vec3 → ℝ,
        LocallyIntegrable g volume → HasWeakPartialDerivOn univ k (fun x => p (x, t)) g →
        (fun x => D (x, t)) =ᵐ[volume] g := by
  let K : ℕ → Vec3 → ℝ := fun n y =>
    (fderiv ℝ (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n)) y) (basisVec k)
  have hK : ∀ n, Continuous (K n) := fun n =>
    ((mollifier_contDiff (d := 3) (sliceRadius_pos n) (n := 2)).continuous_fderiv
      (by simp)).clm_apply continuous_const
  let G : ℕ → Vec3 × ℝ → ℝ := fun n z => ∫ y, K n y * p (z.1 - y, z.2)
  have hG : ∀ n, StronglyMeasurable (G n) := fun n =>
    stronglyMeasurable_slice_kernel_integral (hK n) hp.stronglyMeasurable
  have hkey : ∀ᵐ t ∂volume, ∀ g : Vec3 → ℝ,
      LocallyIntegrable g volume → HasWeakPartialDerivOn univ k (fun x => p (x, t)) g →
      ∀ᵐ x ∂volume, Tendsto (fun n => G n (x, t)) atTop (𝓝 (g x)) := by
    filter_upwards [hploc] with t ht g hg hw
    have heq (n : ℕ) (x : Vec3) :
        G n (x, t) = mollify g (sliceRadius n) (sliceRadius_pos n) x := by
      exact integral_fderiv_mollifier_mul_eq_mollify ht hg hw (sliceRadius_pos n)
        (subset_univ _)
    simpa only [heq] using ae_tendsto_mollify_sliceRadius (d := 3) hg
  let S : Set (Vec3 × ℝ) := {z | ∃ c : ℝ, Tendsto (fun n => G n z) atTop (𝓝 c)}
  have hS : MeasurableSet S := measurableSet_exists_tendsto (fun n => (hG n).measurable)
  have hconv : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), z ∈ S := by
    rw [volume_eq_prod]
    apply ae_prod_of_ae_ae_snd hS
    filter_upwards [hslice, hkey] with t ht hk
    obtain ⟨g, hg, hw⟩ := ht
    filter_upwards [hk g hg hw] with x hx
    exact ⟨g x, hx⟩
  let D : Vec3 × ℝ → ℝ := fun z => limUnder atTop (fun n => G n z)
  have hD : AEMeasurable D volume := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => (hG n).measurable.aemeasurable)
    filter_upwards [hconv] with z hz
    exact tendsto_nhds_limUnder hz
  refine ⟨hD.mk D, hD.measurable_mk, ?_⟩
  have heq : D =ᵐ[(volume : Measure Vec3).prod (volume : Measure ℝ)] hD.mk D := by
    rw [← volume_eq_prod]
    exact hD.ae_eq_mk
  filter_upwards [hkey, ae_ae_of_ae_prod_snd heq] with t ht hm g hg hw
  filter_upwards [ht g hg hw, hm] with x hx hxm
  exact hxm.symm.trans hx.limUnder_eq

end CKN
