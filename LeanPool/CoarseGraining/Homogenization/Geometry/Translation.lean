/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Translation -/

@[expose] public section

namespace Homogenization

open MeasureTheory

/-- Translate a set in `Vec d` by the vector `z`. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  { x | ∃ y ∈ U, x = y + z }

theorem mem_translateSet_iff_sub_mem {d : ℕ} {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_assoc]
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp [sub_eq_add_neg, add_assoc]

theorem preimage_subRight_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x - z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem]

theorem preimage_addNeg_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + -z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]

theorem preimage_addRight_translateSet_eq {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) ⁻¹' translateSet z U = U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc]

theorem image_addRight_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) '' U = translateSet z U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem translateSet_inter {d : ℕ} (z : Vec d) (U V : Set (Vec d)) :
    translateSet z (U ∩ V) = translateSet z U ∩ translateSet z V := by
  ext y
  simp [mem_translateSet_iff_sub_mem]

@[simp] theorem translateSet_zero {d : ℕ} (U : Set (Vec d)) :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]

theorem translateSet_translateSet {d : ℕ} (z w : Vec d) (U : Set (Vec d)) :
    translateSet w (translateSet z U) = translateSet (z + w) U := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp [add_assoc]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + z, ⟨u, hu, rfl⟩, by simp [add_assoc]⟩

theorem measurePreserving_subRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (MeasureTheory.volume.restrict (translateSet z U))
      (MeasureTheory.volume.restrict U) := by
  let hμ :
      MeasurePreserving (fun x : Vec d => x + -z)
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))
        MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) (-z)
  simpa [preimage_addNeg_eq_translateSet (z := z) U, sub_eq_add_neg] using
    MeasurePreserving.restrict_preimage_emb hμ (Homeomorph.subRight z).measurableEmbedding U

theorem measurePreserving_addRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict (translateSet z U)) := by
  let hμ :
      MeasurePreserving (fun x : Vec d => x + z)
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))
        MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) z
  simpa [preimage_addNeg_eq_translateSet (z := z) U, image_addRight_eq_translateSet (z := z) U,
    sub_eq_add_neg] using
    MeasurePreserving.restrict_image_emb hμ (Homeomorph.addRight z).measurableEmbedding U

theorem setIntegral_comp_subRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in translateSet z U, f (x - z) ∂MeasureTheory.volume =
      ∫ y in U, f y ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_subRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.subRight z).measurableEmbedding f

theorem setIntegral_comp_addRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂MeasureTheory.volume =
      ∫ x in translateSet z U, f x ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem volume_translateSet_eq {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasureTheory.volume (translateSet z U) = MeasureTheory.volume U := by
  have h :=
    MeasurePreserving.measure_preimage_emb
      (measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) z)
      (Homeomorph.addRight z).measurableEmbedding
      (translateSet z U)
  simpa [preimage_addRight_translateSet_eq] using h.symm

end Homogenization
