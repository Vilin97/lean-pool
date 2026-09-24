/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationLaplacian

/-!
# Localized Equation Gradient Transfer

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Step3

/-! A spacetime version of the slice weak-gradient integration-by-parts rule. -/

lemma spacetime_weak_partial_transfer
    {Ω' : Set Vec3} {J : Set ℝ} {a d : ParabolicPoint → ℝ}
    {b : Vec3 × ℝ → ℝ} {j : Fin 3}
    (hJ : MeasurableSet J)
    (hleft : Integrable (fun z => d z * b z) volume)
    (hright : Integrable (fun z => a z * spatialPartial b j z) volume)
    (hzero_left : ∀ z ∉ spaceTimeSet Ω' J, d z * b z = 0)
    (hzero_right : ∀ z ∉ spaceTimeSet Ω' J,
      a z * spatialPartial b j z = 0)
    (hgrad : ∀ᵐ t ∂volume.restrict J,
      HasWeakPartialDerivOn Ω' j (fun x => a (x, t))
        (fun x => d (x, t)))
    (hb : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => b (x, t)))
    (hbc : ∀ t : ℝ, HasCompactSupport (fun x : Vec3 => b (x, t)))
    (hbΩ : ∀ t : ℝ, tsupport (fun x : Vec3 => b (x, t)) ⊆ Ω') :
    (∫ z, d z * b z) = -(∫ z, a z * spatialPartial b j z) := by
  have hleft_box := hleft.mono_measure
    (Measure.restrict_le_self :
      volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  have hright_box := hright.mono_measure
    (Measure.restrict_le_self :
      volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  change Integrable (fun q : Vec3 × ℝ => d (q.1, q.2) * b q)
      (((volume : Measure Vec3).prod volume).restrict (Ω' ×ˢ J)) at hleft_box
  change Integrable (fun q : Vec3 × ℝ => a (q.1, q.2) * spatialPartial b j q)
      (((volume : Measure Vec3).prod volume).restrict (Ω' ×ˢ J)) at hright_box
  rw [← Measure.prod_restrict Ω' J] at hleft_box hright_box
  have hleft_slice := hleft_box.prod_left_ae
  have hright_slice := hright_box.prod_left_ae
  have hslice : ∀ᵐ t ∂volume.restrict J,
      (∫ x in Ω', d (x, t) * b (x, t)) =
        -(∫ x in Ω', a (x, t) * spatialPartial b j (x, t)) := by
    filter_upwards [hgrad, hleft_slice, hright_slice]
      with t hgt hleft_t hright_t
    have htest := hgt (fun x : Vec3 => b (x, t))
      (hb t) (hbc t) (hbΩ t)
    have hpartial : ∀ x : Vec3,
        spatialPartial b j (x, t) =
          (fderiv ℝ (fun y : Vec3 => b (y, t)) x) (basisVec j) := by
      intro x
      rfl
    calc
      (∫ x in Ω', d (x, t) * b (x, t)) =
          -(-(∫ x in Ω', d (x, t) * b (x, t))) := by ring
      _ = -(∫ x in Ω', a (x, t) *
          (fderiv ℝ (fun y : Vec3 => b (y, t)) x) (basisVec j)) := by
        rw [← htest]
      _ = -(∫ x in Ω', a (x, t) * spatialPartial b j (x, t)) := by
        congr 1
  calc
    (∫ z, d z * b z) =
        ∫ t, ∫ x in Ω', d (x, t) * b (x, t) :=
      global_integral_eq_box_slices hleft hzero_left
    _ = ∫ t, -(∫ x in Ω', a (x, t) * spatialPartial b j (x, t)) := by
      apply integral_congr_ae
      have hslice' := (ae_restrict_iff' hJ).mp hslice
      filter_upwards [hslice'] with t ht
      by_cases htJ : t ∈ J
      · exact ht htJ
      · have hleft_zero : (∫ x in Ω', d (x, t) * b (x, t)) = 0 := by
          calc
            (∫ x in Ω', d (x, t) * b (x, t)) = ∫ x in Ω', (0 : ℝ) := by
              apply integral_congr_ae
              filter_upwards [] with x
              apply hzero_left (x, t)
              intro hbox
              exact htJ hbox.2
            _ = 0 := by simp
        have hright_zero :
            (∫ x in Ω', a (x, t) * spatialPartial b j (x, t)) = 0 := by
          calc
            (∫ x in Ω', a (x, t) * spatialPartial b j (x, t)) =
                ∫ x in Ω', (0 : ℝ) := by
              apply integral_congr_ae
              filter_upwards [] with x
              apply hzero_right (x, t)
              intro hbox
              exact htJ hbox.2
            _ = 0 := by simp
        rw [hleft_zero, hright_zero]
        simp
    _ = -(∫ z, a z * spatialPartial b j z) := by
      rw [integral_neg]
      congr 1
      exact (global_integral_eq_box_slices hright hzero_right).symm

end CKN.Core.Step3
