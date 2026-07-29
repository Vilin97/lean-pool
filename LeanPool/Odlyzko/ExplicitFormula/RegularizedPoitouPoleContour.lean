/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaPoleContour
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouContour

/-!
# Regularized Poitou Pole Contour

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

theorem regularizedPoitou_completedZetaPole_centeredRectangle_identity
    {y δ b T : ℝ} (hδ : 0 < δ) (hb : 1 < b) (hT : 0 < T) :
    horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        (1 - b) b (-T) -
      horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        b (-T) T =
      4 * Real.pi * I *
        poitouTransform (regularizedScaledTartar y δ) 1 := by
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      completedZetaPoleLogDeriv s
  have hanti : ∀ s, q (1 - s) = -q s :=
    mul_antiInvariant_of_invariant_of_antiInvariant
      (fun s ↦ poitouTransform_one_sub
        (regularizedScaledTartar_even y δ) s)
      completedZetaPoleLogDeriv_one_sub
  change
    horizontalIntegral q (1 - b) b (-T) -
        horizontalIntegral q (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral q b (-T) T = _
  rw [← rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    hanti]
  have hpole :=
    rectangleIntegral_mul_completedZetaPoleLogDeriv
      (a := 1 - b) (b := b) (u := -T) (v := T)
      (h := poitouTransform (regularizedScaledTartar y δ))
      (by linarith) hb (by linarith) hT
      (by
        intro z _
        exact analyticOnNhd_poitouTransform_regularizedScaledTartar
          hδ z (mem_univ z))
  have h01 :
      poitouTransform (regularizedScaledTartar y δ) 0 =
        poitouTransform (regularizedScaledTartar y δ) 1 := by
    simpa using
      (poitouTransform_one_sub
        (regularizedScaledTartar_even y δ) (1 : ℂ))
  rw [h01] at hpole
  have hrhs :
      2 * (Real.pi : ℂ) * I *
          (poitouTransform (regularizedScaledTartar y δ) 1 +
            poitouTransform (regularizedScaledTartar y δ) 1) =
        4 * (Real.pi : ℂ) * I *
          poitouTransform (regularizedScaledTartar y δ) 1 := by
    ring
  rw [hrhs] at hpole
  simpa only [q, ofReal_neg] using hpole

end NumberField.Odlyzko
