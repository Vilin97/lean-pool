/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationErrorDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScaling

/-! # Basic -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# Basic Helpers for Chapter 2.5 Homogenization Error

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

@[simp] theorem scaleResponseAtScale_infinity_eq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℤ) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q k .infinity a a0 =
      Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k a a0)
        (1 / 2 : ℝ) := rfl

@[simp] theorem homogenizationErrorFinite_infinity_one_eq_tsum {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    HomogenizationErrorFinite Q n s .infinity 1 a a0 =
      ∑' l : ℕ,
        geometricWeight s 1 l *
          scaleResponseAtScale Q (n - (l : ℤ)) .infinity a a0 := by
  unfold HomogenizationErrorFinite
  simp

@[simp] theorem homogenizationErrorOnCube_infinity_one_eq_tsum {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 =
      ∑' l : ℕ,
        geometricWeight s 1 l *
          scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0 := by
  unfold HomogenizationErrorOnCube HomogenizationError
  simp

@[simp] theorem maxDescendantNormalizedBlockResponseAtScale_self {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q Q.scale a a0 =
      normalizedBlockResponseMax Q a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSupReal
  rw [descendantsAtScale_self]
  simp

@[simp] theorem scaleResponseAtScale_infinity_self_eq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q Q.scale .infinity a a0 =
      Real.rpow (normalizedBlockResponseMax Q a a0) (1 / 2 : ℝ) := by
  simp [scaleResponseAtScale_infinity_eq]

/-- Average over a finite image, specialized to the public Chapter 2
`finsetAverageReal` convention. -/
theorem finsetAverageReal_image {α β : Type*} [DecidableEq β] (s : Finset α)
    (φ : α → β) (hφ : Set.InjOn φ (↑s : Set α)) (f : β → ℝ) (g : α → ℝ)
    (hfg : ∀ x ∈ s, f (φ x) = g x) :
    finsetAverageReal (s.image φ) f = finsetAverageReal s g := by
  unfold finsetAverageReal
  rw [Finset.card_image_of_injOn hφ, Finset.sum_image hφ]
  exact congrArg (fun x : ℝ => ((s.card : ℝ)⁻¹) * x)
    (Finset.sum_congr rfl hfg)

/-- Translating triadic cube indices by a fixed shift is injective. -/
theorem translateCube_injective {d : ℕ} (z : Fin d → ℤ) :
    Function.Injective (translateCube z : TriadicCube d → TriadicCube d) := by
  intro Q R hQR
  cases Q with
  | mk Qscale Qindex =>
      cases R with
      | mk Rscale Rindex =>
          have hscale : Qscale = Rscale := congrArg TriadicCube.scale hQR
          have hindex : Qindex = Rindex := by
            funext i
            have hi := congrArg (fun S : TriadicCube d => S.index i) hQR
            change Qindex i + z i = Rindex i + z i at hi
            exact add_right_cancel hi
          cases hscale
          cases hindex
          rfl

end

end Ch02
end Book
end Homogenization
