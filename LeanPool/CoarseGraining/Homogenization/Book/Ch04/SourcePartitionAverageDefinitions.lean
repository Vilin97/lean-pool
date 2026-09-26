/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.PartitionAverageConstants
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.TriadicCubeTranslation

/-!
# Source-carrier partition-average definitions

The exact coarse-source counterparts of the origin-cube partition averages.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- An integrable one-origin source observable centered by its expectation. -/
noncomputable def sourceCenteredObservable {d : ℕ} (P : SourceCoeffLaw d)
    (X : Source.Coarse.Carrier d → ℝ) (_hX_int : Integrable X P) :
    Source.Coarse.Carrier d → ℝ :=
  fun a => X a - ∫ b, X b ∂P

/-- The one-origin source observable transported by an arbitrary integer shift. -/
noncomputable def sourceTranslatedObservable {d : ℕ} (z : Fin d → ℤ)
    (X : Source.Coarse.Carrier d → ℝ) :
    Source.Coarse.Carrier d → ℝ :=
  X ∘ Source.Coarse.Carrier.translate z

/-- The centered average of an integrable one-origin observable transported to
the scale-`n` descendants of the origin cube at scale `m`. -/
noncomputable def sourceCenteredTranslatedDescendantAverage {d : ℕ}
    (P : SourceCoeffLaw d) (n m : ℤ) (_hn : 0 ≤ n) (_hnm : n ≤ m)
    (X : Source.Coarse.Carrier d → ℝ) (_hX_int : Integrable X P) :
    Source.Coarse.Carrier d → ℝ :=
  fun a =>
    ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScale (originCube d m) n,
        (sourceTranslatedObservable (scaleTranslationShift n R) X a - ∫ b, X b ∂P)

end

end Homogenization.Book.Ch04
