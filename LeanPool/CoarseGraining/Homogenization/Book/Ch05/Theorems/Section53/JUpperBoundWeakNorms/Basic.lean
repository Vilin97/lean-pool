/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.Common

/-! # Basic -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# Basic

Basic right-hand-side definitions for the first Section 5.3 lemma.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Private right-hand side for the cutoff-product estimate used in the first
Section 5.3 lemma.  This is just the active deterministic cutoff-product
bound, renamed with the roles used in the manuscript proof. -/
noncomputable def cutoffProductBridgeRHS {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (cutoffGradient : Vec d → Vec d)
    (fluxWeakOne fluxWeakS fluxAverage cutoffCircOne poincareConst
      cutoffConstant centeredCutoffConstant : ℝ) : ℝ :=
  (d : ℝ) *
    (((3 : ℝ) ^ ((d : ℝ) + 1) *
      (cubeBesovScaleWeight (-1) Q * fluxWeakOne)) * cutoffConstant) +
    ((d : ℝ) *
      (fluxAverage * (cubeLpNorm Q ∞ cutoffGradient *
        (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * fluxWeakS)) *
          (cubeBesovScaleWeight s Q * centeredCutoffConstant))))

/-- Private coefficient in the manuscript product estimate after centering the
potential and applying Ch01's legacy disjoint-Besov cutoff-product bound. -/
noncomputable def cutoffProductScaledWeakNormCoeff {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s t B : ℝ) (cutoffGradient : Vec d → Vec d) : ℝ :=
  let gradCoeff :=
    (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ cutoffGradient) *
      ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        (Fintype.card (Fin d) : ℝ))
  let fluxCoeff :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + (1 - s)) *
        cubeBesovScaleWeight (-(1 - s - t)) Q)
  gradCoeff * fluxCoeff

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
