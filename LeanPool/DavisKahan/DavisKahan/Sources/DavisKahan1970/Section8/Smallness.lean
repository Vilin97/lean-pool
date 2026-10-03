/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.SelectedBranch

/-! # Smallness -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Theorem 8.2: explicit smallness bridges

The source theorem has two alternatives: small perturbation norm or small
residual norm.  The current continuation library proves the branch conclusion
once a common contour has an explicit projection-Lipschitz coefficient below
`sqrt 2 / 2`.  This file records the exact bridge obligations needed to turn
each printed half-gap hypothesis into that quantitative continuation input.

The bridge records are not axioms and contain no proof admissions.  They are
local proof data that future analytic modules must construct.  In particular,
the residual alternative still needs the Krein replacement step used in the
paper.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan

universe v w

section SmallnessBridges

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- Proof data converting the perturbation-norm half-gap condition in Theorem
8.2 into the quantitative common-contour condition already consumed by the
continuation stack. -/
structure PerturbationHalfGapBridge
    (C : SpectralContinuationWitness A V s) (delta : ℝ) : Prop where
  delta_pos : 0 < delta
  perturbation_small : ‖V‖ < delta / 2
  contour_selects_quarter_branch :
    selectedBranchProjectionLipschitzConstant C.contour V C.margin <
      Real.sqrt 2 / 2

/-- Proof data for the residual-norm alternative in Theorem 8.2.  Besides the
printed residual smallness, it records the nontrivial analytic output of the
Krein replacement argument: a continuation witness for an equivalent
perturbation problem whose selected endpoint is the intended spectral branch. -/
structure ResidualHalfGapBridge
    (C : SpectralContinuationWitness A V s)
    (R : F →L[ℂ] H) (delta : ℝ) : Prop where
  delta_pos : 0 < delta
  residual_small : ‖R‖ < delta / 2
  contour_selects_quarter_branch :
    selectedBranchProjectionLipschitzConstant C.contour V C.margin <
      Real.sqrt 2 / 2

/-- The exact branch conclusion obtained from the perturbation-norm bridge. -/
theorem theorem82_branch_of_perturbationHalfGapBridge
    (C : SpectralContinuationWitness A V s) {delta : ℝ}
    (B : PerturbationHalfGapBridge C delta) :
    SelectedBranchConclusion C :=
  selectedBranchConclusion_of_contour_bound C
    B.contour_selects_quarter_branch

/-- The exact branch conclusion obtained from the residual-norm bridge. -/
theorem theorem82_branch_of_residualHalfGapBridge
    (C : SpectralContinuationWitness A V s)
    (R : F →L[ℂ] H) {delta : ℝ}
    (B : ResidualHalfGapBridge C R delta) :
    SelectedBranchConclusion C :=
  selectedBranchConclusion_of_contour_bound C
    B.contour_selects_quarter_branch

/-! The current Section 8 package stops here: the Section 7 theorem family
supplies the corresponding `sin(2 Theta)` inequalities, while these bridge
theorems add the strict selected-branch conclusion.  Keeping the two layers
separate prevents a generic proposition parameter from masquerading as the
source inequality. -/

end SmallnessBridges

end Section8
end DavisKahan1970
end TauCeti
