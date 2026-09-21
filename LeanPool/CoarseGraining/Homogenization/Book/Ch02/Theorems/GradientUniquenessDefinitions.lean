/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.ExistenceDefinitions

/-! # Gradient Uniqueness Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for uniqueness of the response maximizer gradient.

The statement is deliberately a.e. in the gradient. A later Poincare argument can
upgrade this to uniqueness of the mean-zero representative. The canonical
public theorem proving this package is `responseGradientUniquenessTheory` in
`GradientUniqueness.lean`. -/
structure ResponseGradientUniquenessTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    Prop where
  unique_gradient :
    ∀ p q : Vec d, ∀ v w : Solution U a,
      IsResponseMaximizer U a p q v →
        IsResponseMaximizer U a p q w → Solution.SameGradientAE v w

namespace ResponseGradientUniquenessTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hUnique : ResponseGradientUniquenessTheory U a) :
    ResponseGradientUniquenessTheory U b where
  unique_gradient := by
    intro p q v w hv hw
    let va : Solution U a := Solution.ofAEEq h.symm v
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hmax_v : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hmax_w : IsResponseMaximizer U a p q wa := hw.ofAEEq h.symm
    have hsame := hUnique.unique_gradient p q va wa hmax_v hmax_w
    simpa [Solution.SameGradientAE, va, wa] using hsame

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseGradientUniquenessTheory U a ↔ ResponseGradientUniquenessTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseGradientUniquenessTheory

theorem sameGradientAE_of_response_maximizers {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hUnique : ResponseGradientUniquenessTheory U a)
    {p q : Vec d} {v w : Solution U a}
    (hv : IsResponseMaximizer U a p q v) (hw : IsResponseMaximizer U a p q w) :
    Solution.SameGradientAE v w :=
  hUnique.unique_gradient p q v w hv hw

theorem canonicalMaximizer_sameGradientAE {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a)
    (hUnique : ResponseGradientUniquenessTheory U a)
    {p q : Vec d} {v : Solution U a} (hv : IsResponseMaximizer U a p q v) :
    Solution.SameGradientAE (canonicalMaximizer hTheory p q).toSolution v :=
  sameGradientAE_of_response_maximizers hUnique
    (canonicalMaximizer_isMaximizer hTheory p q) hv

end

end Ch02
end Book
end Homogenization
