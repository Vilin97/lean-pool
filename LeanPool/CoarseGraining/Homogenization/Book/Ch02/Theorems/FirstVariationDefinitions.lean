/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.ExistenceDefinitions

/-! # First Variation Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for the first-variation theorem.

This is not a definition of maximizer; it is the proposition-valued package
proved by `responseFirstVariationTheory` in `FirstVariation.lean`. Downstream
note-facing wrappers should use that theorem rather than carry this package as
an additional input. -/
structure ResponseFirstVariationTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop where
  first_variation :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        ∀ w : Solution U a, firstVariationValue U a p q v w = 0

namespace ResponseFirstVariationTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hFirst : ResponseFirstVariationTheory U a) :
    ResponseFirstVariationTheory U b where
  first_variation := by
    intro p q v hv w
    let va : Solution U a := Solution.ofAEEq h.symm v
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hmax_a : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hzero := hFirst.first_variation p q va hmax_a wa
    have hvalue :
        firstVariationValue U a p q va wa = firstVariationValue U b p q v w := by
      simpa [va, wa] using firstVariationValue_ofAEEq h.symm p q v w
    simpa [hvalue] using hzero

theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseFirstVariationTheory U a ↔ ResponseFirstVariationTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseFirstVariationTheory

theorem firstVariationValue_eq_zero_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hFirst : ResponseFirstVariationTheory U a) {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) (w : Solution U a) :
    firstVariationValue U a p q v w = 0 :=
  hFirst.first_variation p q v hv w

theorem canonicalMaximizer_firstVariationValue_eq_zero {d : ℕ}
    {U : Domain d} {a : CoeffOn U}
    (hTheory : ResponseExistenceTheory U a)
    (hFirst : ResponseFirstVariationTheory U a) (p q : Vec d)
    (w : Solution U a) :
    firstVariationValue U a p q (canonicalMaximizer hTheory p q).toSolution w = 0 :=
  firstVariationValue_eq_zero_of_isResponseMaximizer hFirst
    (canonicalMaximizer_isMaximizer hTheory p q) w

end

end Ch02
end Book
end Homogenization
