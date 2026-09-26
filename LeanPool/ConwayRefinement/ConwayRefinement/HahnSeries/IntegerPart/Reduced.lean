/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Order.Archimedean.Class

/-!
# Reduced Hahn series

LM24, Definition 8.2.6 calls a nonzero series reduced when the intersection of its support with
the support after subtracting one lies in a single Archimedean class. We retain the zero class:
`ArchimedeanClass.mk 0 = ⊤`. This matters when the constant coefficient is neither zero nor one,
and distinguishes the printed definition from the incorrect variant that inspects only nonzero
exponents.
-/

public section

namespace HahnSeries.Nonpositive

variable {G R : Type*}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Ring R]

/-- LM24, Definition 8.2.6: a nonzero nonpositive Hahn series whose support and shifted support
intersect in one Archimedean class. The class may be the zero class `⊤`. -/
def IsReduced (b : Nonpositive G R) : Prop :=
  b ≠ 0 ∧ ∃ c : ArchimedeanClass G,
    (b : R⟦G⟧).support ∩ ((b - 1 : Nonpositive G R) : R⟦G⟧).support ⊆
      {x | ArchimedeanClass.mk x = c}

/-- Elimination rule for reducedness. -/
theorem IsReduced.elim {b : Nonpositive G R} (hb : IsReduced b) :
    b ≠ 0 ∧ ∃ c : ArchimedeanClass G,
      (b : R⟦G⟧).support ∩ ((b - 1 : Nonpositive G R) : R⟦G⟧).support ⊆
        {x | ArchimedeanClass.mk x = c} :=
  hb

/-- Introduction rule for reducedness. -/
theorem isReduced_of_support_inter_support_sub_one_subset {b : Nonpositive G R}
    (hb : b ≠ 0) (c : ArchimedeanClass G)
    (hsupport :
      (b : R⟦G⟧).support ∩ ((b - 1 : Nonpositive G R) : R⟦G⟧).support ⊆
        {x | ArchimedeanClass.mk x = c}) :
    IsReduced b :=
  ⟨hb, c, hsupport⟩

end HahnSeries.Nonpositive
