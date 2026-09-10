/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.Pi

/-!
# Star operations on indicator functions
-/

open scoped ComplexConjugate Indicator


namespace Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp]
public
lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [indicator_apply]



end Set
