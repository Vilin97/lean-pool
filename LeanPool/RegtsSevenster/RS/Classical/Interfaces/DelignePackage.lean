/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.SuperVect

/-!
# The Deligne fibre-functor interface

What the development actually consumes from a fibre functor.
Deligne's theorem is stated with his own hypotheses in
`DeligneTheorem.lean`, and its conclusion is
`DeligneFibreFunctor`: an exact, faithful, ℂ-linear symmetric
monoidal functor to super vector spaces.  Only the symmetric
monoidal ℂ-linear structure is used downstream, so exactness and
faithfulness are forgotten here, by
`DeligneFibreFunctor.toPackage`.  Weakening the interface weakens
what is assumed.

The package is stated over an arbitrary carrier, so it can be
instantiated at the constructed envelope; the hypotheses of the
cited theorem are discharged for that envelope in
`RS/Novel/Envelope/EnvDelignePackage.lean`.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-- The Deligne fibre-functor input for a candidate tensor
category: a ℂ-linear symmetric monoidal functor into SuperVect.
This is the conclusion of Deligne's theorem for a category
satisfying its hypotheses, weakened to the structure the
Regts–Sevenster extraction consumes. -/
structure DelignePackage (A : Type*) [Category A] [MonoidalCategory A]
    [SymmetricCategory A] [Preadditive A] [Linear ℂ A] where
  /-- The fibre functor. -/
  ω : A ⥤ SuperVect
  /-- The fibre functor is symmetric monoidal. -/
  braided : ω.Braided
  /-- The fibre functor is additive. -/
  additive : ω.Additive
  /-- The fibre functor is ℂ-linear. -/
  linear : ω.Linear ℂ

end RS
