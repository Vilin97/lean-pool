/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Growth

/-!
# Deligne's theorem on tensor categories

`DeligneTheoremStatement`, carrying Deligne's own hypotheses with
`DeligneFibreFunctor` as its conclusion, is stated in
`RS/Definitions.lean`, together with a hypothesis-by-hypothesis
correspondence against Théorème 0.6 and §0.1 of *Catégories
tensorielles* (Moscow Math. J. **2** (2002), 227–248; see also
Ostrik, arXiv:math/0401347, Thm 2.3).  It is proved in
`RS/Classical/Deligne/`, as `RS.deligne_theorem`.

This module carries the step from the conclusion to the consumed
interface: `DeligneFibreFunctor.toPackage` forgets faithfulness and
exactness, leaving the symmetric monoidal ℂ-linear functor the
development uses (`DelignePackage`).  The conclusion is taken in
fibre-functor form rather than as the ⊗-equivalence with the
representations of a supergroup, which yields the functor by
composing with the forgetful functor.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

/-- Forgetting exactness and faithfulness of a Deligne fibre functor
leaves the structure the development consumes. -/
def DeligneFibreFunctor.toPackage {A : Type*} [Category A]
    [MonoidalCategory A] [SymmetricCategory A] [Preadditive A]
    [Linear ℂ A] (F : DeligneFibreFunctor A) : DelignePackage A where
  ω := F.ω
  braided := F.braided
  additive := F.additive
  linear := F.linear

end RS
