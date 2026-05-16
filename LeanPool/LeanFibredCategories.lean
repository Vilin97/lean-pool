/-
Copyright (c) 2026 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import LeanPool.LeanFibredCategories.ForMathlib

/-!
# Lean4 Formalization Of Fibred Categories

Source: https://github.com/sinhp/LeanFibredCategories
Authors: Sina Hazratpour
Status: verified
Main declarations: `CategoryTheory.Fiber`, `CategoryTheory.FiberCat`,
  `CategoryTheory.BasedLift`, `CategoryTheory.CartMor`, `CategoryTheory.TotalCat`
Tags: category-theory, fibrations, cartesian-morphisms
MSC: 18D30, 18A22

This pool entry vendors the *For_Mathlib* core of Sina Hazratpour's Lean4
formalisation of the theory of Grothendieck fibrations. The development gives
foundational API for the type `Fiber` of the fiber of a functor at a base
object, the category structure on these fibers, the type `BasedLift` of lifts of
morphisms in the base, the typeclass `BasedLift.Cartesian` for cartesian
based-lifts, the class `CartMor` of cartesian morphisms in the domain category
and its closure properties (identity, composition, isomorphisms, pullbacks), the
category of cartesian morphisms, and the total category `∫ P` of a functor.
-/
