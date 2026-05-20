/-
Copyright (c) 2026 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import LeanPool.LeanFibredCategories.ForMathlib

/-!
# Cartesian Morphisms for Fibred Categories

Source: doi:10.1017/CBO9780511525865
Authors: Sina Hazratpour
Status: verified
Main declarations: `CategoryTheory.BasedLift`, `CategoryTheory.CartMor`
Tags: category-theory, fibrations, cartesian-morphisms
MSC: 18D30, 18A22
-/

/-!
## Mathematical overview

This pool entry vendors the *For_Mathlib* core of Sina Hazratpour's Lean4
formalisation of category-theory API used in fibred-category developments. It
does not claim a complete formalization of Grothendieck fibrations; the delivered
scope is the infrastructure around fibers and cartesian morphisms.

The development gives foundational API for the type `Fiber` of the fiber of a
functor at a base object, the category structure on these fibers, the type
`BasedLift` of lifts of morphisms in the base, the typeclass
`BasedLift.Cartesian` for cartesian based-lifts, the class `CartMor` of
cartesian morphisms in the domain category and its closure properties (identity,
composition, isomorphisms, pullbacks), the category of cartesian morphisms, and
the total category `∫ P` of a functor.

The Lean code is imported from <https://github.com/sinhp/LeanFibredCategories>.
-/
