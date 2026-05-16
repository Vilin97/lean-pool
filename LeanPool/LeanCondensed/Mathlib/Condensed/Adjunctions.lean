/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Condensed.Module

/-!
# Adjunctions regarding categories of condensed objects

This file records faithfulness of the forgetful functor from condensed
modules to condensed sets.
-/

universe u

variable (R : Type _) [Ring R]

open CategoryTheory

namespace Condensed

instance : (Condensed.forget R).Faithful := (inferInstance : (sheafCompose _ _).Faithful)

end Condensed
