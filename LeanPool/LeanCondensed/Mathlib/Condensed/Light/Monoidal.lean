/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.Basic
import Mathlib.Condensed.Light.Instances
import Mathlib.Condensed.Light.Monoidal
import Mathlib.Condensed.Light.Small
import LeanPool.LeanCondensed.Projects.MonoidalLinear

/-!
# Monoidal preadditive structure on light condensed modules

The category of light condensed `R`-modules is monoidal preadditive, obtained by
specializing the monoidal preadditive structure on sheaves to the sheafification
adjunction defining light condensed modules.
-/

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : MonoidalPreadditive (LightCondMod.{u} R) :=
  CategoryTheory.Sheaf.monoidalPreadditive _ _

end LightCondensed

end
