/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
import Mathlib.Data.Part

/-!
# Notation and core classes for partial combinatory algebras

A notation for totality of a partial element, a generic class for a
left-associative binary application operator, and the class for a partial
binary operation on a type.
-/

namespace LeanPool.PartialCombinatoryAlgebras

/-- A notation for totality of a partial element (we find writing `x.Dom` a bit silly). -/
notation:50 u:max " ⇓" => Part.Dom u

/-- A generic notation for a left-associative binary operation. -/
class HasDot (A : Type*) where
  /-- (possibly partial) binary application -/
  dot : A → A → A

@[inherit_doc]
infixl:70 " ⬝ " => HasDot.dot

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- Partial application -/
  app : Part A → Part A → Part A

namespace PartialApplication

instance hasDot {A : Type*} [PartialApplication A] : HasDot (Part A) where
  dot := app

end PartialApplication

end LeanPool.PartialCombinatoryAlgebras
