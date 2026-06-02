/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import LeanPool.QuasiBorelSpaces.MeasureTheory.Cases
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import LeanPool.QuasiBorelSpaces.MeasureTheory.Instances


/-!
# Quasi-Borel Spaces

This file defines the concept of a quasi-borel space, as given by [HeunenKSY17].
-/

open scoped MeasureTheory

/--
A quasi‑borel space consists of a type `A` together with a set of "random
variables" in `ℝ → A` satisfying closure under constants, measurable
precomposition, and gluing along borel partitions.

See [HeunenKSY17], Definition 7.
-/
@[ext]
class QuasiBorelSpace (A : Type*) where
  /--
  `IsVar φ` denotes whether `φ` is a random variable. Variables can be
  approximately thought of as the measurable functions in `ℝ → A`.
  Avoid using this predicate directly. Prefer `IsHom` instead.
  -/
  IsVar : (ℝ → A) → Prop
  /-- Variables are closed under constant functions. -/
  isVar_const (x : A) : IsVar (fun _ : ℝ ↦ x)
  /-- Variables are closed under precomposition with measurable functions. -/
  isVar_comp {f : ℝ → ℝ} {φ : ℝ → A}
    : Measurable f
    → IsVar φ
    → IsVar (fun r ↦ φ (f r))
  /-- Variables are closed under gluing of countable families. -/
  isVar_cases' {ix : ℝ → ℕ} {φ : ℕ → ℝ → A}
    : Measurable ix
    → (∀n, IsVar (φ n))
    → IsVar (fun r ↦ φ (ix r) r)

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace QuasiBorelSpace

attribute [fun_prop] IsVar isVar_const isVar_comp

/--
A function `f : A → B` between `QuasiBorelSpace`s is a _morphism_ if it
preserves variables under pre-composition.

See [HeunenKSY17], Definition 11.
-/
@[fun_prop]
inductive IsHom (f : A → B) : Prop where
  /-- Do not use this directly. -/
  | intro : (∀⦃φ⦄, IsVar φ → IsVar (fun x ↦ f (φ x))) → IsHom f

@[inherit_doc IsHom]
scoped notation "IsHom[" inst₁ ", " inst₂ "]" => @IsHom _ _ inst₁ inst₂

/-- Every `MeasurableSpace` induces a `QuasiBorelSpace`. -/
@[reducible] def ofMeasurableSpace [MeasurableSpace A] : QuasiBorelSpace A where
  IsVar φ := Measurable φ
  isVar_const x := measurable_const
  isVar_comp := by fun_prop
  isVar_cases' := by apply MeasureTheory.measurable_cases

namespace Real
instance : QuasiBorelSpace ℝ := ofMeasurableSpace
end Real

namespace ENNReal
instance : QuasiBorelSpace ENNReal := ofMeasurableSpace
end ENNReal

namespace «Prop»
instance : QuasiBorelSpace Prop := ofMeasurableSpace
end «Prop»

namespace Bool
instance : QuasiBorelSpace Bool := ofMeasurableSpace
end Bool

namespace Empty
instance : QuasiBorelSpace Empty := ofMeasurableSpace
end Empty

namespace PEmpty
instance : QuasiBorelSpace PEmpty := ofMeasurableSpace
end PEmpty

namespace Unit
instance : QuasiBorelSpace Unit := ofMeasurableSpace
end Unit

namespace PUnit
instance : QuasiBorelSpace PUnit := ofMeasurableSpace
end PUnit

namespace Nat
instance : QuasiBorelSpace Nat := ofMeasurableSpace
end Nat

/--
Every `QuasiBorelSpace` induces a `MeasurableSpace`.

See [HeunenKSY17], Proposition 14.
-/
@[reducible] def toMeasurableSpace : MeasurableSpace A where
  MeasurableSet' X := ∀{φ : ℝ → A}, IsHom φ → MeasurableSet (φ ⁻¹' X)
  measurableSet_empty hφ := by
    simp only [Set.preimage_empty, MeasurableSet.empty]
  measurableSet_compl X hX φ hφ := by
    simp only [Set.preimage_compl, MeasurableSet.compl_iff]
    apply hX
    apply hφ
  measurableSet_iUnion f hf φ hφ := by
    simp only [Set.preimage_iUnion]
    apply MeasurableSet.iUnion
    intro n
    apply hf
    apply hφ

/-- We can lift a `QuasiBorelSpace` from one type to another. -/
@[reducible] def lift (f : B → A) : QuasiBorelSpace B where
  IsVar φ := IsVar fun x ↦ f (φ x)
  isVar_const x := isVar_const (f x)
  isVar_comp := isVar_comp
  isVar_cases' := isVar_cases'

instance : Inhabited (QuasiBorelSpace A) where
  default := @ofMeasurableSpace _ ⊤

end QuasiBorelSpace

/--
A _measurable quasi-borel space_ is the quasi-borel space where the notion of
variable aligns with measurable functions.
-/
class MeasurableQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] where
  /-- Variables are measurable functions. -/
  isHom_iff_measurable (φ : ℝ → A) : QuasiBorelSpace.IsHom φ ↔ Measurable φ

/--
A _discrete quasi-borel space_ is the quasi-borel space analogue of the discrete
measurable space.
-/
class DiscreteQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] : Prop
  extends DiscreteMeasurableSpace A, MeasurableQuasiBorelSpace A

instance {A : Type*} [QuasiBorelSpace A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : DiscreteQuasiBorelSpace A := ⟨⟩
