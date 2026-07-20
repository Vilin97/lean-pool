/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
import LeanPool.PartialCombinatoryAlgebras.Basic
import LeanPool.PartialCombinatoryAlgebras.CombinatoryAlgebra

/-! # Free (total) combinatory algebra -/

namespace LeanPool.PartialCombinatoryAlgebras

namespace FreeCA

/-- The underlying expressions fo the free combinatory algebra -/
inductive Expr where
| K : Expr
| S : Expr
| app : Expr → Expr → Expr

instance exprHasDot : HasDot Expr where dot := Expr.app

/-- The equational axioms of the free combinatory algebra.
    Symmetry and transitivity are commented out because
    so far we have not needed them. -/
inductive eq : Expr → Expr → Prop where
| refl : ∀ {a}, eq a a
| app : ∀ {a b c d}, eq a b → eq c d → eq (a ⬝ c) (b ⬝ d)
| K : ∀ {a b}, eq (.app (.app .K a) b) a
| S : ∀ {a b c}, eq (.app (.app (.app .S a) b) c) (.app (.app a c) (.app b c))

@[inherit_doc]
infix:40 " ≈ " => eq

/-- The carrier of the free total combinatory algebra -/
@[reducible]
def carrier := Quot eq

/-- Convert an expression to a (defined) partial element of the carrier. -/
@[reducible]
def mk := Quot.mk eq

instance hasDot : HasDot carrier where
  dot := Quot.lift₂ (fun (x y : Expr) => mk (x ⬝ y))
    (by intros a b c e'; exact Quot.sound (.app .refl ‹_›))
    (by intros a b c e'; exact Quot.sound (.app ‹_› .refl))

@[simp]
theorem eq_mk_app (a b : Expr) : mk a ⬝ mk b = mk (a ⬝ b) := rfl

end FreeCA

/-- The free combinatory algebra -/
instance FreeCA : CA FreeCA.carrier where
  K := FreeCA.mk .K
  S := FreeCA.mk .S

  eq_K := by
    apply Quot.ind; intro a
    apply Quot.ind; intro b
    rw [FreeCA.eq_mk_app, FreeCA.eq_mk_app]
    exact Quot.sound FreeCA.eq.K

  eq_S := by
    apply Quot.ind; intro a
    apply Quot.ind; intro b
    apply Quot.ind; intro c
    rw [FreeCA.eq_mk_app, FreeCA.eq_mk_app, FreeCA.eq_mk_app]
    exact Quot.sound FreeCA.eq.S

end LeanPool.PartialCombinatoryAlgebras
