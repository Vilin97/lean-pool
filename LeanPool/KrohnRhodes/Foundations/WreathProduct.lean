/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Pi

/-!
# Wreath products of monoids and semigroup division

* `SgDiv S T` — semigroup division: `S` is a homomorphic image of a subsemigroup of `T`.
* `WreathProduct A B X` — the wreath product of monoids `A` and `B` relative to an action of
  `B` on a type `X`: pairs `(f : X → A, b : B)` with
  `(p * q).func x = p.func (q.base • x) * q.func x` and `(p * q).base = p.base * q.base`
  (the lemmas `WreathProduct.mul_func` / `mul_base`), with its `Monoid` and `Finite` instances.
  Its monoid is that of the transformation wreath product `(A, A) ≀ (X, B)`.

## References

* [Krohn, Rhodes, *Algebraic Theory of Machines. I.*, Trans. AMS 1965]
* [Eilenberg, *Automata, Languages, and Machines, Vol. B*, 1976]
-/

public section

namespace LeanPool.KrohnRhodes

universe u v w

/-! ### Semigroup division -/

/-- Semigroup `S` divides `T` if `S` is a homomorphic image of a subsemigroup of `T`. -/
@[expose]
def SgDiv (S T : Type*) [Mul S] [Mul T] : Prop :=
  ∃ (U : Subsemigroup T) (φ : U →ₙ* S), Function.Surjective φ

/-! ### Wreath product construction -/

/-- The wreath product of monoids `A` and `B` relative to an action of `B` on a type `X`.
    Elements are pairs `(f, b)` where `f : X → A` and `b : B`.

    Multiplication: `(f₁, b₁) * (f₂, b₂) = (fun x => f₁ (b₂ • x) * f₂ x, b₁ * b₂)` -/
@[ext]
structure WreathProduct (A : Type u) (B : Type v) (X : Type w)
    [Monoid A] [Monoid B] [MulAction B X] where
  /-- The decoration function mapping each point of `X` to an element of `A`. -/
  func : X → A
  /-- The bottom component from `B`. -/
  base : B

namespace WreathProduct

variable {A : Type u} {B : Type v} {X : Type w}
variable [Monoid A] [Monoid B] [MulAction B X]

/-- Multiplication in the wreath product.
    Convention: `(f₁, b₁) * (f₂, b₂) = (x ↦ f₁(b₂ • x) * f₂(x), b₁ * b₂)`.

    This is the standard "left regular" convention where the **right** factor's base
    element acts on the **left** factor's decoration. This convention ensures
    associativity with a standard left `MulAction`.

    Note: some references use `f₁(x) * f₂(b₁⁻¹ • x)` (group case) or
    `f₁(x) * f₂(b₁ • x)` (right-action convention). Our choice is equivalent
    up to reversing the action. -/
instance : Mul (WreathProduct A B X) where
  mul p q := ⟨fun x => p.func (q.base • x) * q.func x, p.base * q.base⟩

/-- The identity element of the wreath product. -/
instance : One (WreathProduct A B X) where
  one := ⟨fun _ => 1, 1⟩

@[simp]
theorem mul_func (p q : WreathProduct A B X) (x : X) :
    (p * q).func x = p.func (q.base • x) * q.func x := rfl

@[simp]
theorem mul_base (p q : WreathProduct A B X) :
    (p * q).base = p.base * q.base := rfl

@[simp]
theorem one_func (x : X) : (1 : WreathProduct A B X).func x = 1 := rfl

@[simp]
theorem one_base : (1 : WreathProduct A B X).base = (1 : B) := rfl

/-- The wreath product of monoids is a monoid. -/
instance instMonoid : Monoid (WreathProduct A B X) where
  mul_assoc p q r := by
    ext x
    · -- LHS: ((p*q)*r).func x = (p*q).func (r.base • x) * r.func x
      --     = p.func (q.base • (r.base • x)) * q.func (r.base • x) * r.func x
      -- RHS: (p*(q*r)).func x = p.func ((q*r).base • x) * (q*r).func x
      --     = p.func ((q.base * r.base) • x) * (q.func (r.base • x) * r.func x)
      -- These are equal by mul_smul and mul_assoc
      simp only [mul_func, mul_base, mul_smul, mul_assoc]
    · simp [mul_assoc]
  one_mul p := by
    ext x
    · simp only [mul_func, one_func, one_mul]
    · simp
  mul_one p := by
    ext x
    · simp only [mul_func, one_func, one_base, one_smul, mul_one]
    · simp

/-- The wreath product of finite types is finite. -/
instance instFinite [Finite X] [Finite A] [Finite B] : Finite (WreathProduct A B X) := by
  have : Finite ((X → A) × B) := inferInstance
  exact Finite.of_injective (fun w => (w.func, w.base))
    (fun a b h => by
      have h1 : a.func = b.func := (Prod.mk.inj h).1
      have h2 : a.base = b.base := (Prod.mk.inj h).2
      exact WreathProduct.ext h1 h2)

end WreathProduct

end LeanPool.KrohnRhodes
