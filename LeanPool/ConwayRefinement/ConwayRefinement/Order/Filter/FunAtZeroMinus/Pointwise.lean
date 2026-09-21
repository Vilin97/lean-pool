/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Pointwise identities in `Fun_{0⁻}(V)`

An equation in `Fun_{0⁻}(V)` is an equation between representatives for all `γ < 0` sufficiently
close to `0`. This module collects the forms in which such equations arise: a function at `0⁻`
vanishing, or equal to a constant function, or equal to a constant times a function at `0⁻`, each
reduced to a statement about the representatives on some interval `(-ε, 0)`. A `K`-algebra `A`
acts on `Fun_{0⁻}(A)` through constant functions, and that action is scalar multiplication.
-/

open Filter Topology

public section

universe v

namespace FunAtZeroMinus

variable {V : Type v}

/-- A function at `0⁻` is zero exactly when its representatives vanish near zero. -/
theorem coe_eq_zero_iff [Zero V] (f : ℝ → V) :
    ((f : ℝ → V) : FunAtZeroMinus V) = 0 ↔ ∀ᶠ γ in 𝓝[<] (0 : ℝ), f γ = 0 :=
  Filter.Germ.coe_eq

/-- A function at `0⁻` is zero exactly when its representatives vanish on some `(-ε, 0)`. -/
theorem coe_eq_zero_iff_exists [Zero V] (f : ℝ → V) :
    ((f : ℝ → V) : FunAtZeroMinus V) = 0 ↔ ∃ η < (0 : ℝ), ∀ γ, η < γ → γ < 0 → f γ = 0 := by
  rw [coe_eq_zero_iff, eventually_nhdsLT_iff_exists]

/-- A function at `0⁻` equals a constant function exactly when its representatives take that
value near zero. -/
theorem coe_eq_const_iff (f : ℝ → V) (x : V) :
    ((f : ℝ → V) : FunAtZeroMinus V) = (x : FunAtZeroMinus V) ↔ ∀ᶠ γ in 𝓝[<] (0 : ℝ), f γ = x :=
  Filter.Germ.coe_eq

/-- Two functions at `0⁻` are equal when their representatives agree near zero; the converse is
`Filter.Germ.coe_eq`. -/
theorem coe_eq_coe_of_eventually {f g : ℝ → V} (h : ∀ᶠ γ in 𝓝[<] (0 : ℝ), f γ = g γ) :
    ((f : ℝ → V) : FunAtZeroMinus V) = (g : ℝ → V) :=
  Filter.Germ.coe_eq.mpr h

/-- Addition of constant functions. -/
theorem const_add [Add V] (x y : V) :
    ((x + y : V) : FunAtZeroMinus V) = (x : FunAtZeroMinus V) + (y : FunAtZeroMinus V) := rfl

/-- The constant function `0`. -/
theorem const_zero [Zero V] : ((0 : V) : FunAtZeroMinus V) = 0 := rfl

section Ring

variable {R : Type v} [Semiring R]

/-- A constant function times a function at `0⁻` is the class of the pointwise products. -/
theorem const_mul_coe (x : R) (f : ℝ → R) :
    (x : FunAtZeroMinus R) * ((f : ℝ → R) : FunAtZeroMinus R) =
      ((fun γ ↦ x * f γ : ℝ → R) : FunAtZeroMinus R) :=
  rfl

/-- A function at `0⁻` times a constant function is the class of the pointwise products. -/
theorem coe_mul_const (f : ℝ → R) (x : R) :
    ((f : ℝ → R) : FunAtZeroMinus R) * (x : FunAtZeroMinus R) =
      ((fun γ ↦ f γ * x : ℝ → R) : FunAtZeroMinus R) :=
  rfl

/-- A constant function times a function at `0⁻` is zero exactly when the pointwise products
vanish near zero. -/
theorem const_mul_coe_eq_zero_iff (x : R) (f : ℝ → R) :
    (x : FunAtZeroMinus R) * ((f : ℝ → R) : FunAtZeroMinus R) = 0 ↔
      ∀ᶠ γ in 𝓝[<] (0 : ℝ), x * f γ = 0 := by
  rw [const_mul_coe, coe_eq_zero_iff]

end Ring

section Algebra

variable {K : Type*} {A : Type v} [CommSemiring K] [Semiring A] [Algebra K A]

/-- The constant function of a scalar acts on `Fun_{0⁻}(A)`, `A` a `K`-algebra, by scalar
multiplication. -/
theorem const_algebraMap_mul (k : K) (g : FunAtZeroMinus A) :
    ((algebraMap K A k : A) : FunAtZeroMinus A) * g = k • g := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [← Filter.Germ.coe_smul, const_mul_coe]
    exact congrArg _ (funext fun γ ↦ (Algebra.smul_def k (f γ)).symm)

/-- An element of `Fun_{0⁻}(A)`, `A` a `K`-algebra, times the constant function of a scalar is
scalar multiplication. -/
theorem mul_const_algebraMap (k : K) (g : FunAtZeroMinus A) :
    g * ((algebraMap K A k : A) : FunAtZeroMinus A) = k • g := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [← Filter.Germ.coe_smul, coe_mul_const]
    exact congrArg _ (funext fun γ ↦ (Algebra.commutes k (f γ)).symm.trans
      (Algebra.smul_def k (f γ)).symm)

end Algebra

end FunAtZeroMinus

end
