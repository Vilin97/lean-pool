/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Algebra.FactorialTrace
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.ScalarPermTrace

/-!
# Nilpotent categorical traces from the factorial obstruction

The permutation action and scalar cycle-trace formula of an object
form a `CycleTraceTower`. Schrijver's factorial obstruction gives
nilpotent-trace vanishing from a single tensor level of dimension
less than `n!`, and hence from exponential endomorphism growth.
The Frobenius and trace-zeta route is retained in `ObjectTower`.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

variable {A : Type u}

/-- The cycle-trace tower of an object, with no growth assumption. -/
noncomputable def objectCycleTraceTower
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A) :
    CycleTraceTower (fun n => End (tensorPow A X n)) (End X) where
  traceA := scalarTrace hu X
  trace n := scalarTrace hu (tensorPow A X n)
  rep n := {
    toFun := permMor X n
    map_one' := permMor_one X n
    map_mul' := permMor_mul X n
  }
  pow n g := powHom X g n
  cycleTrace n π g := by
    change scalarTrace hu (tensorPow A X n)
      (powHom X g n ≫ permMor X n π) = _
    rw [scalarTrace_comp_comm, scalarTrace_permMor_powHom,
      prod_fullCycleType, pow_one]

/-- A nonzero nilpotent trace forces factorial dimension at every
finite-dimensional tensor level. -/
theorem factorial_le_finrank_of_nonzero_nilpotent_trace
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A) {g : End X} (hg : IsNilpotent g)
    (hτ : scalarTrace hu X g ≠ 0) (n : ℕ)
    [Module.Finite ℂ (End (tensorPow A X n))] :
    n.factorial ≤ Module.finrank ℂ (End (tensorPow A X n)) :=
  (objectCycleTraceTower hu X).factorial_le_finrank hg hτ n

/-- One tensor level of dimension less than its factorial suffices
for nilpotent categorical traces to vanish. -/
theorem scalarTrace_eq_zero_of_finrank_lt_factorial
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A) {n : ℕ}
    [Module.Finite ℂ (End (tensorPow A X n))]
    (hbound : Module.finrank ℂ (End (tensorPow A X n)) < n.factorial)
    {g : End X} (hg : IsNilpotent g) : scalarTrace hu X g = 0 :=
  (objectCycleTraceTower hu X).traceA_eq_zero_of_finrank_lt_factorial
    hbound hg

/-- The factorial proof of nilpotent categorical trace vanishing
under exponential endomorphism growth. -/
theorem scalarTrace_eq_zero_of_isNilpotent_factorial
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A)
    [∀ n, Module.Finite ℂ (End (tensorPow A X n))] (B : ℝ)
    (hbound : ∀ n,
      (Module.finrank ℂ (End (tensorPow A X n)) : ℝ) ≤ B ^ n)
    {g : End X} (hg : IsNilpotent g) : scalarTrace hu X g = 0 :=
  (objectCycleTraceTower hu X).traceA_eq_zero_of_exponential_bound
    B hbound hg

end RS
