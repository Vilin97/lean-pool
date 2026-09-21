/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightIntersection

/-!
# Generic finite triangular denominator arguments

This file records the purely module-theoretic part of the triangular
denominator argument.  The coefficients act on the right, represented by
scalars in `Rᵐᵒᵖ`; in particular `(op s) • m` means `m * s`.

There are two useful forms.  First, a finite family of torsion generators has
one common nonzero denominator, obtained from the finite intersection of their
right annihilator ideals.  Second, explicit denominator clearance through a
finite filtration composes to denominator clearance for the whole quotient.
The hypotheses describing the filtration are data, rather than an assertion
that an arbitrary Ore extension is free or flat.
-/

namespace AlgebraicAnalysis
namespace TriangularDenominator

open MulOpposite
open AlgebraicAnalysis.OreRightIntersection

universe u v

section FiniteGenerators

variable {R : Type u} [Ring R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The right-action map associated to a vector. -/
def rightActionLinear (m : M) : R →ₗ[Rᵐᵒᵖ] M where
  toFun s := (op s) • m
  map_add' s t := by
    simp [add_smul]
  map_smul' a s := by
    change (op (s * unop a)) • m = a • ((op s) • m)
    rw [op_mul, smul_smul]
    rfl

/-- The right annihilator of a vector, represented as a right ideal. -/
def rightAnnihilator (m : M) : Submodule Rᵐᵒᵖ R :=
  LinearMap.ker (rightActionLinear m)

/-- A finite family of torsion vectors admits one common nonzero denominator. -/
theorem finite_vectors_common_annihilator
    {n : ℕ} (g : Fin n → M)
    (hAnn : ∀ i, ∃ s : R, s ≠ 0 ∧ (op s) • g i = 0)
    (hOre : RightOreCondition R) :
    ∃ s : R, s ≠ 0 ∧ ∀ i, (op s) • g i = 0 := by
  classical
  let I : Fin n → Submodule Rᵐᵒᵖ R := fun i => rightAnnihilator (g i)
  have hI : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∃ x ∈ I i, x ≠ 0 := by
    intro i hi
    rcases hAnn i with ⟨s, hs, hsg⟩
    refine ⟨s, ?_, hs⟩
    apply LinearMap.mem_ker.mpr
    exact hsg
  obtain ⟨s, hs, hsI⟩ :=
    exists_mem_finset_rightIdeals (R := R) (Finset.univ : Finset (Fin n)) I hI hOre
  refine ⟨s, hs, ?_⟩
  intro i
  exact LinearMap.mem_ker.mp (hsI i (Finset.mem_univ i))

end FiniteGenerators

section Filtration

variable {R : Type u} [Ring R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- One explicit denominator-clearing step of a filtration. -/
def StepClearance (F : ℕ → Submodule Rᵐᵒᵖ M) (i : ℕ) : Prop :=
  ∀ m : M, m ∈ F (i + 1) →
    ∃ s : R, s ≠ 0 ∧ (op s) • m ∈ F i

/-- Iterating finitely many explicit triangular steps clears a denominator. -/
theorem filtration_clearance
    (F : ℕ → Submodule Rᵐᵒᵖ M) (n : ℕ)
    (hstep : ∀ i < n, StepClearance F i) {m : M} (hm : m ∈ F n) :
    ∃ s : R, s ≠ 0 ∧ (op s) • m ∈ F 0 := by
  induction n generalizing m with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      simpa using hm
  | succ n ih =>
      rcases hstep n (Nat.lt_succ_self n) m hm with ⟨s, hs, hsm⟩
      have hstep' : ∀ i < n, StepClearance F i := by
        intro i hi
        exact hstep i (by omega)
      rcases ih hstep' hsm with ⟨t, ht, htm⟩
      refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
      change (op (s * t)) • m ∈ F 0
      simpa only [op_mul, smul_smul] using htm

/-- A finite cleared filtration makes the terminal quotient torsion. -/
def IsTorsionRight (N : Submodule Rᵐᵒᵖ M) : Prop :=
  ∀ z : M ⧸ N, ∃ s : R, s ≠ 0 ∧ (op s) • z = 0

theorem filtration_quotient_isTorsion
    (F : ℕ → Submodule Rᵐᵒᵖ M) (n : ℕ)
    (hstep : ∀ i < n, StepClearance F i)
    (htop : F n = ⊤) :
    IsTorsionRight (R := R) (M := M) (F 0) := by
  intro z
  refine Submodule.Quotient.induction_on (F 0) z ?_
  intro m
  have hm : m ∈ F n := by
    rw [htop]
    trivial
  rcases filtration_clearance F n hstep hm with ⟨s, hs, hsm⟩
  refine ⟨s, hs, ?_⟩
  change (F 0).mkQ ((op s) • m) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hsm

end Filtration


end TriangularDenominator
end AlgebraicAnalysis
