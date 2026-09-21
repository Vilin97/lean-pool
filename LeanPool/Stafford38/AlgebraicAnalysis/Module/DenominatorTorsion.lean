/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# Generic denominator clearing and torsion quotients

This is the unconditional part of packet 9.  It separates the algebraic
quotient argument from the still-unformalized triangular PBW reduction.  An
explicit clearing witness for each vector implies torsion of the quotient;
the principal right-ideal case is proved directly from the opposite Ore
condition.  No stage freeness or noncommutative flatness is postulated.
-/

namespace AlgebraicAnalysis
namespace DenominatorTorsion

open nonZeroDivisors
open MulOpposite

universe u v

section AbstractClearance

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- Right-module torsion, with the right scalar displayed as `op s`. -/
def IsTorsionRight : Prop :=
  ∀ m : M, ∃ s : R, s ≠ 0 ∧ (op s) • m = 0

/-- A denominator-clearing witness for a right submodule quotient. -/
def HasDenominatorClearance (N : Submodule Rᵐᵒᵖ M) : Prop :=
  ∀ m : M, ∃ s : R, s ≠ 0 ∧ (op s) • m ∈ N

theorem quotient_isTorsion_of_clearance
    (N : Submodule Rᵐᵒᵖ M)
    (hclear : HasDenominatorClearance (R := R) N) :
    IsTorsionRight (R := R) (M := M ⧸ N) := by
  intro z
  refine Submodule.Quotient.induction_on N z ?_
  intro m
  rcases hclear m with ⟨s, hs, hsm⟩
  refine ⟨s, hs, ?_⟩
  change N.mkQ ((op s) • m) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hsm

end AbstractClearance

section PrincipalRightIdeal

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]
variable [OreLocalization.OreSet (Rᵐᵒᵖ)⁰]

/-- Left multiplication by `q` is a right-`R`-linear map. -/
def leftMulLinear (q : R) : R →ₗ[Rᵐᵒᵖ] R where
  toFun x := q * x
  map_add' x y := by
    change q * (x + y) = q * x + q * y
    rw [mul_add]
  map_smul' a x := by
    change q * (x * (unop a)) = (q * x) * (unop a)
    rw [mul_assoc]

/-- The right ideal `qR`, represented as the range of left multiplication. -/
def principalRightIdeal (q : R) : Submodule Rᵐᵒᵖ R :=
  LinearMap.range (leftMulLinear q)
theorem principalRightIdeal_mem (q x : R) :
    q * x ∈ principalRightIdeal q := by
  exact ⟨x, rfl⟩

theorem principal_quotient_isTorsion (q : R) (hq : q ≠ 0) :
    IsTorsionRight (R := R)
      (M := R ⧸ principalRightIdeal q) := by
  intro z
  refine Submodule.Quotient.induction_on (principalRightIdeal q) z ?_
  intro x
  let qop : (Rᵐᵒᵖ)⁰ :=
    ⟨op q, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using hq)⟩
  rcases OreLocalization.oreCondition (op x) qop with ⟨num, den, hOre⟩
  let denR : R := unop (den : Rᵐᵒᵖ)
  have hOre' : x * denR = q * unop num := by
    have h := congrArg unop hOre
    simpa only [unop_mul, unop_op, denR, qop] using h
  refine ⟨denR, ?_, ?_⟩
  · intro hden
    have hden' : (den : Rᵐᵒᵖ) = 0 := by
      apply unop_injective
      simpa [denR] using hden
    exact (nonZeroDivisors.coe_ne_zero den) hden'
  change (principalRightIdeal q).mkQ ((op denR) • x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨unop num, ?_⟩
  change q * unop num = x * denR
  exact hOre'.symm

end PrincipalRightIdeal


end DenominatorTorsion
end AlgebraicAnalysis
