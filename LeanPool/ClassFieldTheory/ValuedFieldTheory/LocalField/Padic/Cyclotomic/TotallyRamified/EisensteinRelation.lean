/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.PrimeElement
/-!
# The Eisenstein relation for the cyclotomic uniformizer

This file extracts the unit relation `p · u = (ζ - 1)^φ` from the translated Eisenstein polynomial.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

/-- The `ℤ_[p]`-algebra on the cyclotomic extension is induced through `ℚ_[p]`. -/
local instance padicCyclotomicTotallyRamifiedEisensteinRelationAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedEisensteinRelationScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The Eisenstein relation behind total ramification: in
`ℤ_[p][ζ - 1]`, the base prime times a unit is the field generator raised
to the full power-basis degree. -/
theorem padicCyclotomicTotallyRamified_exists_unit_mul_p_eq_sub_one_pow
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    let α : L := ζ - 1
    let A := Algebra.adjoin ℤ_[p] ({α} : Set L)
    ∃ y : A, IsUnit y ∧
      algebraMap ℤ_[p] A (p : ℤ_[p]) * y =
        (⟨α, Algebra.self_mem_adjoin_singleton ℤ_[p] α⟩ : A) ^
          Nat.totient (p ^ (k + 1)) := by
  let α : L := ζ - 1
  have hintα : IsIntegral ℤ_[p] α :=
    (padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt ζ hζ).sub isIntegral_one
  let A := Algebra.adjoin ℤ_[p] ({α} : Set L)
  let : Module.IsTorsionFree ℤ_[p] L :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[p] ℚ_[p] L
  let B : PowerBasis ℤ_[p] A := Algebra.adjoin.powerBasis' hintα
  let : Module.Finite ℤ_[p] A := B.finite
  let : Module.Free ℤ_[p] A := Module.Free.of_basis B.basis
  have hmin : minpoly ℤ_[p] α =
      padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k := by
    simpa [α] using padicCyclotomicTotallyRamified_minpoly_sub_one_padicInt ζ hζ hgen
  have hei : (minpoly ℤ_[p] α).IsEisensteinAt
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
    rw [hmin]
    exact padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt p k
  have heiB : (minpoly ℤ_[p] B.gen).IsEisensteinAt
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
    rw [← Algebra.adjoin.powerBasis'_minpoly_gen hintα]
    exact hei
  obtain ⟨y, _hyMem, hy⟩ :=
    heiB.isWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree
      (minpoly.aeval ℤ_[p] B.gen) (minpoly.monic B.isIntegral_gen)
  have hy' : algebraMap ℤ_[p] A (p : ℤ_[p]) * y = B.gen ^ B.dim := by
    rw [(minpoly.monic B.isIntegral_gen).natDegree_map,
      B.natDegree_minpoly] at hy
    simpa using hy
  have hnorm : Algebra.norm ℤ_[p] B.gen =
      (-1) ^ B.dim * (p : ℤ_[p]) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      ← Algebra.adjoin.powerBasis'_minpoly_gen hintα, hmin,
      coeff_zero_eq_eval_zero]
    simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, eval_comp]
  have hnormEq := congrArg (Algebra.norm ℤ_[p]) hy'
  rw [map_mul, Algebra.norm_algebraMap_of_basis B.basis, map_pow,
    hnorm, mul_pow] at hnormEq
  have hcancel : Algebra.norm ℤ_[p] y =
      ((-1 : ℤ_[p]) ^ B.dim) ^ B.dim := by
    apply mul_left_cancel₀ (pow_ne_zero B.dim PadicInt.prime_p.ne_zero)
    simpa [mul_comm] using hnormEq
  have hyu : IsUnit y := by
    apply (padicCyclotomicTotallyRamified_norm_isUnit_iff (R := ℤ_[p]) (A := A) y).mp
    rw [hcancel]
    exact (isUnit_neg_one.pow _).pow _
  have hdim : B.dim = Nat.totient (p ^ (k + 1)) := by
    calc
      B.dim = (minpoly ℤ_[p] α).natDegree := by simp [B]
      _ = (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).natDegree :=
        congrArg Polynomial.natDegree hmin
      _ = Nat.totient (p ^ (k + 1)) := by
        rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, natDegree_comp,
          show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
          natDegree_X_add_C, mul_one, natDegree_cyclotomic]
  refine ⟨y, hyu, ?_⟩
  rw [hdim] at hy'
  simpa [B, Algebra.adjoin.powerBasis'_gen, α] using hy'

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
