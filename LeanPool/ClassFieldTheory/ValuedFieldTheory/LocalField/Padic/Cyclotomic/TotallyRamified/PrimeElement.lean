/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralClosure
/-!
# A prime element for the totally ramified cyclotomic extension

This file proves directly from its norm that `1 - ζ` is prime in the explicit DVR `ℤ_[p][ζ]`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedPrimeElementAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedPrimeElementScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The element `1 - ζ`, viewed in the explicit integer ring `ℤ_[p][ζ]`. -/
def padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger (ζ : L) :
    Algebra.adjoin ℤ_[p] ({ζ} : Set L) :=
  ⟨1 - ζ, Subalgebra.sub_mem _ (Subalgebra.one_mem _)
    (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)⟩

/-- the totally ramified cyclotomic theorem(iv): `1 - ζ` is a prime element of `ℤ_[p][ζ]`. -/
theorem padicCyclotomicTotallyRamified_one_sub_primitiveRoot_prime
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    Prime (padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger (p := p) ζ) := by
  let α : L := ζ - 1
  have hintα : IsIntegral ℤ_[p] α := by
    exact (padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt ζ hζ).sub isIntegral_one
  let Aζ := Algebra.adjoin ℤ_[p] ({ζ} : Set L)
  let A := Algebra.adjoin ℤ_[p] ({α} : Set L)
  let : Module.IsTorsionFree ℤ_[p] L :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[p] ℚ_[p] L
  let B : PowerBasis ℤ_[p] A := Algebra.adjoin.powerBasis' hintα
  let : Module.Finite ℤ_[p] A := B.finite
  let : Module.Free ℤ_[p] A := Module.Free.of_basis B.basis
  have hadjoin : Aζ = A := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change ζ ∈ A
      simpa [α] using Subalgebra.add_mem _
        (Algebra.self_mem_adjoin_singleton ℤ_[p] α)
        (Subalgebra.one_mem _)
    · apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change α ∈ Aζ
      exact Subalgebra.sub_mem _
        (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
        (Subalgebra.one_mem _)
  let : IsDiscreteValuationRing Aζ := by
    simpa [Aζ] using
      padicCyclotomicTotallyRamified_adjoin_isDiscreteValuationRing ζ hζ hgen
  let e : Aζ ≃+* A := (Subalgebra.equivOfEq Aζ A hadjoin).toRingEquiv
  let : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmin : minpoly ℤ_[p] α =
      padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k := by
    simpa [α] using padicCyclotomicTotallyRamified_minpoly_sub_one_padicInt ζ hζ hgen
  have hnorm : Algebra.norm ℤ_[p] B.gen =
      (-1) ^ B.dim * (p : ℤ_[p]) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      ← Algebra.adjoin.powerBasis'_minpoly_gen hintα, hmin,
      coeff_zero_eq_eval_zero]
    simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, eval_comp]
  have hirrNorm : Irreducible (Algebra.norm ℤ_[p] B.gen) := by
    rw [hnorm]
    have ha : Associated
        (((-1 : ℤ_[p]) ^ B.dim) * (p : ℤ_[p])) (p : ℤ_[p]) :=
      associated_unit_mul_left _ _ (isUnit_neg_one.pow _)
    exact ha.symm.irreducible PadicInt.irreducible_p
  let : IsLocalHom (Algebra.norm ℤ_[p] : A →* ℤ_[p]) :=
    ⟨fun y hy => (padicCyclotomicTotallyRamified_norm_isUnit_iff y).mp hy⟩
  have hirrGen : Irreducible B.gen := hirrNorm.of_map
  have hirrNegGen : Irreducible (-B.gen) := by
    have ha : Associated (-B.gen) B.gen :=
      (Associated.refl B.gen).neg_left
    exact ha.symm.irreducible hirrGen
  have hprimeNegGen : Prime (-B.gen) := hirrNegGen.prime
  apply (MulEquiv.prime_iff e).mp
  convert hprimeNegGen using 1
  apply Subtype.ext
  simp [e, padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger, B,
    Algebra.adjoin.powerBasis'_gen, α, Aζ, A]

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
