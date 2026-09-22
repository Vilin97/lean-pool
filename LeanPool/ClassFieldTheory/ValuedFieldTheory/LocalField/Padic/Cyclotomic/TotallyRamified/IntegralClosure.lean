/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial
/-!
# The integral closure in the totally ramified cyclotomic extension

This file identifies `ℤ_[p][ζ]` with the actual integral closure and proves
that it is a discrete valuation ring.
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

/-- The `ℤ_[p]`-algebra on the cyclotomic extension is induced through `ℚ_[p]`. -/
local instance padicCyclotomicTotallyRamifiedIntegralClosureAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedIntegralClosureScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- the totally ramified cyclotomic theorem(iii): `ℤ_[p][ζ]` is the integral closure of `ℤ_[p]`
in `ℚ_[p](ζ)`.  Since the base is complete, the integral closure is the
unique valuation ring upstairs. -/
theorem padicCyclotomicTotallyRamified_isIntegralClosure_adjoin
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set L)) ℤ_[p] L := by
  let n := p ^ (k + 1)
  let : NeZero n := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let hcycl : IsCyclotomicExtension {n} ℚ_[p] L := by
    simpa [n] using padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  let : FiniteDimensional ℚ_[p] L :=
    IsCyclotomicExtension.finiteDimensional {n} ℚ_[p] L
  let : Algebra.IsSeparable ℚ_[p] L := by infer_instance
  have hirr : Irreducible (cyclotomic n ℚ_[p]) := by
    simpa [n] using padicCyclotomicPolynomial_irreducible_prime_pow_succ p k
  have hintζ : IsIntegral ℤ_[p] ζ :=
    padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt ζ hζ
  have hintα : IsIntegral ℤ_[p] (ζ - 1) := hintζ.sub isIntegral_one
  let Bζ := hζ.powerBasis ℚ_[p]
  let Bα := hζ.subOnePowerBasis ℚ_[p]
  have hintBζ : IsIntegral ℤ_[p] Bζ.gen := by
    simpa [Bζ] using hintζ
  have hintBα : IsIntegral ℤ_[p] Bα.gen := by
    simpa [Bα] using hintα
  have hadjoin :
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) =
        Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      simpa using Subalgebra.add_mem _
        (Algebra.self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
        (Subalgebra.one_mem _)
    · apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subalgebra.sub_mem _
        (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
        (Subalgebra.one_mem _)
  refine ⟨Subtype.val_injective, @fun x => ⟨fun hx => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure hintζ)).isIntegral _)
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ_[p] hintBζ hx
  obtain ⟨u, r, hu⟩ :=
    IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow hζ hirr
  rw [hu] at H
  let uZ : ℤ_[p]ˣ := Units.map (algebraMap ℤ ℤ_[p]) u
  replace H := Subalgebra.smul_mem _ H (↑(uZ⁻¹) : ℤ_[p])
  have huZ : algebraMap ℤ_[p] ℚ_[p] (uZ : ℤ_[p]) = (u : ℚ_[p]) := by
    simp [uZ]
  have huZL : algebraMap ℤ_[p] L (uZ : ℤ_[p]) =
      algebraMap ℚ_[p] L (u : ℚ_[p]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L, huZ]
  have Hζ : (↑(uZ⁻¹) : ℤ_[p]) •
      (((uZ : ℤ_[p]) * (p : ℤ_[p]) ^ r) • x) ∈
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
    simpa [Bζ, Algebra.smul_def, IsScalarTower.algebraMap_apply, huZ, huZL,
      map_mul, map_pow] using H
  have Hpow : (p : ℤ_[p]) ^ r • x ∈
      Algebra.adjoin ℤ_[p] ({Bα.gen} : Set L) := by
    rw [hadjoin] at Hζ
    simpa [Bα, ← mul_smul, mul_assoc] using Hζ
  have hmin :
      (minpoly ℤ_[p] Bα.gen).IsEisensteinAt
        (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
    rw [show Bα.gen = ζ - 1 by simp [Bα],
      padicCyclotomicTotallyRamified_minpoly_sub_one_padicInt ζ hζ hgen]
    exact padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt p k
  have hxα : x ∈ Algebra.adjoin ℤ_[p] ({Bα.gen} : Set L) :=
    mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (n := r) PadicInt.prime_p hintBα hx Hpow hmin
  rw [show Algebra.adjoin ℤ_[p] ({Bα.gen} : Set L) =
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) by simpa [Bα] using hadjoin.symm] at hxα
  exact hxα

/-- Literal ring-of-integers equality in the totally ramified cyclotomic theorem(iii). -/
theorem padicCyclotomicTotallyRamified_integralClosure_eq_adjoin
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    integralClosure ℤ_[p] L = Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  let hIC := padicCyclotomicTotallyRamified_isIntegralClosure_adjoin ζ hζ hgen
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := hIC.isIntegral_iff.mp hx
    rw [← hy]
    exact y.2
  · exact adjoin_le_integralClosure
      (padicCyclotomicTotallyRamified_primitiveRoot_isIntegral_padicInt ζ hζ)

/-- The explicit ring `ℤ_[p][ζ]` is a DVR.  This transports the standard
finite-integral-closure theorem across the concrete equivalence between
`ℤ_[p]` and the valuation subring of `ℚ_[p]`. -/
theorem padicCyclotomicTotallyRamified_adjoin_isDiscreteValuationRing
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    IsDiscreteValuationRing (Algebra.adjoin ℤ_[p] ({ζ} : Set L)) := by
  let n := p ^ (k + 1)
  let : NeZero n := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : IsCyclotomicExtension {n} ℚ_[p] L := by
    simpa [n] using padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  let : FiniteDimensional ℚ_[p] L :=
    IsCyclotomicExtension.finiteDimensional {n} ℚ_[p] L
  let : Algebra.IsSeparable ℚ_[p] L := by infer_instance
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let V := base.valuationSubring
  let : Algebra V L :=
    ((algebraMap ℚ_[p] L).comp (algebraMap V ℚ_[p])).toAlgebra
  let : IsScalarTower V ℚ_[p] L := IsScalarTower.of_algebraMap_eq' rfl
  let e : ℤ_[p] ≃+* V :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p
  have he : (algebraMap V L).comp e.toRingHom = algebraMap ℤ_[p] L := by
    ext z
    rfl
  let eIC : integralClosure ℤ_[p] L ≃+* integralClosure V L :=
    { toFun := fun z => ⟨z.1, (e.isIntegral_iff he z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (e.isIntegral_iff he z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let : IsDiscreteValuationRing (integralClosure V L) :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosure_isDiscreteValuationRing_of_finite_separable
      base
  let : IsDiscreteValuationRing (integralClosure ℤ_[p] L) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eIC.symm
  let eA : integralClosure ℤ_[p] L ≃+*
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) :=
    (Subalgebra.equivOfEq _ _
      (padicCyclotomicTotallyRamified_integralClosure_eq_adjoin ζ hζ hgen)).toRingEquiv
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
