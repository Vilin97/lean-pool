/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointBase
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# The zero-divisor Riemann space and the exact constant field

The functions regular at every exhaustive place form a finite-dimensional
subalgebra of the function field.  Consequently every such function is
algebraic over the constant field.  When the relative algebraic closure of
the constants is trivial, this identifies `L(0)` with the image of the
constant field and gives its finrank exactly equal to one.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance regularConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance regularConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance regularInfinityNonempty : Nonempty (FiniteExtensionInfinityPlace K L) := by
  let _ : Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L
  let _ : Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
    Module.IsTorsionFree.trans_faithfulSMul
      (RatFuncInfinityIntegers K) (RatFunc K) L
  let _ : Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L
  exact Ideal.nonempty_primesOver (ratFuncInfinityPlace K).asIdeal

local instance regularPlaceNonempty : Nonempty (FiniteExtensionPlace K L) :=
  Nonempty.map Sum.inr (regularInfinityNonempty K L)

/-- The subalgebra of functions regular at every exhaustive place. -/
def finiteExtensionRegularSubalgebra : Subalgebra K L where
  carrier := finiteExtensionRiemannSpace K L 0
  add_mem' := (finiteExtensionRiemannSpace K L 0).add_mem
  zero_mem' := (finiteExtensionRiemannSpace K L 0).zero_mem
  mul_mem' := by
    intro x y hx hy
    simpa using finiteExtensionRiemannSpace_mul_mem K L hx hy
  one_mem' := by
    simpa using algebraMap_mem_finiteExtensionRiemannSpace_of_effective
      K L (D := 0) (by simp) (1 : K)
  algebraMap_mem' := by
    intro c
    exact algebraMap_mem_finiteExtensionRiemannSpace_of_effective
      K L (D := 0) (by simp) c

@[simp]
theorem mem_finiteExtensionRegularSubalgebra {x : L} :
    x ∈ finiteExtensionRegularSubalgebra K L ↔
      x ∈ finiteExtensionRiemannSpace K L 0 := Iff.rfl

/-- The regular subalgebra and the zero-divisor Riemann space have the same
underlying vector space. -/
def finiteExtensionRegularSubalgebraEquiv :
    finiteExtensionRegularSubalgebra K L ≃ₗ[K]
      finiteExtensionRiemannSpace K L 0 where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The all-place zero-divisor Riemann space is finite-dimensional. -/
theorem finiteExtensionRiemannSpace_zero_moduleFinite :
    Module.Finite K (finiteExtensionRiemannSpace K L 0) := by
  let Q : FiniteExtensionInfinityPlace K L := Classical.choice inferInstance
  let P : FiniteExtensionPlace K L := .inr Q
  have h := finiteExtensionOnePointRiemannSpace_zero_moduleFinite K L P
  change Module.Finite K
    (finiteExtensionRiemannSpace K L (Finsupp.single P (0 : ℤ))) at h
  have hzero : Finsupp.single P (0 : ℤ) =
      (0 : FiniteExtensionDivisor K L) := by
    ext v
    by_cases hv : v = P <;> simp [hv]
  rw [hzero] at h
  exact h

/-- The everywhere-regular subalgebra is finite-dimensional. -/
theorem finiteExtensionRegularSubalgebra_moduleFinite :
    Module.Finite K (finiteExtensionRegularSubalgebra K L) := by
  let : Module.Finite K (finiteExtensionRiemannSpace K L 0) :=
    finiteExtensionRiemannSpace_zero_moduleFinite K L
  exact Module.Finite.equiv (finiteExtensionRegularSubalgebraEquiv K L).symm

/-- With exact constants, every everywhere-regular function is a constant. -/
theorem finiteExtensionRiemannSpace_zero_eq_range
    (hconstants : algebraicClosure K L = ⊥) :
    finiteExtensionRiemannSpace K L 0 =
      LinearMap.range (Algebra.linearMap K L) := by
  apply le_antisymm
  · intro x hx
    let : Module.Finite K (finiteExtensionRegularSubalgebra K L) :=
      finiteExtensionRegularSubalgebra_moduleFinite K L
    let x' : finiteExtensionRegularSubalgebra K L := ⟨x, hx⟩
    have hxAlg' : IsAlgebraic K x' := IsAlgebraic.of_finite K x'
    have hxAlg : IsAlgebraic K x :=
      hxAlg'.algHom (Subalgebra.val (finiteExtensionRegularSubalgebra K L))
    have hxClosure : x ∈ algebraicClosure K L :=
      mem_algebraicClosure_iff.mpr hxAlg
    rw [hconstants] at hxClosure
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hxClosure
    exact ⟨c, rfl⟩
  · rintro x ⟨c, rfl⟩
    exact algebraMap_mem_finiteExtensionRiemannSpace_of_effective
      K L (D := 0) (by simp) c

/-- With exact constants, `L(0)` has dimension one. -/
theorem finiteExtensionRiemannSpace_zero_finrank
    (hconstants : algebraicClosure K L = ⊥) :
    Module.finrank K (finiteExtensionRiemannSpace K L 0) = 1 := by
  rw [finiteExtensionRiemannSpace_zero_eq_range K L hconstants]
  have hinjective : Function.Injective (Algebra.linearMap K L) :=
    (algebraMap K L).injective
  let e : K ≃ₗ[K] LinearMap.range (Algebra.linearMap K L) :=
    LinearEquiv.ofInjective (Algebra.linearMap K L) hinjective
  calc
    Module.finrank K (LinearMap.range (Algebra.linearMap K L)) =
        Module.finrank K K := e.finrank_eq.symm
    _ = 1 := Module.finrank_self K

end

end BGS.HasseWeil
