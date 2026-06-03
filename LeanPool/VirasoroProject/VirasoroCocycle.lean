/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import LeanPool.VirasoroProject.LieCohomologySmallDegree
import LeanPool.VirasoroProject.WittAlgebra
/-!
# The Virasoro 2-cocycle of the Witt algebra

This file defines the 2-cocycle of the Witt algebra with coefficients in ground field 𝕜, which
defines the (unique) one-dimenensional central extension known as the Virasoro algebra.
It is proven that the Virasoro cocycle is nontrivial, and in particular the cohomology of the
Witt algebra in degree two does not vanish.

## Main definitions

* `WittAlgebra.virasoroCocycle`: The 2-cocycle which defines the Virasoro algebra as a central
  extension of the Witt algebra and whose cohomology class generates H²(WittAlgebra, 𝕜).

## Main statements

* `WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero`: The cohomology class of the Virasoro
  cocycle is nonzero.
* `WittAlgebra.nontrivial_lieTwoCohomology`: The Witt algebra cohomology in degree two is
  nontrivial, H²(WittAlgebra, 𝕜) ≠ 0.

## Tags

Witt algebra, Virasoro algebra, Lie algebra cohomology

-/

namespace VirasoroProject

namespace WittAlgebra

variable (𝕜 : Type*) [Field 𝕜]

/-- A bilinear map version of the Virasoro cocycle.
(Defining formula: `γ (lgen n) (lgen m) = (n^3 - n) / 12 * δ[n+m,0]`.) -/
noncomputable def virasoroCocycleBilin : (WittAlgebra 𝕜) →ₗ[𝕜] (WittAlgebra 𝕜) →ₗ[𝕜] 𝕜 :=
  (lgen 𝕜).constr 𝕜 <| fun n ↦ (lgen 𝕜).constr 𝕜 <| fun m ↦
      if n + m = 0 then (n^3 - n) / 12 else 0

lemma virasoroCocycleBilin_apply_lgen_lgen (n m : ℤ) :
    virasoroCocycleBilin 𝕜 (lgen 𝕜 n) (lgen 𝕜 m)
      = if n + m = 0 then (n^3 - n : 𝕜) / 12 else 0 := by
  simp [virasoroCocycleBilin]

lemma virasoroCocycleBilin_apply_lgen_lgen' (n m : ℤ) :
    virasoroCocycleBilin 𝕜 (lgen 𝕜 n) (lgen 𝕜 m)
      = if n + m = 0 then (n-1 : 𝕜) * n * (n + 1) / 12 else 0 := by
  rw [virasoroCocycleBilin_apply_lgen_lgen]; congr; ring

lemma virasoroCocycleBilin_eq_neg_flip :
    virasoroCocycleBilin 𝕜 = -(virasoroCocycleBilin 𝕜).flip := by
  apply LinearMap.ext_basis (lgen _) (lgen _)
  intro n m
  simp only [LinearMap.neg_apply, LinearMap.flip_apply, virasoroCocycleBilin_apply_lgen_lgen]
  by_cases opp : n + m = 0
  · simp only [add_comm m n, opp, ↓reduceIte]
    have obs : m = -n := by linarith
    rw [show (m : 𝕜) = -(n : 𝕜) by simp [obs]]
    ring
  · simp only [add_comm m n, opp, ↓reduceIte, neg_zero]

/-- An auxiliary for of the Leibniz identity of the Virasoro cocycle `WittAlgebra`. -/
 lemma virasoroCocycleBracketCyclic_eq_zero :
    cyclicTripleSumHom (bracket 𝕜) (virasoroCocycleBilin 𝕜) = 0 := by
  apply LinearMap.ext_basis (lgen _) (lgen _)
  intro n m
  apply (lgen _).ext
  intro k
  simp only [cyclicTripleSumHom_apply, bracket_lgen_lgen', map_smul, smul_eq_mul,
             LinearMap.zero_apply]
  simp only [virasoroCocycleBilin, Module.Basis.constr_basis, mul_ite, mul_zero]
  rw [show n + (m + k) = n + m + k by ring,
      show m + (k + n) = n + m + k by ring,
      show k + (n + m) = n + m + k by ring]
  by_cases degzero : n + m + k = 0
  · simp only [degzero, ↓reduceIte]
    simp only [show k = -m + -n by linarith, Int.cast_add, Int.cast_neg]
    ring
  · simp [degzero]

variable [CharZero 𝕜]

/-- The Virasoro cocycle. -/
noncomputable def virasoroCocycle :
    LieTwoCocycle 𝕜 (WittAlgebra 𝕜) 𝕜 where
  toBilin := virasoroCocycleBilin 𝕜
  self' X := by
    apply self_eq_neg.mp
    simpa only [LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply]
      using LinearMap.congr_fun₂ (virasoroCocycleBilin_eq_neg_flip 𝕜) X X
  leibniz' X Y Z := by
    have key' := LinearMap.congr_fun₂ (virasoroCocycleBracketCyclic_eq_zero 𝕜) X Y
    have key := LinearMap.congr_fun key' Z
    simp only [LinearMap.zero_apply, cyclicTripleSumHom_apply] at key
    rw [add_assoc] at key
    have aux := eq_neg_of_add_eq_zero_left key
    rw [neg_add, show (bracket 𝕜) Y Z = ⁅Y, Z⁆ from rfl] at aux
    have aux' : ((virasoroCocycleBilin 𝕜) ⁅X, Y⁆) Z = -((virasoroCocycleBilin 𝕜) Z) ⁅X, Y⁆ := by
      simp only [LinearMap.congr_fun₂ (virasoroCocycleBilin_eq_neg_flip 𝕜) Z ⁅X, Y⁆,
                 LinearMap.neg_apply, neg_neg]
      rfl
    rw [aux, aux', (lie_skew X Z).symm, map_neg,
        show (bracket 𝕜) X Y = ⁅X, Y⁆ from rfl, show (bracket 𝕜) Z X = ⁅Z, X⁆ from rfl]
    ring

lemma virasoroCocycle_apply_lgen_lgen (n m : ℤ) :
    virasoroCocycle 𝕜 (lgen 𝕜 n) (lgen 𝕜 m) = if n + m = 0 then (n^3 - n : 𝕜)/12 else 0 :=
  virasoroCocycleBilin_apply_lgen_lgen 𝕜 n m

variable {𝕜}

lemma bdry_lgen_lgen_neg_eq (β : LieOneCochain 𝕜 (WittAlgebra 𝕜) 𝕜) (n : ℤ) :
    β.bdry (lgen 𝕜 n) (lgen 𝕜 (-n)) = 2 * n * β (lgen 𝕜 0) := by
  simp [LieOneCochain.bdry_apply, ← (two_mul (n : 𝕜))]

variable (𝕜)

/-- The Virasoro cocycle is cohomologically nontrivial. -/
theorem cohomologyClass_virasoroCocycle_ne_zero :
    (virasoroCocycle 𝕜).cohomologyClass ≠ 0 := by
  intro con
  obtain ⟨β, hβ⟩ := LieTwoCocycle.exists_eq_bdry _ con
  have hβ' (n : ℤ) :
      (virasoroCocycle 𝕜) (lgen 𝕜 n) (lgen 𝕜 (-n)) = β.bdry (lgen 𝕜 n) (lgen 𝕜 (-n)) := by
    grind
  simp_rw [bdry_lgen_lgen_neg_eq β] at hβ'
  have obsV₁ := virasoroCocycle_apply_lgen_lgen 𝕜 3 (-3)
  have obsV₂ := virasoroCocycle_apply_lgen_lgen 𝕜 6 (-6)
  rw [hβ'] at obsV₁ obsV₂
  norm_num at obsV₁ obsV₂
  have aux := congrArg (2 * ·) obsV₁
  simp only [← mul_assoc] at aux
  norm_num at aux
  apply (show (4 : 𝕜) ≠ 35/2 by norm_num) <| by grind

/-- The Witt algebra 2-cohomology `H²(WittAlgebra, 𝕜)` is nontrivial. -/
theorem nontrivial_lieTwoCohomology :
    Nontrivial (LieTwoCohomology 𝕜 (WittAlgebra 𝕜) 𝕜) :=
  nontrivial_of_ne _ _ (cohomologyClass_virasoroCocycle_ne_zero 𝕜)

end WittAlgebra

end VirasoroProject -- namespace
