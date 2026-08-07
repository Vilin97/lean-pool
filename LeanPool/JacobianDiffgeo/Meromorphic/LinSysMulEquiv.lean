/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic.LinearSystem

/-!
# Multiplication linear equivalence for `L(D)` (design §6.7, closing the documented gap)

Unit: meromorphic-and-divisors. `linSysMulEquiv`: for `φ ≠ 0` on a connected surface,
multiplication by `φ` is a `ℂ`-linear equivalence `L(D) ≃ₗ L(D - divisor φ)` (Miranda V.3.11
vocabulary; riemann-roch's lattice tool).
-/

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X] [IsManifold 𝓘(ℂ) ω X]

theorem mul_mem_linSys_sub_divisor [ConnectedSpace X] {φ : ℳ X} (hφ : φ ≠ 0) {D : Divisor X}
    {ψ : ℳ X} (hψ : ψ ∈ LinSys D) : φ * ψ ∈ LinSys (D - divisor φ) := by
  intro x
  have hφx : ((divisor φ x : ℤ) : WithTop ℤ) = φ.ord x :=
    WithTop.coe_untop₀_of_ne_top (Mero.ord_ne_top hφ x)
  rw [MeroGermOn.ord_mul isOpen_univ (mem_univ x), Divisor.sub_apply]
  have hz : (-(D x - divisor φ x) : ℤ) = divisor φ x + -(D x) := by ring
  have hrw : ((-(D x - divisor φ x) : ℤ) : WithTop ℤ) = φ.ord x + ((-(D x) : ℤ) : WithTop ℤ) := by
    rw [hz]; push_cast; rw [hφx]
  rw [hrw]
  gcongr
  exact hψ x

/-- Multiplication equivalence (linear equivalence of linear systems; Miranda V.3.11 vocab,
riemann-roch's lattice tool): for `φ ≠ 0`, `ψ ↦ φ • ψ` maps `L(D)` isomorphically to
`L(D - divisor φ)`. -/
noncomputable def linSysMulEquiv [ConnectedSpace X] {φ : ℳ X} (hφ : φ ≠ 0) (D : Divisor X) :
    LinSys D ≃ₗ[ℂ] LinSys (D - divisor φ) := by
  have hDeq : D - divisor φ - -divisor φ = D := by abel
  have hφφinv : φ * φ⁻¹ = 1 := Mero.mul_inv_cancel hφ
  have hφinvφ : φ⁻¹ * φ = 1 := by rw [mul_comm]; exact hφφinv
  have hφinv : (φ⁻¹ : ℳ X) ≠ 0 := by
    intro h
    apply (zero_ne_one (α := ℳ X))
    rw [← hφφinv, h, mul_zero]
  refine LinearEquiv.ofLinear
    { toFun := fun ψ => ⟨φ * ψ.1, mul_mem_linSys_sub_divisor hφ ψ.2⟩
      map_add' := fun ψ1 ψ2 => Subtype.ext (mul_add φ ψ1.1 ψ2.1)
      map_smul' := fun c ψ => Subtype.ext (mul_smul_comm c φ ψ.1) }
    { toFun := fun χ => ⟨φ⁻¹ * χ.1, by
        have hmem := mul_mem_linSys_sub_divisor hφinv χ.2
        rwa [divisor_inv, hDeq] at hmem⟩
      map_add' := fun χ1 χ2 => Subtype.ext (mul_add φ⁻¹ χ1.1 χ2.1)
      map_smul' := fun c χ => Subtype.ext (mul_smul_comm c φ⁻¹ χ.1) } ?_ ?_
  · apply LinearMap.ext; intro χ
    apply Subtype.ext
    change φ * (φ⁻¹ * χ.1) = χ.1
    rw [← mul_assoc, hφφinv, one_mul]
  · apply LinearMap.ext; intro ψ
    apply Subtype.ext
    change φ⁻¹ * (φ * ψ.1) = ψ.1
    rw [← mul_assoc, hφinvφ, one_mul]

end RS
