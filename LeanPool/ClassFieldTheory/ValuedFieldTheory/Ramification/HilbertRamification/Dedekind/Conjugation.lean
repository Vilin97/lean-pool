/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# Hilbert ramification theory: conjugate prime ideals

This file records the conjugation statement in prime-decomposition theory:
the decomposition group of a conjugate prime ideal is the conjugate subgroup.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Decomposition and inertia groups satisfy:
the decomposition group of the conjugate prime `σ P` is the conjugate
subgroup `σ G_P σ⁻¹`. -/
theorem dedekindDecomposition_decompositionGroup_smul_eq_map_conj
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B]
    (σ : G) :
    decompositionGroup (σ • P) G =
      (decompositionGroup P G).map (MulAut.conj σ).toMonoidHom := by
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj σ P

/-- Prime-decomposition statement:
membership in the inertia group of a conjugate prime ideal.  This is the
inertia-group part of the simultaneous conjugacy used later for Frobenius
classes. -/
theorem mem_inertiaGroup_smul_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B]
    {σ τ : G} :
    τ ∈ inertiaGroup (σ • P) G ↔
      σ⁻¹ * τ * σ ∈ inertiaGroup P G := by
  rw [mem_inertiaGroup_iff, mem_inertiaGroup_iff]
  constructor
  · intro h x
    have hx := h (σ • x)
    have hx' :
        σ⁻¹ • (τ • (σ • x) - σ • x) ∈ σ⁻¹ • (σ • P) :=
      Ideal.smul_mem_pointwise_smul σ⁻¹ _ _ hx
    simpa [smul_sub, mul_smul, mul_assoc, inv_smul_smul] using hx'
  · intro h x
    have hx := h (σ⁻¹ • x)
    have hx' :
        σ • ((σ⁻¹ * τ * σ) • (σ⁻¹ • x) - σ⁻¹ • x) ∈ σ • P :=
      Ideal.smul_mem_pointwise_smul σ _ _ hx
    simpa [smul_sub, mul_smul, mul_assoc] using hx'

/-- Prime-decomposition statement:
the inertia group of the conjugate prime `σ P` is the conjugate subgroup
`σ I_P σ⁻¹`. -/
theorem dedekindRamification_inertiaGroup_smul_eq_map_conj
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B]
    (σ : G) :
    inertiaGroup (σ • P) G =
      (inertiaGroup P G).map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [mem_inertiaGroup_smul_iff (P := P) (G := G) (σ := σ)]
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end Dedekind
end HilbertRamification
