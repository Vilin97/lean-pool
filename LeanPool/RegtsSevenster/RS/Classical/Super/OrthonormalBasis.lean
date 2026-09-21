/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Orthonormal basis for nondegenerate symmetric bilinear
  forms

For a finite-dimensional complex vector space `V` equipped
with a symmetric nondegenerate bilinear form `B`, there
exists an orthonormal basis — a basis `b` indexed by
`Fin (finrank ℂ V)` such that
`B (b i) (b j) = if i = j then 1 else 0`.

The proof proceeds by:

1. Using `exists_orthogonal_basis` (Mathlib) to obtain an
   orthogonal basis `b₀` with `B (b₀ i) (b₀ j) = 0` for
   `i ≠ j`.
2. Showing each diagonal value `B (b₀ i) (b₀ i) ≠ 0`
   via nondegeneracy.
3. Rescaling by inverse square roots (which exist over `ℂ`
   since `ℂ` is algebraically closed) to normalise the
   diagonal entries to `1`.
-/

noncomputable section

namespace RS

open LinearMap (BilinForm)
open LinearMap.BilinForm
open Module Submodule FiniteDimensional

/-- **Orthonormal basis**: a finite-dimensional complex
vector space carrying a symmetric nondegenerate bilinear
form admits a basis `b` such that
`B (b i) (b j) = if i = j then 1 else 0`. -/
theorem exists_orthonormal_basis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (B : BilinForm ℂ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ b : Basis (Fin (finrank ℂ V)) ℂ V,
      ∀ i j, B (b i) (b j) =
        if i = j then 1 else 0 := by
  -- Orthogonal basis (Invertible 2 via CharZero ℂ)
  obtain ⟨b₀, hortho⟩ :=
    exists_orthogonal_basis
      (isSymm_iff.mp ⟨hsymm⟩)
  -- Diagonal entries nonzero by nondegeneracy
  have hdiag : ∀ i, B (b₀ i) (b₀ i) ≠ 0 :=
    hortho.not_isOrtho_basis_self_of_separatingLeft
      hnd
  -- Square roots exist over ℂ (algebraically closed)
  choose s hs using fun i =>
    IsAlgClosed.exists_eq_mul_self
      (B (b₀ i) (b₀ i))
  have hs_ne : ∀ i, s i ≠ 0 := fun i hi =>
    hdiag i (by rw [hs i, hi, mul_zero])
  -- Rescale by inverse square roots
  refine ⟨b₀.unitsSMul (fun i =>
    Units.mk0 (s i)⁻¹ (inv_ne_zero (hs_ne i))),
    fun i j => ?_⟩
  simp only [Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij; rw [hs i]; field_simp [hs_ne i]
  · rw [hortho hij, mul_zero, mul_zero]

end RS
