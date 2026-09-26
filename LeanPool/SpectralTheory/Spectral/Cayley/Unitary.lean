/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.Cayley.Basic


/-!
# Unitarity of the Cayley transform

This file proves the Cayley transform of a self-adjoint operator is
surjective, and combines this with its isometry (from `Spectral.Cayley.Basic`)
to show it is unitary.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem cayleyTransform_surjective
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (cayleyTransform A hA) := by
  intro y
  obtain ⟨x, hx⟩ := sub_I_surjective_of_isSelfAdjoint A hA y
  refine ⟨A x + Complex.I • (x : E), ?_⟩
  exact (cayleyTransform_apply_plus A hA x).trans hx

theorem cayleyTransform_unitary
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    cayleyTransform A hA ∈ unitary (E →L[ℂ] E) := by
  let f : E →ₗᵢ[ℂ] E := LinearIsometry.mk (cayleyTransform A hA).toLinearMap
    (norm_cayleyTransform A hA)
  let e : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective f (cayleyTransform_surjective A hA)
  let u : unitary (E →L[ℂ] E) := Unitary.linearIsometryEquiv.symm e
  have hueq : (u : E →L[ℂ] E) = cayleyTransform A hA := by
    ext x
    change e x = cayleyTransform A hA x
    change f x = cayleyTransform A hA x
    rfl
  rw [← hueq]
  exact u.property

theorem one_not_mem_eigenvalues_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∀ x, cayleyTransform A hA x = x → x = 0 := by
  intro y hy
  obtain ⟨x, hx⟩ := add_I_surjective_of_isSelfAdjoint A hA y
  change A x + Complex.I • (x : E) = y at hx
  have heq : A x - Complex.I • (x : E) = A x + Complex.I • (x : E) := by
    calc
      A x - Complex.I • (x : E) = cayleyTransform A hA
          (A x + Complex.I • (x : E)) := (cayleyTransform_apply_plus A hA x).symm
      _ = cayleyTransform A hA y := by rw [hx]
      _ = y := hy
      _ = A x + Complex.I • (x : E) := hx.symm
  rw [sub_eq_add_neg] at heq
  have hneg : -(Complex.I • (x : E)) = Complex.I • (x : E) :=
    add_left_cancel heq
  have htwo : (2 : ℂ) • (Complex.I • (x : E)) = 0 := by
    rw [two_smul]
    calc
      Complex.I • (x : E) + Complex.I • (x : E) =
          -(Complex.I • (x : E)) + Complex.I • (x : E) :=
        congrArg (fun z : E => z + Complex.I • (x : E)) hneg.symm
      _ = 0 := neg_add_cancel _
  have hIx : Complex.I • (x : E) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hxE : (x : E) = 0 :=
    (smul_eq_zero.mp hIx).resolve_left Complex.I_ne_zero
  have hx0 : x = 0 := Subtype.ext hxE
  rw [← hx, hx0]
  change A (0 : A.domain) + Complex.I • ((0 : A.domain) : E) = 0
  rw [LinearPMap.map_zero A, Submodule.coe_zero, smul_zero, add_zero]

theorem dense_range_one_sub_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    DenseRange (fun x => x - cayleyTransform A hA x) := by
  apply hA.dense_domain.mono
  intro z hz
  let x : A.domain := ⟨z, hz⟩
  have hgap :
      (A x + Complex.I • (x : E)) - (A x - Complex.I • (x : E)) =
        ((2 : ℂ) * Complex.I) • (x : E) := by
    module
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  refine ⟨(((2 : ℂ) * Complex.I)⁻¹) • (A x + Complex.I • (x : E)), ?_⟩
  calc
    ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          cayleyTransform A hA
            (((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E))) =
        ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          ((2 * Complex.I)⁻¹ : ℂ) •
            cayleyTransform A hA (A x + Complex.I • (x : E)) := by
              rw [map_smul]
    _ = ((2 * Complex.I)⁻¹ : ℂ) • (A x + Complex.I • (x : E)) -
          ((2 * Complex.I)⁻¹ : ℂ) • (A x - Complex.I • (x : E)) := by
            rw [cayleyTransform_apply_plus A hA x]
    _ = ((2 * Complex.I)⁻¹ : ℂ) •
          ((A x + Complex.I • (x : E)) - (A x - Complex.I • (x : E))) := by
            exact (smul_sub _ _ _).symm
    _ = ((2 * Complex.I)⁻¹ : ℂ) • (((2 : ℂ) * Complex.I) • (x : E)) := by
          rw [hgap]
    _ = (x : E) := by
          rw [smul_smul, inv_mul_cancel₀ htwoI, one_smul]
    _ = z := rfl
