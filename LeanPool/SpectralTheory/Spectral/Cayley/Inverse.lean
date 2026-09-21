/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.SpectralTheory.Spectral.Cayley.Unitary

/-!
# The inverse Cayley transform

This file shows the Cayley transform of a self-adjoint operator is
surjective onto `1 - U`'s complement, giving the inverse construction used to
recover the self-adjoint operator from its unitary Cayley transform.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private def oneSub (U : E →L[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.id - U.toLinearMap

private def oneAdd (U : E →L[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.id + U.toLinearMap

omit [CompleteSpace E] in
private theorem oneSub_injective (U : E →L[ℂ] E)
    (hInj : ∀ x, U x = x → x = 0) : Function.Injective (oneSub U) := by
  intro x y hxy
  have hfixed : U (x - y) = x - y := by
    change x - U x = y - U y at hxy
    rw [map_sub]
    rw [sub_eq_sub_iff_add_eq_add] at hxy ⊢
    simpa only [add_comm] using hxy.symm
  exact sub_eq_zero.mp (hInj (x - y) hfixed)

/-- The inverse Cayley transform `i(I + U)(I - U)⁻¹`, with domain `ran(I - U)`. -/
noncomputable def inverseCayley
    (U : E →L[ℂ] E) (_hU : U ∈ unitary (E →L[ℂ] E))
    (hInj : ∀ x, U x = x → x = 0)
    (_hDense : DenseRange (fun x => x - U x)) : E →ₗ.[ℂ] E :=
  let e : E ≃ₗ[ℂ] LinearMap.range (oneSub U) :=
    LinearEquiv.ofInjective (oneSub U) (oneSub_injective U hInj)
  { domain := LinearMap.range (oneSub U)
    toFun := Complex.I • (oneAdd U).comp e.symm.toLinearMap }

private theorem oneSub_cayley_apply_plus
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (x : A.domain) :
    oneSub (cayleyTransform A hA) (A x + Complex.I • (x : E)) =
      ((2 : ℂ) * Complex.I) • (x : E) := by
  change (A x + Complex.I • (x : E)) -
    cayleyTransform A hA (A x + Complex.I • (x : E)) = _
  rw [cayleyTransform_apply_plus A hA x]
  module

private theorem range_oneSub_cayley_eq_domain
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    LinearMap.range (oneSub (cayleyTransform A hA)) = A.domain := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
    obtain ⟨x, hx⟩ := add_I_surjective_of_isSelfAdjoint A hA z
    change A x + Complex.I • (x : E) = z at hx
    have hyEq : y = ((2 : ℂ) * Complex.I) • (x : E) := by
      rw [← hz, ← hx]
      exact oneSub_cayley_apply_plus A hA x
    rw [hyEq]
    exact A.domain.smul_mem ((2 : ℂ) * Complex.I) x.property
  · intro y hy
    let x : A.domain := ⟨y, hy⟩
    have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by norm_num) Complex.I_ne_zero
    refine LinearMap.mem_range.mpr
      ⟨(((2 : ℂ) * Complex.I)⁻¹) • (A x + Complex.I • (x : E)), ?_⟩
    rw [map_smul, oneSub_cayley_apply_plus A hA x, smul_smul,
      inv_mul_cancel₀ htwoI, one_smul]

/-- Applying the inverse Cayley transform to the Cayley transform recovers the original operator. -/
theorem inverseCayley_cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    inverseCayley (cayleyTransform A hA) (cayleyTransform_unitary A hA)
      (one_not_mem_eigenvalues_cayleyTransform A hA)
      (dense_range_one_sub_cayleyTransform A hA) = A := by
  apply LinearPMap.dExt (range_oneSub_cayley_eq_domain A hA)
  intro x y hxy
  let U := cayleyTransform A hA
  let L := oneSub U
  let e : E ≃ₗ[ℂ] LinearMap.range L :=
    LinearEquiv.ofInjective L
      (oneSub_injective U (one_not_mem_eigenvalues_cayleyTransform A hA))
  let z : E := (((2 : ℂ) * Complex.I)⁻¹) • (A y + Complex.I • (y : E))
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hLz : L z = (y : E) := by
    change oneSub U z = (y : E)
    change oneSub U
      ((((2 : ℂ) * Complex.I)⁻¹) • (A y + Complex.I • (y : E))) = (y : E)
    rw [map_smul, oneSub_cayley_apply_plus A hA y, smul_smul,
      inv_mul_cancel₀ htwoI, one_smul]
  have hez : e.symm x = z := by
    apply oneSub_injective U (one_not_mem_eigenvalues_cayleyTransform A hA)
    change L (e.symm x) = L z
    rw [hLz]
    have heapply := congrArg Subtype.val (e.apply_symm_apply x)
    change L (e.symm x) = (x : E) at heapply
    exact heapply.trans hxy
  change Complex.I • oneAdd U (e.symm x) = A y
  rw [hez]
  change Complex.I • (z + U z) = A y
  change Complex.I •
    (((2 * Complex.I)⁻¹ : ℂ) • (A y + Complex.I • (y : E)) +
      U (((2 * Complex.I)⁻¹ : ℂ) • (A y + Complex.I • (y : E)))) = A y
  rw [map_smul, cayleyTransform_apply_plus A hA y, ← smul_add]
  have hsum : (A y + Complex.I • (y : E)) + (A y - Complex.I • (y : E)) =
      (2 : ℂ) • A y := by
    module
  rw [hsum, smul_smul, smul_smul]
  have hc : Complex.I * ((2 * Complex.I)⁻¹ : ℂ) * 2 = 1 := by
    calc
      Complex.I * ((2 * Complex.I)⁻¹ : ℂ) * 2 =
          ((2 * Complex.I)⁻¹ : ℂ) * (2 * Complex.I) := by ring
      _ = 1 := inv_mul_cancel₀ htwoI
  rw [hc, one_smul]
