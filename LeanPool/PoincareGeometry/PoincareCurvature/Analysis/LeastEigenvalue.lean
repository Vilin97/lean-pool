/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# Rayleigh support for the least eigenvalue in dimension three

The tensor maximum principle uses a unit least eigenvector at a contact
point and extends that vector locally.  The basic support inequality is that
the least eigenvalue of a symmetric endomorphism is bounded above by every
unit Rayleigh quotient.  This file proves that finite-dimensional statement
for the ordered three-dimensional spectrum used by Hamilton--Ivey.
-/

@[expose] public noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace LinearMap.IsSymmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The last ordered eigenvalue of a symmetric endomorphism in dimension
three is at most every unit Rayleigh quotient. -/
theorem eigenvalue_two_le_inner_apply_of_norm_eq_one
    {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric)
    (hdim : Module.finrank ℝ V = 3) {v : V} (hv : ‖v‖ = 1) :
    hA.eigenvalues hdim (2 : Fin 3) ≤ inner ℝ v (A v) := by
  let b : OrthonormalBasis (Fin 3) ℝ V := hA.eigenvectorBasis hdim
  have hformula :
      inner ℝ v (A v) =
        ∑ i : Fin 3, (inner ℝ (b i) v) ^ 2 * hA.eigenvalues hdim i := by
    rw [← b.sum_inner_mul_inner v (A v)]
    apply Finset.sum_congr rfl
    intro i hi
    have hsymm := hA (b i) v
    have heigen := hA.apply_eigenvectorBasis hdim i
    rw [← hsymm, heigen, real_inner_smul_left, real_inner_comm v (b i)]
    simp
    ring
  have hleast : ∀ i : Fin 3,
      hA.eigenvalues hdim (2 : Fin 3) ≤ hA.eigenvalues hdim i := by
    intro i
    exact hA.eigenvalues_antitone hdim (by omega)
  have hweighted :
      ∑ i : Fin 3,
          (inner ℝ (b i) v) ^ 2 * hA.eigenvalues hdim (2 : Fin 3) ≤
        ∑ i : Fin 3,
          (inner ℝ (b i) v) ^ 2 * hA.eigenvalues hdim i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hleast i) (sq_nonneg _)
  have hsquares := b.sum_sq_inner_right v
  rw [hv, one_pow] at hsquares
  calc
    hA.eigenvalues hdim (2 : Fin 3) =
        (∑ i : Fin 3, (inner ℝ (b i) v) ^ 2) *
          hA.eigenvalues hdim (2 : Fin 3) := by rw [hsquares, one_mul]
    _ = ∑ i : Fin 3,
          (inner ℝ (b i) v) ^ 2 * hA.eigenvalues hdim (2 : Fin 3) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin 3,
          (inner ℝ (b i) v) ^ 2 * hA.eigenvalues hdim i := hweighted
    _ = inner ℝ v (A v) := hformula.symm

/-- Homogeneous Rayleigh support: the least eigenvalue times the squared norm
is bounded by the quadratic form.  This form is suited to local extensions of
a contact eigenvector, since no pointwise renormalization is required. -/
theorem eigenvalue_two_mul_norm_sq_le_inner_apply
    {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric)
    (hdim : Module.finrank ℝ V = 3) (v : V) :
    hA.eigenvalues hdim (2 : Fin 3) * ‖v‖ ^ 2 ≤ inner ℝ v (A v) := by
  by_cases hv : v = 0
  · subst v
    simp
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : V := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvpos]
      exact inv_mul_cancel₀ hvpos.ne'
    have hunit := hA.eigenvalue_two_le_inner_apply_of_norm_eq_one hdim hu
    have hnormne : ‖v‖ ≠ 0 := hvpos.ne'
    have hinneru : inner ℝ u (A u) = inner ℝ v (A v) / ‖v‖ ^ 2 := by
      dsimp [u]
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp [hnormne]
    rw [hinneru] at hunit
    exact (le_div_iff₀ (sq_pos_of_pos hvpos)).mp hunit

end LinearMap.IsSymmetric
