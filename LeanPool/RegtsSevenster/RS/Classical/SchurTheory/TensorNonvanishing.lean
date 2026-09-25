/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SignedTensor

/-!
# Nonvanishing of idempotent images from Schur values

Generic functional evaluations of `charIdempotent`: any linear
functional whose values on permutations are the (plain or signed)
constant cycle products evaluates the idempotent to a multiple of
the Schur value at the (plain or negated) constant sequence.
Consequently a linear map out of the group algebra admitting such
a functional cannot kill the idempotent when the Schur value is
nonzero — the even and odd sectors of the dimension-bound
dichotomy.
-/

@[expose] public section

namespace RS

open Finset

open scoped Classical in
/-- Evaluating a linear functional on `charIdempotent` through its
values on permutations. -/
theorem functional_charIdempotent (μ : YoungDiagram) (d : ℕ)
    (L : SymGroupAlgebra μ.card →ₗ[ℂ] ℂ)
    (φ : Equiv.Perm (Fin μ.card) → ℂ)
    (hL : ∀ π, L (MonoidAlgebra.of ℂ (Equiv.Perm (Fin μ.card)) π) =
      φ π) :
    L (charIdempotent d (jtChar μ)) =
      ((d : ℂ) / (μ.card.factorial : ℂ)) *
        ∑ π : Equiv.Perm (Fin μ.card), jtChar μ π * φ π := by
  rw [charIdempotent, map_smul, map_sum]
  rw [Finset.sum_congr rfl
    (fun (π : Equiv.Perm (Fin μ.card)) (_ : π ∈ Finset.univ) =>
      map_smul L (jtChar μ π) _)]
  rw [Finset.sum_congr rfl
    (fun (π : Equiv.Perm (Fin μ.card)) (_ : π ∈ Finset.univ) => by
      rw [hL π])]
  rw [smul_eq_mul]
  rw [show (∑ π : Equiv.Perm (Fin μ.card), jtChar μ π • φ π) =
    ∑ π : Equiv.Perm (Fin μ.card), jtChar μ π * φ π from
    Finset.sum_congr rfl fun π _ => smul_eq_mul _ _]

open scoped Classical in
/-- **The even evaluation**: a functional whose permutation values
are the constant cycle products evaluates the idempotent to
`d · s_μ(m, m, …)`. -/
theorem functional_charIdempotent_frobenius (m : ℕ)
    (μ : YoungDiagram) (d : ℕ)
    (L : SymGroupAlgebra μ.card →ₗ[ℂ] ℂ)
    (hL : ∀ π, L (MonoidAlgebra.of ℂ (Equiv.Perm (Fin μ.card)) π) =
      cycleProd (fun _ => (m : ℂ)) π) :
    L (charIdempotent d (jtChar μ)) =
      (d : ℂ) * diagramSchur μ (fun _ => (m : ℂ)) := by
  rw [functional_charIdempotent μ d L _ hL]
  rw [show ((d : ℂ) / (μ.card.factorial : ℂ)) *
      (∑ π : Equiv.Perm (Fin μ.card),
        jtChar μ π * cycleProd (fun _ => (m : ℂ)) π) =
    (d : ℂ) * (((μ.card.factorial : ℂ))⁻¹ *
      ∑ π : Equiv.Perm (Fin μ.card),
        jtChar μ π * cycleProd (fun _ => (m : ℂ)) π) from by
    ring]
  rw [jtChar_frobenius' μ (fun _ => (m : ℂ))]

open scoped Classical in
/-- **The odd evaluation**: a functional whose permutation values
are the sign-twisted constant cycle products evaluates the
idempotent to `(−1)^n · d · s_μ(−m, −m, …)`. -/
theorem functional_charIdempotent_signed (m : ℕ)
    (μ : YoungDiagram) (d : ℕ)
    (L : SymGroupAlgebra μ.card →ₗ[ℂ] ℂ)
    (hL : ∀ π, L (MonoidAlgebra.of ℂ (Equiv.Perm (Fin μ.card)) π) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) *
        cycleProd (fun _ => (m : ℂ)) π) :
    L (charIdempotent d (jtChar μ)) =
      ((-1 : ℂ)) ^ μ.card *
        ((d : ℂ) * diagramSchur μ (fun _ => -(m : ℂ))) := by
  rw [functional_charIdempotent μ d L _ hL]
  rw [signed_tensor_sum m μ]
  have hfac : ((μ.card.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero μ.card
  field_simp

/-- **Even nonvanishing**: a linear map out of the group algebra
admitting a trace functional with constant-cycle-product character
cannot kill `charIdempotent` when the Schur value at the constant
sequence is nonzero. -/
theorem charIdempotent_image_ne_zero {M : Type*} [AddCommGroup M]
    [Module ℂ M] (m : ℕ) (μ : YoungDiagram) (d : ℕ) (hd : 0 < d)
    (ρ : SymGroupAlgebra μ.card →ₗ[ℂ] M) (tr : M →ₗ[ℂ] ℂ)
    (htr : ∀ π, tr (ρ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin μ.card)) π)) =
      cycleProd (fun _ => (m : ℂ)) π)
    (hSchur : diagramSchur μ (fun _ => (m : ℂ)) ≠ 0) :
    ρ (charIdempotent d (jtChar μ)) ≠ 0 := by
  intro h0
  have h := functional_charIdempotent_frobenius m μ d (tr.comp ρ)
    (fun π => by rw [LinearMap.comp_apply]; exact htr π)
  rw [LinearMap.comp_apply, h0, map_zero] at h
  exact hSchur ((mul_eq_zero.mp h.symm).resolve_left
    (Nat.cast_ne_zero.mpr hd.ne'))

/-- **Odd nonvanishing**: a linear map admitting a trace functional
with sign-twisted constant-cycle-product character cannot kill
`charIdempotent` when the Schur value at the negated constant
sequence is nonzero. -/
theorem charIdempotent_image_ne_zero_signed {M : Type*}
    [AddCommGroup M] [Module ℂ M] (m : ℕ) (μ : YoungDiagram)
    (d : ℕ) (hd : 0 < d)
    (ρ : SymGroupAlgebra μ.card →ₗ[ℂ] M) (tr : M →ₗ[ℂ] ℂ)
    (htr : ∀ π, tr (ρ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin μ.card)) π)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) *
        cycleProd (fun _ => (m : ℂ)) π)
    (hSchur : diagramSchur μ (fun _ => -(m : ℂ)) ≠ 0) :
    ρ (charIdempotent d (jtChar μ)) ≠ 0 := by
  intro h0
  have h := functional_charIdempotent_signed m μ d (tr.comp ρ)
    (fun π => by rw [LinearMap.comp_apply]; exact htr π)
  rw [LinearMap.comp_apply, h0, map_zero] at h
  have h1 : ((-1 : ℂ)) ^ μ.card ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have h2 := (mul_eq_zero.mp h.symm).resolve_left h1
  exact hSchur ((mul_eq_zero.mp h2).resolve_left
    (Nat.cast_ne_zero.mpr hd.ne'))

end RS
