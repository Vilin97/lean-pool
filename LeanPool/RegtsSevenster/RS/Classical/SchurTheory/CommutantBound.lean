/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharDecomp
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeFaithful

/-!
# Dimension bounds through the commutant

A representation factoring through an algebra of dimension at most
`B ^ 2` has dimension at most `B` times the dimension of its commutant.
Each simple constituent has dimension at most `B`, by native block
faithfulness, and the commutant dimension bounds the number of simple
summands, counted with multiplicity.
-/

namespace RS

open Finset LinearMap Representation
open scoped Classical

noncomputable section

variable {G V W : Type*}

private def IsNativeCharacterSum [Group G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {m : ℕ}
    (S : Fin m → Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)) : Prop :=
  ∀ g, ρ.character g = ∑ i, nChar (S i) g

private noncomputable instance cardComplexInvertible
    [Group G] [Fintype G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)

private theorem intertwining_finrank_sum_right
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    {m : ℕ}
    (S : Fin m → Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G))
    (hchar : IsNativeCharacterSum ρ S) :
    Module.finrank ℂ (IntertwiningMap τ ρ) =
      ∑ i, Module.finrank ℂ (IntertwiningMap τ (rhoS (S i))) := by
  dsimp only [IsNativeCharacterSum] at hchar
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_sum]
  simp_rw [← card_inv_mul_sum_char_mul_char_eq_finrank, hchar,
    nChar, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

private theorem intertwining_finrank_sum_left
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    {m : ℕ}
    (S : Fin m → Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G))
    (hchar : IsNativeCharacterSum ρ S) :
    Module.finrank ℂ (IntertwiningMap ρ τ) =
      ∑ i, Module.finrank ℂ (IntertwiningMap (rhoS (S i)) τ) := by
  dsimp only [IsNativeCharacterSum] at hchar
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_sum]
  simp_rw [← card_inv_mul_sum_char_mul_char_eq_finrank, hchar,
    nChar, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem constituent_multiplicity_pos
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {m : ℕ}
    (S : Fin m → Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G))
    (hS : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i))
    (hchar : IsNativeCharacterSum ρ S)
    (i : Fin m) :
    0 < Module.finrank ℂ (IntertwiningMap (rhoS (S i)) ρ) := by
  rw [intertwining_finrank_sum_right ρ _ S hchar]
  haveI := rhoS_isIrreducible (S i) (hS i)
  have hself : Module.finrank ℂ
      (IntertwiningMap (rhoS (S i)) (rhoS (S i))) = 1 := by simp
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      Nat.zero_le (Module.finrank ℂ
        (IntertwiningMap (rhoS (S i)) (rhoS (S j)))))
    (Finset.mem_univ i)
  rw [hself] at hle
  exact hle

private theorem trace_nProjector
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (nProjector S)) =
      (nDim S : ℂ) *
        Module.finrank ℂ (IntertwiningMap (rhoS S) ρ) := by
  rw [nProjector, trace_asAlgebraHom_classElem,
    ← card_inv_mul_sum_char_mul_char_eq_finrank]
  simp_rw [nCoeff, nChar, div_eq_mul_inv]
  rw [Nat.card_eq_fintype_card, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- A nonzero native block in a finite-dimensional algebra has at
least the square of its simple constituent's dimension. -/
theorem nDim_sq_le_finrank_of_projector_ne_zero
    [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S)
    {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] A)
    (hne : φ (nProjector S) ≠ 0) :
    nDim S ^ 2 ≤ Module.finrank ℂ A := by
  rw [← nProjector_block_rank S hS]
  let I := LinearMap.range (LinearMap.mulLeft ℂ (nProjector S))
  have hinj : Function.Injective (φ.toLinearMap.comp I.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hzero
    obtain ⟨y, rfl⟩ := hx
    have hy : φ (nProjector S * y) = 0 := by
      simpa [LinearMap.mulLeft_apply] using hzero
    simpa [LinearMap.mulLeft_apply] using
      nProjector_block_faithful S hS φ hne y hy
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The dimension of a finite-group representation is bounded by
the square root of the dimension of a factoring algebra, times the
dimension of its commutant. -/
theorem finrank_le_sqrt_mul_commutant
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] A)
    (hker : ∀ x, φ x = 0 → ρ.asAlgebraHom x = 0) :
    Module.finrank ℂ V ≤
      Nat.sqrt (Module.finrank ℂ A) *
        Module.finrank ℂ (IntertwiningMap ρ ρ) := by
  classical
  obtain ⟨m, S, hS, hchar⟩ := character_eq_sum_nChar ρ
  have hdim : Module.finrank ℂ V = ∑ i, nDim (S i) := by
    have h := hchar 1
    simp only [nChar, char_one] at h
    exact_mod_cast h
  let B := Nat.sqrt (Module.finrank ℂ A)
  have hsimple : ∀ i, nDim (S i) ≤ B := by
    intro i
    have hne : φ (nProjector (S i)) ≠ 0 := by
      intro hzero
      have ht := congrArg (LinearMap.trace ℂ V) (hker _ hzero)
      rw [trace_nProjector, map_zero] at ht
      haveI : Nontrivial (subCarrier (S i)) :=
        (isIrredRep_rhoS (S i) (hS i)).1
      have hd : (nDim (S i) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      have hm : (Module.finrank ℂ
          (IntertwiningMap (rhoS (S i)) ρ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (constituent_multiplicity_pos ρ S hS hchar i).ne'
      exact (mul_ne_zero hd hm) ht
    exact Nat.le_sqrt'.mpr
      (nDim_sq_le_finrank_of_projector_ne_zero (S i) (hS i) φ hne)
  have hlength : m ≤ Module.finrank ℂ (IntertwiningMap ρ ρ) := by
    rw [intertwining_finrank_sum_left ρ ρ S hchar]
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => show 1 ≤ Module.finrank ℂ
        (IntertwiningMap (rhoS (S i)) ρ) from
          constituent_multiplicity_pos ρ S hS hchar i)
  calc
    Module.finrank ℂ V = ∑ i, nDim (S i) := hdim
    _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hsimple i
    _ = B * m := by simp [Nat.mul_comm]
    _ ≤ B * Module.finrank ℂ (IntertwiningMap ρ ρ) :=
      Nat.mul_le_mul_left B hlength

/-- If a finite-group representation factors through an algebra of
dimension at most `B ^ 2`, its dimension is at most `B` times the
dimension of its commutant. -/
theorem finrank_le_mul_commutant
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] A)
    (hker : ∀ x, φ x = 0 → ρ.asAlgebraHom x = 0)
    (B : ℕ) (hB : Module.finrank ℂ A ≤ B ^ 2) :
    Module.finrank ℂ V ≤
      B * Module.finrank ℂ (IntertwiningMap ρ ρ) := by
  have hsqrt : Nat.sqrt (Module.finrank ℂ A) ≤ B := by
    have := Nat.sqrt_le' (Module.finrank ℂ A)
    nlinarith
  exact (finrank_le_sqrt_mul_commutant ρ φ hker).trans
    (Nat.mul_le_mul_right _ hsqrt)

/-- The square of the representation dimension is at most the
factoring algebra dimension times the square of the commutant
dimension. -/
theorem finrank_sq_le_mul_commutant_sq
    [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] A)
    (hker : ∀ x, φ x = 0 → ρ.asAlgebraHom x = 0) :
    Module.finrank ℂ V ^ 2 ≤ Module.finrank ℂ A *
      Module.finrank ℂ (IntertwiningMap ρ ρ) ^ 2 := by
  have h := finrank_le_sqrt_mul_commutant ρ φ hker
  calc
    Module.finrank ℂ V ^ 2 ≤
        (Nat.sqrt (Module.finrank ℂ A) *
          Module.finrank ℂ (IntertwiningMap ρ ρ)) ^ 2 := by
      exact Nat.pow_le_pow_left h 2
    _ = Nat.sqrt (Module.finrank ℂ A) ^ 2 *
        Module.finrank ℂ (IntertwiningMap ρ ρ) ^ 2 := mul_pow _ _ _
    _ ≤ Module.finrank ℂ A *
        Module.finrank ℂ (IntertwiningMap ρ ρ) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.sqrt_le' _)

end

end RS
