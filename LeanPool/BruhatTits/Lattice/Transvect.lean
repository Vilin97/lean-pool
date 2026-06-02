/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import LeanPool.BruhatTits.Lattice.Construction
import LeanPool.BruhatTits.Utils.LinearAlgebra

/-!
# Transvection automorphisms and their action on lattices

If `b = (b₀, b₁)` is a basis of a two-dimensional `K`-vector space `V` and `x : K` a
scalar, we have a transvection automorphism of `V` given by `b₀ ↦ b₀` and
`b₁ ↦ x • b₀ + b₁`. In the coordinate system induced by `b`, this is
a transvection by `x`.

We call the basis representing this automorphism the unipotent matrix associated to `b` and `x`.

## Main definitions

- `Basis.transvect`: The basis of `K^2` given by the image of `b` under the transvection
  automorphism.
- `Basis.transvectEquiv`: The transvection automorphism induced by `b` and `x`.
- `Basis.unipotent`: The unipotent matrix realising the transvection automorphism.

## Main results

- `unipotent_pow_irred_smul_eq_submodule`: If `b = (b₀, b₁)` is a basis of `K^2`, then the submodule
  spanned by `(ϖ ^ k • b₀, b₁)` is invariant under the action of `b.unipotent (ϖ ^ n * x)` if
  `n ≥ k`.
-/

open Module


variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
Given a basis `b = (b₀, b₁)` of a `K`-vector space `V` and an element `x : K`, this is the basis
`(b₀, x • b₀ + b₁)` of `V`. Hence, this is a transvection in the coordinate system induced by `b`.
-/
noncomputable def Module.Basis.transvect (b : Basis (Fin 2) K V) (x : K) : Basis (Fin 2) K V :=
  let v : Fin 2 → V
    | 0 => b 0
    | 1 => x • b 0 + b 1
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← b.span_eq]
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      match i with
      | 0 => apply Submodule.subset_span; use 0
      | 1 =>
      rw [show b 1 = v 1 - x • v 0 by simp [v]]
      apply Submodule.sub_mem
      · apply Submodule.subset_span; use 1
      · apply Submodule.smul_mem
        apply Submodule.subset_span; use 0
    · simp
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      exact Submodule.smul_mem _ a hx
  have hli : LinearIndependent K v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    exact (Module.finrank_eq_card_basis b).symm
  Basis.mk hli hsp

@[simp] lemma Module.Basis.transvect_apply₀ (b : Basis (Fin 2) K V) (x : K) :
    b.transvect x 0 = b 0 := by
  simp [Module.Basis.transvect]

@[simp] lemma Module.Basis.transvect_apply₁ (b : Basis (Fin 2) K V) (x : K) :
    b.transvect x 1 = x • b 0 + b 1 := by
  simp [Module.Basis.transvect]

variable {R : Subring K}

/-- Special case of `Basis.transvect` for `V = Fin 2 → K` for ease of application. -/
noncomputable def Module.Basis.transvect' (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    Basis (Fin 2) K (Fin 2 → K) :=
  b.transvect x

@[simp]
lemma Module.Basis.transvect'_apply₀ (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvect' x 0 = b 0 := by
  simp [Module.Basis.transvect']

@[simp]
lemma Module.Basis.transvect'_apply₁ (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvect' x 1 = x • b 0 + b 1 := by
  simp [Module.Basis.transvect', Subring.smul_def]

/-- The `K`-automorphism of `Fin 2 → K` induced by sending `b` to the transvection of `b`
by `x`. -/
noncomputable def Module.Basis.transvectEquiv (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  Module.Basis.equiv b (b.transvect' x) (Equiv.refl _)

@[simp]
lemma Module.Basis.transvectEquiv_apply₀ (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectEquiv x (b 0) = b 0 := by
  simp [Module.Basis.transvectEquiv]

@[simp]
lemma Module.Basis.transvectEquiv_apply₁ (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectEquiv x (b 1) = x • b 0 + b 1 := by
  simp [Module.Basis.transvectEquiv]

lemma Module.Basis.transvectEquiv_pow_irred_mul_eq (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (n : ℕ)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.transvectEquiv (ϖ ^ n * x) = (b.ntwist₂ hϖ n 0).transvectEquiv x := by
  rw [← LinearEquiv.toLinearMap_inj]
  apply (b.ntwist₂ hϖ n 0).ext
  intro i
  simp only [LinearEquiv.coe_coe]
  match i with
  | 0 =>
      simpa [Subring.smul_def] using
        (Module.Basis.transvectEquiv_apply₀ (b := b.ntwist₂ hϖ n 0) x).symm
  | 1 =>
      simpa [Subring.smul_def, mul_comm, smul_smul] using
        (Module.Basis.transvectEquiv_apply₁ (b := b.ntwist₂ hϖ n 0) x).symm

/--
The basis associated to the transvection automorphism `Basis.transvectEquiv` induced by `x`.
In the coordinate system of `b`, this is the upper triangular matrix with `1` on the diagonal
and `x` in the top-right.
-/
noncomputable
def Module.Basis.unipotent (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.toLin.symm <| .ofLinearEquiv (b.transvectEquiv x)

lemma Module.Basis.unipotent_mulVec (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (y : Fin 2 → K) :
    (b.unipotent x).val.mulVec y = b.transvectEquiv x y := by
  simp [Module.Basis.unipotent]

lemma Module.Basis.unipotent_pow_irred_mul_eq (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (n : ℕ)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.unipotent (ϖ ^ n * x) = (b.ntwist₂ hϖ n 0).unipotent x := by
  simp only [Module.Basis.unipotent]
  rw [Module.Basis.transvectEquiv_pow_irred_mul_eq _ _ _ hϖ]

/--
If `b = (b₀, b₁)` is a basis of `K^2`, then the submodule spanned by `(ϖ ^ k • b₀, b₁)`
is invariant under the action of `b.unipotent (ϖ ^ n * x)` if `n ≥ k`.

This is used in `Lattice.exists_GL_forall_smul_eq_ntwist₂_of_isSimpleChain_cons`: We use
such unipotent matrices to inductively bring a simple chain of lattices in standard form. This
makes sure that in the `n + 1`th step, multiplying with a unipotent matrix does not change
the first `n` terms of the chain.

See `unipotent_pow_irred_smul_eq` for a version for `Basis.toLattice`.
-/
lemma unipotent_pow_irred_smul_eq_submodule {ϖ : R} (hϖ : Irreducible ϖ)
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (k n : ℕ) (hkn : k ≤ n) :
    b.unipotent (ϖ ^ n * x) • (b.ntwist₂ hϖ k 0).toSubmodule (R := R) =
      (b.ntwist₂ hϖ k 0).toSubmodule := by
  change Submodule.map
    ((Matrix.GeneralLinearGroup.toLin (b.unipotent _)).val : (Fin 2 → K) →ₗ[R] (Fin 2 → K))
      _ = _
  have heq : (ϖ ^ n * x) • b 0 = (ϖ ^ (n - k) * x) • ϖ ^ k • b 0 := by
    conv_lhs => rw [show n = n - k + k by omega]
    rw [pow_add, mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, ← smul_smul]
  simp only [Module.Basis.toSubmodule, Module.Basis.unipotent, MulEquiv.apply_symm_apply,
    ]
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro - ⟨-, ⟨j, rfl⟩, rfl⟩
    simp only [Module.Basis.transvectEquiv, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
      LinearMap.coe_restrictScalars, SetLike.mem_coe]
    match j with
    | 0 =>
    simp only [Fin.isValue, Module.Basis.ntwist₂_apply₀]
    apply Submodule.subset_span
    use 0
    simp only [Fin.isValue, Module.Basis.ntwist₂_apply₀, Subring.smul_def, SubmonoidClass.coe_pow,
      map_smul, Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.transvect'_apply₀]
    | 1 =>
    simp only [Fin.isValue, Module.Basis.ntwist₂_apply₁, pow_zero, one_smul,
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.transvect'_apply₁]
    apply Submodule.add_mem
    · rw [heq]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      use 0
      simp
    · apply Submodule.subset_span
      use 1
      simp
  · rw [Submodule.span_le]
    rintro - ⟨i, rfl⟩
    simp only [Module.Basis.transvectEquiv, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
      LinearMap.coe_restrictScalars, SetLike.mem_coe]
    match i with
    | 0 =>
    simp only [Fin.isValue, Module.Basis.ntwist₂_apply₀]
    apply Submodule.subset_span
    refine ⟨ϖ ^ k • b 0, ?_, ?_⟩
    · use 0
      simp
    · simp [Subring.smul_def, map_smul]
    | 1 =>
    simp only [Fin.isValue, Module.Basis.ntwist₂_apply₁, pow_zero, one_smul]
    have : b 1 = (ϖ ^ n * x) • b 0 + b 1 - (ϖ ^ n * x) • b 0 := by simp
    rw [this]
    apply Submodule.sub_mem
    · apply Submodule.subset_span
      refine ⟨b 1, ?_, ?_⟩
      · use 1
        simp
      · simp
    · rw [heq]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨ϖ ^ k • b 0, ?_, ?_⟩
      · use 0
        simp
      · simp [Subring.smul_def, map_smul]

/-- Version of `unipotent_pow_irred_smul_eq_submodule` for `Basis.toLattice`. -/
lemma unipotent_pow_irred_smul_eq {ϖ : R} (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K))
    (x : R) (k n : ℕ) (hkn : k ≤ n) :
    b.unipotent (ϖ ^ n * x) • (b.ntwist₂ hϖ k 0).toLattice (R := R) =
      (b.ntwist₂ hϖ k 0).toLattice := by
  apply BruhatTits.Lattice.ext
  apply unipotent_pow_irred_smul_eq_submodule
  assumption

variable [IsDiscreteValuationRing R]

lemma Module.Basis.transvectEquiv_mem_of_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : Fin 2 → K) (hy : y ∈ b.toSubmodule (R := R)) :
    b.transvectEquiv x y ∈ b.toSubmodule (R := R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [← b.ntwist₂_zero_zero hϖ]
  rw [← unipotent_pow_irred_smul_eq_submodule (n := 0) (x := x) (hkn := by omega),
    pow_zero, one_mul]
  rw [Matrix.GeneralLinearGroup.mem_smul]
  use y
  rw [b.ntwist₂_zero_zero]
  refine ⟨hy, ?_⟩
  rw [b.unipotent_mulVec]

lemma Module.Basis.transvectEquiv_symm_mem_of_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : Fin 2 → K) (hy : y ∈ b.toSubmodule (R := R)) :
    (b.transvectEquiv x).symm y ∈ b.toSubmodule (R := R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [← b.ntwist₂_zero_zero hϖ] at hy
  rw [← unipotent_pow_irred_smul_eq_submodule (n := 0) (x := x) (hkn := by omega),
    pow_zero, one_mul] at hy
  rw [Matrix.GeneralLinearGroup.mem_smul] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  rw [b.unipotent_mulVec]
  rw [b.ntwist₂_zero_zero] at ha
  simpa
