/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Algebra.Algebra.TransferInstance

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic

/-!
# Quantum Sets on Finite Products

This file restores the finite-product quantum set instance from upstream
`Monlib.LinearAlgebra.QuantumSet.Pi`.
-/

open scoped BigOperators InnerProductSpace

section Pi

variable {ι : Type*} {A : ι -> Type*}

/-- The `L²` finite product of quantum sets. -/
abbrev PiQ (A : ι -> Type*) :=
  PiLp 2 A

variable [hA : (i : ι) -> starAlgebra (A i)]

@[reducible, default_instance]
noncomputable instance : Ring (PiQ A) :=
  (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i)).ring

@[reducible, default_instance]
noncomputable instance : Algebra ℂ (PiQ A) :=
  Equiv.algebra ℂ (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i))

instance : Star (PiQ A) where
  star x := WithLp.toLp (2 : ENNReal) (star x.ofLp)

@[simp]
lemma PiLp.star_apply (x : PiQ A) (i : ι) :
    (star x) i = star (x i) :=
  rfl

@[simp]
lemma PiLp.mul_apply_quantum (x y : PiQ A) (i : ι) :
    (x * y) i = x i * y i :=
  rfl

lemma PiLp.mul_apply (x y : PiQ A) (i : ι) :
    (x * y) i = x i * y i :=
  PiLp.mul_apply_quantum x y i

instance : StarRing (PiQ A) where
  star_involutive x := by
    ext i
    change star (star (x i)) = x i
    rw [star_star]
  star_mul x y := by
    ext i
    change star (x i * y i) = star (y i) * star (x i)
    rw [star_mul]
  star_add x y := by
    ext i
    change star (x i + y i) = star (x i) + star (y i)
    rw [star_add]

instance : StarModule ℂ (PiQ A) where
  star_smul c x := by
    ext i
    change star (c • x i) = star c • star (x i)
    rw [star_smul]

/-- The pointwise modular automorphism on a finite product quantum set. -/
noncomputable def Pi.modAut (r : ℝ) : PiQ A ≃ₐ[ℂ] PiQ A :=
  let e : PiQ A ≃ₐ[ℂ] ((i : ι) -> A i) :=
    Equiv.algEquiv ℂ (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i))
  e.trans ((AlgEquiv.piCongrRight fun i => (hA i).modAut r).trans e.symm)

@[simp]
lemma Pi.modAut_apply (r : ℝ) (x : PiQ A) (i : ι) :
    Pi.modAut r x i = (hA i).modAut r (x i) :=
  rfl

@[reducible, instance]
noncomputable def piStarAlgebra : starAlgebra (PiQ A) where
  modAut r := Pi.modAut r
  modAut_trans r s := by
    ext x i
    simp [starAlgebra.modAut_apply_modAut, add_comm]
  modAut_star r x := by
    ext i
    simp [starAlgebra.modAut_star]

@[simp]
lemma piStarAlgebra_modAut_apply (r : ℝ) (x : PiQ A) (i : ι) :
    piStarAlgebra.modAut r x i = (hA i).modAut r (x i) :=
  rfl

variable [hQ : (i : ι) -> QuantumSet (A i)]
variable [Fintype ι]

noncomputable instance piInnerProductAlgebra : InnerProductAlgebra (PiQ A) where
  norm_smul_le := norm_smul_le
  norm_sq_eq_inner := norm_sq_eq_re_inner
  dist_eq x y := by
    rw [dist_eq_norm']
    congr 1
    ext i
    simp [sub_eq_add_neg, add_comm]
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left

theorem piInnerProductAlgebra_inner_apply (a b : PiQ A) :
    ⟪a, b⟫_ℂ = ∑ i, ⟪a i, b i⟫_ℂ := by
  rw [PiLp.inner_apply]

theorem piInnerProductAlgebra.inner_apply (a b : PiQ A) :
    ⟪a, b⟫_ℂ = ∑ i, ⟪a i, b i⟫_ℂ :=
  piInnerProductAlgebra_inner_apply a b

noncomputable instance Pi.quantumSet [Fact (∀ i, (hQ i).k = 0)] : QuantumSet (PiQ A) where
  modAut_isSymmetric r x y := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [piStarAlgebra_modAut_apply, piStarAlgebra_modAut_apply,
      QuantumSet.modAut_isSymmetric]
  k := 0
  inner_star_left x y z := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.mul_apply_quantum, PiLp.mul_apply_quantum, piStarAlgebra_modAut_apply,
      PiLp.star_apply]
    have hk : (hQ i).k = 0 := (Fact.out : ∀ i, (hQ i).k = 0) i
    have h := (hQ i).inner_star_left (x i) (y i) (z i)
    rw [hk] at h
    exact h
  inner_conj_left x y z := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.mul_apply_quantum, PiLp.mul_apply_quantum, piStarAlgebra_modAut_apply,
      PiLp.star_apply]
    have hk : (hQ i).k = 0 := (Fact.out : ∀ i, (hQ i).k = 0) i
    simpa [hk] using (hQ i).inner_conj_left (x i) (y i) (z i)
  n := (i : ι) × n (A i)
  nIsFintype := by
    letI : (i : ι) -> Fintype (n (A i)) := fun i => (hQ i).nIsFintype
    infer_instance
  nIsDecidableEq := Classical.typeDecidableEq ((i : ι) × n (A i))
  onb := by
    letI : (i : ι) -> Fintype (n (A i)) := fun i => (hQ i).nIsFintype
    exact Pi.orthonormalBasis fun i => (hQ i).onb

end Pi
