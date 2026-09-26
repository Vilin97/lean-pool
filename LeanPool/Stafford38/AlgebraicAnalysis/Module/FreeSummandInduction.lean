/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.Unimodular


/-!
# Finite iteration of unimodular splittings

This file packages the unconditional finite iteration of normalized
functionals.  It does not assert that such a sequence can be constructed
from rank or torsion hypotheses.
-/

@[expose] public section

namespace AlgebraicAnalysis.FreeSummandInduction

variable {R : Type*} [Ring R]

/-- The harmless zero-factor equivalence used at the start of an iteration. -/
def emptyFactorEquiv (M : Type*) [AddCommGroup M] [Module R M] :
    M ≃ₗ[R] M × (Fin 0 → R) :=
  { toFun := fun m ↦ (m, fun i ↦ Fin.elim0 i)
    invFun := fun z ↦ z.1
    left_inv := by intro m; rfl
    right_inv := by
      intro z
      apply Prod.ext
      · rfl
      · apply Subsingleton.elim
    map_add' := by
      intro m n
      apply Prod.ext
      · rfl
      · apply Subsingleton.elim
    map_smul' := by
      intro r m
      apply Prod.ext
      · rfl
      · apply Subsingleton.elim }

theorem emptyFactorEquiv_apply (M : Type*) [AddCommGroup M] [Module R M]
    (m : M) : emptyFactorEquiv (R := R) M m = (m, fun i ↦ Fin.elim0 i) := rfl

/-- If every stage in a finite sequence has a specified unimodular element,
and the next module is identified with the preceding kernel, then all the
specified free rank-one factors split off simultaneously. -/
theorem finite_unimodular_splitting
    (M : ℕ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (φ : ∀ i, M i →ₗ[R] R) (x : ∀ i, M i)
    (hx : ∀ i, φ i (x i) = 1)
    (hres : ∀ i, M (i + 1) ≃ₗ[R] LinearMap.ker (φ i)) :
    ∀ n, Nonempty (M 0 ≃ₗ[R] M n × (Fin n → R)) := by
  have hstep : ∀ i, M i ≃ₗ[R] M (i + 1) × R := by
    intro i
    exact (AlgebraicAnalysis.Unimodular.unimodularSplitEquiv (φ i) (x i)
      (hx i)).trans ((hres i).symm.prodCongr (LinearEquiv.refl R R))
  intro n
  induction n with
  | zero =>
      exact ⟨emptyFactorEquiv (R := R) (M 0)⟩
  | succ n ih =>
      obtain ⟨e⟩ := ih
      let factors : (R × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R) :=
        (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R)).trans
          (LinearEquiv.refl R (Fin (n + 1) → R))
      let rearrange :=
        (LinearEquiv.prodAssoc R (M (n + 1)) R (Fin n → R)).trans
          ((LinearEquiv.refl R (M (n + 1))).prodCongr factors)
      exact ⟨e.trans (((hstep n).prodCongr
        (LinearEquiv.refl R (Fin n → R))).trans rearrange)⟩


end AlgebraicAnalysis.FreeSummandInduction
