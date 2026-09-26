/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Common

/-! # Zero Dim -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Zero-Dimensional Symmetric Dirichlet-Neumann Theory

This file is split mechanically out of `Internal.Ch02.SymmetricDirichletNeumann`.
-/

theorem matLoewnerLE_zero_dim {A B : Mat 0} :
    MatLoewnerLE A B := by
  intro p
  have hp : p = 0 := Subsingleton.elim p 0
  subst p
  simp [vecDot, matVecMul]

theorem symmetricDirichletEnergyValue_zero_dim
    (U : Domain 0) (a : CoeffOn U)
    (u : H1Function (U : Set (Vec 0))) :
    symmetricDirichletEnergyValue U a u = 0 := by
  change
    volumeAverage (U : Set (Vec 0))
      (fun x =>
        (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul (a.toCoeffField x) (u.grad x))) = 0
  rw [show
      (fun x =>
        (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul (a.toCoeffField x) (u.grad x))) =
        (0 : Vec 0 → ℝ) by
    funext x
    simp [vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

theorem symmetricNeumannEnergyValue_zero_dim
    (U : Domain 0) (a : CoeffOn U) (q : Vec 0)
    (u : H1Function (U : Set (Vec 0))) :
    symmetricNeumannEnergyValue U a q u = 0 := by
  change
    volumeAverage (U : Set (Vec 0))
      (fun x =>
        vecDot q (u.grad x) -
          (1 / 2 : ℝ) * vecDot (u.grad x)
            (matVecMul (a.toCoeffField x) (u.grad x))) = 0
  rw [show
      (fun x =>
        vecDot q (u.grad x) -
          (1 / 2 : ℝ) * vecDot (u.grad x)
            (matVecMul (a.toCoeffField x) (u.grad x))) =
        (0 : Vec 0 → ℝ) by
    funext x
    simp [vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

theorem isSymmetricDirichletAdmissible_zero_dim
    (U : Domain 0) (p : Vec 0)
    (u : H1Function (U : Set (Vec 0))) :
    IsSymmetricDirichletAdmissible U p u := by
  have hzero :
      (fun x : Vec 0 => u.grad x - p) = (0 : Vec 0 → Vec 0) := by
    funext x
    exact Subsingleton.elim _ _
  rw [IsSymmetricDirichletAdmissible, hzero]
  simpa using!
    Book.Ch01.potentialZeroTraceFieldOn_of_h10
      (U := (U : Set (Vec 0))) (0 : H10Function (U : Set (Vec 0)))

theorem isSymmetricDirichletMinimizer_zero_dim
    (U : Domain 0) (a : CoeffOn U) (p : Vec 0)
    (u : H1Function (U : Set (Vec 0))) :
    IsSymmetricDirichletMinimizer U a p u := by
  refine ⟨isSymmetricDirichletAdmissible_zero_dim U p u, ?_⟩
  intro w _hw
  rw [symmetricDirichletEnergyValue_zero_dim U a u,
    symmetricDirichletEnergyValue_zero_dim U a w]

theorem isSymmetricNeumannMaximizer_zero_dim
    (U : Domain 0) (a : CoeffOn U) (q : Vec 0)
    (u : H1Function (U : Set (Vec 0))) :
    IsSymmetricNeumannMaximizer U a q u := by
  intro w
  rw [symmetricNeumannEnergyValue_zero_dim U a q w,
    symmetricNeumannEnergyValue_zero_dim U a q u]

theorem symmetricDirichletNu_zero_dim
    (U : Domain 0) (a : CoeffOn U) (p : Vec 0) :
    symmetricDirichletNu U a p = 0 := by
  have hmin :
      IsSymmetricDirichletMinimizer U a p (0 : H1Function (U : Set (Vec 0))) :=
    isSymmetricDirichletMinimizer_zero_dim U a p 0
  rw [symmetricDirichletNu_eq_of_minimizer hmin,
    symmetricDirichletEnergyValue_zero_dim U a]

theorem symmetricNeumannNu_zero_dim
    (U : Domain 0) (a : CoeffOn U) (q : Vec 0) :
    symmetricNeumannNu U a q = 0 := by
  have hmax :
      IsSymmetricNeumannMaximizer U a q (0 : H1Function (U : Set (Vec 0))) :=
    isSymmetricNeumannMaximizer_zero_dim U a q 0
  rw [symmetricNeumannNu_eq_of_maximizer hmax,
    symmetricNeumannEnergyValue_zero_dim U a q]

theorem responseJ_zero_dim (U : Domain 0) (a : CoeffOn U)
    (p q : Vec 0) :
    responseJ U a p q = 0 := by
  have hp : p = 0 := Subsingleton.elim p 0
  have hq : q = 0 := Subsingleton.elim q 0
  subst p
  subst q
  have h :=
    (canonicalResponseMatrixIdentities U a).full_response (0 : Vec 0) (0 : Vec 0)
  simpa [vecDot, matVecMul] using h

theorem responseSymmetricDirichletNeumannTheory_zero_dim
    (U : Domain 0) (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    ResponseSymmetricDirichletNeumannTheory U a hsym := by
  refine
    { dirichlet_minimizer_exists := ?_
      neumann_meanZero_maximizer_exists := ?_
      response_maximizer_split := ?_
      response_dirichlet_neumann_split := ?_
      dirichlet_value_by_sigma := ?_
      neumann_value_by_sigmaStarInv := ?_
      kappa_eq_zero := ?_
      dirichlet_average_gradient := ?_
      dirichlet_average_flux := ?_
      neumann_average_flux := ?_
      neumann_average_gradient := ?_
      response_completed_square := ?_
      derived_matrices := ?_
      dirichlet_neumann_bracketing := ?_ }
  · intro p
    exact ⟨0, isSymmetricDirichletMinimizer_zero_dim U a p 0⟩
  · intro q
    refine ⟨0, ?_, isSymmetricNeumannMaximizer_zero_dim U a q 0⟩
    unfold MeanZeroOn
    simp
  · intro p q v hv uD uN huD huN
    exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _
  · intro p q
    rw [responseJ_zero_dim U a p q, symmetricDirichletNu_zero_dim U a p,
      symmetricNeumannNu_zero_dim U a q]
    simp [vecDot]
  · intro p
    rw [symmetricDirichletNu_zero_dim U a p]
    have hp : p = 0 := Subsingleton.elim p 0
    subst p
    simp [vecDot, matVecMul]
  · intro q
    rw [symmetricNeumannNu_zero_dim U a q]
    have hq : q = 0 := Subsingleton.elim q 0
    subst q
    simp [vecDot, matVecMul]
  · exact Subsingleton.elim _ _
  · intro p uD huD
    exact Subsingleton.elim _ _
  · intro p uD huD
    exact Subsingleton.elim _ _
  · intro q uN huN
    exact Subsingleton.elim _ _
  · intro q uN huN
    exact Subsingleton.elim _ _
  · intro p q
    rw [responseJ_zero_dim U a p q]
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    simp [vecDot, matVecMul]
  · refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · refine ⟨matLoewnerLE_zero_dim, matLoewnerLE_zero_dim, matLoewnerLE_zero_dim⟩


end BookCh02

end

end Ch02
end Internal
end Homogenization
