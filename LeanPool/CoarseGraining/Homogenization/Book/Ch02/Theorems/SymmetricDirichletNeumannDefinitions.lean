/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentitiesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Symmetric

/-! # Symmetric Dirichlet Neumann Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for
`l.symmetric.dirichlet.neumann.split.basic.definitions`.

The symmetric hypothesis is a.e.-native: no public theorem in this package uses
pointwise symmetry of the coefficient representative. The canonical public
theorem proving this package is `responseSymmetricDirichletNeumannTheory` in
`SymmetricDirichletNeumann.lean`. -/
structure ResponseSymmetricDirichletNeumannTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) : Prop where
  dirichlet_minimizer_exists :
    ∀ p : Vec d,
      ∃ u : H1Function (U : Set (Vec d)),
        IsSymmetricDirichletMinimizer U a p u
  neumann_meanZero_maximizer_exists :
    ∀ q : Vec d,
      ∃ u : H1Function (U : Set (Vec d)),
        MeanZeroOn (U : Set (Vec d)) u.toFun ∧
          IsSymmetricNeumannMaximizer U a q u
  response_maximizer_split :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        ∀ uD uN : H1Function (U : Set (Vec d)),
          IsSymmetricDirichletMinimizer U a p uD →
            IsSymmetricNeumannMaximizer U a q uN →
              v.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
                fun x => uN.grad x - uD.grad x
  response_dirichlet_neumann_split :
    ∀ p q : Vec d,
      responseJ U a p q =
        symmetricDirichletNu U a p + symmetricNeumannNu U a q - vecDot p q
  dirichlet_value_by_sigma :
    ∀ p : Vec d,
      symmetricDirichletNu U a p =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p)
  neumann_value_by_sigmaStarInv :
    ∀ q : Vec d,
      symmetricNeumannNu U a q =
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q)
  kappa_eq_zero :
    kappaCoarse U a = 0
  dirichlet_average_gradient :
    ∀ p : Vec d, ∀ uD : H1Function (U : Set (Vec d)),
      IsSymmetricDirichletMinimizer U a p uD →
        h1AverageGradient U uD = p
  dirichlet_average_flux :
    ∀ p : Vec d, ∀ uD : H1Function (U : Set (Vec d)),
      IsSymmetricDirichletMinimizer U a p uD →
        h1AverageFlux U a uD = matVecMul (sigmaCoarse U a) p
  neumann_average_flux :
    ∀ q : Vec d, ∀ uN : H1Function (U : Set (Vec d)),
      IsSymmetricNeumannMaximizer U a q uN →
        h1AverageFlux U a uN = q
  neumann_average_gradient :
    ∀ q : Vec d, ∀ uN : H1Function (U : Set (Vec d)),
      IsSymmetricNeumannMaximizer U a q uN →
        h1AverageGradient U uN = matVecMul (sigmaStarInvCoarse U a) q
  response_completed_square :
    ∀ p q : Vec d,
      responseJ U a p q =
        (1 / 2 : ℝ) *
          vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul (sigmaStarCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a)
              (q - matVecMul (sigmaStarCoarse U a) p))
  derived_matrices :
    aCoarse U a = sigmaCoarse U a ∧
      aStarCoarse U a = sigmaStarCoarse U a ∧
      bCoarse U a = sigmaCoarse U a
  dirichlet_neumann_bracketing :
    MatLoewnerLE (averagedSymmPartInv U a)⁻¹ (sigmaStarCoarse U a) ∧
      MatLoewnerLE (sigmaStarCoarse U a) (sigmaCoarse U a) ∧
      MatLoewnerLE (sigmaCoarse U a) (averageMat U a.toCoeffField)

namespace ResponseSymmetricDirichletNeumannTheory

/-- Transport the full symmetric Dirichlet--Neumann theorem package across an
a.e. coefficient change. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    {hsym_a : CoeffOn.IsSymmetric a} {hsym_b : CoeffOn.IsSymmetric b}
    (h : CoeffOn.AEEq a b)
    (hTheory : ResponseSymmetricDirichletNeumannTheory U a hsym_a) :
    ResponseSymmetricDirichletNeumannTheory U b hsym_b where
  dirichlet_minimizer_exists := by
    intro p
    rcases hTheory.dirichlet_minimizer_exists p with ⟨u, hu⟩
    exact ⟨u, hu.ofAEEq h⟩
  neumann_meanZero_maximizer_exists := by
    intro q
    rcases hTheory.neumann_meanZero_maximizer_exists q with ⟨u, hmean, hu⟩
    exact ⟨u, hmean, hu.ofAEEq h⟩
  response_maximizer_split := by
    intro p q v hv uD uN huD huN
    let va : Solution U a := Solution.ofAEEq h.symm v
    have hmax_a : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have huD_a : IsSymmetricDirichletMinimizer U a p uD :=
      huD.ofAEEq h.symm
    have huN_a : IsSymmetricNeumannMaximizer U a q uN :=
      huN.ofAEEq h.symm
    have hsplit :=
      hTheory.response_maximizer_split p q va hmax_a uD uN huD_a huN_a
    simpa [va] using hsplit
  response_dirichlet_neumann_split := by
    intro p q
    simpa [responseJ_eq_ofAEEq h p q,
      symmetricDirichletNu_eq_ofAEEq h p,
      symmetricNeumannNu_eq_ofAEEq h q] using
      hTheory.response_dirichlet_neumann_split p q
  dirichlet_value_by_sigma := by
    intro p
    simpa [symmetricDirichletNu_eq_ofAEEq h p,
      sigmaCoarse_eq_ofAEEq h] using hTheory.dirichlet_value_by_sigma p
  neumann_value_by_sigmaStarInv := by
    intro q
    simpa [symmetricNeumannNu_eq_ofAEEq h q,
      sigmaStarInvCoarse_eq_ofAEEq h] using
      hTheory.neumann_value_by_sigmaStarInv q
  kappa_eq_zero := by
    simpa [kappaCoarse_eq_ofAEEq h] using hTheory.kappa_eq_zero
  dirichlet_average_gradient := by
    intro p uD huD
    exact hTheory.dirichlet_average_gradient p uD (huD.ofAEEq h.symm)
  dirichlet_average_flux := by
    intro p uD huD
    have hflux :=
      hTheory.dirichlet_average_flux p uD (huD.ofAEEq h.symm)
    simpa [h1AverageFlux_eq_ofAEEq h uD, sigmaCoarse_eq_ofAEEq h] using hflux
  neumann_average_flux := by
    intro q uN huN
    have hflux :=
      hTheory.neumann_average_flux q uN (huN.ofAEEq h.symm)
    simpa [h1AverageFlux_eq_ofAEEq h uN] using hflux
  neumann_average_gradient := by
    intro q uN huN
    simpa [sigmaStarInvCoarse_eq_ofAEEq h] using
      hTheory.neumann_average_gradient q uN (huN.ofAEEq h.symm)
  response_completed_square := by
    intro p q
    simpa [responseJ_eq_ofAEEq h p q, sigmaCoarse_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h, sigmaStarInvCoarse_eq_ofAEEq h] using
      hTheory.response_completed_square p q
  derived_matrices := by
    simpa [aCoarse_eq_ofAEEq h, aStarCoarse_eq_ofAEEq h,
      bCoarse_eq_ofAEEq h, sigmaCoarse_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h] using hTheory.derived_matrices
  dirichlet_neumann_bracketing := by
    simpa [averagedSymmPartInv_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h, sigmaCoarse_eq_ofAEEq h,
      averageMat_toCoeffField_eq_ofAEEq h] using
      hTheory.dirichlet_neumann_bracketing

/-- A.e.-equivalent coefficient representatives satisfy the same symmetric
Dirichlet--Neumann theorem package. -/
theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    {hsym_a : CoeffOn.IsSymmetric a} {hsym_b : CoeffOn.IsSymmetric b}
    (h : CoeffOn.AEEq a b) :
    ResponseSymmetricDirichletNeumannTheory U a hsym_a ↔
      ResponseSymmetricDirichletNeumannTheory U b hsym_b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

/-- Accessor for the symmetric completed-square formula
`e.symmetric.J.completed.square.basic.definitions`. -/
theorem response_completed_square_eq {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {hsym : CoeffOn.IsSymmetric a}
    (h : ResponseSymmetricDirichletNeumannTheory U a hsym) (p q : Vec d) :
    responseJ U a p q =
      (1 / 2 : ℝ) *
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) +
      (1 / 2 : ℝ) *
        vecDot (q - matVecMul (sigmaStarCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a) p)) :=
  h.response_completed_square p q

/-- Accessor for the symmetric Dirichlet--Neumann gap formula
`e.symmetric.J.DN.gap.basic.definitions`, in the public coarse-matrix form. -/
theorem response_gap_eq {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {hsym : CoeffOn.IsSymmetric a}
    (h : ResponseSymmetricDirichletNeumannTheory U a hsym) (p : Vec d) :
    responseJ U a p (matVecMul (sigmaStarCoarse U a) p) =
      (1 / 2 : ℝ) *
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  simpa [vecDot, matVecMul] using
    h.response_completed_square p (matVecMul (sigmaStarCoarse U a) p)

end ResponseSymmetricDirichletNeumannTheory

end

end Ch02
end Book
end Homogenization
