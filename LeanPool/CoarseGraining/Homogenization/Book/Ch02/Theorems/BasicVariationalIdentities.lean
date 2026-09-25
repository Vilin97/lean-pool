/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Existence
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.BasicVariationalIdentities

/-! # Basic Variational Identities -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 basic variational identities for the canonical
coarse-grained matrices. -/
theorem responseBasicVariationalIdentitiesTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ResponseBasicVariationalIdentitiesTheory U a (coarseMatrices U a) :=
  Homogenization.Internal.Ch02.BookCh02.responseBasicVariationalIdentitiesTheory U a

/-- Public lower bound in the coarse matrix order chain
`e.cg.bounds.basic.definitions`. -/
theorem harmonicMean_le_sigmaStarCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    MatLoewnerLE (averagedSymmPartInv U a)⁻¹ (sigmaStarCoarse U a) := by
  simpa using
    (responseBasicVariationalIdentitiesTheory U a).harmonicMean_le_sigmaStar

/-- Public non-obvious order in the coarse matrix chain
`e.cg.bounds.basic.definitions`. -/
theorem sigmaStarCoarse_le_sigmaCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    MatLoewnerLE (sigmaStarCoarse U a) (sigmaCoarse U a) := by
  simpa using
    (responseBasicVariationalIdentitiesTheory U a).sigmaStar_le_sigma

/-- Public derived-matrix order in `e.cg.bounds.basic.definitions`. -/
theorem sigmaCoarse_le_bCoarse {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    MatLoewnerLE (sigmaCoarse U a) (bCoarse U a) := by
  simpa [bCoarse] using
    (responseBasicVariationalIdentitiesTheory U a).sigma_le_b

/-- Public upper bound in the coarse matrix order chain
`e.cg.bounds.basic.definitions`. -/
theorem bCoarse_le_averagedSymmPartPlusCorrection {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    MatLoewnerLE (bCoarse U a) (averagedSymmPartPlusCorrection U a) := by
  simpa [bCoarse] using
    (responseBasicVariationalIdentitiesTheory U a).b_le_averagedSymmPartPlusCorrection

/-- Public second-variation identity `e.quadresp.basic.definitions`. -/
theorem secondVariation_eq_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    {v : Solution U a} (hv : IsResponseMaximizer U a p q v)
    (w : Solution U a) :
    responseJ U a p q - responseValue U a p q w =
      secondVariationEnergyValue U a v w :=
  ResponseBasicVariationalIdentitiesTheory.secondVariation_eq
    (responseBasicVariationalIdentitiesTheory U a) hv w

/-- Public maximizer-energy identity `e.Jenergyv.basic.definitions`. -/
theorem responseJ_eq_energy_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    {v : Solution U a} (hv : IsResponseMaximizer U a p q v) :
    responseJ U a p q = (1 / 2 : ℝ) * variationEnergyValue U a v :=
  ResponseBasicVariationalIdentitiesTheory.responseJ_eq_energy
    (responseBasicVariationalIdentitiesTheory U a) hv

/-- Public averaged-gradient formula
`e.v.spatial.averages.basic.definitions`. -/
theorem averageGradient_eq_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    {v : Solution U a} (hv : IsResponseMaximizer U a p q v) :
    averageGradient U a v =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) :=
  ResponseBasicVariationalIdentitiesTheory.averageGradient_eq
    (responseBasicVariationalIdentitiesTheory U a) hv

/-- Public averaged-flux formula
`e.v.spatial.averages.basic.definitions`. -/
theorem averageFlux_eq_of_isResponseMaximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {p q : Vec d}
    {v : Solution U a} (hv : IsResponseMaximizer U a p q v) :
    averageFlux U a v =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse U a) p := by
  simpa [bCoarse] using
    ResponseBasicVariationalIdentitiesTheory.averageFlux_eq
      (responseBasicVariationalIdentitiesTheory U a) hv

/-- The whole-domain averaged gradient of the public canonical maximizer is the
canonical coarse-matrix formula.  This is a finite-dimensional consequence of
the variational identities; it is not a measurable-selection statement for the
maximizer field. -/
theorem averageGradient_canonicalMaximizer_eq {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    averageGradient U a (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) :=
  averageGradient_eq_of_isResponseMaximizer
    (canonicalMaximizer_isMaximizer (responseExistenceTheory U a) p q)

/-- The whole-domain averaged flux of the public canonical maximizer is the
canonical coarse-matrix formula. -/
theorem averageFlux_canonicalMaximizer_eq {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    averageFlux U a (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse U a) p :=
  averageFlux_eq_of_isResponseMaximizer
    (canonicalMaximizer_isMaximizer (responseExistenceTheory U a) p q)

/-- Block-matrix form of `averageGradient_canonicalMaximizer_eq`.  Chapter 4
uses this finite formula as the measurable representative of the whole-cube
canonical averaged gradient. -/
theorem averageGradient_canonicalMaximizer_eq_blockMatrix {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    averageGradient U a (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p := by
  rw [averageGradient_canonicalMaximizer_eq]
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_mul, neg_matVecMul, add_assoc,
    add_left_comm, add_comm]

/-- Block-matrix form of `averageFlux_canonicalMaximizer_eq`.  Chapter 4 uses
this finite formula as the measurable representative of the whole-cube
canonical averaged flux. -/
theorem averageFlux_canonicalMaximizer_eq_blockMatrix {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    averageFlux U a (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p := by
  rw [averageFlux_canonicalMaximizer_eq]
  simp [sub_eq_add_neg, matVecMul_mul, neg_matVecMul, add_left_comm, add_comm]

end

end Ch02
end Book
end Homogenization
