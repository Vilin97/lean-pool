/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction

/-! # Basic Variational Identities Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for Lemma
`l.basic.cg.identities.basic.definitions`.

This packages exactly the basic variational identities of Section 2.3.1:
the matrix order chain `e.cg.bounds.basic.definitions`, the second-variation
identity `e.quadresp.basic.definitions`, the maximizer energy identity
`e.Jenergyv.basic.definitions`, and the averaged-gradient/flux formulas
`e.v.spatial.averages.basic.definitions`.

The canonical public theorem proving this package is
`responseBasicVariationalIdentitiesTheory` in
`BasicVariationalIdentities.lean`.
-/
structure ResponseBasicVariationalIdentitiesTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (M : CoarseMatrices d) : Prop where
  matrix_identities : ResponseMatrixIdentities U a M
  sigmaStar_symm : M.sigmaStar.IsSymm
  harmonicMean_le_sigmaStar :
    MatLoewnerLE (averagedSymmPartInv U a)⁻¹ M.sigmaStar
  sigmaStar_le_sigma :
    MatLoewnerLE M.sigmaStar M.sigma
  sigma_le_b :
    MatLoewnerLE M.sigma M.b
  b_le_averagedSymmPartPlusCorrection :
    MatLoewnerLE M.b (averagedSymmPartPlusCorrection U a)
  second_variation :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        ∀ w : Solution U a,
          responseJ U a p q - responseValue U a p q w =
            secondVariationEnergyValue U a v w
  maximizer_energy :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        responseJ U a p q = (1 / 2 : ℝ) * variationEnergyValue U a v
  average_gradient :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        averageGradient U a v =
          -p + matVecMul M.sigmaStarInv (q + matVecMul M.kappa p)
  average_flux :
    ∀ p q : Vec d, ∀ v : Solution U a,
      IsResponseMaximizer U a p q v →
        averageFlux U a v =
          q - matVecMul (matTranspose M.kappa) (matVecMul M.sigmaStarInv q) -
            matVecMul M.b p

namespace ResponseBasicVariationalIdentitiesTheory

/-- The basic variational identities depend only on the coefficient field up
to a.e. equality on the public domain. The matrix package is fixed; canonical
packages can be rewritten separately by `coarseMatrices_eq_ofAEEq`. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {M : CoarseMatrices d}
    (hTheory : ResponseBasicVariationalIdentitiesTheory U a M) :
    ResponseBasicVariationalIdentitiesTheory U b M where
  matrix_identities := hTheory.matrix_identities.ofAEEq h
  sigmaStar_symm := hTheory.sigmaStar_symm
  harmonicMean_le_sigmaStar := by
    simpa [averagedSymmPartInv_eq_ofAEEq h] using
      hTheory.harmonicMean_le_sigmaStar
  sigmaStar_le_sigma := hTheory.sigmaStar_le_sigma
  sigma_le_b := hTheory.sigma_le_b
  b_le_averagedSymmPartPlusCorrection := by
    simpa [averagedSymmPartPlusCorrection_eq_ofAEEq h] using
      hTheory.b_le_averagedSymmPartPlusCorrection
  second_variation := by
    intro p q v hv w
    let va : Solution U a := Solution.ofAEEq h.symm v
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hmax : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hOld := hTheory.second_variation p q va hmax wa
    simpa [va, wa, responseJ_eq_ofAEEq h p q,
      responseValue_ofAEEq h.symm p q w,
      secondVariationEnergyValue_ofAEEq h.symm v w] using hOld
  maximizer_energy := by
    intro p q v hv
    let va : Solution U a := Solution.ofAEEq h.symm v
    have hmax : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hOld := hTheory.maximizer_energy p q va hmax
    simpa [va, responseJ_eq_ofAEEq h p q,
      variationEnergyValue_ofAEEq h.symm v] using hOld
  average_gradient := by
    intro p q v hv
    let va : Solution U a := Solution.ofAEEq h.symm v
    have hmax : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hOld := hTheory.average_gradient p q va hmax
    simpa [va, averageGradient_ofAEEq h.symm v] using hOld
  average_flux := by
    intro p q v hv
    let va : Solution U a := Solution.ofAEEq h.symm v
    have hmax : IsResponseMaximizer U a p q va := hv.ofAEEq h.symm
    have hOld := hTheory.average_flux p q va hmax
    simpa [va, averageFlux_ofAEEq h.symm v] using hOld

/-- A.e.-equivalent coefficient representatives satisfy the same basic
variational theorem package for a fixed matrix package. -/
theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {M : CoarseMatrices d} :
    ResponseBasicVariationalIdentitiesTheory U a M ↔
      ResponseBasicVariationalIdentitiesTheory U b M :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

/-- The basic variational identities contain the matrix-extraction identities. -/
theorem toResponseMatrixIdentities {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {M : CoarseMatrices d}
    (h : ResponseBasicVariationalIdentitiesTheory U a M) :
    ResponseMatrixIdentities U a M :=
  h.matrix_identities

/-- Accessor for the second-variation identity
`e.quadresp.basic.definitions`. -/
theorem secondVariation_eq {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {M : CoarseMatrices d}
    (h : ResponseBasicVariationalIdentitiesTheory U a M)
    {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) (w : Solution U a) :
    responseJ U a p q - responseValue U a p q w =
      secondVariationEnergyValue U a v w :=
  h.second_variation p q v hv w

/-- Accessor for the maximizer energy identity
`e.Jenergyv.basic.definitions`. -/
theorem responseJ_eq_energy {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {M : CoarseMatrices d}
    (h : ResponseBasicVariationalIdentitiesTheory U a M)
    {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    responseJ U a p q = (1 / 2 : ℝ) * variationEnergyValue U a v :=
  h.maximizer_energy p q v hv

/-- Accessor for the averaged-gradient formula in
`e.v.spatial.averages.basic.definitions`. -/
theorem averageGradient_eq {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {M : CoarseMatrices d}
    (h : ResponseBasicVariationalIdentitiesTheory U a M)
    {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    averageGradient U a v =
      -p + matVecMul M.sigmaStarInv (q + matVecMul M.kappa p) :=
  h.average_gradient p q v hv

/-- Accessor for the averaged-flux formula in
`e.v.spatial.averages.basic.definitions`. -/
theorem averageFlux_eq {d : ℕ} {U : Domain d} {a : CoeffOn U}
    {M : CoarseMatrices d}
    (h : ResponseBasicVariationalIdentitiesTheory U a M)
    {p q : Vec d} {v : Solution U a}
    (hv : IsResponseMaximizer U a p q v) :
    averageFlux U a v =
      q - matVecMul (matTranspose M.kappa) (matVecMul M.sigmaStarInv q) -
        matVecMul M.b p :=
  h.average_flux p q v hv

end ResponseBasicVariationalIdentitiesTheory

end

end Ch02
end Book
end Homogenization
