/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.Elliptic.Core7

/-!
# Hopf problem: foundations · period torus type one one

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def PeriodTorusTypeOneOne.coordinateValue {R : Type*} [CommRing R] (E : Fin 6 → R)
    (x y : Fin 4 → R) : R :=
  E 0 * (x 0 * y 1 - x 1 * y 0) + E 1 * (x 0 * y 2 - x 2 * y 0) + E 2 * (x 0 * y 3 - x 3 * y 0) +
        E 3 * (x 1 * y 2 - x 2 * y 1) +
      E 4 * (x 1 * y 3 - x 3 * y 1) +
    E 5 * (x 2 * y 3 - x 3 * y 2)

/-- The ordered coordinate pair represented by each exterior-square basis index. -/
public
def PeriodTorusTypeOneOne.coefficientPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
public
theorem PeriodTorusCohomologyCup.pairIndices_eq_coefficientPair (k : Fin 6) :
    LocalSystemMatrices.pairIndices k =
      ![(PeriodTorusTypeOneOne.coefficientPair k).1,
        (PeriodTorusTypeOneOne.coefficientPair k).2] := by fin_cases k <;> rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair (k : Fin 6) :
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates
        (PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4)
          (FirstHurewicz.loopHomologyClass
            (PeriodTorusHigherHomology.coordinatePeriodLoop 4
              (Pi.single (PeriodTorusTypeOneOne.coefficientPair k).1 1)))
          (FirstHurewicz.loopHomologyClass
            (PeriodTorusHigherHomology.coordinatePeriodLoop 4
              (Pi.single (PeriodTorusTypeOneOne.coefficientPair k).2 1)))) =
      Pi.single k 1 := by
  have hp :
    PeriodTorusHigherHomology.coordinateTorusWedgeTwo
        (PeriodTorusHigherHomologyExterior.squareBasis k) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4
            (Pi.single (PeriodTorusTypeOneOne.coefficientPair k).1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4
            (Pi.single (PeriodTorusTypeOneOne.coefficientPair k).2 1))) := by
    rw [PeriodTorusHigherHomologyExterior.squareBasis_apply,
      PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti_periodLoops
        (Elliptic.examplePeriod .four),
      pairIndices_eq_coefficientPair]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      PeriodTorusHigherHomologyExterior.latticeBasis, Pi.basisFun_apply]
  rw [← hp]
  change
    PeriodTorusHigherHomologyExterior.squareCoordinates
        (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
          (PeriodTorusHigherHomology.coordinateTorusWedgeTwo
            (PeriodTorusHigherHomologyExterior.squareBasis k))) =
      _
  rw [PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_wedge]
  ext l
  simp [PeriodTorusHigherHomologyExterior.squareCoordinates_apply, Finsupp.single_apply,
    Pi.single_apply, eq_comm]

end Mathoverflow1973

end
