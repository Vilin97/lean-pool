/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightPBW
import Mathlib.LinearAlgebra.Basis.Basic
import LeanPool.Stafford38.Stafford38.Ore.ScalarAlgebra

/-!
# A coordinate-momentum pair over a coefficient ring

Two successive Ore extensions adjoin a central coordinate and then its
derivation momentum.  This file packages the resulting three canonical
generator families and proves their exact relations.
-/

namespace Stafford38.OrePairStage

open AlgebraicAnalysis
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightPBW
open Stafford38.OreCoordinateStage

noncomputable section

variable {B : Type*} [Ring B]

/-- First adjoin a central coordinate, then a momentum differentiating it. -/
abbrev PairStage :=
  NormalOre (coordinateDerivation :
    OreDivisionDerivation (CoordinateStage (B := B)))

private abbrev innerD : OreDivisionDerivation B := zeroDerivation

private abbrev outerD : OreDivisionDerivation (CoordinateStage (B := B)) :=
  coordinateDerivation

/-- Embed the old coefficient ring through both Ore stages. -/
def pairCoefficient : B →+* PairStage (B := B) :=
  (normalCoefficient outerD).comp (normalCoefficient innerD)

/-- The newly adjoined coordinate. -/
def pairCoordinate : PairStage (B := B) :=
  normalCoefficient outerD (normalVariable innerD)

/-- The newly adjoined momentum. -/
def pairMomentum : PairStage (B := B) :=
  normalVariable outerD

/-- The checked right PBW basis for the momentum stage over the coordinate
stage.  This is a consumer of the reusable one-stage right-PBW interface; the
pair-specific generators and Weyl relation remain owned by Stafford38. -/
def pairStageRightOrePBWBasis [Nontrivial B] :
    Module.Basis ℕ (CoordinateStage (B := B))ᵐᵒᵖ (PairStage (B := B)) :=
  rightOrePBWBasis coordinateDerivation

/-- The new coordinate commutes with every old coefficient. -/
theorem pairCoordinate_mul_coefficient (b : B) :
    pairCoordinate * pairCoefficient b = pairCoefficient b * pairCoordinate := by
  change
    normalCoefficient outerD (normalVariable innerD) *
        normalCoefficient outerD (normalCoefficient innerD b) =
      normalCoefficient outerD (normalCoefficient innerD b) *
        normalCoefficient outerD (normalVariable innerD)
  rw [← (normalCoefficient outerD).map_mul,
    ← (normalCoefficient outerD).map_mul]
  congr 1
  have h := normalVariable_mul_coefficient innerD b
  rw [zeroDerivation_apply, map_zero, add_zero] at h
  exact h

/-- The new momentum commutes with every old coefficient. -/
theorem pairMomentum_mul_coefficient (b : B) :
    pairMomentum * pairCoefficient b = pairCoefficient b * pairMomentum := by
  change
    normalVariable outerD * normalCoefficient outerD (normalCoefficient innerD b) =
      normalCoefficient outerD (normalCoefficient innerD b) * normalVariable outerD
  have h := normalVariable_mul_coefficient outerD (normalCoefficient innerD b)
  rw [coordinateDerivation_coefficient, map_zero, add_zero] at h
  exact h

/-- The new pair satisfies the Weyl relation in the manuscript convention. -/
theorem pairMomentum_mul_coordinate :
    pairMomentum (B := B) * pairCoordinate =
      pairCoordinate * pairMomentum + 1 := by
  change
    normalVariable outerD * normalCoefficient outerD (normalVariable innerD) =
      normalCoefficient outerD (normalVariable innerD) * normalVariable outerD + 1
  have h := normalVariable_mul_coefficient outerD
    (normalVariable innerD : CoordinateStage (B := B))
  rw [coordinateDerivation_variable, map_one] at h
  exact h

theorem pairCoordinate_commutator_momentum :
    pairCoordinate (B := B) * pairMomentum - pairMomentum * pairCoordinate = -1 := by
  rw [pairMomentum_mul_coordinate]
  noncomm_ring

section Scalars

variable {k : Type*} [CommRing k] [Algebra k B]

/-- The scalar algebra structure on the central-coordinate stage. -/
@[instance_reducible]
def coordinateStageAlgebra : Algebra k (CoordinateStage (B := B)) :=
  Stafford38.OreScalarAlgebra.normalOreAlgebra innerD fun c => by
    exact zeroDerivation_apply (algebraMap k B c)

theorem coordinateDerivation_algebraMap (c : k) :
    @coordinateDerivation B _
      (@algebraMap k (CoordinateStage (B := B)) _ _ coordinateStageAlgebra c) = 0 := by
  change coordinateDerivation
    (normalCoefficient innerD (algebraMap k B c)) = 0
  exact coordinateDerivation_coefficient (algebraMap k B c)

/-- The scalar algebra structure on the full coordinate-momentum pair. -/
@[instance_reducible]
def pairStageAlgebra : Algebra k (PairStage (B := B)) := by
  letI : Algebra k (CoordinateStage (B := B)) := coordinateStageAlgebra
  exact Stafford38.OreScalarAlgebra.normalOreAlgebra outerD
    coordinateDerivation_algebraMap

theorem pairStageAlgebra_algebraMap :
    @algebraMap k (PairStage (B := B)) _ _ pairStageAlgebra =
      (pairCoefficient (B := B)).comp (algebraMap k B) := rfl

end Scalars


end
end Stafford38.OrePairStage
