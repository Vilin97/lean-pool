/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightPBW
public import Mathlib.LinearAlgebra.Basis.Basic
public import LeanPool.Stafford38.Stafford38.Ore.ScalarAlgebra


/-!
# A coordinate-momentum pair over a coefficient ring

Two successive Ore extensions adjoin a central coordinate and then its
derivation momentum.  This file packages the resulting three canonical
generator families and proves their exact relations.
-/

@[expose] public section

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

/-- The zero derivation adjoining the central coordinate. -/
abbrev innerDerivation : OreDivisionDerivation B := zeroDerivation

/-- The coordinate derivation adjoining the momentum. -/
abbrev outerDerivation : OreDivisionDerivation (CoordinateStage (B := B)) :=
  coordinateDerivation

/-- Embed the old coefficient ring through both Ore stages. -/
def pairCoefficient : B →+* PairStage (B := B) :=
  (normalCoefficient outerDerivation).comp (normalCoefficient innerDerivation)

/-- The newly adjoined coordinate. -/
def pairCoordinate : PairStage (B := B) :=
  normalCoefficient outerDerivation (normalVariable innerDerivation)

/-- The newly adjoined momentum. -/
def pairMomentum : PairStage (B := B) :=
  normalVariable outerDerivation

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
    normalCoefficient outerDerivation (normalVariable innerDerivation) *
        normalCoefficient outerDerivation (normalCoefficient innerDerivation b) =
      normalCoefficient outerDerivation (normalCoefficient innerDerivation b) *
        normalCoefficient outerDerivation (normalVariable innerDerivation)
  rw [← (normalCoefficient outerDerivation).map_mul,
    ← (normalCoefficient outerDerivation).map_mul]
  congr 1
  have h := normalVariable_mul_coefficient innerDerivation b
  rw [zeroDerivation_apply, map_zero, add_zero] at h
  exact h

/-- The new momentum commutes with every old coefficient. -/
theorem pairMomentum_mul_coefficient (b : B) :
    pairMomentum * pairCoefficient b = pairCoefficient b * pairMomentum := by
  change
    normalVariable outerDerivation *
        normalCoefficient outerDerivation (normalCoefficient innerDerivation b) =
      normalCoefficient outerDerivation (normalCoefficient innerDerivation b) *
        normalVariable outerDerivation
  have h := normalVariable_mul_coefficient outerDerivation (normalCoefficient innerDerivation b)
  rw [coordinateDerivation_coefficient, map_zero, add_zero] at h
  exact h

/-- The new pair satisfies the Weyl relation in the manuscript convention. -/
theorem pairMomentum_mul_coordinate :
    pairMomentum (B := B) * pairCoordinate =
      pairCoordinate * pairMomentum + 1 := by
  change
    normalVariable outerDerivation *
        normalCoefficient outerDerivation (normalVariable innerDerivation) =
      normalCoefficient outerDerivation (normalVariable innerDerivation) *
        normalVariable outerDerivation + 1
  have h := normalVariable_mul_coefficient outerDerivation
    (normalVariable innerDerivation : CoordinateStage (B := B))
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
  Stafford38.OreScalarAlgebra.normalOreAlgebra innerDerivation fun c => by
    exact zeroDerivation_apply (algebraMap k B c)

theorem coordinateDerivation_algebraMap (c : k) :
    @coordinateDerivation B _
      (@algebraMap k (CoordinateStage (B := B)) _ _ coordinateStageAlgebra c) = 0 := by
  change coordinateDerivation
    (normalCoefficient innerDerivation (algebraMap k B c)) = 0
  exact coordinateDerivation_coefficient (algebraMap k B c)

/-- The scalar algebra structure on the full coordinate-momentum pair. -/
@[instance_reducible]
def pairStageAlgebra : Algebra k (PairStage (B := B)) := by
  letI : Algebra k (CoordinateStage (B := B)) := coordinateStageAlgebra
  exact Stafford38.OreScalarAlgebra.normalOreAlgebra outerDerivation
    coordinateDerivation_algebraMap

theorem pairStageAlgebra_algebraMap :
    @algebraMap k (PairStage (B := B)) _ _ pairStageAlgebra =
      (pairCoefficient (B := B)).comp (algebraMap k B) := rfl

end Scalars


end
end Stafford38.OrePairStage
