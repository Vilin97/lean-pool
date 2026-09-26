/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannRoch
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointDivisorSplit

/-!
# One-point Riemann lower bounds from the intrinsic genus

Riemann's inequality gives the intrinsic function-field genus itself as a
simultaneous budget for every one-point Riemann space.  This applies to the
exhaustive BGS place type, including both finite and infinity places.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance genusRiemannConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance genusRiemannConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) genusRiemannPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance genusRiemannPolynomialRatFuncTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance genusRiemannConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Riemann's inequality gives the intrinsic genus as a simultaneous budget
for every one-point Riemann space in the exhaustive finite/infinity place
model. -/
theorem finiteExtension_onePoint_riemann_lower_of_genus
    [FunctionField.IsFullConstantField K L]
    (P : FiniteExtensionPlace K L) (N : Nat) :
    N * finiteExtensionPlaceDegree K L P + 1 ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L P N) +
        FunctionField.genus K L := by
  let D : FiniteExtensionDivisor K L := Finsupp.single P (N : Int)
  let Dchart := finiteExtensionDivisorEquivChart K L D
  have hRR := FunctionField.Chart.riemann_ineq K L Dchart
  have hdegree : FunctionField.Chart.deg K L Dchart =
      (N * finiteExtensionPlaceDegree K L P : Nat) := by
    rw [← finiteExtensionDivisorDegree_eq_chart K L D]
    dsimp only [D]
    rw [finiteExtensionDivisorDegree_single]
    norm_num
  have hspace : FunctionField.Chart.RRspace K L Dchart =
      finiteExtensionOnePointRiemannSpace K L P N := by
    rw [← finiteExtensionRiemannSpace_eq_chart K L D]
    rfl
  rw [FunctionField.Chart.ell, hspace, hdegree,
    ← FunctionField.genus_eq_genusChart K L] at hRR
  change ((Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P N) : Nat) : Int) ≥
    ((N * finiteExtensionPlaceDegree K L P : Nat) : Int) + 1 -
      (FunctionField.genus K L : Int) at hRR
  exact_mod_cast (show N * finiteExtensionPlaceDegree K L P + 1 ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L P N) +
        FunctionField.genus K L by omega)

end

end BGS.HasseWeil
