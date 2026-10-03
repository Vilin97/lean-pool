/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality
/-!
# Restriction naturality of the actual abelian local Artin map

The actual algebraic and continuous Artin maps commute with restriction
between finite abelian intermediate fields of the fixed separable closure.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory
open RamificationTheory

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Restriction between the actual Galois groups of two finite intermediate
fields, bundled as a continuous homomorphism for their finite Krull
topologies. -/
noncomputable def intermediateFieldRestrictContinuous
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K F]
    [IsGalois K E] :
    Gal(F/K) →ₜ* Gal(E/K) :=
  { intermediateFieldRestrictNormalHom E F hEF with
    continuous_toFun := continuous_of_discreteTopology }

/-- Finite Artin homomorphisms commute with restriction along a
tower of finite abelian intermediate fields. -/
theorem abelianLocalArtinMonoidHom_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictNormalHom E F hEF).comp
        (abelianLocalArtinMonoidHom K F) =
      abelianLocalArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro a
  exact localArtinAutomorphism_restrict K E F hEF a

/-- The continuous actual finite Artin maps commute with restriction along
a tower of finite abelian intermediate fields. -/
theorem abelianLocalArtinMap_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictContinuous K E F hEF).comp
        (abelianLocalArtinMap K F) =
      abelianLocalArtinMap K E := by
  apply ContinuousMonoidHom.ext
  intro a
  change intermediateFieldRestrictNormalHom E F hEF
      (abelianLocalArtinMap K F a) =
    abelianLocalArtinMap K E a
  rw [show abelianLocalArtinMap K F a =
      abelianLocalArtinMonoidHom K F a by
        exact DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K F) a,
    show abelianLocalArtinMap K E a =
      abelianLocalArtinMonoidHom K E a by
        exact DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K E) a]
  exact DFunLike.congr_fun
    (abelianLocalArtinMonoidHom_restrict K E F hEF) a

end LocalClassFieldTheory
