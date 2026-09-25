/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Abelianization.Defs
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
/-!
# The actual abelian local Artin map

For a finite abelian Galois extension, finite local reciprocity takes values
in the actual Galois group, not merely its abelianization.  This module
provides both the algebraic homomorphism and its continuous refinement for
the native topologies.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory
open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite local Artin homomorphism with values in the actual Galois
group of an abelian extension. -/
noncomputable def abelianLocalArtinMonoidHom :
    Kˣ →* Gal(L/K) :=
  ((Abelianization.equivOfComm (H := Gal(L/K))).symm).toMonoidHom.comp
    (localArtinMonoidHom K L)

/-- The actual abelian local Artin homomorphism is surjective. -/
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
  (Abelianization.equivOfComm (H := Gal(L/K))).symm.surjective.comp
    (localArtinMonoidHom_surjective K L)

/-- The kernel of the actual abelian local Artin homomorphism is the norm
subgroup. -/
theorem abelianLocalArtinMonoidHom_ker :
    MonoidHom.ker (abelianLocalArtinMonoidHom K L) =
      localNormSubgroup K L := by
  rw [← localArtinMonoidHom_ker K L]
  ext a
  simp only [MonoidHom.mem_ker, abelianLocalArtinMonoidHom,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro ha
    apply (Abelianization.equivOfComm (H := Gal(L/K))).symm.injective
    simpa using ha
  · intro ha
    rw [ha, map_one]

/-- For a finite abelian Galois extension, topological abelianization is
canonically homeomorphic to the actual Galois group. -/
noncomputable def topologicalAbelianizationEquivSelf :
    TopologicalAbelianization Gal(L/K) ≃ₜ* Gal(L/K) := by
  letI : DiscreteTopology (TopologicalAbelianization Gal(L/K)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : TopologicalAbelianization Gal(L/K) ≃* Gal(L/K) :=
    (topologicalAbelianizationFiniteEquiv K L).symm.trans
      (Abelianization.equivOfComm (H := Gal(L/K))).symm
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The continuous local Artin map with values in the actual Galois group
of a finite abelian extension. -/
noncomputable def abelianLocalArtinMap :
    Kˣ →ₜ* Gal(L/K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (topologicalAbelianizationEquivSelf K L)).comp
    (localArtinMap K L)

/-- Forgetting topology from the continuous actual Artin map recovers the
algebraic actual Artin homomorphism. -/
theorem abelianLocalArtinMap_toMonoidHom :
    (abelianLocalArtinMap K L).toMonoidHom =
      abelianLocalArtinMonoidHom K L := by
  change
    ((Abelianization.equivOfComm (H := Gal(L/K))).symm).toMonoidHom.comp
        ((topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
          (localArtinMap K L).toMonoidHom) =
      ((Abelianization.equivOfComm (H := Gal(L/K))).symm).toMonoidHom.comp
        (localArtinMonoidHom K L)
  rw [localArtinMap_toMonoidHom K L]

/-- The continuous actual abelian local Artin map is surjective. -/
theorem abelianLocalArtinMap_surjective :
    Function.Surjective (abelianLocalArtinMap K L) :=
  (topologicalAbelianizationEquivSelf K L).surjective.comp
    (localArtinMap_surjective K L)

/-- The kernel of the continuous actual abelian local Artin map is the norm
subgroup. -/
theorem abelianLocalArtinMap_ker :
    (abelianLocalArtinMap K L).toMonoidHom.ker =
      localNormSubgroup K L := by
  rw [abelianLocalArtinMap_toMonoidHom,
    abelianLocalArtinMonoidHom_ker]

end LocalClassFieldTheory
