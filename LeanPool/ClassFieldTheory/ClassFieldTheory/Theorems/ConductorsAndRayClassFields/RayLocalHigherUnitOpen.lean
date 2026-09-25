/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
/-!
# Openness of local higher-unit groups

For every depth, including zero, the higher-unit subgroup is open in the
multiplicative group of the finite completion.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- Every local higher-unit group is open in the local multiplicative group. -/
theorem isOpen_rayLocalHigherUnitGroup
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsOpen ((rayLocalHigherUnitGroup v n :
      Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ) := by
  change IsOpen ((RayClass.localHigherUnitGroup v n :
    Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ)
  exact RayClass.isOpen_localHigherUnitGroup v n

end ClassFieldTheory
