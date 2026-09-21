/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv
import Mathlib.Algebra.Group.Subgroup.Map
/-!
# Norm membership under compatible field equivalences

Transporting both fields of a finite extension through compatible ring
equivalences preserves the actual field norms, not merely their index.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w x

/-- An element is a field norm exactly when its image under a compatible
base-field equivalence is a field norm in the transported extension. -/
theorem mem_fieldNormSubgroup_iff_ringEquiv
    {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
    [Field F] [Field M] [Field F'] [Field M']
    [Algebra F M] [Algebra F' M']
    [FiniteDimensional F M] [FiniteDimensional F' M']
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (a : Fˣ) :
    a ∈ fieldNormSubgroup F M ↔
      (Units.mapEquiv eF.toMulEquiv) a ∈ fieldNormSubgroup F' M' := by
  rw [← fieldNormSubgroup_map_ringEquiv eF eM he]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end ClassFieldTheory
