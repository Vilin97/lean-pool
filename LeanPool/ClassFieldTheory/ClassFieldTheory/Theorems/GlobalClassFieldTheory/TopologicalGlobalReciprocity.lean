/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-! # Topological Global Reciprocity -/

@[expose] public section
open scoped NumberField

/-!
# Topological global reciprocity

For a number field `K`, the idèle class group modulo its identity component
is topologically isomorphic to the maximal abelian quotient of the absolute
Galois group. The statement uses Mathlib's groups on both sides.
-/

namespace ClassFieldTheory

universe u

/-- The topological form of global class field theory. -/
theorem topologicalGlobalReciprocity
    (K : Type u) [Field K] [NumberField K] :
    Nonempty (IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K) := by
  let : Small.{0} K := numberField_small K
  let S := Shrink.{0} K
  let : NumberField S := numberField_shrink K
  let e : S ≃ₐ[ℚ] K := (Shrink.ringEquiv K).toRatAlgEquiv
  let cS : IdeleClassGroup S ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 S) S :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib S
  let cK : IdeleClassGroup K ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let c : NumberField.IdeleClassGroup (𝓞 S) S ≃ₜ*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    cS.symm.trans ((ideleClassCongrContinuousMulEquiv e).trans cK)
  let q : IdeleClassConnectedQuotient S ≃ₜ*
      IdeleClassConnectedQuotient K :=
    connectedComponentQuotientCongr c
  let g : Field.absoluteGaloisGroupAbelianization S ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
  let r : IdeleClassConnectedQuotient S ≃ₜ*
      Field.absoluteGaloisGroupAbelianization S :=
    GlobalClassFieldTheory.Reciprocity.mathlibIdeleClassConnectedQuotientEquivAbelianization S
  exact ⟨q.symm.trans (r.trans g)⟩

end ClassFieldTheory
