/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.Basic
/-!
# A finite normal closure of a number-field extension

This file places the normal-closure construction used throughout the
global theory below the adelic and splitting developments that consume
it.  The closure is formed inside mathlib's fixed algebraic closure, and
the original field is embedded by the canonical chosen lift.
-/

@[expose] public section

noncomputable
section

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The normal closure of `L / K`, constructed inside a fixed
algebraic closure of `K`. -/
abbrev finiteNormalClosure :=
  IntermediateField.normalClosure K L (AlgebraicClosure K)

noncomputable instance finiteNormalClosure_numberField :
    NumberField (finiteNormalClosure K L) :=
  NumberField.of_module_finite K (finiteNormalClosure K L)

noncomputable instance finiteNormalClosure_isGalois :
    IsGalois K (finiteNormalClosure K L) := by
  let f : L →ₐ[K] AlgebraicClosure K :=
    IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure K) :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq'
      f.comp_algebraMap.symm
  infer_instance

/-- A fixed embedding of `L` into its normal closure. -/
noncomputable def finiteNormalClosureEmbedding :
    L →ₐ[K] finiteNormalClosure K L :=
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  f.codRestrict
    (IntermediateField.normalClosure K L
      (AlgebraicClosure K)).toSubalgebra
    (fun x =>
      f.fieldRange_le_normalClosure
        (show f x ∈ f.fieldRange from ⟨x, rfl⟩))

/-- The distinguished copy of `L` in its finite normal closure. -/
noncomputable def finiteNormalClosureOriginalField :
    IntermediateField K (finiteNormalClosure K L) :=
  (finiteNormalClosureEmbedding K L).fieldRange

/-- The original extension is canonically equivalent to its
distinguished copy in the finite normal closure. -/
noncomputable def finiteNormalClosureOriginalFieldEquiv :
    L ≃ₐ[K] finiteNormalClosureOriginalField K L :=
  (finiteNormalClosureEmbedding K L).equivFieldRange

omit [NumberField K] [NumberField L] in
/-- Normal closure is invariant under replacing its source by an
isomorphic field. -/
theorem normalClosure_eq_top_of_source_algEquiv
    {M E : Type*}
    [Field M] [Algebra K M]
    [Field E] [Algebra K E]
    (e : L ≃ₐ[K] E)
    (hclosure :
      IntermediateField.normalClosure K L M = ⊤) :
    IntermediateField.normalClosure K E M = ⊤ := by
  apply top_unique
  rw [← hclosure]
  apply
    (normalClosure_le_iff
      (K := L)).2
  intro f
  let g : E →ₐ[K] M :=
    f.comp e.symm.toAlgHom
  have hRange :
      f.fieldRange = g.fieldRange := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [g]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by simp [g]⟩
  rw [hRange]
  exact g.fieldRange_le_normalClosure

/-- The distinguished copy of `L` generates its finite normal closure
under its `K`-conjugates. -/
theorem finiteNormalClosureOriginalField_normalClosure_eq_top :
    IntermediateField.normalClosure K
        (finiteNormalClosureOriginalField K L)
        (finiteNormalClosure K L) =
      ⊤ := by
  let : Nonempty (L →ₐ[K] AlgebraicClosure K) :=
    ⟨IsAlgClosed.lift⟩
  have hAbstract :
      IntermediateField.normalClosure K L
          (finiteNormalClosure K L) =
        ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (show IsNormalClosure K L
          (finiteNormalClosure K L) from inferInstance)).2
  exact
    normalClosure_eq_top_of_source_algEquiv
      (K := K) (L := L)
      (finiteNormalClosureOriginalFieldEquiv K L)
      hAbstract

/-- The degree of the original extension is bounded by the degree of
its finite normal closure. -/
theorem finrank_le_finiteNormalClosure :
    Module.finrank K L ≤
      Module.finrank K (finiteNormalClosure K L) := by
  exact
    (finiteNormalClosureEmbedding K L).toLinearMap
      |>.finrank_le_finrank_of_injective
        (finiteNormalClosureEmbedding K L).injective

/-- A degree-one finite field extension is the base field as an
algebra. -/
noncomputable def algEquivBaseOfFinrankEqOne
    (hdegree : Module.finrank K L = 1) :
    L ≃ₐ[K] K :=
  (AlgEquiv.ofBijective
    (Algebra.ofId K L)
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
      hdegree)).symm
