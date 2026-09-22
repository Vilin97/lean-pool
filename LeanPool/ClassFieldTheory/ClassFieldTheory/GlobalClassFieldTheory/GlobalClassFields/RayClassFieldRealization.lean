/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue
/-!
# Actual ray class fields

For a modulus `m` of a number field `K`, its ray congruence subgroup
`C_K^m` is closed and has finite index.  The finite-index class-field
construction therefore selects an actual finite abelian extension whose
determinant-norm range is exactly `C_K^m`.

The construction first occurs over the canonical fixed-field copy of `K`
inside the rational separable closure.  We then install the canonical
scalar structure from the original field, identify the norm range over
that original field, and obtain the genuine reciprocity equivalence

`Gal(K^m / K) ≃ C_K / C_K^m`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity
open CyclicCohomology

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The concrete finite Galois norm neighbourhood used to select the
ray class field attached to `m`. -/
noncomputable abbrev rayClassFieldNormAmbient
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The compatible abstract base subgroup used by the selected ray
class-field realization. -/
noncomputable abbrev rayClassFieldBaseSubgroup
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The finite abelian subextension selected by the ray congruence
subgroup `C_K^m`. -/
noncomputable abbrev rayClassFieldSubextension
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    FiniteAbelianSubextension
      (rayClassFieldBaseSubgroup K m) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The canonical fixed-field copy of the original number field in the
selected ray class-field realization. -/
noncomputable abbrev rayClassFieldBase
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- A chosen finite ray-class-field realization attached to `m`, selected
inside the rational separable closure.  Its intrinsic realization in the
fixed separable closure of `K` is `rayClassFieldSubfield`. -/
noncomputable abbrev rayClassField
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) : Type :=
  closedFiniteIndexClassField
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The canonical equivalence from `K` to the fixed-field base of its
selected ray class field. -/
noncomputable abbrev rayClassFieldBaseEquiv
    (m : RayClass.Modulus K) :
    K ≃ₐ[ℚ] rayClassFieldBase K m :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The ray congruence subgroup transported to the fixed-field base of
the selected realization. -/
def rayClassFieldTransportedCongruenceSubgroup
    (m : RayClass.Modulus K) :
    Subgroup
      (IdeleClassGroup (rayClassFieldBase K m)) :=
  (RayClass.Modulus.congruenceSubgroup m).map
    (ideleClassCongr
      (rayClassFieldBaseEquiv (K := K) m)).toMonoidHom

open scoped Classical in
/-- The determinant-norm range over the fixed-field base of the
selected ray class field is the transported ray congruence subgroup. -/
theorem rayClassField_ideleClassNorm_range
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm
      (rayClassFieldBase K m)
      (rayClassField K m)).range =
      rayClassFieldTransportedCongruenceSubgroup
        (K := K) m := by
  simpa only [rayClassFieldTransportedCongruenceSubgroup,
    rayClassFieldBaseEquiv, rayClassField, rayClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m))

open scoped Classical in
/-- The fixed-field base of the selected ray class field, regarded as
an algebra over the original number field. -/
noncomputable abbrev rayClassFieldBaseAlgebraOverOriginal
    (m : RayClass.Modulus K) :
    Algebra K (rayClassFieldBase K m) :=
  closedFiniteIndexClassFieldBaseAlgebraOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The canonical fixed-field identification as an equivalence over
the original number field. -/
noncomputable abbrev rayClassFieldBaseEquivOverOriginal
    (m : RayClass.Modulus K) :
    K ≃ₐ[K] rayClassFieldBase K m :=
  closedFiniteIndexClassFieldBaseEquivOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The selected ray class field as an algebra over the original
number field. -/
noncomputable abbrev rayClassFieldAlgebraOverOriginal
    (m : RayClass.Modulus K) :
    Algebra K (rayClassField K m) :=
  closedFiniteIndexClassFieldAlgebraOverOriginal
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The scalar map into the ray class field is the canonical base
equivalence followed by fixed-field inclusion. -/
@[simp]
theorem rayClassField_algebraMap_original
    (m : RayClass.Modulus K) (x : K) :
    algebraMap K (rayClassField K m) x =
      algebraMap
        (rayClassFieldBase K m)
        (rayClassField K m)
        (rayClassFieldBaseEquiv (K := K) m x) := by
  simpa only [rayClassField, rayClassFieldBase,
    rayClassFieldBaseEquiv] using
    (closedFiniteIndexClassField_algebraMap_original
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) x)

open scoped Classical in
/-- A chosen embedding of the finite ray-class-field realization into the
fixed separable closure of its original base field. -/
noncomputable def rayClassFieldEmbedding
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    rayClassField K m →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

open scoped Classical in
/-- The intrinsic ray class field as an intermediate field of the fixed
separable closure of `K`. -/
noncomputable def rayClassFieldSubfield
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    IntermediateField K (SeparableClosure K) :=
  (rayClassFieldEmbedding K m).fieldRange

open scoped Classical in
/-- Every embedding of the chosen finite ray-class-field realization into
the fixed separable closure has the intrinsic ray-class-field range. -/
theorem rayClassFieldSubfield_eq_fieldRange
    (m : RayClass.Modulus K)
    (f : rayClassField K m →ₐ[K] SeparableClosure K) :
    rayClassFieldSubfield K m = f.fieldRange :=
  AlgHom.fieldRange_eq_of_normal
    (rayClassFieldEmbedding K m) f

open scoped Classical in
/-- Over the original number field, the determinant-norm range of the
selected ray class field is exactly `C_K^m`. -/
theorem rayClassField_ideleClassNorm_range_over_original
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm K (rayClassField K m)).range =
      RayClass.Modulus.congruenceSubgroup m := by
  simpa only [rayClassField] using
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m))

open scoped Classical in
/-- A finite abelian extension is isomorphic over `K` to the selected
ray class field of modulus `m` exactly when its genuine idèle-class
norm range is `C_K^m`.  This is the actual-field uniqueness statement
for ray class fields. -/
theorem
    nonempty_algEquiv_rayClassField_iff_ideleClassNorm_range_eq
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L ≃ₐ[K] rayClassField K m) ↔
      (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup m := by
  rw [
    nonempty_algEquiv_iff_ideleClassNorm_range_eq,
    rayClassField_ideleClassNorm_range_over_original]

open scoped Classical in
/-- Increasing the modulus decreases the actual determinant-norm
range of the selected ray class field.  This is the norm-subgroup
form of the contravariant inclusion of ray class fields. -/
theorem rayClassField_ideleClassNorm_range_antitone
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    (_root_.ideleClassNorm K (rayClassField K n)).range ≤
      (_root_.ideleClassNorm K (rayClassField K m)).range := by
  calc
    (_root_.ideleClassNorm K (rayClassField K n)).range =
        RayClass.Modulus.congruenceSubgroup n :=
      rayClassField_ideleClassNorm_range_over_original
        (K := K) n
    _ ≤ RayClass.Modulus.congruenceSubgroup m :=
      rayClassCongruenceSubgroup_antitone
        (K := K) hmn
    _ = (_root_.ideleClassNorm K (rayClassField K m)).range :=
      (rayClassField_ideleClassNorm_range_over_original
        (K := K) m).symm

open scoped Classical in
/-- Divisibility of moduli produces an embedding between the selected
ray-class-field types over the original number field.  Literal containment
inside the fixed separable closure is instead stated by
`rayClassFieldSubfield_mono`. -/
theorem rayClassField_nonempty_algHom_of_le
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    Nonempty
      (rayClassField K m →ₐ[K]
        rayClassField K n) :=
  finiteAbelianExtension_nonempty_algHom_of_normRange_le
    (K := K)
    (rayClassField K m)
    (rayClassField K n)
    (rayClassField_ideleClassNorm_range_antitone
      (K := K) hmn)

open scoped Classical in
/-- Divisibility of moduli gives literal inclusion of the corresponding
intrinsic ray class fields inside the fixed separable closure. -/
theorem rayClassFieldSubfield_mono
    {m n : RayClass.Modulus K}
    (hmn : m ≤ n) :
    rayClassFieldSubfield K m ≤ rayClassFieldSubfield K n := by
  let f : rayClassField K m →ₐ[K] rayClassField K n :=
    Classical.choice
      (rayClassField_nonempty_algHom_of_le (K := K) hmn)
  calc
    rayClassFieldSubfield K m =
        ((rayClassFieldEmbedding K n).comp f).fieldRange :=
      rayClassFieldSubfield_eq_fieldRange
        (K := K) m ((rayClassFieldEmbedding K n).comp f)
    _ ≤ (rayClassFieldEmbedding K n).fieldRange := by
      intro x hx
      rcases AlgHom.mem_fieldRange.mp hx with ⟨y, rfl⟩
      exact AlgHom.mem_fieldRange.mpr ⟨f y, rfl⟩
    _ = rayClassFieldSubfield K n := rfl

open scoped Classical in
/-- A finite abelian extension embeds in the selected ray class field
of modulus `m` exactly when `m` is a defining modulus for its genuine
idèle-class norm subgroup. -/
theorem
    nonempty_algHom_to_rayClassField_iff_isDefiningModulus
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      IsDefiningModulus
        ((_root_.ideleClassNorm K L).range) m := by
  change
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range
  rw [
    nonempty_algHom_iff_ideleClassNorm_range_le,
    rayClassField_ideleClassNorm_range_over_original]

open scoped Classical in
/-- Actual containment in a narrow ray class field is equivalent to
divisibility by the exact narrow finite conductor. -/
theorem
    nonempty_algHom_to_rayClassField_narrowOfFinite_iff_narrowFiniteConductor_le
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (n : RayClass.FiniteModulus K) :
    Nonempty
        (L →ₐ[K]
          rayClassField K (RayClass.Modulus.narrowOfFinite n)) ↔
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) ≤ n := by
  rw [nonempty_algHom_to_rayClassField_iff_isDefiningModulus]
  constructor
  · intro hm
    simpa only [ideleClassNormNarrowFiniteConductor,
      RayClass.Modulus.finitePart_narrowOfFinite] using
      (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).narrowFiniteConductor_le hm
  · intro hn
    exact
      isDefiningModulus_mono
        ((_root_.ideleClassNorm K L).range)
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        ⟨hn, Finset.subset_univ _⟩

open scoped Classical in
/-- The ray class field of the exact narrow finite conductor genuinely
contains the given finite abelian extension. -/
theorem
    finiteAbelianExtension_nonempty_algHom_to_conductorRayClassField
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Nonempty
      (L →ₐ[K]
        rayClassField K
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) :=
  (nonempty_algHom_to_rayClassField_iff_isDefiningModulus
    (K := K) L
    (RayClass.Modulus.narrowOfFinite
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)))).2
    (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
      (K := K) (L := L))

open scoped Classical in
/-- Every finite abelian extension is genuinely contained in a ray
class field over the original base. -/
theorem finiteAbelianExtension_exists_rayClassFieldEmbedding
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ∃ m : RayClass.Modulus K,
      Nonempty (L →ₐ[K] rayClassField K m) :=
  ⟨RayClass.Modulus.narrowOfFinite
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)),
    finiteAbelianExtension_nonempty_algHom_to_conductorRayClassField
      (K := K) L⟩

open scoped Classical in
/-- The exact narrow finite conductor is the greatest common divisor
of the finite parts of the moduli of the actual ray class fields
containing a finite abelian extension. -/
theorem
    ideleClassNorm_narrowFiniteConductor_is_gcd_of_rayClassField_embeddings
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    (∀ m : RayClass.Modulus K,
        Nonempty (L →ₐ[K] rayClassField K m) →
          ideleClassNormNarrowFiniteConductor
              (K := K) (L := L) ≤ m.finitePart) ∧
      (∀ d : RayClass.FiniteModulus K,
        (∀ m : RayClass.Modulus K,
          Nonempty (L →ₐ[K] rayClassField K m) →
            d ≤ m.finitePart) →
          d ≤ ideleClassNormNarrowFiniteConductor
            (K := K) (L := L)) := by
  have hgcd :=
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor_is_gcd
  constructor
  · intro m hm
    simpa only [ideleClassNormNarrowFiniteConductor] using
      hgcd.1 m
        ((nonempty_algHom_to_rayClassField_iff_isDefiningModulus
          (K := K) L m).1 hm)
  · intro d hd
    simpa only [ideleClassNormNarrowFiniteConductor] using
      hgcd.2 d (fun m hm =>
        hd m
          ((nonempty_algHom_to_rayClassField_iff_isDefiningModulus
            (K := K) L m).2 hm))

open scoped Classical in
/-- Global reciprocity for the selected ray class field as a
homeomorphic multiplicative equivalence

`Gal(K^m / K) ≃ₜ* C_K / C_K^m`.

The topology is the genuine finite Krull topology on the Galois group
and the native quotient topology on the ray class group. -/
noncomputable def
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃ₜ*
      RayClass.RayClassGroup m := by
  letI : DiscreteTopology (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup m)
  exact
    { closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

open scoped Classical in
/-- The underlying map of topological ray-class reciprocity is the
general closed-finite-index reciprocity equivalence. -/
@[simp]
theorem
    rayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
    (m : RayClass.Modulus K)
    (σ : Gal((rayClassField K m)/K)) :
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m σ =
      closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) (RayClass.Modulus.congruenceSubgroup m)
        (RayClass.isClosed_congruenceSubgroup m) σ := by
  rfl

open scoped Classical in
/-- On an idèle-class representative, topological ray-class
reciprocity sends its genuine global norm-residue symbol to its ray
class modulo `C_K^m`. -/
theorem
    rayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    rayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (Reciprocity.globalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  rw [rayClassFieldGaloisContinuousMulEquivRayClassGroup_apply]
  simpa only [rayClassField] using
    (closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) c)

open scoped Classical in
/-- The degree of the selected ray class field is the order of the ray
class group. -/
theorem rayClassField_finrank_eq_rayClassGroup_card
    (m : RayClass.Modulus K) :
    Module.finrank K (rayClassField K m) =
      Nat.card (RayClass.RayClassGroup m) := by
  calc
    Module.finrank K (rayClassField K m) =
        (RayClass.Modulus.congruenceSubgroup m).index :=
      by
        simpa only [rayClassField] using
          (closedFiniteIndexClassField_finrank_eq_index
            (K := K) (RayClass.Modulus.congruenceSubgroup m)
            (RayClass.isClosed_congruenceSubgroup m))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            RayClass.Modulus.congruenceSubgroup m) :=
      Subgroup.index_eq_card
        (RayClass.Modulus.congruenceSubgroup m)
    _ =
        Nat.card (RayClass.RayClassGroup m) :=
      rfl

open scoped Classical in
/-- Global reciprocity identifies the genuine Galois group of the
selected ray class field with the ray class group `C_K / C_K^m`. -/
noncomputable abbrev rayClassFieldGaloisEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃*
      RayClass.RayClassGroup m :=
  closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (K := K) (RayClass.Modulus.congruenceSubgroup m)
    (RayClass.isClosed_congruenceSubgroup m)

open scoped Classical in
/-- The subfield of the ray class field fixed by a prescribed ray-class
subgroup, transported through the genuine reciprocity equivalence. -/
noncomputable def rayClassSubgroupFixedField
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    IntermediateField K (rayClassField K m) :=
  IntermediateField.fixedField
    (H.map (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm.toMonoidHom)

open scoped Classical in
/-- The fixed field, embedded in the chosen separable closure of the original
number field. -/
noncomputable def rayClassSubgroupSubfield
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    IntermediateField K (SeparableClosure K) :=
  (rayClassSubgroupFixedField (K := K) m H).map
    (rayClassFieldEmbedding K m)

open scoped Classical in
/-- The fixed field is a finite abelian extension of the original field. -/
noncomputable def rayClassSubgroupSubextension
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    ClassFieldTheory.FiniteAbelianExtension K := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let E := F.map j
  have hfin : FiniteDimensional K E :=
    (IntermediateField.equivMap F j).toLinearEquiv.finiteDimensional
  have hab : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom
      (IntermediateField.equivMap F j).symm.toAlgHom
  exact ⟨E, hfin, hab⟩

open scoped Classical in
/-- The ray class group acts on the subfield fixed by `H` by restricting
the reciprocity action on the full ray class field. -/
noncomputable def rayClassSubgroupFixedFieldArtin
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.RayClassGroup m →*
      (rayClassSubgroupFixedField (K := K) m H ≃ₐ[K]
        rayClassSubgroupFixedField (K := K) m H) :=
  (AlgEquiv.restrictNormalHom
      (rayClassSubgroupFixedField (K := K) m H)).comp
    (rayClassFieldGaloisEquivRayClassGroup (K := K) m).symm.toMonoidHom

open scoped Classical in
/-- The restricted reciprocity action reaches every automorphism of
the fixed field. -/
theorem rayClassSubgroupFixedFieldArtin_surjective
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    Function.Surjective (rayClassSubgroupFixedFieldArtin (K := K) m H) := by
  intro τ
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (E := rayClassField K m) τ
  refine ⟨rayClassFieldGaloisEquivRayClassGroup (K := K) m σ, ?_⟩
  simpa [rayClassSubgroupFixedFieldArtin] using hσ

open scoped Classical in
/-- The exact kernel of the fixed-field reciprocity action is `H`. -/
theorem rayClassSubgroupFixedFieldArtin_ker
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    (rayClassSubgroupFixedFieldArtin (K := K) m H).ker = H := by
  let e := rayClassFieldGaloisEquivRayClassGroup (K := K) m
  let F := rayClassSubgroupFixedField (K := K) m H
  have hfix : F.fixingSubgroup = H.map e.symm.toMonoidHom := by
    exact IntermediateField.fixingSubgroup_fixedField
      (H.map e.symm.toMonoidHom)
  ext x
  change e.symm x ∈ (AlgEquiv.restrictNormalHom F).ker ↔ x ∈ H
  rw [F.restrictNormalHom_ker, hfix]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (e.symm.injective hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

open scoped Classical in
private theorem rayClassGroup_mul_comm
    (m : RayClass.Modulus K)
    (x y : RayClass.RayClassGroup m) : x * y = y * x := by
  refine QuotientGroup.induction_on x ?_
  intro a
  refine QuotientGroup.induction_on y ?_
  intro b
  simpa only [← QuotientGroup.mk_mul, QuotientGroup.mk'_apply] using
    congrArg (QuotientGroup.mk' (RayClass.Modulus.congruenceSubgroup m))
      (mul_comm a b)

open scoped Classical in
/-- Inversion of ray classes is a homomorphism because idèle classes
commute. This form does not require a commutative-group instance on the
quotient presentation. -/
private def rayClassGroupInvHom (m : RayClass.Modulus K) :
    RayClass.RayClassGroup m →* RayClass.RayClassGroup m where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' x y := by
    rw [mul_inv_rev]
    exact rayClassGroup_mul_comm (K := K) m y⁻¹ x⁻¹

open scoped Classical in
/-- Arithmetic reciprocity on the fixed field, transported to the chosen
subextension of the separable closure of `K`. The ambient ray-class
equivalence is geometrically normalized, so its input is inverted. -/
noncomputable def rayClassSubgroupArtin
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.RayClassGroup m →*
      (rayClassSubgroupSubextension (K := K) m H ≃ₐ[K]
        rayClassSubgroupSubextension (K := K) m H) :=
  (AlgEquiv.autCongr
      (IntermediateField.equivMap
        (rayClassSubgroupFixedField (K := K) m H)
        (rayClassFieldEmbedding K m))).toMonoidHom.comp
    ((rayClassSubgroupFixedFieldArtin (K := K) m H).comp
      (rayClassGroupInvHom (K := K) m))

open scoped Classical in
/-- The transported reciprocity map is surjective. -/
theorem rayClassSubgroupArtin_surjective
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    Function.Surjective (rayClassSubgroupArtin (K := K) m H) := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let α := AlgEquiv.autCongr (IntermediateField.equivMap F j)
  change Function.Surjective
    (α.toMonoidHom.comp
      ((rayClassSubgroupFixedFieldArtin (K := K) m H).comp
        (rayClassGroupInvHom (K := K) m)))
  exact (α.surjective.comp
    (rayClassSubgroupFixedFieldArtin_surjective (K := K) m H)).comp
      (fun x => ⟨x⁻¹, inv_inv x⟩)

open scoped Classical in
/-- The transported reciprocity map has exactly the prescribed kernel. -/
theorem rayClassSubgroupArtin_ker
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    (rayClassSubgroupArtin (K := K) m H).ker = H := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let α := AlgEquiv.autCongr (IntermediateField.equivMap F j)
  let a := rayClassSubgroupFixedFieldArtin (K := K) m H
  ext x
  change α (a x⁻¹) = 1 ↔ x ∈ H
  have hx : a x⁻¹ = 1 ↔ x⁻¹ ∈ H := by
    change x⁻¹ ∈ a.ker ↔ x⁻¹ ∈ H
    rw [rayClassSubgroupFixedFieldArtin_ker (K := K) m H]
  constructor
  · intro h
    exact H.inv_mem_iff.mp
      (hx.mp (α.injective (h.trans (map_one α).symm)))
  · intro h
    simp only [hx.mpr (H.inv_mem_iff.mpr h), map_one]

open scoped Classical in
/-- The fixed subextension has a norm subgroup containing the ray
congruence subgroup. This is the defining-modulus input for its
unramifiedness away from the modulus. -/
theorem rayClassSubgroupSubextension_norm_range
    (m : RayClass.Modulus K)
    (H : Subgroup (RayClass.RayClassGroup m)) :
    RayClass.Modulus.congruenceSubgroup m ≤
      (_root_.ideleClassNorm K
        (rayClassSubgroupSubextension (K := K) m H)).range := by
  let F := rayClassSubgroupFixedField (K := K) m H
  let j := rayClassFieldEmbedding K m
  let E := rayClassSubgroupSubextension (K := K) m H
  let f : E →ₐ[K] rayClassField K m :=
    (IntermediateField.val F).comp
      (IntermediateField.equivMap F j).symm.toAlgHom
  have hle :
      (_root_.ideleClassNorm K (rayClassField K m)).range ≤
        (_root_.ideleClassNorm K E).range :=
    ideleClassNorm_range_le_of_algHom (K := K) E (rayClassField K m) f
  calc
    RayClass.Modulus.congruenceSubgroup m =
        (_root_.ideleClassNorm K (rayClassField K m)).range :=
      (rayClassField_ideleClassNorm_range_over_original m).symm
    _ ≤ (_root_.ideleClassNorm K E).range := hle
    _ = (_root_.ideleClassNorm K
        (rayClassSubgroupSubextension (K := K) m H)).range := rfl

open scoped Classical in
/-- Under ray-class reciprocity, the actual global norm-residue symbol
is the ray class of its idèle-class representative. -/
theorem rayClassFieldGaloisEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    rayClassFieldGaloisEquivRayClassGroup
        (K := K) m
        (globalNormResidueMonoidHom K
          (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  simpa only [rayClassField, rayClassFieldGaloisEquivRayClassGroup] using
    (closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
      (K := K) (RayClass.Modulus.congruenceSubgroup m)
      (RayClass.isClosed_congruenceSubgroup m) c)

end GlobalClassFields
end GlobalClassFieldTheory
