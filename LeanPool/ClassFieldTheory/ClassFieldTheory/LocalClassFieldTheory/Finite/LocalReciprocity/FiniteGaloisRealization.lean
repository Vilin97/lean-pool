/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.SeparableClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient

/-! # Finite Galois Realization -/
namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

/-!
# Finite local reciprocity: realizing finite Galois extensions in a separable closure

Every finite Galois extension `L/K` is embedded into the chosen separable
closure of `K`.  Its image supplies the concrete closed subgroup used by the
abstract class-field theory.  The resulting abstract fixed coefficient group
is `Lˣ`, and the resulting abstract extension quotient is the actual
`Gal(L/K)`.

No perfectness hypothesis is imposed; this includes equal-characteristic
local fields such as finite extensions of `𝔽_q((t))`.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Realization relative to an explicit embedding -/

/-- The embedded copy of `L` determined by an explicit embedding into the
fixed separable closure.  Keeping the embedding visible is what makes the
canonicity argument in the finite local reciprocity theorem meaningful. -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range. -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

/-- The closed fixing subgroup attached to an explicit realization of
`L/K` in the separable closure. -/
def finiteGaloisClosedFixingSubgroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  closedFixingSubgroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The fixing subgroup of an embedded finite Galois extension is normal in the absolute
subgroup. -/
noncomputable instance finiteGaloisExtensionSubgroupOfEmbedding_normal
    (i : L →ₐ[K] SeparableClosure K) :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal := by
  change
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (closedFixingSubgroup K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
  infer_instance

/-- The fixed coefficient group attached to an explicit realization is
canonically the actual unit group `Lˣ`. -/
def finiteGaloisUnitsEquivAbstractFixedOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) :=
  embeddedFieldUnitsEquivGaloisFixed K (SeparableClosure K) L i

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed-module equivalence sends a field unit to the unit induced by the chosen embedding. -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe
    (i : L →ₐ[K] SeparableClosure K) (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L i
      (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

/-- The abstract class-formation extension quotient attached to an explicit realization
of `L/K` is the actual relative Galois group. -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ((closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) ≃*
      Gal(L / K) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)).trans
      (AlgEquiv.autCongr
        (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm

/-- The subgroup attached to an explicit finite Galois realization has
index equal to the ordinary field degree. -/
theorem finiteGaloisExtensionSubgroupOfEmbedding_index_eq_finrank
    (i : L →ₐ[K] SeparableClosure K) :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))).index =
      Module.finrank K L := by
  let : Finite
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))) :=
    Finite.of_equiv (Gal(L / K))
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).symm.toEquiv
  calc
    _ = Nat.card
        ((closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
          extensionSubgroup
            (closedFixingSubgroup K (SeparableClosure K)
              (⊥ : IntermediateField K (SeparableClosure K)))
            (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
            (fixingSubgroupLeBase K (SeparableClosure K)
              (finiteGaloisFieldRangeOfEmbedding K L i))) :=
      Subgroup.index_eq_card _
    _ = Nat.card (Gal(L / K)) :=
      Nat.card_congr
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).toEquiv
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-! ## The chosen realization -/

/-- The embedded copy of `L` inside the fixed separable closure. -/
def finiteGaloisFieldRange : IntermediateField K (SeparableClosure K) :=
  finiteGaloisFieldRangeOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen embedding identifies `L` with its actual field range. -/
def finiteGaloisFieldRangeEquiv :
    L ≃ₐ[K] finiteGaloisFieldRange K L :=
  finiteGaloisFieldRangeEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite Galois extension is Galois over the base field. -/
instance finiteGaloisFieldRange_isGalois :
    IsGalois K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_isGalois K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite extension is finite-dimensional over the base field. -/
instance finiteGaloisFieldRange_finiteDimensional :
    FiniteDimensional K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_finiteDimensional K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The concrete closed subgroup of the absolute separable Galois group
attached to `L/K`. -/
def finiteGaloisClosedFixingSubgroup :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  finiteGaloisClosedFixingSubgroupOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The fixing subgroup of the canonical finite Galois realization is normal. -/
instance finiteGaloisExtensionSubgroup_normal :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroup K L)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRange K L))).Normal := by
  change
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (closedFixingSubgroup K (SeparableClosure K)
        (finiteGaloisFieldRange K L))
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRange K L))).Normal
  infer_instance

/-- The actual coefficient group fixed by the concrete subgroup attached to
`L/K` is canonically `Lˣ`. -/
def finiteGaloisUnitsEquivAbstractFixed :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroup K L) :=
  finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

omit [FiniteDimensional K L] in
/-- The canonical fixed-module equivalence sends a unit through the chosen embedding. -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixed_coe (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixed K L (Additive.ofMul x)).1 =
      Additive.ofMul
        (Units.map
          (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L).toRingHom.toMonoidHom
            x) :=
  rfl

/-- For the concrete realization of `L/K`, the exact quotient used by
the abstract class-formation framework is canonically the actual Galois group `Gal(L/K)`. -/
def finiteGaloisAbstractQuotientEquivGaloisGroup :
    ((closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (finiteGaloisClosedFixingSubgroup K L)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRange K L))) ≃*
      Gal(L / K) :=
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The chosen realization has subgroup index equal to `[L : K]`. -/
theorem finiteGaloisExtensionSubgroup_index_eq_finrank :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroup K L)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRange K L))).index =
      Module.finrank K L :=
  finiteGaloisExtensionSubgroupOfEmbedding_index_eq_finrank K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

end
end LocalClassFieldTheory
