/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
/-!
# Splitting in the small Hilbert class field

The small Hilbert class field has reciprocity quotient the ordinary ideal
class group.  Thus the Frobenius class of a finite prime is its ordinary
ideal class, and it is trivial precisely when the prime ideal is principal.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

/-- Canonical class-group commutativity supplies normality for the quotient. -/
private theorem smallHilbertSplittingClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] smallHilbertSplittingClassGroupIsMulCommutative

variable {K : Type*} [Field K] [NumberField K]

/-- The Frobenius class of a finite prime in the reciprocity quotient of
the small Hilbert class field. -/
noncomputable def smallHilbertFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      GlobalClassFields.smallHilbertClassFieldNormSubgroup :=
  (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm
    (ClassGroup.mk K (FractionalIdealGroup.prime v))

/-- Reciprocity formulation of complete splitting in the small Hilbert
class field: the prime Frobenius class is trivial. -/
def SplitsCompletelyInSmallHilbertClassField
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  smallHilbertFrobeniusClass v = 1

/-- A finite prime splits completely in the small Hilbert class
field if and only if its prime ideal is principal. -/
theorem splitsCompletelyInSmallHilbertClassField_iff_principal
    (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletelyInSmallHilbertClassField v ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  change
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)).symm
          (ClassGroup.mk K (FractionalIdealGroup.prime v)) =
        1 ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range
  rw [←
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.map_one,
    (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm.injective.eq_iff]
  exact
    IdeleGroup.classGroup_mk_eq_one_iff
      (FractionalIdealGroup.prime v)

/-- Existential generator form of the small Hilbert splitting criterion. -/
theorem splitsCompletelyInSmallHilbertClassField_iff_exists_generator
    (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletelyInSmallHilbertClassField v ↔
      ∃ x : Kˣ,
        toPrincipalIdeal (𝓞 K) K x =
          FractionalIdealGroup.prime v := by
  rw [splitsCompletelyInSmallHilbertClassField_iff_principal]
  rfl

end IdealClassFieldTheory
end GlobalClassFieldTheory
