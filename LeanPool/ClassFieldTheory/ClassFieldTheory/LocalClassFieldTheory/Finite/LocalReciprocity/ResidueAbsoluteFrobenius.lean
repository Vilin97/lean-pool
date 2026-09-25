/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius

/-! # Residue Absolute Frobenius -/

@[expose] public section
namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension

The finite Frobenius exponent maps are compatible with restriction.  This
file therefore assembles them in the actual inverse-limit presentation of an
infinite Galois group.  It produces the canonical continuous homomorphism
from the profinite integers to the Galois group of an algebraic Galois
extension of a finite field.

For an algebraic closure this is the Frobenius map compared with the degree
map in finite local reciprocity. The construction itself does not require a
bijectivity hypothesis.
-/

noncomputable
section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The finite Frobenius action on an intermediate field, with finiteness
derived from finite-dimensionality over the finite base. -/
def finiteResidueFrobeniusIntermediate
    (E : FiniteGaloisIntermediateField k Omega) :
    ZHatMul →ₜ* (E ≃ₐ[k] E) := by
  letI : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat k E

/-- The compatible finite Frobenius coordinates attached to one profinite
integer. -/
def residueFrobeniusLimitPoint (z : ZHatMul) :
    limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  val := fun E => finiteResidueFrobeniusIntermediate k Omega E.unop z
  property := by
    intro E F f
    algebraize [Subsemiring.inclusion <| leOfHom f.1]
    have : IsScalarTower k F.unop E.unop :=
      IsScalarTower.of_algebraMap_eq (congrFun rfl)
    let : Finite F.unop := Module.finite_of_finite k
    let : Finite E.unop := Module.finite_of_finite k
    change AlgEquiv.restrictNormalHom F.unop
        (finiteResidueFrobeniusFromZHat k E.unop z) =
      finiteResidueFrobeniusFromZHat k F.unop z
    exact restrictNormalHom_finiteResidueFrobeniusFromZHat
      (k := k) (E := F.unop) (F := E.unop) z

/-- The compatible Frobenius coordinates as a continuous homomorphism into
the finite-Galois inverse limit. -/
def residueFrobeniusToLimit :
    ZHatMul →ₜ* limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  toFun := residueFrobeniusLimitPoint k Omega
  map_one' := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_mul x y
  continuous_toFun := by
    have hcontinuous (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
          inferInstance (krullTopology k E.unop)
          (finiteResidueFrobeniusIntermediate k Omega E.unop) :=
      (finiteResidueFrobeniusIntermediate k Omega E.unop).continuous_toFun
    let (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        TopologicalSpace (E.unop ≃ₐ[k] E.unop) :=
      ((InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega).obj E).toProfinite.toTop.str
    apply Continuous.subtype_mk
    exact continuous_pi fun E => by
      change @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
        inferInstance inferInstance
        (finiteResidueFrobeniusIntermediate k Omega E.unop)
      rw [show
        (inferInstance : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) =
          krullTopology k E.unop by
        change (⊥ : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) = krullTopology k E.unop
        exact (@DiscreteTopology.eq_bot _ (krullTopology k E.unop) inferInstance).symm]
      exact hcontinuous E

omit [IsGalois k Omega] in
/-- States the theorem `residueFrobeniusToLimit_apply_component`. -/
theorem residueFrobeniusToLimit_apply_component (z : ZHatMul)
    (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
    (residueFrobeniusToLimit k Omega z).val E =
      finiteResidueFrobeniusIntermediate k Omega E.unop z :=
  rfl

/-- The canonical continuous Frobenius-parameter homomorphism
`ℤ̂ → Gal(Omega/k)` for a Galois algebraic extension of a finite field. -/
def residueAbsoluteFrobenius : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit k Omega).symm).comp
    (residueFrobeniusToLimit k Omega)

/-- Restricting the assembled Frobenius to a finite Galois intermediate
field gives exactly the finite Frobenius coordinate. -/
theorem restrictNormalHom_residueAbsoluteFrobenius
    (z : ZHatMul) (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z) =
      finiteResidueFrobeniusIntermediate k Omega E z := by
  have hcomponent := congrArg (fun q => q.val (op E))
    ((InfiniteGalois.continuousMulEquivToLimit k Omega).apply_symm_apply
      (residueFrobeniusToLimit k Omega z))
  exact hcomponent

/-- The element `1 ∈ ℤ̂` gives the actual arithmetic Frobenius on every
finite Galois residue subextension. -/
theorem restrictNormalHom_residueAbsoluteFrobenius_one
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ZHat))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  rw [restrictNormalHom_residueAbsoluteFrobenius]
  let : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat_one k E

/-- Arithmetic Frobenius on an algebraic Galois extension restricts to
arithmetic Frobenius on every finite Galois intermediate field. -/
theorem restrictNormalHom_frobeniusAlgEquivOfAlgebraic
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Omega).injective
  calc
    algebraMap E Omega
        ((AlgEquiv.restrictNormalHom E
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega
          (algebraMap E Omega x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) E x
    _ = algebraMap E Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k E x) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E Omega) x (Fintype.card k)).symm

/-- The distinguished element `1 ∈ ℤ̂` acts on the whole algebraic Galois
extension by the actual arithmetic Frobenius. -/
@[simp]
theorem residueAbsoluteFrobenius_one :
    residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega := by
  apply (InfiniteGalois.continuousMulEquivToLimit k Omega).injective
  apply Subtype.ext
  funext E
  change AlgEquiv.restrictNormalHom E.unop
      (residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat))) =
    AlgEquiv.restrictNormalHom E.unop
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
  rw [restrictNormalHom_residueAbsoluteFrobenius_one,
    restrictNormalHom_frobeniusAlgEquivOfAlgebraic]

end
end LocalClassFieldTheory
