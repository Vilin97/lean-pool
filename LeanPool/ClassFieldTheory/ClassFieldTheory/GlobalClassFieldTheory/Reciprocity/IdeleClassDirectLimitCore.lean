/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.NormKernelVanishing
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.FieldTheory.Galois.Profinite
/-!
# The rational absolute idele-class direct limit

Finite Galois relative idele class groups over `ℚ`, their scalar-extension
maps, and the induced absolute Galois representation.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

universe u

/-- The rational algebra structure on the chosen separable closure is
the one induced by its realization inside the algebraic closure. -/
@[reducible]
noncomputable instance rationalSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  letI : Algebra ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instAlgebra ℚ
  IntermediateField.algebra' (R' := ℚ)
    (separableClosure ℚ (AlgebraicClosure ℚ))

/-- A rational intermediate field uses its actual inclusion into the
chosen separable closure as its algebra structure. -/
@[reducible]
noncomputable instance rationalIntermediateFieldAlgebra
    (E : IntermediateField ℚ (SeparableClosure ℚ)) :
    Algebra ℚ E :=
  IntermediateField.algebra' (R' := ℚ) E

/-- Every finite-dimensional rational intermediate field is a number
field. -/
noncomputable instance rationalIntermediateFieldNumberField
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E] :
    NumberField E :=
  NumberField.of_module_finite ℚ E

/-- A finite quotient of nested closed rational absolute Galois
subgroups carries its canonical finite type. -/
noncomputable instance rationalClosedSubgroupQuotientFintype
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Fintype (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Fintype.ofFinite _

/-- Extending the diagonal rational idele class through two nested
intermediate fields is the diagonal class at the larger field. -/
theorem rationalRelativeIdeleClassEmbedding_classInclusion
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F]
    (h : E ≤ F)
    (c : IdeleClassGroup ℚ) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.classInclusion ℚ E c) =
      RelativeIdeleGroup.classInclusion ℚ F c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl

/-- The action of the rational absolute Galois group on one finite
relative idele class group, obtained by restricting automorphisms. -/
@[reducible]
noncomputable def rationalAbsoluteGaloisIdeleClassAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) := by
  letI :
      MulDistribMulAction (E ≃ₐ[ℚ] E)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ E
  exact
    MulDistribMulAction.compHom
      (RelativeIdeleGroup.ClassGroup ℚ E)
      (AlgEquiv.restrictNormalHom E)

/-- The rational absolute Galois action on every finite-Galois
relative idele class group. -/
noncomputable instance rationalFiniteGaloisIdeleClassMulDistribMulAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) :=
  rationalAbsoluteGaloisIdeleClassAction E

private instance
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    Monoid (RelativeIdeleGroup.ClassGroup ℚ E) :=
  inferInstance

private noncomputable instance :
    ∀ E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ),
      MulDistribMulAction
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
  fun E => rationalAbsoluteGaloisIdeleClassAction E

private noncomputable instance :
    ∀ E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ),
      SMul
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
  fun E => (rationalAbsoluteGaloisIdeleClassAction E).toSMul

theorem rationalAbsoluteGaloisIdeleClass_smul_mk
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (a : RelativeIdeleGroup ℚ E) :
    σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ E) a =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ E)
        ((AlgEquiv.restrictNormalHom E σ) • a) :=
  rfl

/-- Relative-adele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeAdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.conjugation ℚ E τ z) =
      RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.conjugation_tmul,
        RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
      apply Subtype.ext
      calc
        ((IntermediateField.inclusion h (τ x) : F) :
            SeparableClosure ℚ) =
            ((τ x : E) : SeparableClosure ℚ) := rfl
        _ = σ (x : SeparableClosure ℚ) := hστ x
        _ = σ ((IntermediateField.inclusion h x : F) :
            SeparableClosure ℚ) := rfl
        _ = (((AlgEquiv.restrictNormalHom F σ)
              (IntermediateField.inclusion h x) : F) :
            SeparableClosure ℚ) :=
          (AlgEquiv.restrictNormal_commutes σ F
            (IntermediateField.inclusion h x)).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Relative-idele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeIdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (a : RelativeIdeleGroup ℚ E) :
    RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h)
        (τ • a) =
      (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h) a := by
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_conjugation_of_restrict
      h σ τ hστ
      (a : RelativeAdeleRing ℚ E)

/-- Relative idele-class scalar extension intertwines conjugation with
the restriction of an absolute Galois automorphism. -/
theorem
    rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (τ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
    (rationalRelativeIdeleEmbedding_conjugation_of_restrict
      h σ τ hστ a)

/-- The transition map between finite Galois relative idele class groups
is equivariant for the rational absolute Galois action. -/
theorem rationalRelativeIdeleClassEmbedding_smul
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (σ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  apply rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    h σ (AlgEquiv.restrictNormalHom E σ)
  intro x
  simp only [AlgEquiv.restrictNormalHom_apply]

/-- Acting after scalar extension agrees with the class embedding induced
by the resulting restricted field embedding. -/
theorem
    rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c =
      RelativeIdeleGroup.classEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h)) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
  apply Units.ext
  change
    RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
          (a : RelativeAdeleRing ℚ E)) =
      RelativeIdeleGroup.adeleEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h))
        (a : RelativeAdeleRing ℚ E)
  induction (a : RelativeAdeleRing ℚ E) using
      TensorProduct.inductionOn with
  | tmul y x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- The equivariant scalar-extension transition map in the
finite-Galois idele-class system. -/
noncomputable def rationalRelativeIdeleClassTransition
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F) :
    MulDistribMulActionHom
      (MonoidHom.id
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      (RelativeIdeleGroup.ClassGroup ℚ E)
      (RelativeIdeleGroup.ClassGroup ℚ F) where
  toMonoidHom :=
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h)
  map_smul' σ c := by
    simpa using rationalRelativeIdeleClassEmbedding_smul h σ c

/-- Scalar extension of relative adeles along the identity inclusion is
the identity. -/
theorem rationalRelativeAdeleEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative adeles is transitive in a tower of
intermediate fields. -/
theorem rationalRelativeAdeleEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hEF) z) =
      RelativeIdeleGroup.adeleEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) z := by
  exact congrArg (fun f => f z)
    (Algebra.TensorProduct.map_id_comp
      (S := NumberField.AdeleRing (𝓞 ℚ) ℚ)
      (A := NumberField.AdeleRing (𝓞 ℚ) ℚ)
      (IntermediateField.inclusion hFH) (IntermediateField.inclusion hEF)).symm

/-- Scalar extension of relative idele classes along the identity
inclusion is the identity. -/
theorem rationalRelativeIdeleClassEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) c = c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ E))
    (Units.ext
      (rationalRelativeAdeleEmbedding_self E
        (a : RelativeAdeleRing ℚ E)))

/-- Scalar extension of relative idele classes is transitive in a tower
of intermediate fields. -/
theorem rationalRelativeIdeleClassEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hEF) c) =
      RelativeIdeleGroup.classEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) c := by
  have hinc : (IntermediateField.inclusion hFH).comp (IntermediateField.inclusion hEF) =
      IntermediateField.inclusion (hEF.trans hFH) := by
    ext x
    rfl
  calc
    _ = RelativeIdeleGroup.classEmbedding
        ((IntermediateField.inclusion hFH).comp (IntermediateField.inclusion hEF)) c :=
      RelativeIdeleGroup.classEmbedding_comp (K := ℚ) (L := E) (M := F) (N := H)
        (IntermediateField.inclusion hFH) (IntermediateField.inclusion hEF) c
    _ = _ := congrArg (fun f => RelativeIdeleGroup.classEmbedding f c) hinc

private noncomputable instance :
    DirectedSystem
      (fun E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
        RelativeIdeleGroup.ClassGroup ℚ E)
      (fun _ _ h => rationalRelativeIdeleClassTransition h) where
  map_self {i} c :=
    rationalRelativeIdeleClassEmbedding_self
      (i : IntermediateField ℚ (SeparableClosure ℚ)) c
  map_map {k} {j} {i} hIJ hJK c :=
    rationalRelativeIdeleClassEmbedding_comp
      (E := (i : IntermediateField ℚ (SeparableClosure ℚ)))
      (F := (j : IntermediateField ℚ (SeparableClosure ℚ)))
      (H := (k : IntermediateField ℚ (SeparableClosure ℚ)))
      hIJ hJK c

/-- The direct limit of the actual idele class groups of the finite
Galois subextensions of `SeparableClosure ℚ / ℚ`. -/
noncomputable abbrev rationalIdeleClassDirectLimit :=
  DirectLimit
    (fun E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
      RelativeIdeleGroup.ClassGroup ℚ E)
    (fun _ _ h => rationalRelativeIdeleClassTransition h)

/-- The multiplicative structure on the rational absolute idele-class
direct limit supplied by Mathlib's directed-limit construction. -/
noncomputable instance rationalIdeleClassDirectLimitMonoid :
    Monoid rationalIdeleClassDirectLimit :=
  DirectLimit.instMonoid

theorem rationalIdeleClassDirectLimit_mk_apply
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (c : RelativeIdeleGroup.ClassGroup ℚ E)
    (h : E ≤ F) :
    (⟦⟨F, RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c⟩⟧ :
        rationalIdeleClassDirectLimit) =
      ⟦⟨E, c⟩⟧ := by
  exact
    DirectLimit.mk_apply
      (F := fun E :
        FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
          RelativeIdeleGroup.ClassGroup ℚ E)
      (f := fun _ _ h =>
        rationalRelativeIdeleClassTransition h)
      E F c h

/-- The canonical map from one finite-level relative idele class group
to the directed limit. -/
def rationalRelativeIdeleClassToDirectLimit
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    RelativeIdeleGroup.ClassGroup ℚ E →*
      rationalIdeleClassDirectLimit where
  toFun c := ⟦⟨E, c⟩⟧
  map_one' := by
    exact
      (DirectLimit.one_def
        (G := fun E :
          FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
            RelativeIdeleGroup.ClassGroup ℚ E)
        (f := fun _ _ h =>
          rationalRelativeIdeleClassTransition h)
        E).symm
  map_mul' c d := by
    exact
      (DirectLimit.mul_def
        (G := fun E :
          FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
            RelativeIdeleGroup.ClassGroup ℚ E)
        (f := fun _ _ h =>
          rationalRelativeIdeleClassTransition h)
        E c d).symm

/-- The rational absolute Galois action on the idele-class direct limit,
supplied by Mathlib from the equivariant transition maps. -/
noncomputable instance
    rationalIdeleClassDirectLimitMulDistribMulAction :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      rationalIdeleClassDirectLimit :=
  DirectLimit.instMulDistribMulActionOfMulActionHomClass
    (R := SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (G := fun E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
      RelativeIdeleGroup.ClassGroup ℚ E)
    (f := fun _ _ h => rationalRelativeIdeleClassTransition h)

/-- The scalar action underlying the canonical absolute Galois action on
the rational idele-class direct limit. -/
noncomputable instance rationalIdeleClassDirectLimitSMul :
    SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      rationalIdeleClassDirectLimit :=
  rationalIdeleClassDirectLimitMulDistribMulAction.toSMul

/-- The coefficient representation of the global class formation:
the rational absolute Galois group acts on the direct limit of the
actual finite-level idele class groups. -/
noncomputable def rationalIdeleClassRepresentation :
    Rep ℤ (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  Rep.ofMulDistribMulAction
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    rationalIdeleClassDirectLimit

end Reciprocity
end GlobalClassFieldTheory
