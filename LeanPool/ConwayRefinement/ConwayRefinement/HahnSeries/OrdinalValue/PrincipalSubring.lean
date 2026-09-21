/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# The subring $\widehat{\mathrm P}$ of principal elements

This module defines $\widehat{\mathrm P}$ intrinsically as the external direct sum

`P̂ = ⨁ α, P_α`,

where `P_α = J_{ω^(α+1)} / J_{ω^α}`. Its multiplication is induced by the homogeneous maps
`P_α × P_β → P_(α + β)`, where addition of `NatOrdinal` is Hessenberg addition. No basis,
complement, or chosen representatives enter this definition, and `P̂` is a graded commutative
`K`-algebra over every coefficient field: it is the associated graded ring of the max-additive
degree `ordinalValueDegreeValuation`, which rests on Berarducci, Lemma 5.5 alone.

LM24, Definition 6.1.1 instead presents `P̂` as the subring of the degree-graded ring `RV̂`
whose homogeneous components are zero or principal. Both rings are associated graded rings of
`K((ℝ^{≤0}))`, for the degree and ordinal-value filtrations; since
`ordinalValueDegree b ≤ degree b`, the identity of `K((ℝ^{≤0}))` induces the canonical graded
algebra map `rvProjection : RV̂ → P̂`, the generic map of associated graded rings of
a coarsening, again over every field. The map `principalSubringEmbedding` in the other direction
chooses principal representatives of exact degree; it is a section of the projection, and its
range is exactly the componentwise-principal subalgebra. This explicit round trip identifies the
intrinsic direct sum with the paper's subring, and the projection is the left inverse that makes
the embedding injective.

The embedding is where characteristic zero enters: it is multiplicative because the product of
two principal series is principal (LM24, Proposition 3.6.1, from Berarducci, Theorem 9.7) and
because degree is multiplicative (LM24, Theorem D). Both graded rings carry their
coefficient-field algebra structures componentwise; the embedding is an algebra homomorphism and
commutes with every homogeneous projection.
-/

universe v

public noncomputable section

namespace Berarducci

open scoped DirectSum HahnSeries NatOrdinal

variable {K : Type v} [Field K]

variable (K) in
/-- The intrinsic direct sum `P̂ = ⨁ α, P_α`. -/
abbrev PrincipalSubring :=
  (ordinalValueDegreeValuation K).AssociatedGraded

variable (K) in
/-- The associated graded ring of Hahn-series degree. This is the paper's `RV̂` in the
real-exponent setting. -/
abbrev DegreeGraded :=
  (HahnSeries.Nonpositive.degreeValuation K).AssociatedGraded

/-- The coefficient-field algebra structure on `P̂`. -/
instance principalSubringGAlgebra :
    DirectSum.GAlgebra K (PrincipalComponent K) where
  toFun := (principalComponentScalarHom K).toAddMonoidHom
  map_one := map_one (principalComponentScalarHom K)
  map_mul r s := by
    change GradedMonoid.mk 0 (principalComponentScalarHom K (r * s)) = _
    rw [(principalComponentScalarHom K).map_mul]
    exact GradedMonoid.mk_zero_smul _ _
  commutes _ x := DirectSum.GCommSemiring.mul_comm _ x
  smul_def r x :=
    GradedMonoid.mk_zero_smul (principalComponentScalarHom K r) x.2

/-- The coefficient-field algebra structure on the degree-graded ring `RV̂`. -/
instance degreeGradedGAlgebra :
    DirectSum.GAlgebra K
      (HahnSeries.Nonpositive.degreeValuation K).Component where
  toFun := (degreeLayerScalarHom K).toAddMonoidHom
  map_one := map_one (degreeLayerScalarHom K)
  map_mul r s := by
    change GradedMonoid.mk 0 (degreeLayerScalarHom K (r * s)) = _
    rw [(degreeLayerScalarHom K).map_mul]
    exact GradedMonoid.mk_zero_smul _ _
  commutes _ x := DirectSum.GCommSemiring.mul_comm _ x
  smul_def r x := GradedMonoid.mk_zero_smul (degreeLayerScalarHom K r) x.2

/-- The coefficient-field algebra structure on `P̂`. Recovering it re-traverses
`DirectSum.GAlgebra` and the componentwise multiplication, and the `Module` and `SMul` structures
used throughout are projections of it. -/
instance principalSubringAlgebra :
    Algebra K (PrincipalSubring K) :=
  inferInstance

/-- The commutative ring structure on `P̂`, named for the reason given at
`principalSubringAlgebra`. -/
instance principalSubringCommRing :
    CommRing (PrincipalSubring K) :=
  inferInstance

/-- The semiring structure on `P̂`. `Algebra K P̂` takes a `Semiring P̂` argument, so every
occurrence of the algebra structure resolves this too. The levels below are named for the same
reason. -/
instance principalSubringSemiring :
    Semiring (PrincipalSubring K) :=
  inferInstance

instance principalSubring :
    Ring (PrincipalSubring K) :=
  inferInstance

instance principalSubringCommSemiring :
    CommSemiring (PrincipalSubring K) :=
  inferInstance

instance principalSubringAddCommGroup :
    AddCommGroup (PrincipalSubring K) :=
  inferInstance

/-- The coefficient-field algebra structure on `RV̂`, named for the reason given at
`principalSubringAlgebra`. -/
instance degreeGradedAlgebra :
    Algebra K (DegreeGraded K) :=
  inferInstance

/-- The commutative ring structure on `RV̂`, named for the reason given at
`principalSubringAlgebra`. -/
instance degreeGradedCommRing :
    CommRing (DegreeGraded K) :=
  inferInstance

/-- The semiring structure on `RV̂`, named for the reason given at `principalSubringSemiring`. -/
instance degreeGradedSemiring :
    Semiring (DegreeGraded K) :=
  inferInstance

instance degreeGradedRing :
    Ring (DegreeGraded K) :=
  inferInstance

instance degreeGradedAddCommGroup :
    AddCommGroup (DegreeGraded K) :=
  inferInstance

/-- The coefficient-field algebra map lands in the intrinsic degree-zero component. -/
@[simp]
theorem principalSubring_algebraMap_apply (k : K) :
    algebraMap K (PrincipalSubring K) k =
      DirectSum.of (PrincipalComponent K) 0 (principalComponentScalarHom K k) :=
  DirectSum.algebraMap_apply K (PrincipalComponent K) k

/-- The ring `P̂` is nontrivial because its degree-zero component contains the
coefficient field. -/
instance principalSubringNontrivial :
    Nontrivial (PrincipalSubring K) :=
  (DirectSum.of_injective (β := PrincipalComponent K) 0).nontrivial

variable (K) in
/-- The coefficient-field embedding into `P̂` is injective. -/
theorem principalSubring_algebraMap_injective :
    Function.Injective (algebraMap K (PrincipalSubring K)) := by
  intro k l hkl
  apply principalComponentScalarHom_injective K
  apply DirectSum.of_injective (β := PrincipalComponent K) 0
  simpa only [principalSubring_algebraMap_apply] using hkl

/-- Scalar multiplication by the coefficient field on `P̂` is
faithful. -/
instance principalSubringFaithfulSMul :
    FaithfulSMul K (PrincipalSubring K) :=
  (faithfulSMul_iff_algebraMap_injective K _).mpr
    (principalSubring_algebraMap_injective K)

/-- The coefficient-field algebra map for `RV̂` lands in degree zero. -/
@[simp]
theorem degreeGraded_algebraMap_apply (k : K) :
    algebraMap K (DegreeGraded K) k =
      DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component
        0 (degreeLayerScalarHom K k) :=
  DirectSum.algebraMap_apply K
    (HahnSeries.Nonpositive.degreeValuation K).Component k

variable (K) in
/-- The inclusion of `P_α` into the degree-`α` component of `RV̂`. -/
def principalComponentToHahnDegreeLayer (α : NatOrdinal) :
    PrincipalComponent K α →ₗ[K]
      (HahnSeries.Nonpositive.degreeValuation K).Component α :=
  (principalDegreeClasses K α).subtype.comp
    (principalDegreeClassesEquivPrincipalComponent K α).symm.toLinearMap

@[simp]
theorem degreeLayerToPrincipalComponent_principalComponentToHahnDegreeLayer
    (α : NatOrdinal) (x : PrincipalComponent K α) :
    degreeLayerToPrincipalComponent K α
        (principalComponentToHahnDegreeLayer K α x) = x := by
  let e := principalDegreeClassesEquivPrincipalComponent K α
  have hcoe : principalComponentToHahnDegreeLayer K α x =
      ((e.symm x : principalDegreeClasses K α) :
        (HahnSeries.Nonpositive.degreeValuation K).Component α) :=
    rfl
  rw [hcoe, ← principalDegreeClassesEquivPrincipalComponent_apply]
  exact e.apply_symm_apply x

variable (K) in
/-- The inclusion of `P_α` into the degree-`α` component of `RV̂` is injective. -/
theorem principalComponentToHahnDegreeLayer_injective (α : NatOrdinal) :
    Function.Injective (principalComponentToHahnDegreeLayer K α) := by
  intro x y hxy
  apply (degreeLayerToPrincipalComponent_principalComponentToHahnDegreeLayer α x).symm.trans
  rw [hxy]
  exact degreeLayerToPrincipalComponent_principalComponentToHahnDegreeLayer α y

variable (K) in
/-- The inclusion of `P_0` sends its identity to the identity of `RV̂`. -/
theorem principalComponentToHahnDegreeLayer_componentOne :
    principalComponentToHahnDegreeLayer K 0
        (ordinalValueDegreeValuation K).componentOne =
      (HahnSeries.Nonpositive.degreeValuation K).componentOne := by
  let wOrder := ordinalValueDegreeValuation K
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  let e := principalDegreeClassesEquivPrincipalComponent K 0
  have honeDegree : (((1 : Series K) : K⟦ℝ⟧)).degree =
      (0 : WithBot NatOrdinal) := by
    rw [← map_one (HahnSeries.Nonpositive.C : K →+* Series K)]
    exact degree_C_eq_zero_of_ne one_ne_zero
  have honeClass : wDegree.componentOne ∈ principalDegreeClasses K 0 := by
    rw [mem_principalDegreeClasses_iff, isPrincipalDegreeClass_iff]
    refine Or.inr ⟨1, HahnSeries.Nonpositive.isPrincipal_one, honeDegree, ?_⟩
    rw [wDegree.componentOne_eq_componentMk, degreeLayerMk_eq_componentMk]
  change ((e.symm wOrder.componentOne : principalDegreeClasses K 0) :
      wDegree.Component 0) = wDegree.componentOne
  have heq : e.symm wOrder.componentOne = ⟨wDegree.componentOne, honeClass⟩ := by
    apply e.injective
    rw [e.apply_symm_apply,
      principalDegreeClassesEquivPrincipalComponent_apply,
      degreeLayerToPrincipalComponent_eq_componentMap]
    exact (MaxAddDegree.componentMap_componentOne _ _ _ _).symm
  exact congrArg Subtype.val heq

variable (K) in
/-- The canonical component map sends the degree-zero scalar of `k` to its class in
`P_0`. -/
theorem degreeLayerToPrincipalComponent_degreeLayerScalarHom (k : K) :
    degreeLayerToPrincipalComponent K 0 (degreeLayerScalarHom K k) =
      principalComponentScalarHom K k := by
  rw [degreeLayerScalarHom_apply, degreeLayerToPrincipalComponent_mk,
    principalComponentScalarHom_apply]

variable (K) in
/-- The canonical graded algebra map from `RV̂` to `P̂`: the map of associated graded rings
induced by the identity of `K((ℝ^{≤0}))`, which carries the degree
filtration into the coarser ordinal-value filtration because `ordinalValueDegree b ≤ degree b`. -/
def rvProjection :
    DegreeGraded K →ₐ[K] PrincipalSubring K where
  toRingHom :=
    (HahnSeries.Nonpositive.degreeValuation K).associatedGradedMap
      (ordinalValueDegreeValuation K) (RingHom.id (Series K))
      (ordinalValueDegreeValuation_le_degreeValuation K)
  commutes' k := by
    change (HahnSeries.Nonpositive.degreeValuation K).associatedGradedMap
      (ordinalValueDegreeValuation K) (RingHom.id (Series K))
      (ordinalValueDegreeValuation_le_degreeValuation K)
      (algebraMap K (DegreeGraded K) k) = algebraMap K (PrincipalSubring K) k
    rw [degreeGraded_algebraMap_apply, principalSubring_algebraMap_apply,
      MaxAddDegree.associatedGradedMap_of, ← degreeLayerToPrincipalComponent_eq_componentMap,
      degreeLayerToPrincipalComponent_degreeLayerScalarHom K k]

/-- The graded projection sends a homogeneous vector to the same grade. -/
@[simp]
theorem rvProjection_of (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α) :
    rvProjection K (DirectSum.of _ α x) =
      DirectSum.of _ α (degreeLayerToPrincipalComponent K α x) := by
  rw [degreeLayerToPrincipalComponent_eq_componentMap]
  exact MaxAddDegree.associatedGradedMap_of _ _ _ _ α x

/-- The graded projection commutes with every homogeneous projection. -/
@[simp]
theorem rvProjection_apply (x : DegreeGraded K) (α : NatOrdinal) :
    rvProjection K x α =
      degreeLayerToPrincipalComponent K α (x α) := by
  rw [degreeLayerToPrincipalComponent_eq_componentMap]
  exact MaxAddDegree.associatedGradedMap_apply _ _ _ _ x α

/-- Every vector in the image of a fixed intrinsic component is a principal degree class. -/
theorem principalComponentToHahnDegreeLayer_isPrincipal
    (α : NatOrdinal) (x : PrincipalComponent K α) :
    IsPrincipalDegreeClass α
      (principalComponentToHahnDegreeLayer K α x) := by
  apply (mem_principalDegreeClasses_iff α _).mp
  exact (principalDegreeClassesEquivPrincipalComponent K α).symm x |>.2

/-- On a principal class of `RV̂`, projection followed by inclusion is the identity. -/
theorem principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
    (α : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component α)
    (hx : IsPrincipalDegreeClass α x) :
    principalComponentToHahnDegreeLayer K α
        (degreeLayerToPrincipalComponent K α x) = x := by
  let e := principalDegreeClassesEquivPrincipalComponent K α
  let x' : principalDegreeClasses K α :=
    ⟨x, (mem_principalDegreeClasses_iff α x).mpr hx⟩
  change ((e.symm (degreeLayerToPrincipalComponent K α x) :
      principalDegreeClasses K α) :
        (HahnSeries.Nonpositive.degreeValuation K).Component α) = x
  have hex : e x' = degreeLayerToPrincipalComponent K α x :=
    principalDegreeClassesEquivPrincipalComponent_apply α x'
  rw [← hex, e.symm_apply_apply]

/-- The componentwise predicate in LM24, Definition 6.1.1: every homogeneous component is zero
or principal. -/
def IsPrincipalGraded (x : DegreeGraded K) : Prop :=
  ∀ α, IsPrincipalDegreeClass α (x α)

/-- Characterization of the paper's componentwise principal predicate. -/
theorem isPrincipalGraded_iff (x : DegreeGraded K) :
    IsPrincipalGraded x ↔
      ∀ α, IsPrincipalDegreeClass α (x α) :=
  Iff.rfl

section Embedding

variable [CharZero K]

/-- The inclusion of each homogeneous component commutes with homogeneous multiplication. -/
theorem principalComponentToHahnDegreeLayer_mul
    {α β : NatOrdinal} (x : PrincipalComponent K α) (y : PrincipalComponent K β) :
    principalComponentToHahnDegreeLayer K (α + β)
        (principalComponentMul x y) =
      (HahnSeries.Nonpositive.degreeValuation K).componentMul
        (principalComponentToHahnDegreeLayer K α x)
        (principalComponentToHahnDegreeLayer K β y) := by
  let eα := principalDegreeClassesEquivPrincipalComponent K α
  let eβ := principalDegreeClassesEquivPrincipalComponent K β
  let eαβ := principalDegreeClassesEquivPrincipalComponent K (α + β)
  let x' := eα.symm x
  let y' := eβ.symm y
  have hmul' := principalDegreeClassesEquivPrincipalComponent_mul x' y'
  have hsource : eαβ.symm (principalComponentMul x y) =
      principalDegreeClassesMul x' y' := by
    apply eαβ.injective
    simpa [eα, eβ, eαβ, x', y'] using hmul'.symm
  change ((eαβ.symm (principalComponentMul x y) :
      principalDegreeClasses K (α + β)) :
        (HahnSeries.Nonpositive.degreeValuation K).Component
          (α + β)) = _
  rw [hsource]
  exact coe_principalDegreeClassesMul x' y'

variable (K) in
private def principalComponentToHahnDegreeGradedLinear (α : NatOrdinal) :
    PrincipalComponent K α →ₗ[K] DegreeGraded K :=
  (DirectSum.lof K NatOrdinal
    (HahnSeries.Nonpositive.degreeValuation K).Component α).comp
      (principalComponentToHahnDegreeLayer K α)

variable (K) in
/-- The component-compatible algebra embedding of `P̂` into `RV̂`. -/
def principalSubringEmbedding :
    PrincipalSubring K →ₐ[K] DegreeGraded K :=
  DirectSum.toAlgebra K _
    (principalComponentToHahnDegreeGradedLinear K)
    (by
      let wOrder := ordinalValueDegreeValuation K
      let wDegree := HahnSeries.Nonpositive.degreeValuation K
      change DirectSum.of wDegree.Component 0
          (principalComponentToHahnDegreeLayer K 0 wOrder.componentOne) =
        DirectSum.of wDegree.Component 0 wDegree.componentOne
      rw [principalComponentToHahnDegreeLayer_componentOne K])
    (by
      intro α β x y
      simp only [principalComponentToHahnDegreeGradedLinear, LinearMap.comp_apply,
        DirectSum.lof_eq_of]
      rw [DirectSum.of_mul_of]
      have hmulCompat :=
        principalComponentToHahnDegreeLayer_mul x y
      rw [principalComponentMul_eq_componentMul] at hmulCompat
      exact congrArg
        (DirectSum.of
          (HahnSeries.Nonpositive.degreeValuation K).Component
          (α + β))
        hmulCompat)

/-- The graded embedding sends a homogeneous vector to the same grade. -/
@[simp]
theorem principalSubringEmbedding_of (α : NatOrdinal) (x : PrincipalComponent K α) :
    principalSubringEmbedding K
        (DirectSum.of (PrincipalComponent K) α x) =
      DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation K).Component
        α (principalComponentToHahnDegreeLayer K α x) := by
  simp [principalSubringEmbedding, principalComponentToHahnDegreeGradedLinear,
    DirectSum.toAlgebra, DirectSum.lof_eq_of]

/-- The graded projection is a left inverse of the principal graded embedding. -/
theorem rvProjection_principalGradedEmbedding (x : PrincipalSubring K) :
    rvProjection K
        (principalSubringEmbedding K x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of α x =>
      rw [principalSubringEmbedding_of, rvProjection_of,
        degreeLayerToPrincipalComponent_principalComponentToHahnDegreeLayer]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (K) in
/-- The principal graded embedding is injective. -/
theorem principalSubringEmbedding_injective :
    Function.Injective (principalSubringEmbedding K) :=
  Function.LeftInverse.injective
    rvProjection_principalGradedEmbedding

/-- The principal graded embedding commutes with every homogeneous projection. -/
@[simp]
theorem principalSubringEmbedding_apply (x : PrincipalSubring K) (α : NatOrdinal) :
    principalSubringEmbedding K x α =
      principalComponentToHahnDegreeLayer K α (x α) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of β x =>
      rw [principalSubringEmbedding_of]
      by_cases hβα : β = α
      · subst β
        simp
      · simp [DirectSum.of_apply, hβα]
  | add x y hx hy => simp [map_add, hx, hy]

variable (K) in
/-- The paper's principal graded subalgebra inside `RV̂`. -/
def principalSubringSubalgebra :
    Subalgebra K (DegreeGraded K) :=
  (principalSubringEmbedding K).range

/-- The intrinsic range is exactly the componentwise definition of `P̂` from LM24,
Definition 6.1.1. -/
theorem mem_principalGradedSubalgebra_iff (x : DegreeGraded K) :
    x ∈ principalSubringSubalgebra K ↔
      IsPrincipalGraded x := by
  constructor
  · rintro ⟨y, hy⟩
    change principalSubringEmbedding K y = x at hy
    intro α
    rw [← hy, principalSubringEmbedding_apply]
    exact principalComponentToHahnDegreeLayer_isPrincipal α (y α)
  · intro hx
    refine ⟨rvProjection K x, ?_⟩
    change principalSubringEmbedding K
      (rvProjection K x) = x
    apply DirectSum.ext
    intro α
    rw [principalSubringEmbedding_apply, rvProjection_apply]
    exact
      principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
        α (x α) (hx α)

/-- Every element in the range of the intrinsic principal graded embedding is
componentwise principal. -/
theorem principalSubringEmbedding_isPrincipal (x : PrincipalSubring K) :
    IsPrincipalGraded (principalSubringEmbedding K x) :=
  (mem_principalGradedSubalgebra_iff _).mp ⟨x, rfl⟩

variable (K) in
/-- The intrinsic direct sum `P̂` is canonically algebra-equivalent to the subalgebra of principal
elements of `RV̂`. -/
def principalSubringEquivSubalgebra :
    PrincipalSubring K ≃ₐ[K] principalSubringSubalgebra K :=
  AlgEquiv.ofLeftInverse
    (f := principalSubringEmbedding K)
    (g := rvProjection K)
    rvProjection_principalGradedEmbedding

/-- The forward map of the intrinsic-to-paper equivalence is the graded embedding. -/
@[simp]
theorem principalSubringEquivSubalgebra_apply (x : PrincipalSubring K) :
    ((principalSubringEquivSubalgebra K x :
        principalSubringSubalgebra K) :
      DegreeGraded K) =
      principalSubringEmbedding K x :=
  (rfl)

/-- The inverse map of the intrinsic-to-paper equivalence is the graded projection. -/
@[simp]
theorem principalSubringEquivSubalgebra_symm_apply (x : principalSubringSubalgebra K) :
    (principalSubringEquivSubalgebra K).symm x =
      rvProjection K x :=
  (rfl)

end Embedding

end Berarducci
