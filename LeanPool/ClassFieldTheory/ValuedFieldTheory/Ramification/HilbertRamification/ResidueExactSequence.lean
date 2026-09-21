/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.ClosedSubgroups
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.ProfiniteInvariant

/-! # Residue Exact Sequence -/
namespace RamificationTheory

/-!
# The residue-action exact sequence

For a (possibly infinite) Galois extension and a chosen extension valuation,
the residue extension over the decomposition field is normal and reduction
gives the exact sequence

`1 → I_w → G_w → Gal(λ/κ) → 1`.

The base residue field is presented intrinsically as the quotient of the
fixed subring of the chosen valuation ring by the contraction of its maximal
ideal.  This fixed subring is exactly the valuation ring on the decomposition
field.  The profinite surjectivity proof is the compact inverse-limit argument
used in this construction, supplied by `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- The valuation ring on the decomposition field, represented inside the
chosen valuation ring as the fixed subring of the decomposition group. -/
abbrev decompositionFixedSubring (A : _root_.ValuationSubring L) : Subring A :=
  FixedPoints.subring A (decompositionGroup K A)

/-- The maximal ideal of the decomposition-field valuation ring. -/
abbrev decompositionFixedMaximalIdeal (A : _root_.ValuationSubring L) :
    Ideal (decompositionFixedSubring K A) :=
  (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype

/-- The actual base residue field `κ` in the residue-action exact sequence. -/
abbrev decompositionResidueField (A : _root_.ValuationSubring L) :=
  decompositionFixedSubring K A ⧸ decompositionFixedMaximalIdeal K A

/-- The actual target residue field `λ`. -/
abbrev selectedResidueField (A : _root_.ValuationSubring L) :=
  IsLocalRing.ResidueField A

/-- The literal valuation ring on the classical decomposition field `Z_w`. -/
abbrev decompositionFieldValuationSubring
    (A : _root_.ValuationSubring L) :
    _root_.ValuationSubring (decompositionField K A) :=
  A.comap (decompositionField K A).val

/-- The fixed-subring presentation used in the residue-action exact sequence is canonically
the literal valuation ring on `Z_w`. -/
def decompositionFieldValuationSubringEquivFixedSubring
    (A : _root_.ValuationSubring L) :
    decompositionFieldValuationSubring K A ≃+*
      decompositionFixedSubring K A where
  toFun z :=
    ⟨⟨((z : decompositionField K A) : L), z.property⟩, by
      intro sigma
      apply Subtype.ext
      change ((sigma : decompositionGroup K A) : L ≃ₐ[K] L)
          ((z : decompositionField K A) : L) =
        ((z : decompositionField K A) : L)
      exact (IntermediateField.mem_fixedField_iff
        (H := decompositionGroup K A) ((z : decompositionField K A) : L)).mp
          (z : decompositionField K A).property
          (sigma : L ≃ₐ[K] L) sigma.property⟩
  invFun r := by
    let z : decompositionField K A :=
      ⟨((r : A) : L), by
        rw [IntermediateField.mem_fixedField_iff]
        intro sigma hsigma
        have hr := r.property ⟨sigma, hsigma⟩
        exact congrArg Subtype.val hr⟩
    exact ⟨z, r.val.property⟩
  left_inv z := by ext; rfl
  right_inv r := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- Provides the instance `instIsLocalRing`. -/
instance decompositionFixedSubring.instIsLocalRing
    (A : _root_.ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  (decompositionFieldValuationSubringEquivFixedSubring (K := K) A).isLocalRing

private theorem decompositionGroup_action_locallyConstant
    (A : _root_.ValuationSubring L) (a : A) :
    IsLocallyConstant (fun g : decompositionGroup K A ↦ g • a) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let E : IntermediateField K L := IntermediateField.adjoin K {(a : L)}
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (a : L))
  let U : Set (decompositionGroup K A) :=
    ((↑) : decompositionGroup K A → (L ≃ₐ[K] L)) ⁻¹'
      (((sigma : L ≃ₐ[K] L)) • (E.fixingSubgroup : Set (L ≃ₐ[K] L)))
  refine ⟨U, E.fixingSubgroup_isOpen.smul
      (sigma : L ≃ₐ[K] L) |>.preimage continuous_subtype_val, ?_, ?_⟩
  · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩
  · intro tau htau
    rcases htau with ⟨g, hg, heq⟩
    have hga : g (a : L) = (a : L) :=
      (IntermediateField.mem_fixingSubgroup_iff E g).mp hg (a : L)
        (IntermediateField.subset_adjoin (F := K) (S := {(a : L)}) (by simp))
    apply Subtype.ext
    change (((tau : decompositionGroup K A) : L ≃ₐ[K] L) (a : L)) =
      (((sigma : decompositionGroup K A) : L ≃ₐ[K] L) (a : L))
    rw [← heq]
    simp [AlgEquiv.mul_apply, hga]

private theorem decompositionGroup_continuousSMul
    (A : _root_.ValuationSubring L) :
    letI : TopologicalSpace A := ⊥
    ContinuousSMul (decompositionGroup K A) A := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  constructor
  rw [continuous_prod_of_discrete_right]
  intro a
  exact (decompositionGroup_action_locallyConstant (K := K) A a).continuous

private theorem decompositionGroup_compactSpace
    (A : _root_.ValuationSubring L) :
    CompactSpace (decompositionGroup K A) := by
  have hc : IsCompact (decompositionGroup K A : Set (L ≃ₐ[K] L)) :=
    (decompositionGroup_isClosed K A).isCompact
  exact isCompact_iff_compactSpace.mp hc

omit [IsGalois K L] in
private theorem decompositionFixedSubring_smulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A := by
  constructor
  intro g r x
  change g • ((r : A) * x) = (r : A) * (g • x)
  rw [smul_mul', r.property g]

omit [IsGalois K L] in
private theorem decompositionFixedSubring_isInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) := by
  constructor
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Provides the instance `instSMulCommClass`. -/
instance decompositionFixedSubring.instSMulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
  decompositionFixedSubring_smulCommClass (K := K) A

/-- Provides the instance `instIsInvariant`. -/
instance decompositionFixedSubring.instIsInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
  decompositionFixedSubring_isInvariant (K := K) A

private theorem decompositionFixedMaximalIdeal_isMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  let : Algebra.IsIntegral (decompositionFixedSubring K A) A :=
    Algebra.IsInvariant.isIntegral_of_profinite
      (G := decompositionGroup K A)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (decompositionFixedSubring K A).subtype
    (fun x => Algebra.IsIntegral.isIntegral x)
    (IsLocalRing.maximalIdeal A)

/-- Provides the instance `instIsMaximal`. -/
instance decompositionFixedMaximalIdeal.instIsMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  decompositionFixedMaximalIdeal_isMaximal (K := K) A

/-- The contracted ideal used in the intrinsic presentation is the actual
maximal ideal of the valuation ring on `Z_w`. -/
theorem decompositionFixedMaximalIdeal_eq_maximalIdeal
    (A : _root_.ValuationSubring L) :
    decompositionFixedMaximalIdeal K A =
      IsLocalRing.maximalIdeal (decompositionFixedSubring K A) :=
  IsLocalRing.eq_maximalIdeal
    (decompositionFixedMaximalIdeal.instIsMaximal (K := K) A)

/-- Canonical identification of the literal residue field of `Z_w` with the
base residue field used by the residue-action exact sequence. -/
def decompositionFieldResidueEquiv
    (A : _root_.ValuationSubring L) :
    IsLocalRing.ResidueField (decompositionFieldValuationSubring K A) ≃+*
      decompositionResidueField K A :=
  (IsLocalRing.ResidueField.mapEquiv
      (decompositionFieldValuationSubringEquivFixedSubring (K := K) A)).trans
    (Ideal.quotientEquivAlgOfEq ℤ
      (decompositionFixedMaximalIdeal_eq_maximalIdeal (K := K) A).symm).toRingEquiv

/-- Provides the instance `instLiesOver`. -/
instance selectedMaximalIdeal.instLiesOver
    (A : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A) := by
  constructor
  rfl

/-- Provides the instance `instField`. -/
noncomputable instance decompositionResidueField.instField
    (A : _root_.ValuationSubring L) :
    Field (decompositionResidueField K A) :=
  Ideal.Quotient.field (decompositionFixedMaximalIdeal K A)

/-- Provides the instance `instAlgebra`. -/
noncomputable instance selectedResidueField.instAlgebra
    (A : _root_.ValuationSubring L) :
    Algebra (decompositionResidueField K A) (selectedResidueField A) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (le_of_eq ((IsLocalRing.maximalIdeal A).over_def
      (decompositionFixedMaximalIdeal K A)))

omit [IsGalois K L] in
/-- Every decomposition-group automorphism stabilizes the maximal ideal of
the selected valuation ring. -/
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top
    (A : _root_.ValuationSubring L) :
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma⁻¹)
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma)

/-- The canonical identification of the decomposition group with the
stabilizer of the selected maximal ideal. -/
def decompositionGroupToMaximalIdealStabilizer
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) where
  toFun sigma := ⟨sigma, by
    rw [decompositionGroup_maximalIdeal_stabilizer_eq_top (K := K) A]
    exact Subgroup.mem_top sigma⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The residue-action exact sequence: the residue action of `G_w` on `λ/κ`. -/
def decompositionGroupResidueAction
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (Ideal.Quotient.stabilizerHom
      (IsLocalRing.maximalIdeal A)
      (decompositionFixedMaximalIdeal K A)
      (decompositionGroup K A)).comp
    (decompositionGroupToMaximalIdealStabilizer (K := K) A)

omit [IsGalois K L] in
/-- States the theorem `decompositionGroupResidueAction_residue`. -/
@[simp] theorem decompositionGroupResidueAction_residue
    (A : _root_.ValuationSubring L)
    (sigma : decompositionGroup K A) (x : A) :
    decompositionGroupResidueAction (K := K) A sigma
        (IsLocalRing.residue A x) =
      IsLocalRing.residue A (sigma • x) :=
  rfl

/-- The canonical embedding of the literal residue field of `Z_w` into the
selected residue field `λ`; it is the usual residue map, expressed through
the canonical fixed-subring comparison. -/
def decompositionFieldResidueMapToSelected
    (A : _root_.ValuationSubring L) :
    IsLocalRing.ResidueField (decompositionFieldValuationSubring K A) →+*
      selectedResidueField A :=
  (algebraMap (decompositionResidueField K A)
      (selectedResidueField A)).comp
    (decompositionFieldResidueEquiv (K := K) A).toRingHom

/-- The residue action in the exact sequence fixes the actual residue field of the
decomposition field.  This is the action-compatibility part of the bridge
from the intrinsic quotient presentation to the classical `λ/κ`. -/
theorem decompositionGroupResidueAction_commutes_decompositionFieldResidue
    (A : _root_.ValuationSubring L)
    (sigma : decompositionGroup K A)
    (x : IsLocalRing.ResidueField
      (decompositionFieldValuationSubring K A)) :
    decompositionGroupResidueAction (K := K) A sigma
        (decompositionFieldResidueMapToSelected (K := K) A x) =
      decompositionFieldResidueMapToSelected (K := K) A x := by
  exact (decompositionGroupResidueAction (K := K) A sigma).commutes
    (decompositionFieldResidueEquiv (K := K) A x)

omit [IsGalois K L] in
/-- The residue-action homomorphism has the ordinary inertia group as kernel. -/
theorem decompositionGroupResidueAction_ker
    (A : _root_.ValuationSubring L) :
    MonoidHom.ker (decompositionGroupResidueAction (K := K) A) =
      inertiaGroup K A := by
  ext sigma
  rw [MonoidHom.mem_ker, ← residueAction_ker (K := K) A,
    MonoidHom.mem_ker]
  constructor
  · intro hsigma
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have h := DFunLike.congr_fun hsigma (IsLocalRing.residue A x)
    exact h
  · intro hsigma
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have h := DFunLike.congr_fun hsigma (IsLocalRing.residue A x)
    exact h

/-- The residue-action exact sequence, including the infinite case: reduction is onto the full
residue Galois group. -/
theorem decompositionGroupResidueAction_surjective
    (A : _root_.ValuationSubring L) :
    Function.Surjective (decompositionGroupResidueAction (K := K) A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  intro sigma
  obtain ⟨tau, htau⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := decompositionGroup K A)
      (decompositionFixedMaximalIdeal K A)
      (IsLocalRing.maximalIdeal A) sigma
  refine ⟨tau.1, ?_⟩
  have htau_eq :
      decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1 = tau := by
    apply Subtype.ext
    rfl
  change
    Ideal.Quotient.stabilizerHom
        (IsLocalRing.maximalIdeal A)
        (decompositionFixedMaximalIdeal K A)
        (decompositionGroup K A)
        (decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1) =
      sigma
  rw [htau_eq]
  exact htau

/-- The residue-action exact sequence: `λ/κ` is normal, also in the infinite case. -/
instance decompositionResidueExtension_normal
    (A : _root_.ValuationSubring L) :
    Normal (decompositionResidueField K A) (selectedResidueField A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  exact RamificationTheory.Ideal.Quotient.normal_of_profinite
    (G := decompositionGroup K A)
    (decompositionFixedMaximalIdeal K A)
    (IsLocalRing.maximalIdeal A)

omit [IsGalois K L] in
/-- Exactness at `G_w` in the residue-action exact sequence. -/
theorem inertiaGroup_mulExact_decompositionGroupResidueAction
    (A : _root_.ValuationSubring L) :
    Function.MulExact (inertiaGroup K A).subtype
      (decompositionGroupResidueAction (K := K) A) := by
  rw [MonoidHom.mulExact_iff, decompositionGroupResidueAction_ker]
  exact (Subgroup.range_subtype _).symm

/-- The residue-action exact sequence, arbitrary Galois form:
`1 → I_w → G_w → Gal(λ/κ) → 1`. -/
theorem decompositionGroupResidueAction_shortExact
    (A : _root_.ValuationSubring L) :
    Function.Injective (inertiaGroup K A).subtype ∧
      Function.MulExact (inertiaGroup K A).subtype
        (decompositionGroupResidueAction (K := K) A) ∧
      Function.Surjective (decompositionGroupResidueAction (K := K) A) := by
  exact ⟨Subtype.coe_injective,
    inertiaGroup_mulExact_decompositionGroupResidueAction (K := K) A,
    decompositionGroupResidueAction_surjective (K := K) A⟩

/-- Quotient form of the residue-action exact sequence. -/
def decompositionQuotientEquivResidueGalois
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (QuotientGroup.quotientMulEquivOfEq
      (decompositionGroupResidueAction_ker (K := K) A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (decompositionGroupResidueAction (K := K) A)
      (decompositionGroupResidueAction_surjective (K := K) A))

/-- States the theorem `decompositionQuotientEquivResidueGalois_mk`. -/
@[simp] theorem decompositionQuotientEquivResidueGalois_mk
    (A : _root_.ValuationSubring L) (sigma : decompositionGroup K A) :
    decompositionQuotientEquivResidueGalois (K := K) A
        (QuotientGroup.mk' (inertiaGroup K A) sigma) =
      decompositionGroupResidueAction (K := K) A sigma := by
  exact QuotientGroup.kerLift_mk (decompositionGroupResidueAction (K := K) A) sigma

end ValuationSubring
end HilbertRamification

end

end RamificationTheory
