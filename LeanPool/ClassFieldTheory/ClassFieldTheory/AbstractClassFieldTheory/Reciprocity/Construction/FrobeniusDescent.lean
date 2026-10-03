/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField

/-! # Frobenius Descent -/

@[expose] public section
namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: descent from the Frobenius semigroup

The two maps on `G(\widetilde L/K)`--restriction to `G(L/K)` and normalized
degree--are jointly injective.  This is the group-theoretic fact used when two Frobenius lifts
have the same
restriction and degree.
-/

noncomputable
section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `G_L` in `G_K / I_L`. -/
def extensionImageInInertiaQuotient (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Subgroup (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  (extensionSubgroup K L hLK).map
    (QuotientGroup.mk' (D.extensionInertiaWithin K L hLK))

/-- The image of `G_L` in `G_K / I_L` is closed.  This is the compact-image
step implicit in the Galois correspondence used. -/
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let E := extensionSubgroup K.field L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)

/-- A finite field fixed by both the relative inertia and one representative
of a Frobenius lift is contained in the lift's Frobenius fixed field.  This
is the closed-subgroup minimality argument used in finiteness of the Frobenius fixed field. -/
theorem frobeniusFixedField_le_of_inertia_le_of_lift_mem
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L M : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    (hMK : M.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK)]
    (σ : D.FrobeniusElements K L hLK)
    (hI : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field M hMK)
    (s : K.field.toSubgroup)
    (hsM : s ∈ extensionSubgroup K.field M hMK)
    (hsσ : (QuotientGroup.mk s :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = σ.1) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      M.toSubgroup := by
  let H := D.extensionInertiaWithin K.field L hLK
  let E := extensionSubgroup K.field M hMK
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := E.map (QuotientGroup.mk' H)
  let : IsClosed (H : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (M : Set G)) := by
      rfl
    rw [hcarrier]
    exact M.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hMfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  have hJclosed : IsClosed (J : Set Q) := by
    change IsClosed ((QuotientGroup.mk' H) '' (E : Set K.field.toSubgroup))
    exact J.isClosed_of_isOpen
      (QuotientGroup.isOpenMap_coe (N := H)
        (E : Set K.field.toSubgroup) hEopen)
  have hσJ : σ.1 ∈ J := ⟨s, hsM, hsσ⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure
      (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact hJclosed
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hI hdiff
  have hkE : k ∈ E := by
    have hmul := E.mul_mem heE hdiffE
    simpa [mul_assoc] using hmul
  change (k : G) ∈ M
  exact hkE

/-- If a Frobenius lift restricts trivially to `L`, its fixed field contains
`L` (equivalently `G_Σ ≤ G_L`). -/
theorem frobeniusFixedField_le_of_restriction_eq_one
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      L.toSubgroup := by
  let H := D.extensionInertiaWithin K.field L hLK
  let E := extensionSubgroup K.field L hLK
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := D.extensionImageInInertiaQuotient K.field L hLK
  have hσJ : σ.1 ∈ J := by
    let k : K.field.toSubgroup := Quotient.out σ.1
    have hkq : QuotientGroup.mk k = σ.1 := Quotient.out_eq' σ.1
    have hkE : k ∈ E := by
      have hq : (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) = 1 := by
        change D.extensionRestriction K.field L hLK
          (QuotientGroup.mk k : K.field.toSubgroup ⧸ H) = 1
        rw [hkq]
        exact hσ
      simpa using QuotientGroup.eq.mp hq.symm
    exact ⟨k, hkE, hkq⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact D.extensionImageInInertiaQuotient_isClosed K L hLK
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hdiff.1
  have hkE : k ∈ E := by
    have := E.mul_mem heE hdiffE
    simpa [mul_assoc] using this
  change (k : G) ∈ L
  exact hkE

/-- Restriction and normalized degree jointly distinguish elements of
`G(\widetilde L/K)`. -/
theorem extensionRestriction_normalizedDegree_joint_injective
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q)) := by
  intro q r hqr
  refine Quotient.inductionOn₂' q r ?_ hqr
  intro a b hab
  apply QuotientGroup.eq.mpr
  have hRestriction : QuotientGroup.mk a =
      (QuotientGroup.mk b :
        K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) := by
    exact congrArg Prod.fst hab
  have hExtension : a⁻¹ * b ∈ extensionSubgroup K.field L hLK :=
    QuotientGroup.eq.mp hRestriction
  have hDegree : D.normalizedDegree K a =
      D.normalizedDegree K b :=
    congrArg Prod.snd hab
  refine ⟨hExtension, ?_⟩
  rw [← D.normalizedDegree_ker K]
  change D.normalizedDegree K (a⁻¹ * b) = 1
  rw [map_mul, map_inv, hDegree, inv_mul_cancel]

/--
`frobeniusRestriction` satisfies the multiplication formula `D.frobeniusRestriction K L hLK (σ *
τ) = D.frobeniusRestriction K L hLK σ * D.frobeniusRestriction K L hLK τ`.
-/
@[simp]
theorem frobeniusRestriction_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.frobeniusRestriction K L hLK (σ * τ) =
      D.frobeniusRestriction K L hLK σ *
        D.frobeniusRestriction K L hLK τ := by
  change D.extensionRestriction K.field L hLK (σ.1 * τ.1) =
    D.extensionRestriction K.field L hLK σ.1 *
      D.extensionRestriction K.field L hLK τ.1
  exact map_mul _ _ _

/-- Frobenius elements with equal restriction and equal normalized degree
are equal. -/
theorem frobenius_eq_of_restriction_eq_of_degree_eq
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) :
    σ = τ := by
  apply Subtype.ext
  apply D.extensionRestriction_normalizedDegree_joint_injective
    K L hLK
  exact Prod.ext hRestriction hDegree

end DegreeData

end
end ClassFormation
