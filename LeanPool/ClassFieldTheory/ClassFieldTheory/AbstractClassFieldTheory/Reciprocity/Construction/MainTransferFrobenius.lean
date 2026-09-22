/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry

/-! # Main Transfer Frobenius -/
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory

/-!
# The abstract reciprocity construction, transfer--norm naturality: Frobenius fibers

This module continues the geometric transfer construction with the chosen
norm-orbit representatives, fiber calculations, fixed-field arithmetic, and
the final Frobenius transfer formula.
-/

noncomputable section

open scoped BigOperators

open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace Internal

/-- The chosen representative of a norm orbit is the inverse of the
representative of the corresponding transfer orbit. -/
private noncomputable def chosenTransferNormNaturalityNormOrbitRepresentative
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (qN : Quotient (orbitRel
      (extensionSubgroup E.base.field E.field.field E.below)
      (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
        (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
        (D.frobeniusFixedField_le E.base L
          (hL.trans E.below) σ)))) :
    E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ) :=
  let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
    E L hL σ).symm qN
  QuotientGroup.mk (Quotient.out qT.out.out)⁻¹

private theorem chosenTransferNormNaturalityNormOrbitRepresentative_spec
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Function.LeftInverse Quotient.mk''
      (Internal.chosenTransferNormNaturalityNormOrbitRepresentative
        D E L hL σ) := by
  intro qN
  let orbitEquiv := D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  let qT := orbitEquiv.symm qN
  change Quotient.mk'' (QuotientGroup.mk (Quotient.out qT.out.out)⁻¹) = qN
  rw [← D.transferNormNaturalityTransferNormOrbitEquiv_apply
    E L hL σ qT]
  exact orbitEquiv.apply_symm_apply qN

end Internal

end transferFrobeniusGeometry

section transferOrbitNorms

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace Internal

/-- The relative norm from the Frobenius fixed field is the sum over
the norm double cosets corresponding to the classical transfer orbits.
The representative of the orbit paired with `q` is the inverse of the
transfer representative selected by `Quotient.out`. -/
private theorem transferNormNaturalityNorm_eq_sum_transferOrbitRepresentatives
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    [hLfinite : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field L (hL.trans E.below))]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)) :
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let M := extensionSubgroup E.base.field E.field.field E.below
    let Ω := Quotient (orbitRel M
      (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK))
    let φ : Ω → E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
      Internal.chosenTransferNormNaturalityNormOrbitRepresentative
        D E L hL σ
    letI : Finite (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field S hSK) :=
      D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
    letI : Fintype Ω := Fintype.ofFinite _
    letI (q : Ω) : Fintype (M ⧸ stabilizer M (φ q)) := by
      letI : Finite (orbit M (φ q)) :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI := Fintype.ofFinite (orbit M (φ q))
      exact Fintype.ofEquiv (orbit M (φ q))
        (orbitEquivQuotientStabilizer M (φ q))
    ((relativeNorm A E.base.field S hSK π :
      ambientFixedAddSubgroup A E.base.field) : A.V) =
      ∑ q : Ω, ∑ r : M ⧸ stabilizer M (φ q),
        relativeCosetAction A E.base.field S hSK π (r.out • φ q) := by
  dsimp only
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let M := extensionSubgroup E.base.field E.field.field E.below
  let Ω := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK))
  let φ : Ω → E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
    Internal.chosenTransferNormNaturalityNormOrbitRepresentative
      D E L hL σ
  let : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field S hSK) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  let : Fintype Ω := Fintype.ofFinite _
  let (q : Ω) : Fintype (M ⧸ stabilizer M (φ q)) := by
    letI : Finite (orbit M (φ q)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI := Fintype.ofFinite (orbit M (φ q))
    exact Fintype.ofEquiv (orbit M (φ q))
      (orbitEquivQuotientStabilizer M (φ q))
  rw [relativeNorm_eq_sum_chosenOrbit_of_fintype A E.base.field S hSK M
    (Internal.chosenTransferNormNaturalityNormOrbitRepresentative_spec
      D E L hL σ) π]
  apply Fintype.sum_congr
  intro q
  apply Fintype.sum_congr
  intro r
  rw [chosenOrbitClassEquiv_symm_apply]

end Internal

end transferOrbitNorms

section transferFrobeniusFibers

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Canonical identification of the two realizations of
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusIntermediateEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) ≃*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL :=
  MulEquiv.ofBijective
    (D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl).rangeRestrict
    ⟨fun _ _ h => D.transferNormNaturalityFrobeniusTowerMap_injective
        E L hL (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion E.below k')`.
-/
@[simp]
theorem transferNormNaturalityFrobeniusIntermediateEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (k' : E.field.field.toSubgroup) :
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion E.below k') := rfl

/-- A divisibility fact in `ℤ̂` used to recognize every transfer term as
a positive Frobenius element over `K'`. -/
theorem transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat
    (f N : ℕ) (hf : 0 < f) (hN : 0 < N) (z : ZHat)
    (h : f • z = N • (1 : ZHat)) :
    ∃ n : ℕ, 0 < n ∧ z = n • (1 : ZHat) := by
  have hRange : N • (1 : ZHat) ∈
      (zHatMulNat f).toAddMonoidHom.range := by
    refine ⟨z, ?_⟩
    change f • z = N • (1 : ZHat)
    exact h
  have hKer : N • (1 : ZHat) ∈
      (zHatReduction f hf).toAddMonoidHom.ker := by
    rw [← zHatMulNat_range_eq_ker_reduction f hf]
    exact hRange
  have hmod : (N : ZMod f) = 0 := by
    change zHatReduction f hf (N • (1 : ZHat)) = 0 at hKer
    rw [map_nsmul] at hKer
    have hredOne : zHatReduction f hf (1 : ZHat) = 1 := by
      rfl
    simpa [hredOne] using hKer
  have hdiv : f ∣ N := (ZMod.natCast_eq_zero_iff N f).1 hmod
  let n := N / f
  have hN_eq : N = f * n := (Nat.mul_div_cancel' hdiv).symm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hN hdiv) hf
  refine ⟨n, hn, ?_⟩
  apply zHatMulNat_injective hf
  change f • z = f • (n • (1 : ZHat))
  rw [h, smul_smul, ← hN_eq]

/-- The element `τ⁻¹ σ ^ f(τ) τ` of `H` attached to one double coset in
the transfer formula on `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTerm
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  exact ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem H σ.1 q.out⟩

/-- The transfer term pulled back from `H` to
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTermPreimage
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    E.field.field.toSubgroup ⧸ D.extensionInertiaWithin E.field.field L hL :=
  (D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL).symm
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q)

/-- The pullback of each double-coset term has strictly positive integral
normalized degree, as asserted. -/
theorem transferNormNaturalityFrobeniusTransferTermPreimage_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree E.field L hL
        (D.transferNormNaturalityFrobeniusTransferTermPreimage
          E L hL σ q) =
          (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let := H.fintypeQuotientOfFiniteIndex
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let N := m * D.frobeniusExponent E.base L (hL.trans E.below) σ
  let u := D.transferNormNaturalityFrobeniusTransferTermPreimage
    E L hL σ q
  let f := (E.residueDegree : ℕ)
  let : Finite (orbit (Subgroup.zpowers σ.1) q.out) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : 0 < f := E.residueDegree.property
  have hm : 0 < m := by
    have hm0 : Function.minimalPeriod (σ.1 • ·) q.out ≠ 0 :=
      NeZero.ne _
    simpa [m] using Nat.pos_of_ne_zero hm0
  have hN : 0 < N := Nat.mul_pos hm
    (D.frobeniusExponent_pos E.base L (hL.trans E.below) σ)
  have hu :
      D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl u =
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1 := by
    exact congrArg Subtype.val
      ((D.transferNormNaturalityFrobeniusIntermediateEquiv
        E L hL).apply_symm_apply
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q))
  have hconj :
      D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q).1 =
        D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m) := by
    change D.extensionNormalizedDegree E.base L (hL.trans E.below)
        (q.out.out⁻¹ * σ.1 ^ m * q.out.out) = _
    rw [map_mul, map_mul, map_inv]
    simp [mul_comm]
  have hdegree : f •
      (D.extensionNormalizedDegree E.field L hL u).toAdd =
        N • (1 : ZHat) := by
    calc
      f • (D.extensionNormalizedDegree E.field L hL u).toAdd =
          (D.extensionNormalizedDegree E.base L (hL.trans E.below)
            (D.finiteReciprocityNaturalityFrobeniusTowerMap
              E.base.field E.field.field L L
              (hL.trans E.below) hL E.below le_rfl u)).toAdd := by
        symm
        exact D.finiteReciprocityNaturalityFrobeniusTowerMap_degree
          E L L (hL.trans E.below) hL le_rfl u
      _ = (D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m)).toAdd := by rw [hu, hconj]
      _ = N • (1 : ZHat) := by
        rw [map_pow,
          D.extensionNormalizedDegree_frobenius_eq_pow
            E.base L (hL.trans E.below) σ]
        change m •
            (D.frobeniusExponent E.base L (hL.trans E.below) σ •
              (1 : ZHat)) = N • (1 : ZHat)
        rw [smul_smul]
  obtain ⟨n, hn, hnEq⟩ :=
    transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat f N hf hN
      (D.extensionNormalizedDegree E.field L hL u).toAdd hdegree
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.ext
  exact hnEq

/-- The actual Frobenius lift over `K'` represented by one term of the
transfer product. -/
noncomputable def transferNormNaturalityTransferFrobeniusLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.FrobeniusElements E.field L hL :=
  ⟨D.transferNormNaturalityFrobeniusTransferTermPreimage
      E L hL σ q,
    D.transferNormNaturalityFrobeniusTransferTermPreimage_degree
      E L hL σ q⟩

/--
Establishes the identity `(D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 =
D.transferNormNaturalityFrobeniusTransferTermPreimage E L hL σ q`.
-/
@[simp]
theorem transferNormNaturalityTransferFrobeniusLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    (D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q).1 =
      D.transferNormNaturalityFrobeniusTransferTermPreimage
        E L hL σ q := rfl

/-- The Frobenius lift attached to a transfer orbit maps to the transfer
term `τ⁻¹ σ^f τ` in `G(\widetilde L/K)`. -/
theorem transferNormNaturalityTransferFrobeniusLift_towerMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl
        (D.transferNormNaturalityTransferFrobeniusLift
          E L hL σ q).1 =
      (D.transferNormNaturalityFrobeniusTransferTerm
        E L hL σ q).1 := by
  exact congrArg Subtype.val
    ((D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL).apply_symm_apply
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q))

/-- The closed subgroup generated by a transfer Frobenius lift maps onto
the closed subgroup generated by the corresponding transfer term. -/
theorem transferNormNaturalityTransferFrobeniusLift_closure_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl
    (D.frobeniusClosure E.field L hL β).toSubgroup.map f =
      (closedSubgroupGenerated
        ({(D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1} : Set
            (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
              (hL.trans E.below))) : Subgroup
                (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
                  (hL.trans E.below))) := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let fc := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let u := (D.transferNormNaturalityFrobeniusTransferTerm
    E L hL σ q).1
  have hβu : f β.1 = u :=
    D.transferNormNaturalityTransferFrobeniusLift_towerMap
      E L hL σ q
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ Γβ.toSubgroup at hx
    have hx' : x ∈
        (closedSubgroupGenerated
          ({(D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q).1} : Set
        (E.field.field.toSubgroup ⧸
          D.extensionInertiaWithin E.field.field L hL))).toSubgroup := by
      simpa only [Γβ, DegreeData.frobeniusClosure, Set.range_unique] using hx
    have hmap := map_mem_closedSubgroupGenerated_singleton
      fc (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 hx'
    change f x ∈
      (closedSubgroupGenerated ({f β.1} : Set P) : Subgroup P) at hmap
    rw [hβu] at hmap
    exact hmap
  · have hK'compact : CompactSpace E.field.field.toSubgroup :=
      isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
    let : CompactSpace E.field.field.toSubgroup := hK'compact
    let : IsClosed
        (D.extensionInertiaWithin E.field.field L hL :
          Set E.field.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.field L hL
    let : IsClosed (D.extensionInertiaWithin E.base.field L
        (hL.trans E.below) : Set E.base.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
    have hmapClosed : IsClosed
        ((Γβ.toSubgroup.map f : Subgroup P) : Set P) := by
      have hrange : ((Γβ.toSubgroup.map f : Subgroup P) : Set P) =
          Set.range (fun x : Γβ => f x.1) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x.1, x.2, rfl⟩
      rw [hrange]
      have hclosed :=
        ((isCompact_univ (X := Γβ)).image
          (fc.continuous.comp continuous_subtype_val)).isClosed
      change IsClosed
        ((fun x : Γβ => fc.toMonoidHom x.1) '' Set.univ) at hclosed
      have hclosed' :
          IsClosed (Set.range (fun x : Γβ => fc.toMonoidHom x.1)) := by
        simpa only [Set.image_univ] using hclosed
      have hfc : fc.toMonoidHom = f := by
        rfl
      rw [hfc] at hclosed'
      exact hclosed'
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hβmem : β.1 ∈ Γβ.toSubgroup := by
        have hgen : β.1 ∈
            (closedSubgroupGenerated ({β.1} : Set _) : Subgroup _) :=
          Subgroup.le_topologicalClosure _
            (Subgroup.subset_closure (by simp))
        simpa [Γβ, β, DegreeData.frobeniusClosure] using hgen
      exact ⟨β.1, hβmem, hβu⟩
    · exact hmapClosed

/-- For a transfer orbit represented by `t`, the absolute subgroup fixed
by its Frobenius lift over `K'` is the stabilizer of the norm coset
`t⁻¹ G_Σ`.  This is the intersection
`G_K' ∩ t⁻¹ G_Σ t`. -/
theorem transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let kM : extensionSubgroup E.base.field E.field.field E.below :=
      ⟨Subgroup.inclusion E.below k', k'.2⟩
    k' ∈ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL β)
          (D.frobeniusFixedField_le E.field L hL β) ↔
      kM ∈ MulAction.stabilizer
        (extensionSubgroup E.base.field E.field.field E.below)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
            (D.frobeniusFixedField_le E.base L
              (hL.trans E.below) σ)) := by
  dsimp only
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let P' := E.field.field.toSubgroup ⧸
    D.extensionInertiaWithin E.field.field L hL
  let f : P' →* P := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let t : P := q.out.out
  let tK : E.base.field.toSubgroup := Quotient.out t
  let u : P :=
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q).1
  let Cu : Subgroup P :=
    (closedSubgroupGenerated ({u} : Set P) : Subgroup P)
  let Cpow : Subgroup P :=
    (closedSubgroupGenerated ({σ.1 ^ m} : Set P) : Subgroup P)
  let c : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t }
  let ci : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t⁻¹).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t⁻¹ }
  have hc_apply (y : P) : c y = t * y * t⁻¹ := rfl
  have hci_apply (y : P) : ci y = t⁻¹ * y * t := by
    change t⁻¹ * y * (t⁻¹)⁻¹ = t⁻¹ * y * t
    rw [inv_inv]
  have hclosureMap : Γβ.toSubgroup.map f = Cu := by
    simpa [Γβ, Cu, u, β, f] using
      D.transferNormNaturalityTransferFrobeniusLift_closure_map
        E L hL σ q
  have hpow : Cpow = Γ.toSubgroup ⊓ MulAction.stabilizer P q.out := by
    simpa [Cpow, Γ, DegreeData.frobeniusClosure, m] using
      closedSubgroupGenerated_pow_eq_inf_stabilizer
        H hHclosed σ.1 q.out
  have hcu : c u = σ.1 ^ m := by
    change t * (t⁻¹ * σ.1 ^ m * t) * t⁻¹ = σ.1 ^ m
    simp [mul_assoc]
  have hcig : ci (σ.1 ^ m) = u := by
    rw [hci_apply]
    rfl
  have hVeq : MulAction.stabilizer P q.out =
      H.map (MulAut.conj t).toMonoidHom := by
    have hx : q.out = t • (QuotientGroup.mk 1 : P ⧸ H) := by
      symm
      change QuotientGroup.mk (t * 1) = q.out
      rw [mul_one]
      exact Quotient.out_eq' q.out
    rw [hx, stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  have hclosure_iff (x : P') :
      x ∈ Γβ.toSubgroup ↔ c (f x) ∈ Γ.toSubgroup := by
    constructor
    · intro hx
      have hfx : f x ∈ Cu := by
        rw [← hclosureMap]
        exact ⟨x, hx, rfl⟩
      have hcx := map_mem_closedSubgroupGenerated_singleton c u hfx
      rw [hcu] at hcx
      change c (f x) ∈ Cpow at hcx
      rw [hpow] at hcx
      exact hcx.1
    · intro hx
      have hfxH : f x ∈ H := ⟨x, rfl⟩
      have hcfxV : c (f x) ∈ MulAction.stabilizer P q.out := by
        rw [hVeq]
        exact ⟨f x, hfxH, rfl⟩
      have hcfx : c (f x) ∈ Cpow := by
        rw [hpow]
        exact ⟨hx, hcfxV⟩
      have hcix := map_mem_closedSubgroupGenerated_singleton
        ci (σ.1 ^ m) hcfx
      rw [hcig] at hcix
      have hif : ci (c (f x)) = f x := by
        rw [hci_apply, hc_apply]
        simp [mul_assoc]
      rw [hif] at hcix
      have hmap : f x ∈ Γβ.toSubgroup.map f := by
        rw [hclosureMap]
        exact hcix
      exact (Subgroup.mem_map_iff_mem
        (D.transferNormNaturalityFrobeniusTowerMap_injective
          E L hL)).mp hmap
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let kM : extensionSubgroup E.base.field E.field.field E.below :=
    ⟨Subgroup.inclusion E.below k', k'.2⟩
  rw [D.extensionSubgroup_frobeniusFixedField E.field L hL β]
  change QuotientGroup.mk k' ∈ Γβ.toSubgroup ↔ _
  rw [hclosure_iff]
  rw [mem_relativeNormDoubleCoset_stabilizer_iff
    E.base.field E.field.field S hSK E.below tK⁻¹ kM]
  let zK : E.base.field.toSubgroup :=
    tK * Subgroup.inclusion E.below k' * tK⁻¹
  have htz : c (f (QuotientGroup.mk k')) = QuotientGroup.mk zK := by
    change t * QuotientGroup.mk (Subgroup.inclusion E.below k') * t⁻¹ =
      QuotientGroup.mk zK
    have htK : (QuotientGroup.mk tK : P) = t := Quotient.out_eq' t
    rw [← htK]
    rfl
  rw [htz]
  rw [← D.mem_frobeniusFixedSubgroupWithin_iff E.base L
    (hL.trans E.below) σ zK]
  rw [← D.extensionSubgroup_frobeniusFixedField E.base L
    (hL.trans E.below) σ]
  rw [mem_extensionSubgroup_iff]
  change zK.1 ∈ S.toSubgroup ↔ _
  simp [zK, kM, tK, mul_assoc]

/-- The pointwise fixed-subgroup calculation above, upgraded to the
literal subgroup equality used to identify the stabilizer-coset fiber in
the transfer formula with the norm fiber. -/
theorem transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let e := transferNormNaturalityIntermediateAbsoluteEquiv
      E.base.field E.field.field E.below
    (extensionSubgroup E.field.field
      (D.frobeniusFixedField E.field L hL β)
        (D.frobeniusFixedField_le E.field L hL β)).map e.toMonoidHom =
      MulAction.stabilizer
        (extensionSubgroup E.base.field E.field.field E.below)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
            (D.frobeniusFixedField_le E.base L
              (hL.trans E.below) σ)) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  ext kM
  obtain ⟨k', rfl⟩ := e.surjective kM
  change e k' ∈ Subgroup.map e.toMonoidHom _ ↔ _
  have hmem : e k' ∈ Subgroup.map e.toMonoidHom
      (extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))
        (D.frobeniusFixedField_le E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))) ↔
      k' ∈ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))
        (D.frobeniusFixedField_le E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) :=
    Subgroup.mem_map_iff_mem e.injective
  rw [hmem]
  exact D.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    E L hL σ q k'

end DegreeData

namespace Internal

/-- For each transfer double coset, the quotient by the fixed subgroup of
its Frobenius factor is the stabilizer-coset fiber in the corresponding
norm double coset. -/
private noncomputable def chosenTransferNormNaturalityTransferNormFiberEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    E.field.field.toSubgroup ⧸ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL β)
          (D.frobeniusFixedField_le E.field L hL β) ≃
      (extensionSubgroup E.base.field E.field.field E.below) ⧸
        MulAction.stabilizer
          (extensionSubgroup E.base.field E.field.field E.below)
          (QuotientGroup.mk tK⁻¹ :
            E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
              (D.frobeniusFixedField_le E.base L
                (hL.trans E.below) σ)) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  let Sβsubgroup := extensionSubgroup E.field.field
    (D.frobeniusFixedField E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q))
    (D.frobeniusFixedField_le E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q))
  have hEq := D.transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    E L hL σ q
  exact (leftCosetEquivOfMulEquiv e Sβsubgroup).trans
    (Subgroup.quotientEquivOfEq hEq)

@[simp]
private theorem chosenTransferNormNaturalityTransferNormFiberEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
        D E L hL σ q (QuotientGroup.mk k') =
      QuotientGroup.mk
        (transferNormNaturalityIntermediateAbsoluteEquiv
          E.base.field E.field.field E.below k') := by
  unfold chosenTransferNormNaturalityTransferNormFiberEquiv
  rfl

end Internal

end transferFrobeniusFibers

section transferNormFibers

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace Internal

/-- Under the fiber equivalence, a summand in the double-coset norm is
literally the corresponding summand in `N_{Σₜ/K'}`. -/
private theorem transferNormNaturalityTransferNormFiber_term
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβK' := D.frobeniusFixedField_le E.field L hL β
    ∀ (hSβC : Sβ.toSubgroup ≤ C.toSubgroup)
      (kq : E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK'),
      relativeCosetAction A E.base.field S hSK π
          ((Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
            D E L hL σ q kq).out •
              (QuotientGroup.mk tK⁻¹ :
                E.base.field.toSubgroup ⧸
                  extensionSubgroup E.base.field S hSK)) =
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  intro hSβC kq
  refine QuotientGroup.induction_on kq ?_
  intro k'
  let M := extensionSubgroup E.base.field E.field.field E.below
  let φ : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
    QuotientGroup.mk tK⁻¹
  let kM : M := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below k'
  let fiberEquiv := Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
    D E L hL σ q
  let r : M ⧸ stabilizer M φ := fiberEquiv (QuotientGroup.mk k')
  have hrmk : (QuotientGroup.mk r.out : M ⧸ stabilizer M φ) =
      QuotientGroup.mk kM := by
    calc
      QuotientGroup.mk r.out = r := Quotient.out_eq' r
      _ = fiberEquiv (QuotientGroup.mk k') := rfl
      _ = QuotientGroup.mk kM :=
        Internal.chosenTransferNormNaturalityTransferNormFiberEquiv_mk
          D E L hL σ q k'
  have hrel : r.out⁻¹ * kM ∈ stabilizer M φ :=
    QuotientGroup.eq.mp hrmk
  have hact : r.out • φ = kM • φ := by
    have hh := congrArg (fun z => r.out • z) hrel
    simpa [mul_smul] using hh.symm
  change relativeCosetAction A E.base.field S hSK π (r.out • φ) = _
  rw [hact]
  change relativeCosetAction A E.base.field S hSK π
      (QuotientGroup.mk (kM.1 * tK⁻¹)) = _
  rw [relativeCosetAction_mk, relativeCosetAction_mk]
  simp only [fixedFieldInclusion_coe, conjugateFixedElement_coe]
  change A.ρ (k'.1 * tK.1⁻¹) π.1 = A.ρ k'.1 (A.ρ tK.1⁻¹ π.1)
  rw [map_mul]
  rfl

/-- The inner double-coset sum for a transfer orbit is the relative norm
`N_{Σₜ/K'}(π^t)` appearing. -/
private theorem transferNormNaturalityTransferNormFiber_sum
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    [hL'finite : Finite
      (E.field.field.toSubgroup ⧸ extensionSubgroup E.field.field L hL)]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ))
    (hSβC :
      let β := D.transferNormNaturalityTransferFrobeniusLift
        E L hL σ q
      let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
      let tK : E.base.field.toSubgroup := Quotient.out q.out.out
      (D.frobeniusFixedField E.field L hL β).toSubgroup ≤
        (conjugateClosedSubgroup S tK.1).toSubgroup) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβK' := D.frobeniusFixedField_le E.field L hL β
    let M := extensionSubgroup E.base.field E.field.field E.below
    let φ : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
      QuotientGroup.mk tK⁻¹
    letI : Finite (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK') :=
      D.frobeniusFixedField_finite E.field L hL β
    letI : Fintype (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK') := Fintype.ofFinite _
    let fiberEquiv := Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
      D E L hL σ q
    letI : Fintype (M ⧸ stabilizer M φ) :=
      Fintype.ofEquiv
        (E.field.field.toSubgroup ⧸
          extensionSubgroup E.field.field Sβ hSβK') fiberEquiv
    ∑ r : M ⧸ stabilizer M φ,
        relativeCosetAction A E.base.field S hSK π (r.out • φ) =
      ((relativeNorm A E.field.field Sβ hSβK'
        (fixedFieldInclusion A C Sβ hSβC
          (conjugateFixedElement A S tK.1 π)) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  let M := extensionSubgroup E.base.field E.field.field E.below
  let φ : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
    QuotientGroup.mk tK⁻¹
  let : Finite (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field Sβ hSβK') :=
    D.frobeniusFixedField_finite E.field L hL β
  let : Fintype (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field Sβ hSβK') := Fintype.ofFinite _
  let fiberEquiv := Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
    D E L hL σ q
  let : Fintype (M ⧸ stabilizer M φ) :=
    Fintype.ofEquiv
      (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK') fiberEquiv
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    (∑ r : M ⧸ stabilizer M φ,
        relativeCosetAction A E.base.field S hSK π (r.out • φ)) =
      ∑ kq : E.field.field.toSubgroup ⧸
          extensionSubgroup E.field.field Sβ hSβK',
        relativeCosetAction A E.base.field S hSK π
          ((fiberEquiv kq).out • φ) :=
      (fiberEquiv.sum_comp
        (fun r => relativeCosetAction A E.base.field S hSK π
          (r.out • φ))).symm
    _ = ∑ kq : E.field.field.toSubgroup ⧸
          extensionSubgroup E.field.field Sβ hSβK',
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
      apply Fintype.sum_congr
      intro kq
      exact Internal.transferNormNaturalityTransferNormFiber_term
        D A E L hL σ q π hSβC kq

end Internal

end transferNormFibers

section transferredFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The fixed field `Σₜ` of a transfer Frobenius factor is contained
in the conjugate field `Σ^t`.  On absolute groups this is
`G_{Σₜ} ⊆ G_{Σ^t}` from. -/
theorem transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    Sβ.toSubgroup ≤ C.toSubgroup := by
  dsimp only
  intro x hx
  apply (conjugateClosedSubgroup_mem
    (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
    (Quotient.out q.out.out).1 x).2
  let k' : E.field.field.toSubgroup :=
    ⟨x, (D.frobeniusFixedField_le E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q)) hx⟩
  have hxext : k' ∈ extensionSubgroup E.field.field
      (D.frobeniusFixedField E.field L hL
        (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q))
      (D.frobeniusFixedField_le E.field L hL
        (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q)) := by
    rw [mem_extensionSubgroup_iff]
    exact hx
  have hstab :=
    (D.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
      E L hL σ q k').1 hxext
  have hmem :=
    (mem_relativeNormDoubleCoset_stabilizer_iff
      E.base.field E.field.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ)
      E.below (Quotient.out q.out.out)⁻¹
      (⟨Subgroup.inclusion E.below k', k'.2⟩ :
        extensionSubgroup E.base.field E.field.field E.below)).1 hstab
  change
    ((Quotient.out q.out.out)⁻¹).1⁻¹ *
        (Subgroup.inclusion E.below k').1 *
        ((Quotient.out q.out.out)⁻¹).1 ∈
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup at hmem
  have heq :
      ((Quotient.out q.out.out)⁻¹).1⁻¹ *
          (Subgroup.inclusion E.below k').1 *
          ((Quotient.out q.out.out)⁻¹).1 =
        (Quotient.out q.out.out).1 * x *
          (Quotient.out q.out.out).1⁻¹ := by
    simp [k']
  rw [heq] at hmem
  exact hmem

/-- The extension `Σₜ | Σ^t` attached to one transfer orbit is
unramified, as asserted. -/
theorem transferNormNaturalityTransferFrobenius_fixedField_isUnramified_conjugate
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβC := D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
    (DegreeData.AbstractExtension.mk Sβ C hSβC).IsUnramified D := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  have hSβC : Sβ.toSubgroup ≤ C.toSubgroup := by
    exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  rw [(DegreeData.AbstractExtension.mk Sβ C hSβC).isUnramified_iff_inertia_le D]
  intro x hx
  have hxC : x ∈ C.toSubgroup := hx.1
  have hxd : D.degree x = 1 := hx.2
  have hconjS : tK.1 * x * tK.1⁻¹ ∈ S.toSubgroup := by
    exact (conjugateClosedSubgroup_mem S tK.1 x).1 hxC
  have hconjd : D.degree (tK.1 * x * tK.1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hxd]
    simp
  have hconjI : tK.1 * x * tK.1⁻¹ ∈
      (D.fieldInertia S).toSubgroup := by
    exact ⟨hconjS, hconjd⟩
  have hconjIL : tK.1 * x * tK.1⁻¹ ∈
      (D.fieldInertia L).toSubgroup := by
    rw [← D.frobeniusFixedField_fieldInertia
      E.base L (hL.trans E.below) σ]
    exact hconjI
  have hxK : x ∈ E.base.field.toSubgroup := by
    have hconjK : tK.1 * x * tK.1⁻¹ ∈ E.base.field.toSubgroup :=
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ) hconjS
    have hback := E.base.field.toSubgroup.mul_mem
      (E.base.field.toSubgroup.mul_mem
        (E.base.field.toSubgroup.inv_mem tK.2) hconjK) tK.2
    simpa [mul_assoc] using hback
  let xK : E.base.field.toSubgroup := ⟨x, hxK⟩
  let yK : E.base.field.toSubgroup :=
    ⟨tK.1 * x * tK.1⁻¹,
      E.base.field.toSubgroup.mul_mem
        (E.base.field.toSubgroup.mul_mem tK.2 hxK)
        (E.base.field.toSubgroup.inv_mem tK.2)⟩
  have hyL : yK ∈
      extensionSubgroup E.base.field L (hL.trans E.below) := by
    rw [mem_extensionSubgroup_iff]
    exact hconjIL.1
  have hxLext : xK ∈
      extensionSubgroup E.base.field L (hL.trans E.below) := by
    have hback := hLnormal.conj_mem yK hyL tK⁻¹
    simpa [xK, yK, tK, mul_assoc] using hback
  have hxL : x ∈ L.toSubgroup := by
    exact (mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below) xK).1 hxLext
  have hxIL : x ∈ (D.fieldInertia L).toSubgroup := ⟨hxL, hxd⟩
  have hxISβ : x ∈ (D.fieldInertia Sβ).toSubgroup := by
    rw [D.frobeniusFixedField_fieldInertia E.field L hL β]
    exact hxIL
  exact hxISβ.1

end DegreeData

end transferredFixedFields

section transferNormArithmetic

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- If `π` is prime in `Σ`, its conjugate `π^t`, included into the
unramified extension `Σₜ`, remains prime. -/
theorem transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup F.base.field L (hL.trans F.below)).Normal]
    [hL'normal : (extensionSubgroup F.field.field L hL).Normal]
    [hLfinite : Finite
      (F.field.field.toSubgroup ⧸ extensionSubgroup F.field.field L hL)]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (extensionSubgroup F.base.field L
          (hL.trans F.below)).Normal
        exact hLnormal))
    (q :
      letI : (extensionSubgroup
          (F.toFiniteResidueAbstractExtension D).base.field L
            (hL.trans F.below)).Normal := by
        change (extensionSubgroup F.base.field L
          (hL.trans F.below)).Normal
        exact hLnormal
      letI : (extensionSubgroup
          (F.toFiniteResidueAbstractExtension D).field.field L hL).Normal := by
        change (extensionSubgroup F.field.field L hL).Normal
        exact hL'normal
      Quotient (orbitRel (Subgroup.zpowers σ.1)
      (((F.toFiniteResidueAbstractExtension D).base.field.toSubgroup ⧸
        D.extensionInertiaWithin
          (F.toFiniteResidueAbstractExtension D).base.field L
            (hL.trans F.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            (F.toFiniteResidueAbstractExtension D) L hL
            (hLnormal := by
              change (extensionSubgroup F.base.field L
                (hL.trans F.below)).Normal
              exact hLnormal)
            (hL'normal := by
              change (extensionSubgroup F.field.field L hL).Normal
              exact hL'normal))))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField
        (F.toFiniteResidueAbstractExtension D).base L
        (hL.trans F.below) (hLnormal := by
          change (extensionSubgroup F.base.field L
            (hL.trans F.below)).Normal
          exact hLnormal) σ))
    (hπ :
      let KR := (F.toFiniteResidueAbstractExtension D).base
      letI :
          (extensionSubgroup KR.field L (hL.trans F.below)).Normal := by
        change (extensionSubgroup F.base.field L
          (hL.trans F.below)).Normal
        exact hLnormal
      let T : FiniteTower G := {
        top := L
        middle := F.field.field
        base := F.base.field
        top_le_middle := hL
        middle_le_base := F.below
        finiteTopQuotient := hLfinite
        finiteBaseQuotient := F.finiteQuotient }
      letI : Finite (F.base.field.toSubgroup ⧸
          extensionSubgroup F.base.field L (hL.trans F.below)) :=
        T.totalQuotientFinite
      let S := D.frobeniusFixedField
        KR L (hL.trans F.below) σ
      let Sfinite : FiniteAbstractField G := {
        field := S
        finite := D.frobeniusFixedField_absoluteFinite
          F.base L (hL.trans F.below) σ }
      v.IsPrimeElement Sfinite π) :
    let E := F.toFiniteResidueAbstractExtension D
    letI hLnormalE :
        (extensionSubgroup E.base.field L (hL.trans E.below)).Normal := by
      change (extensionSubgroup F.base.field L
        (hL.trans F.below)).Normal
      exact hLnormal
    letI hL'normalE : (extensionSubgroup E.field.field L hL).Normal := by
      change (extensionSubgroup F.field.field L hL).Normal
      exact hL'normal
    let T : FiniteTower G := {
      top := L
      middle := F.field.field
      base := F.base.field
      top_le_middle := hL
      middle_le_base := F.below
      finiteTopQuotient := hLfinite
      finiteBaseQuotient := F.finiteQuotient }
    letI : Finite (F.base.field.toSubgroup ⧸
        extensionSubgroup F.base.field L (hL.trans F.below)) :=
      T.totalQuotientFinite
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let Sfinite : FiniteAbstractField G := {
      field := S
      finite := by
        simpa [E, S,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using
          D.frobeniusFixedField_absoluteFinite
          F.base L (hL.trans F.below) σ }
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let Cfinite := Sfinite.conjugate tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let Sβfinite : FiniteAbstractField G := {
      field := Sβ
      finite := by
        simpa [E, Sβ,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using
          D.frobeniusFixedField_absoluteFinite F.field L hL β }
    let hSβC : Sβfinite.field.toSubgroup ≤ Cfinite.field.toSubgroup := by
      change Sβ.toSubgroup ≤
        (conjugateClosedSubgroup S tK.1).toSubgroup
      exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
        E L hL σ q
    v.IsPrimeElement Sβfinite
      (fixedFieldInclusion A Cfinite.field Sβfinite.field hSβC
        (conjugateFixedElement A S tK.1 π)) := by
  dsimp only
  let E := F.toFiniteResidueAbstractExtension D
  let hLnormalE :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal := by
    change (extensionSubgroup F.base.field L
      (hL.trans F.below)).Normal
    exact hLnormal
  let hL'normalE : (extensionSubgroup E.field.field L hL).Normal := by
    change (extensionSubgroup F.field.field L hL).Normal
    exact hL'normal
  let T : FiniteTower G := {
    top := L
    middle := F.field.field
    base := F.base.field
    top_le_middle := hL
    middle_le_base := F.below
    finiteTopQuotient := hLfinite
    finiteBaseQuotient := F.finiteQuotient }
  let hLbaseFinite : Finite (F.base.field.toSubgroup ⧸
      extensionSubgroup F.base.field L (hL.trans F.below)) :=
    T.totalQuotientFinite
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let Sfinite : FiniteAbstractField G := {
    field := S
    finite := by
      simpa [E, S,
        FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        D.frobeniusFixedField_absoluteFinite
        F.base L (hL.trans F.below) σ }
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let Cfinite := Sfinite.conjugate tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let Sβfinite : FiniteAbstractField G := {
    field := Sβ
    finite := by
      simpa [E, Sβ,
        FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        D.frobeniusFixedField_absoluteFinite F.field L hL β }
  let hSβC : Sβfinite.field.toSubgroup ≤ Cfinite.field.toSubgroup := by
    change Sβ.toSubgroup ≤
      (conjugateClosedSubgroup S tK.1).toSubgroup
    exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  let hSβabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) Sβfinite.field
        (le_baseField Sβfinite.field)) :=
    Sβfinite.finite
  let hSβCfinite : Finite
      (Cfinite.field.toSubgroup ⧸
        extensionSubgroup Cfinite.field Sβfinite.field hSβC) :=
    FiniteIntermediateField.finite_extension_of_le
      (le_baseField Sβfinite.field) (le_baseField Cfinite.field) hSβC
  let EβC : FiniteAbstractFieldExtension G := {
    field := Sβfinite
    base := Cfinite
    below := hSβC
    finiteQuotient := hSβCfinite }
  let πC : ambientFixedAddSubgroup A Cfinite.field :=
    conjugateFixedElement A S tK.1 π
  have hπC : v.IsPrimeElement Cfinite πC := by
    rw [ValuationData.IsPrimeElement]
    rw [show v.valuationAt Cfinite πC = v.valuationAt Sfinite π by
      simpa [Cfinite, Sfinite, πC] using
        v.normalizedValuation_conjugate Sfinite tK.1 π]
    exact hπ
  have hUn : EβC.IsUnramified D := by
    exact D.transferNormNaturalityTransferFrobenius_fixedField_isUnramified_conjugate
      E L hL σ q
  exact v.prime_of_unramified EβC hUn πC hπC

/-- The norm identity for transfer--norm naturality:
`N_{Σ/K}(π)` is the sum, over transfer double cosets, of
`N_{Σₜ/K'}(π^t)`.  The construction writes this identity multiplicatively. -/
theorem transferNormNaturalityNorm_eq_sum_transferNorms
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup F.base.field L (hL.trans F.below)).Normal]
    [hLfinite : Finite
      (F.field.field.toSubgroup ⧸ extensionSubgroup F.field.field L hL)]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (extensionSubgroup F.base.field L
          (hL.trans F.below)).Normal
        exact hLnormal))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField
        (F.toFiniteResidueAbstractExtension D).base L
        (hL.trans F.below) (hLnormal := by
          change (extensionSubgroup F.base.field L
            (hL.trans F.below)).Normal
          exact hLnormal) σ)) :
    let E := F.toFiniteResidueAbstractExtension D
    letI hLnormalE :
        (extensionSubgroup E.base.field L (hL.trans E.below)).Normal := by
      change (extensionSubgroup F.base.field L
        (hL.trans F.below)).Normal
      exact hLnormal
    let T : FiniteTower G := {
      top := L
      middle := F.field.field
      base := F.base.field
      top_le_middle := hL
      middle_le_base := F.below
      finiteTopQuotient := hLfinite
      finiteBaseQuotient := F.finiteQuotient }
    letI : Finite (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field L (hL.trans E.below)) := by
      change Finite (F.base.field.toSubgroup ⧸
        extensionSubgroup F.base.field L (hL.trans F.below))
      exact T.totalQuotientFinite
    letI : Finite (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field L hL) := by
      change Finite (F.field.field.toSubgroup ⧸
        extensionSubgroup F.field.field L hL)
      exact hLfinite
    letI : (extensionSubgroup E.field.field L hL).Normal :=
      transferNormNaturality_intermediateExtension_normal
        E.base.field E.field.field L hL E.below
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let M := extensionSubgroup E.base.field E.field.field E.below
    let ΩN := Quotient (orbitRel M
      (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK))
    letI : Finite (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field S hSK) :=
      D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
    letI : Fintype ΩN := Fintype.ofFinite _
    ((fixedFieldInclusion A E.base.field E.field.field E.below
      (relativeNorm A E.base.field S hSK π) :
        ambientFixedAddSubgroup A E.field.field) : A.V) =
      ∑ qN : ΩN,
        let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
          E L hL σ).symm qN
        let β := D.transferNormNaturalityTransferFrobeniusLift
          E L hL σ qT
        let tK : E.base.field.toSubgroup := Quotient.out qT.out.out
        let C := conjugateClosedSubgroup S tK.1
        let Sβ := D.frobeniusFixedField E.field L hL β
        let hSβK' := D.frobeniusFixedField_le E.field L hL β
        let hSβC : Sβ.toSubgroup ≤ C.toSubgroup :=
          D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
            E L hL σ qT
        letI : Finite (E.field.field.toSubgroup ⧸
            extensionSubgroup E.field.field Sβ hSβK') :=
          D.frobeniusFixedField_finite E.field L hL β
        ((relativeNorm A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) :
              ambientFixedAddSubgroup A E.field.field) : A.V) := by
  dsimp only
  let E := F.toFiniteResidueAbstractExtension D
  let hLnormalE :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal := by
    change (extensionSubgroup F.base.field L
      (hL.trans F.below)).Normal
    exact hLnormal
  let T : FiniteTower G := {
    top := L
    middle := F.field.field
    base := F.base.field
    top_le_middle := hL
    middle_le_base := F.below
    finiteTopQuotient := hLfinite
    finiteBaseQuotient := F.finiteQuotient }
  let hLbaseFinite : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field L (hL.trans E.below)) := by
    change Finite (F.base.field.toSubgroup ⧸
      extensionSubgroup F.base.field L (hL.trans F.below))
    exact T.totalQuotientFinite
  let hLfieldFinite : Finite (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field L hL) := by
    change Finite (F.field.field.toSubgroup ⧸
      extensionSubgroup F.field.field L hL)
    exact hLfinite
  let hL'normal : (extensionSubgroup E.field.field L hL).Normal :=
    transferNormNaturality_intermediateExtension_normal
      E.base.field E.field.field L hL E.below
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let M := extensionSubgroup E.base.field E.field.field E.below
  let ΩN := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK))
  let φ : ΩN →
      E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK :=
    Internal.chosenTransferNormNaturalityNormOrbitRepresentative
      D E L hL σ
  let : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field S hSK) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  let : Fintype ΩN := Fintype.ofFinite _
  let (qN : ΩN) : Fintype (M ⧸ stabilizer M (φ qN)) := by
    letI : Finite (orbit M (φ qN)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI := Fintype.ofFinite (orbit M (φ qN))
    exact Fintype.ofEquiv (orbit M (φ qN))
      (orbitEquivQuotientStabilizer M (φ qN))
  change ((relativeNorm A E.base.field S hSK π :
    ambientFixedAddSubgroup A E.base.field) : A.V) = _
  rw [relativeNorm_eq_sum_chosenOrbit_of_fintype A E.base.field S hSK M
    (Internal.chosenTransferNormNaturalityNormOrbitRepresentative_spec
      D E L hL σ) π]
  apply Fintype.sum_congr
  intro qN
  let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
    E L hL σ).symm qN
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ qT
  let tK : E.base.field.toSubgroup := Quotient.out qT.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  let hSβC : Sβ.toSubgroup ≤ C.toSubgroup :=
    D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ qT
  let fiberEquiv :
      (E.field.field.toSubgroup ⧸ extensionSubgroup E.field.field Sβ hSβK') ≃
        (M ⧸ stabilizer M (φ qN)) :=
    Internal.chosenTransferNormNaturalityTransferNormFiberEquiv D E L hL σ qT
  let : Finite (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field Sβ hSβK') :=
    D.frobeniusFixedField_finite E.field L hL β
  let : Fintype (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field Sβ hSβK') :=
    Fintype.ofFinite _
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    (∑ r : M ⧸ stabilizer M (φ qN),
        relativeCosetAction A E.base.field S hSK π
          ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
            M (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK)
              (Internal.chosenTransferNormNaturalityNormOrbitRepresentative_spec
                D E L hL σ)).symm ⟨qN, r⟩)) =
      ∑ r : M ⧸ stabilizer M (φ qN),
        relativeCosetAction A E.base.field S hSK π (r.out • φ qN) := by
      apply Fintype.sum_congr
      intro r
      rw [chosenOrbitClassEquiv_symm_apply]
    _ = ∑ kq : E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK',
        relativeCosetAction A E.base.field S hSK π
          ((fiberEquiv kq).out • φ qN) :=
      (fiberEquiv.sum_comp
        (fun r => relativeCosetAction A E.base.field S hSK π
          (r.out • φ qN))).symm
    _ = ∑ kq : E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field Sβ hSβK',
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
      apply Fintype.sum_congr
      intro kq
      exact Internal.transferNormNaturalityTransferNormFiber_term
        D A E L hL σ qT π hSβC kq

end DegreeData

end transferNormArithmetic

section frobeniusTransfer

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The classical transfer on the groups
`G(\widetilde L/K) → G(\widetilde L/K')`, before passage to the finite
Galois quotient. -/
noncomputable def transferNormNaturalityFrobeniusTransfer
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Abelianization (E.base.field.toSubgroup ⧸
        D.extensionInertiaWithin E.base.field L (hL.trans E.below)) →*
      Abelianization (E.field.field.toSubgroup ⧸
        D.extensionInertiaWithin E.field.field L hL) := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let e := D.transferNormNaturalityFrobeniusIntermediateEquiv
    E L hL
  exact e.symm.abelianizationCongr.toMonoidHom.comp
    (Abelianization.lift
      (MonoidHom.transfer (Abelianization.of : H →* Abelianization H)))

/-- The double-coset formula for the preceding Frobenius-level transfer.
Every factor is the positive Frobenius lift constructed above. -/
theorem transferNormNaturalityFrobeniusTransfer_doubleCoset_formula
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
    let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL
    letI : H.FiniteIndex :=
      D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
    letI : Fintype (Quotient (orbitRel (Subgroup.zpowers σ)
        ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below)) ⧸ H))) :=
      Fintype.ofFinite _
    D.transferNormNaturalityFrobeniusTransfer E L hL
        (Abelianization.of σ) =
      ∏ q : Quotient (orbitRel (Subgroup.zpowers σ)
          ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸ H)),
        Abelianization.of
          ((D.transferNormNaturalityFrobeniusIntermediateEquiv
            E L hL).symm
              ⟨q.out.out⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out *
                  q.out.out,
                QuotientGroup.out_conj_pow_minimalPeriod_mem
                  H σ q.out⟩) := by
  dsimp only
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let := Fintype.ofFinite
    (Quotient (orbitRel (Subgroup.zpowers σ)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸ H)))
  unfold transferNormNaturalityFrobeniusTransfer
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  exact abelianizationCongr_of
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL).symm _

end DegreeData
end frobeniusTransfer
end

end ClassFormation
