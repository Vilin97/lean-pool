/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitLocalPowerKernel
/-!
# Finite support for Kummer radicals

A chosen finite enlargement of places containing representatives of every class in a finite Kummer radical.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The finite Kummer radical `D ∩ Kˢ`, where
`D = Lˣⁿ ∩ Kˣ`. -/
def sUnitFiniteKummerRadical
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  SUnitGroup (K := K) S ⊓
    KummerTheory.finiteKummerRadicalSubgroup
      (K := K) (L := L) n

/-- An `S`-unit belongs to the finite Kummer radical exactly when it has
an `n`-th root in `L`. -/
@[simp]
theorem mem_sUnitFiniteKummerRadical_iff
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈ sUnitFiniteKummerRadical (K := K) (L := L) n S ↔
      x ∈ SUnitGroup (K := K) S ∧
        ∃ beta : Lˣ,
          beta ^ (n : ℕ) =
            Units.map (algebraMap K L).toMonoidHom x :=
  Iff.rfl

/-- Adjoin the ambient `n`-th powers to `D ∩ Kˢ`, producing an admissible
object on the subgroup side of Kummer theory. -/
def sUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.KummerSubgroup K n :=
  ⟨sUnitFiniteKummerRadical (K := K) (L := L) n S ⊔
      KummerTheory.unitNthPowersSubgroup K n,
    le_sup_right⟩

/-- The `S`-unit Kummer subgroup lies in the actual radical of `L / K`. -/
theorem sUnitKummerSubgroup_le_finiteKummerRadicalSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup (K := K) (L := L) n S).1 ≤
      KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n := by
  apply sup_le
  · exact inf_le_right
  · intro x hx
    obtain ⟨y, rfl⟩ :=
      (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hx
    exact
      (KummerTheory.mem_finiteKummerRadicalSubgroup_iff n).mpr
        ⟨Units.map (algebraMap K L).toMonoidHom y, by simp⟩

/-- Enlarging the finite set of places enlarges the `S`-unit group. -/
theorem sUnitGroup_mono
    {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    SUnitGroup (K := K) S ≤ SUnitGroup (K := K) T := by
  intro x hx
  rw [mem_SUnitGroup_iff] at hx ⊢
  intro v hvT
  exact hx v (fun hvS => hvT (hST hvS))

/-- A chosen finite set of places outside which a given global unit is
an integral unit. -/
noncomputable def chosenUnitFiniteSupport (x : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Classical.choose
    (IdeleGroup.exists_finset_supportedAt
      (IdeleGroup.principalIdele K x))

/-- A global unit is an `S`-unit for its chosen finite support. -/
theorem mem_sUnitGroup_chosenUnitFiniteSupport (x : Kˣ) :
    x ∈ SUnitGroup (K := K) (chosenUnitFiniteSupport (K := K) x) := by
  rw [mem_SUnitGroup_iff]
  intro v hv
  have hsupported :=
    Classical.choose_spec
      (IdeleGroup.exists_finset_supportedAt
        (IdeleGroup.principalIdele K x))
  have hunit :=
    (IdeleGroup.mem_supportedAt_iff
      (K := K)
      (chosenUnitFiniteSupport (K := K) x : Set _)
      (IdeleGroup.principalIdele K x)).mp hsupported v
      (by simpa using hv)
  rw [
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      at hunit
  change
    Valued.v
        (((IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele K x) :
            (v.adicCompletion K)ˣ) :
          v.adicCompletion K)) = 1 at hunit
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hunit
  exact hunit

omit numberFieldK in
/-- The actual radical quotient of a finite Galois extension is finite.
This is obtained from the concrete finite Kummer character equivalence,
not supplied as a finiteness hypothesis. -/
theorem finite_chosenFiniteKummerRadicalQuotient
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Finite
      ((KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  let H :=
    Gal(L/K) →* KummerTheory.nthRootsSubgroup L (n : ℕ)
  let : Finite H :=
    Finite.of_injective
      (fun chi : H =>
        (chi : Gal(L/K) →
          KummerTheory.nthRootsSubgroup L (n : ℕ)))
      DFunLike.coe_injective
  let hbase :
      KummerTheory.NthRootsOfUnityInBase
        (K := K) (L := L) n :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := L) n hmu
  let e : D.RadicalQuotient ≃* H :=
    KummerTheory.finiteKummerCharacterEquiv n hbase
  exact Finite.of_equiv H e.symm.toEquiv

/-- A chosen representative of a class in the actual finite Kummer
radical quotient. -/
noncomputable def chosenFiniteKummerRadicalRepresentative
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).carrier :=
  Classical.choose
    ((KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).radicalQuotientMk_surjective q)

omit numberFieldK in
/-- The chosen representative maps back to the prescribed radical class. -/
@[simp]
theorem chosenFiniteKummerRadicalRepresentative_spec
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).radicalQuotientMk
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q) = q :=
  Classical.choose_spec
    ((KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).radicalQuotientMk_surjective q)

/-- The union of the supports of one representative of every actual
Kummer radical class. -/
noncomputable def finiteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  letI : Finite D.RadicalQuotient :=
    finite_chosenFiniteKummerRadicalQuotient
      (K := K) (L := L) n hmu
  letI : Fintype D.RadicalQuotient :=
    Fintype.ofFinite D.RadicalQuotient
  exact
    Finset.univ.biUnion fun q =>
      chosenUnitFiniteSupport (K := K)
        (chosenFiniteKummerRadicalRepresentative
          (K := K) (L := L) n q).1

/-- Enlarge any prescribed finite set by the finite supports needed to
represent all actual Kummer radical classes by `S`-units. -/
noncomputable def enlargeByFiniteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  S ∪ finiteKummerRadicalSupport
    (K := K) (L := L) n hmu

/-- The radical-support enlargement contains its starting set. -/
theorem subset_enlargeByFiniteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S ⊆ enlargeByFiniteKummerRadicalSupport
      (K := K) (L := L) n hmu S :=
  Finset.subset_union_left

/-- Each chosen radical representative is an `S`-unit after the chosen
finite enlargement. -/
theorem chosenFiniteKummerRadicalRepresentative_mem_enlargedSUnitGroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1 ∈
      SUnitGroup (K := K)
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S) := by
  apply sUnitGroup_mono
    (K := K)
    (S := chosenUnitFiniteSupport (K := K)
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1)
    (T := enlargeByFiniteKummerRadicalSupport
      (K := K) (L := L) n hmu S)
  · intro v hv
    apply Finset.mem_union_right
    let D :=
      KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n
    let : Finite D.RadicalQuotient :=
      finite_chosenFiniteKummerRadicalQuotient
        (K := K) (L := L) n hmu
    let : Fintype D.RadicalQuotient :=
      Fintype.ofFinite D.RadicalQuotient
    exact Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ q, hv⟩
  · exact mem_sUnitGroup_chosenUnitFiniteSupport
      (K := K)
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1

/-- After the chosen finite enlargement, the actual radical of `L/K`
is generated by its `S`-unit part and the ambient `n`-th powers. -/
theorem finiteKummerRadicalSubgroup_le_enlargedSUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n ≤
      (sUnitKummerSubgroup
        (K := K) (L := L) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S)).1 := by
  intro a ha
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  let aD : D.carrier := ⟨a, ha⟩
  let q : D.RadicalQuotient := D.radicalQuotientMk aD
  let bD : D.carrier :=
    chosenFiniteKummerRadicalRepresentative
      (K := K) (L := L) n q
  have hbclass : D.radicalQuotientMk bD =
      D.radicalQuotientMk aD := by
    exact chosenFiniteKummerRadicalRepresentative_spec
      (K := K) (L := L) n q
  have habpower : aD / bD ∈ D.ambientNthPowersSubgroup := by
    exact (D.radicalQuotientMk_eq_iff aD bD).1 hbclass.symm
  obtain ⟨z, hz⟩ :=
    (D.mem_ambientNthPowersSubgroup_iff).1 habpower
  apply Subgroup.mem_sup.mpr
  refine
    ⟨bD.1,
      ⟨chosenFiniteKummerRadicalRepresentative_mem_enlargedSUnitGroup
          (K := K) (L := L) n hmu S q,
        bD.2⟩,
      z ^ (n : ℕ),
      (KummerTheory.mem_unitNthPowersSubgroup_iff n).2
        ⟨z, rfl⟩,
      ?_⟩
  change bD.1 * z ^ (n : ℕ) = aD.1
  rw [hz]
  change bD.1 * (aD.1 / bD.1) = aD.1
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Exact radical identification after the chosen finite enlargement. -/
theorem enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup
        (K := K) (L := L) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S)).1 =
      KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n :=
  le_antisymm
    (sUnitKummerSubgroup_le_finiteKummerRadicalSubgroup
      (K := K) (L := L) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := L) n hmu S))
    (finiteKummerRadicalSubgroup_le_enlargedSUnitKummerSubgroup
      (K := K) (L := L) n hmu S)

/-- The `S`-unit radical subgroup belonging to an extension is contained
in the full `S`-unit Kummer subgroup. -/
theorem sUnitKummerSubgroup_le_fullSUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup (K := K) (L := L) n S).1 ≤
      (fullSUnitKummerSubgroup (K := K) n S).1 := by
  apply sup_le
  · exact inf_le_left.trans le_sup_left
  · exact le_sup_right

omit numberFieldK in
/-- Monotonicity of the concrete radical-extension construction. -/
theorem kummerRadicalExtension_mono
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (n : ℕ+)
    {Delta Gamma : Subgroup Kˣ}
    (h : Delta ≤ Gamma) :
    KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n Delta ≤
      KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n Gamma := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro beta ⟨a, ha⟩
  apply IntermediateField.subset_adjoin K
    (KummerTheory.kummerRootSet
      (K := K) (Omega := Omega) n Gamma)
  exact ⟨⟨a.1, h a.2⟩, ha⟩

/-- Kummer generation of an abelian exponent-`n` extension from the
`S`-unit radical supplied by the chosen finite enlargement. -/
theorem kummerRadicalExtension_enlargedSUnitKummerSubgroup_eq
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n
        (sUnitKummerSubgroup
          (K := K) (L := E) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)).1 =
      E := by
  rw [
    enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
      (K := K) (L := E) n hmu S]
  exact
    KummerTheory.kummerRadicalExtension_finiteKummerRadicalSubgroup_eq
      E n hmu hexponent

end KummerTheory
