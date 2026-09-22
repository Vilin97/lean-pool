/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue
/-!
# Principal ideles and the rational cyclotomic value

This file isolates the part of the rational principal-idele product
formula which follows from the existing archimedean reciprocity API.
Every rational idele is split into its archimedean and finite parts.
The archimedean part has Artin image of order at most two at every
finite layer; the actual Galois group of the rational `ZHat`-extension
is torsion-free, so its image in that extension is trivial.

Consequently the rational cyclotomic value of a principal idele is
exactly the value of its finite part.  At every finite cyclotomic layer
that remaining value is the genuine finite product of the chosen local
Artin maps.  Proving that product trivial requires a pointwise
compatibility theorem between the chosen finite-place Artin map and
the explicit cyclotomic action; no such compatibility is assumed here.
-/

open scoped BigOperators NumberField IsMulCommutative
open NumberField IsDedekindDomain ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Keep the prime-power presentation explicit for canonical instance synthesis.
-- Both structures are the existing canonical cyclotomic-level instances.
open scoped Classical in
local instance rationalCyclotomicPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrimePowerNumberField

open scoped Classical in
local instance rationalCyclotomicPrimePowerIsGalois
    (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_isGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrimePowerIsGalois

open scoped Classical in
local instance rationalCyclotomicPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
  IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  IsAbelianGalois.of_algHom
    (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩).val

attribute [local instance] rationalCyclotomicPrimePowerIsAbelianGalois

open scoped Classical in
local instance localPrimesInstance1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] localPrimesInstance1

open scoped Classical in
noncomputable local instance
    cyclotomicPrincipalLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  let e :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
  exact
    { is_comm.comm σ τ := by
        apply e.injective
        simp only [map_mul]
        exact mul_comm _ _ }

attribute [local instance] cyclotomicPrincipalLevelIsAbelianGalois

open scoped Classical in
/-- Every finite subextension of the rational cyclotomic closure is
contained in one of its internal finite cyclotomic levels.  The proof
uses finite generation of the intermediate field together with the
divisibility-directed presentation of `ℚ(μ∞)`. -/
theorem finiteSubfieldOfRationalCyclotomicField_le_level
    (E :
      IntermediateField ℚ
        KummerTheory.rationalCyclotomicField)
    [FiniteDimensional ℚ E] :
    ∃ n : ℕ+,
      E ≤ KummerTheory.rationalCyclotomicLevel n := by
  classical
  have hdirected :
      Directed (· ≤ ·)
        (KummerTheory.rationalCyclotomicLevel :
          ℕ+ →
            IntermediateField ℚ
              KummerTheory.rationalCyclotomicField) := by
    intro m n
    refine ⟨m * n, ?_, ?_⟩
    · apply KummerTheory.rationalCyclotomicLevel_mono
      exact ⟨(n : ℕ), rfl⟩
    · apply KummerTheory.rationalCyclotomicLevel_mono
      exact ⟨(m : ℕ), by simp [Nat.mul_comm]⟩
  have helement :
      ∀ x : KummerTheory.rationalCyclotomicField,
        ∃ n : ℕ+,
          x ∈ KummerTheory.rationalCyclotomicLevel n := by
    intro x
    have hx :
        x ∈
          ⋃ n : ℕ+,
            (KummerTheory.rationalCyclotomicLevel n :
              Set KummerTheory.rationalCyclotomicField) := by
      rw [← IntermediateField.coe_iSup_of_directed hdirected,
        KummerTheory.iSup_rationalCyclotomicLevel]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩
  let levelIndex :
      KummerTheory.rationalCyclotomicField → ℕ+ :=
    fun x => Classical.choose (helement x)
  have hlevelIndex
      (x : KummerTheory.rationalCyclotomicField) :
      x ∈
        KummerTheory.rationalCyclotomicLevel
          (levelIndex x) :=
    Classical.choose_spec (helement x)
  have hmoduleFinite : E.toSubmodule.FG :=
    Submodule.FG.of_finite
  have hfg : E.FG :=
    E.fg_of_fg_toSubalgebra
      (Subalgebra.fg_of_fg_toSubmodule hmoduleFinite)
  obtain ⟨s, hsFinite, hsE⟩ :=
    IntermediateField.fg_def.mp hfg
  let t : Finset KummerTheory.rationalCyclotomicField :=
    hsFinite.toFinset
  let N : ℕ :=
    ∏ x ∈ t, (levelIndex x : ℕ)
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Finset.prod_pos fun x _ => (levelIndex x).property
  let n : ℕ+ := ⟨N, hNpos⟩
  refine ⟨n, ?_⟩
  rw [← hsE, IntermediateField.adjoin_le_iff]
  intro x hx
  have hxt : x ∈ t := by
    simpa only [t, Set.Finite.mem_toFinset] using hx
  have hdiv :
      (levelIndex x : ℕ) ∣ (n : ℕ) := by
    change
      (levelIndex x : ℕ) ∣
        ∏ y ∈ t, (levelIndex y : ℕ)
    exact
      Finset.dvd_prod_of_mem
        (fun y => (levelIndex y : ℕ)) hxt
  exact
    KummerTheory.rationalCyclotomicLevel_mono hdiv
      (hlevelIndex x)

open scoped Classical in
/-- Every finite Galois coordinate of the rational cyclotomic
`ZHat`-extension has a canonical image inside a finite internal
cyclotomic level.  The image field is retained explicitly so that
restriction of actual global Artin automorphisms can be applied in a
scalar tower. -/
theorem finiteSubfieldOfRationalCyclotomicZHatField_mapsIntoLevel
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    ∃ (n : ℕ+)
        (F :
          IntermediateField ℚ
            KummerTheory.rationalCyclotomicField)
        (_e : E ≃ₐ[ℚ] F),
      F ≤ KummerTheory.rationalCyclotomicLevel n := by
  let hfull :
      rationalCyclotomicZHatField ≤
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.lift_le
      KummerTheory.rationalCyclotomicTorsionFixedField
  let i :
      rationalCyclotomicZHatField →ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.inclusion hfull
  let F :
      IntermediateField ℚ
        KummerTheory.rationalCyclotomicField :=
    (E : IntermediateField ℚ
      rationalCyclotomicZHatField).map i
  let e : E ≃ₐ[ℚ] F :=
    IntermediateField.equivMap
      (E : IntermediateField ℚ
        rationalCyclotomicZHatField) i
  let _ : FiniteDimensional ℚ F :=
    e.toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ :=
    finiteSubfieldOfRationalCyclotomicField_le_level F
  exact ⟨n, F, e, hn⟩

open scoped Classical in
/-- Restriction to the lifted torsion-free cyclotomic field commutes with its
canonical inclusion into the full rational cyclotomic field.  Keeping this
pointwise compatibility separate prevents the finite-coordinate Artin
comparison below from accumulating the cost of unfolding the lift. -/
private theorem rationalCyclotomicFullRestrictionToZHat_commutes
    (σ : KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicField)
    (x : rationalCyclotomicZHatField) :
    (IntermediateField.inclusion
        (IntermediateField.lift_le
          KummerTheory.rationalCyclotomicTorsionFixedField))
        (rationalCyclotomicFullRestrictionToZHat σ x) =
      σ
        ((IntermediateField.inclusion
          (IntermediateField.lift_le
            KummerTheory.rationalCyclotomicTorsionFixedField)) x) := by
  let T := KummerTheory.rationalCyclotomicTorsionFixedField
  let hTZ : IntermediateField.lift T ≤
      KummerTheory.rationalCyclotomicField :=
    IntermediateField.lift_le T
  let φ := IntermediateField.liftAlgEquiv T
  let _ : Normal ℚ T := by
    dsimp only [T]
    exact KummerTheory.rationalCyclotomicTorsionFixedField_normal
  let rσ : T ≃ₐ[ℚ] T :=
    AlgEquiv.restrictNormalHom T σ
  change
    (IntermediateField.inclusion hTZ) (φ.autCongr rσ x) =
      σ ((IntermediateField.inclusion hTZ) x)
  have hlift (y : T) :
      (IntermediateField.inclusion hTZ) (φ y) = y.1 := by
    apply Subtype.ext
    rfl
  have hinv :
      ((φ.symm x : T) : KummerTheory.rationalCyclotomicField) =
        (IntermediateField.inclusion hTZ) x := by
    apply Subtype.ext
    rfl
  calc
    (IntermediateField.inclusion hTZ) (φ.autCongr rσ x) =
        (IntermediateField.inclusion hTZ) (φ (rσ (φ.symm x))) := by
      rfl
    _ = (rσ (φ.symm x) : T) := hlift _
    _ = σ ((φ.symm x : T) :
          KummerTheory.rationalCyclotomicField) := by
      exact AlgEquiv.restrictNormalHom_apply T σ (φ.symm x)
    _ = σ ((IntermediateField.inclusion hTZ) x) :=
      congrArg σ hinv

open scoped Classical in
/-- Restriction along the two sides of a commuting tower square gives the
same automorphism of the finite bottom field.  Keeping the field types
abstract makes this a stable interface for concrete inverse-limit fields. -/
private theorem restrictNormalHom_eq_of_commuting_square
    (K E Z Ω : Type*)
    [Field K] [Field E] [Field Z] [Field Ω]
    [Algebra K E] [Algebra K Z] [Algebra K Ω]
    [Algebra E Z] [Algebra E Ω] [Algebra Z Ω]
    [IsScalarTower K E Z] [IsScalarTower K E Ω]
    [IsScalarTower E Z Ω]
    [Normal K E]
    (τ : Z ≃ₐ[K] Z) (σ : Ω ≃ₐ[K] Ω)
    (hcommutes : ∀ z : Z,
      algebraMap Z Ω (τ z) = σ (algebraMap Z Ω z)) :
    AlgEquiv.restrictNormalHom E τ =
      AlgEquiv.restrictNormalHom E σ := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  calc
    algebraMap E Ω ((AlgEquiv.restrictNormalHom E τ) x) =
        algebraMap Z Ω
          (algebraMap E Z ((AlgEquiv.restrictNormalHom E τ) x)) :=
      IsScalarTower.algebraMap_apply E Z Ω _
    _ = algebraMap Z Ω (τ (algebraMap E Z x)) :=
      congrArg (algebraMap Z Ω)
        (AlgEquiv.restrictNormal_commutes τ E x)
    _ = σ (algebraMap Z Ω (algebraMap E Z x)) :=
      hcommutes _
    _ = σ (algebraMap E Ω x) :=
      congrArg σ (IsScalarTower.algebraMap_apply E Z Ω x).symm
    _ = algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ) x) :=
      (AlgEquiv.restrictNormal_commutes σ E x).symm

open scoped Classical in
/-- The infinite Artin automorphism of the actual rational
`ZHat`-field is the restriction of the infinite Artin automorphism of
the full rational cyclotomic field.  The statement uses the genuine
torsion-fixed subfield and its actual lift inside `SeparableClosure ℚ`. -/
theorem rationalCyclotomicZHatGlobalArtin_eq_fullRestriction
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatGlobalArtin a =
      rationalCyclotomicFullRestrictionToZHat
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField a) := by
  let hfull :
      rationalCyclotomicZHatField ≤
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.lift_le
      KummerTheory.rationalCyclotomicTorsionFixedField
  let i :
      rationalCyclotomicZHatField →ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.inclusion hfull
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  let E := Eop.unop
  let hENumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let hEAbelian : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom
      (E : IntermediateField ℚ
        rationalCyclotomicZHatField).val
  let : NumberField E := hENumberField
  let : IsAbelianGalois ℚ E := hEAbelian
  let σ : KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicField :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  let j : E →ₐ[ℚ] KummerTheory.rationalCyclotomicField :=
    i.comp
      (E : IntermediateField ℚ
        rationalCyclotomicZHatField).val
  let algZHatFull : Algebra rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    i.toRingHom.toAlgebra
  let _ : SMul rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    @Algebra.toSMul rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField _ _ algZHatFull
  let _ : Algebra rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    algZHatFull
  let _ : IsScalarTower ℚ rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algHom i
  let algEFull : Algebra E
      KummerTheory.rationalCyclotomicField :=
    j.toRingHom.toAlgebra
  let _ : SMul E KummerTheory.rationalCyclotomicField :=
    @Algebra.toSMul E
      KummerTheory.rationalCyclotomicField _ _ algEFull
  let _ : Algebra E KummerTheory.rationalCyclotomicField :=
    algEFull
  let _ : IsScalarTower ℚ E
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algHom j
  let _ : IsScalarTower E rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htransport :
      AlgEquiv.restrictNormalHom E
          (rationalCyclotomicFullRestrictionToZHat σ) =
        AlgEquiv.restrictNormalHom E σ := by
    apply restrictNormalHom_eq_of_commuting_square
      ℚ E rationalCyclotomicZHatField
        KummerTheory.rationalCyclotomicField
    intro x
    exact rationalCyclotomicFullRestrictionToZHat_commutes σ x
  have hfullArtin :
      AlgEquiv.restrictNormalHom E σ =
        globalArtinMonoidHom (K := ℚ) (L := E) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
      ℚ E KummerTheory.rationalCyclotomicField a
  change
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      AlgEquiv.restrictNormalHom E
        (rationalCyclotomicFullRestrictionToZHat
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a))
  calc
    AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin a) =
        globalArtinMonoidHom (K := ℚ) (L := E) a :=
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin a E
    _ = AlgEquiv.restrictNormalHom E σ :=
      hfullArtin.symm
    _ = AlgEquiv.restrictNormalHom E
          (rationalCyclotomicFullRestrictionToZHat σ) :=
      htransport.symm

open scoped Classical in
/-- The rational cyclotomic idele value is the genuine torsion-free
factor of the full cyclotomic character of its infinite Artin symbol. -/
theorem rationalCyclotomicZHatIdeleValue_eq_fullCharacterFreePart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a))).1 := by
  rw [rationalCyclotomicZHatIdeleValue_apply,
    rationalCyclotomicZHatGlobalArtin_eq_fullRestriction,
    rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction]

open scoped Classical in
/-- The archimedean part of a rational idele, with all finite
components replaced by one. -/
def rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    IdeleGroup ℚ :=
  (a.1, 1)

open scoped Classical in
/-- The finite part of a rational idele, with its archimedean
component replaced by one. -/
def rationalIdeleFinitePart
    (a : IdeleGroup ℚ) :
    IdeleGroup ℚ :=
  (1, a.2)

open scoped Classical in
/-- The archimedean part preserves every infinite component. -/
theorem rationalIdeleArchimedeanPart_infiniteComponent
    (a : IdeleGroup ℚ)
    (v : InfinitePlace ℚ) :
    IdeleGroup.infiniteComponent v
        (rationalIdeleArchimedeanPart a) =
      IdeleGroup.infiniteComponent v a :=
  rfl

open scoped Classical in
/-- Every finite component of the archimedean part is one. -/
theorem rationalIdeleArchimedeanPart_finiteComponent
    (a : IdeleGroup ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalIdeleArchimedeanPart a) =
      1 :=
  rfl

open scoped Classical in
/-- Every infinite component of the finite part is one. -/
theorem rationalIdeleFinitePart_infiniteComponent
    (a : IdeleGroup ℚ)
    (v : InfinitePlace ℚ) :
    IdeleGroup.infiniteComponent v
        (rationalIdeleFinitePart a) =
      1 :=
  rfl

open scoped Classical in
/-- The finite part preserves every finite component. -/
theorem rationalIdeleFinitePart_finiteComponent
    (a : IdeleGroup ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalIdeleFinitePart a) =
      IdeleGroup.finiteComponent v a :=
  rfl

open scoped Classical in
private theorem globalArtinMonoidHom_rationalIdeleFinitePart
    {L : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [IsAbelianGalois ℚ L]
    (a : IdeleGroup ℚ) :
    globalArtinMonoidHom (K := ℚ) (L := L)
        (rationalIdeleFinitePart a) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v a) := by
  rw [globalArtinMonoidHom_apply, Fintype.prod_unique]
  have harch (v : InfinitePlace ℚ) :
      chosenInfinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.infiniteComponent v
            (rationalIdeleFinitePart a)) =
        1 := by
    rw [rationalIdeleFinitePart_infiniteComponent, map_one]
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v
            (rationalIdeleFinitePart a))) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          chosenFinitePlaceArtinMonoidHom
            (K := ℚ) (L := L) v
            (IdeleGroup.finiteComponent v a) := by
    apply finprod_congr
    intro v
    rw [rationalIdeleFinitePart_finiteComponent]
  rw [harch, one_mul, hfinite]

open scoped Classical in
/-- The archimedean and finite parts multiply back to the original
rational idele. -/
theorem rationalIdeleArchimedeanPart_mul_finitePart
    (a : IdeleGroup ℚ) :
    rationalIdeleArchimedeanPart a *
        rationalIdeleFinitePart a =
      a := by
  ext <;> simp [rationalIdeleArchimedeanPart,
    rationalIdeleFinitePart]

open scoped Classical in
/-- At a finite abelian layer, the global Artin image of the
archimedean part of a rational idele has order at most two. -/
theorem globalArtinMonoidHom_rationalIdeleArchimedeanPart_sq
    {L : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [IsAbelianGalois ℚ L]
    (a : IdeleGroup ℚ) :
    globalArtinMonoidHom
          (K := ℚ) (L := L)
          (rationalIdeleArchimedeanPart a) ^ 2 =
      1 := by
  rw [globalArtinMonoidHom_apply, Fintype.prod_unique]
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v
            (rationalIdeleArchimedeanPart a))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [rationalIdeleArchimedeanPart_finiteComponent,
      map_one]
  rw [hfinite, mul_one]
  rw [show (default : InfinitePlace ℚ) = Rat.infinitePlace by
    exact Subsingleton.elim _ _]
  rw [← map_pow]
  apply
    chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
      (K := ℚ) (L := L)
      Rat.infinitePlace Rat.isReal_infinitePlace
  have hne :
      InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent
            Rat.infinitePlace
            (rationalIdeleArchimedeanPart a) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) ≠
        0 := by
    exact
      (map_ne_zero
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace)).2
        (Units.ne_zero
          (IdeleGroup.infiniteComponent
            Rat.infinitePlace
            (rationalIdeleArchimedeanPart a)))
  simpa only [Units.val_pow_eq_pow_val, map_pow] using
    sq_pos_of_ne_zero hne

open scoped Classical in
/-- The actual rational `ZHat` Artin homomorphism kills every idele
supported at the archimedean place.  The finite-layer images have
order at most two, while the inverse-limit Galois group is
torsion-free. -/
@[simp]
theorem
    rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatGlobalArtin
        (rationalIdeleArchimedeanPart a) =
      1 := by
  let _
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      NumberField E :=
    NumberField.of_module_finite ℚ E
  let _
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  have hsq :
      rationalCyclotomicZHatGlobalArtin
          (rationalIdeleArchimedeanPart a) ^ 2 =
        1 := by
    have happly :
        InfiniteGalois.continuousMulEquivToLimit
            ℚ rationalCyclotomicZHatField
            (rationalCyclotomicZHatGlobalArtin
              (rationalIdeleArchimedeanPart a)) =
          infiniteGlobalArtinToLimit
            ℚ rationalCyclotomicZHatField
            (rationalIdeleArchimedeanPart a) := by
      exact
        (InfiniteGalois.continuousMulEquivToLimit
          ℚ rationalCyclotomicZHatField).apply_symm_apply _
    apply
      (InfiniteGalois.continuousMulEquivToLimit
        ℚ rationalCyclotomicZHatField).injective
    rw [map_pow, happly, map_one]
    apply Subtype.ext
    funext E
    exact
      globalArtinMonoidHom_rationalIdeleArchimedeanPart_sq
        (L := E.unop) a
  exact
    (pow_left_injective
      (M :=
        rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField)
      (n := 2) (by norm_num))
        (by simpa using hsq)

open scoped Classical in
/-- The rational cyclotomic value kills the archimedean part of every
rational idele. -/
theorem
    rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue
        (rationalIdeleArchimedeanPart a) =
      1 := by
  rw [rationalCyclotomicZHatIdeleValue_apply,
    rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart,
    map_one]

open scoped Classical in
/-- The rational cyclotomic value depends only on the finite part of
an idele. -/
theorem rationalCyclotomicZHatIdeleValue_eq_finitePart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart a) := by
  calc
    rationalCyclotomicZHatIdeleValue a =
        rationalCyclotomicZHatIdeleValue
          (rationalIdeleArchimedeanPart a *
            rationalIdeleFinitePart a) :=
      congrArg rationalCyclotomicZHatIdeleValue
        (rationalIdeleArchimedeanPart_mul_finitePart a).symm
    _ = rationalCyclotomicZHatIdeleValue
          (rationalIdeleArchimedeanPart a) *
        rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart a) :=
      (rationalCyclotomicZHatIdeleValue).map_mul _ _
    _ = rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart a) := by
      rw [
        rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart,
        one_mul]

open scoped Classical in
/-- Restriction of the infinite Artin symbol to a concrete prime-power
cyclotomic level is its finite global Artin symbol. -/
private theorem rationalCyclotomicGlobalArtin_restrict_primePowerLevel
    (a : IdeleGroup ℚ) (p : Nat.Primes) (k : ℕ) :
    AlgEquiv.restrictNormalHom
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField a) =
      globalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_intermediateField
      ℚ KummerTheory.rationalCyclotomicField a
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)

open scoped Classical in
/-- Applying the prime-power cyclotomic character to a finite projection of
the infinite Artin symbol gives the finite global Artin symbol.  This is kept
separate from character evaluation so both dependent comparisons elaborate
within the default heartbeat budget. -/
private theorem rationalCyclotomicGlobalArtin_projection_toZModPow
    (a : IdeleGroup ℚ) (p : Nat.Primes) (k : ℕ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        ((infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a).restrictNormal
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (globalArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          a) := by
  exact
    congrArg
      (IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩))
      (rationalCyclotomicGlobalArtin_restrict_primePowerLevel a p k)

open scoped Classical in
/-- Evaluating the actual infinite global Artin symbol in the full
rational cyclotomic extension at the `p ^ k` cyclotomic character is
exactly the finite global Artin symbol at the internal `p ^ k`-th
cyclotomic level.  This is the field-theoretic bridge from the inverse
limit Artin map to the explicit cyclotomic character. -/
theorem rationalCyclotomicGlobalArtin_character_toZModPow
    (a : IdeleGroup ℚ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a) p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (globalArtinMonoidHom
          (K := ℚ)
          (L :=
            KummerTheory.rationalCyclotomicLevel
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          a) := by
  exact
    (KummerTheory.rationalCyclotomicCharacterPrimeProduct_toZModPow
      (infiniteGlobalArtinMonoidHom
        ℚ KummerTheory.rationalCyclotomicField a) p k).trans
      (rationalCyclotomicGlobalArtin_projection_toZModPow a p k)

open scoped Classical in
/-- After removing the archimedean component, the `p ^ k` coordinate
of the full rational cyclotomic Artin character is the genuine finite
product of the chosen finite-place Artin maps. -/
theorem rationalCyclotomicGlobalArtin_character_toZModPow_finitePart
    (a : IdeleGroup ℚ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (rationalIdeleFinitePart a)) p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v a)) := by
  rw [
    rationalCyclotomicGlobalArtin_character_toZModPow,
    globalArtinMonoidHom_rationalIdeleFinitePart]

open scoped Classical in
/-- The finite-part cyclotomic character is the `finprod` of the
actual chosen local Artin characters.  This is the pointwise form into
which the p-adic unit formula and the unramified Frobenius formula
substitute directly. -/
theorem
    rationalCyclotomicGlobalArtin_character_toZModPow_finitePart_eq_finprod
    (a : IdeleGroup ℚ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (rationalIdeleFinitePart a)) p) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v a)) := by
  rw [rationalCyclotomicGlobalArtin_character_toZModPow_finitePart]
  exact
    MonoidHom.map_finprod
      (IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)).toMonoidHom
      (finitePlaceArtinFactors_hasFiniteMulSupport
        (K := ℚ)
        (L :=
          KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        a)

open scoped Classical in
/-- Principal-idele evaluation reduced to its genuine finite local
part. -/
theorem
    rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (IdeleGroup.principalIdele ℚ x) =
      rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart
          (IdeleGroup.principalIdele ℚ x)) :=
  rationalCyclotomicZHatIdeleValue_eq_finitePart
    (IdeleGroup.principalIdele ℚ x)

open scoped Classical in
/-- At a finite cyclotomic layer, the Artin image of the finite part
of a rational idele is exactly the finite product of the chosen local
Artin symbols. -/
theorem
    restrictNormalHom_rationalCyclotomicZHatGlobalArtin_finitePart
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois ℚ E :=
      IsAbelianGalois.of_algHom E.toIntermediateField.val
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin
          (rationalIdeleFinitePart a)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := E) v
          (IdeleGroup.finiteComponent v a) := by
  let hE : NumberField E :=
    NumberField.of_module_finite ℚ E
  let hAbelian : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  let _ : NumberField E := hE
  let _ : IsAbelianGalois ℚ E := hAbelian
  exact
    (restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
      (rationalIdeleFinitePart a) E hE hAbelian).trans
      (globalArtinMonoidHom_rationalIdeleFinitePart
        (L := E) a)

open scoped Classical in
/-- The unnormalized value on a principal idele over a number field
is the rational cyclotomic value of the finite part of its field-norm
principal idele. -/
theorem cyclotomicZHatNormComposite_principalIdele_eq_finitePart
    (K : Type) [Field K] [NumberField K]
    (x : Kˣ) :
    cyclotomicZHatNormComposite K
        (Additive.ofMul
          (IdeleGroup.principalIdele K x)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart
            (IdeleGroup.principalIdele ℚ
              (Units.map (Algebra.norm ℚ) x)))) := by
  rw [cyclotomicZHatNormComposite_apply,
    IdeleGroup.norm_principalIdele,
    rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart]

open scoped Classical in
/-- Normalized principal-idele vanishing is equivalent to the
remaining rational finite-part product formula.  Thus the only missing
input for descent to the idele class group is the finite local
cyclotomic compatibility, not an archimedean calculation. -/
theorem
    normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero_iff_finitePart
    (K : Type) [Field K] [NumberField K]
    (x : Kˣ) :
    normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul
            (IdeleGroup.principalIdele K x)) =
        0 ↔
      rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart
            (IdeleGroup.principalIdele ℚ
              (Units.map (Algebra.norm ℚ) x))) =
        1 := by
  constructor
  · intro hzero
    have hnormalize :=
      cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
        K
        (Additive.ofMul
          (IdeleGroup.principalIdele K x))
    rw [hzero, smul_zero,
      cyclotomicZHatNormComposite_principalIdele_eq_finitePart]
        at hnormalize
    simpa using hnormalize.symm
  · intro hfinite
    apply
      zHatMulNat_injective
        (cyclotomicZHatIntersectionDegree_pos K)
    rw [zHatMulNat_apply, zHatMulNat_apply,
      cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue,
      cyclotomicZHatNormComposite_principalIdele_eq_finitePart,
      hfinite, smul_zero]
    rfl

end Reciprocity
end GlobalClassFieldTheory
