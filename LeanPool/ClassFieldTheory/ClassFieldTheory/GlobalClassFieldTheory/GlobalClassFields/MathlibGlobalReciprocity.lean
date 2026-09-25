/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticClassFieldCorrespondence
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.InfiniteAbelianClassFieldCorrespondence
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidueAbelianization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

/-! # Mathlib Global Reciprocity -/

@[expose] public section
open scoped NumberField
open NumberField IsDedekindDomain

/-!
# Global class field theory implementation

This is the implementation layer for the reader-facing global CFT module.
It collects the existing finite reciprocity, maximal abelian reciprocity,
class-field existence, and infinite correspondence modules without adding
parallel names or existence wrappers.
-/

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

private instance ideleClassGroupIsMulCommutative
    (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The ramified finite primes form a finite set.  Adding every real place
produces a public modulus outside which a number-field extension is
unramified, independently of any Artin-map construction. -/
theorem exists_unramifiedOutsideModulus
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    ∃ m : RayClassModulus K, IsUnramifiedOutsideModulus K L m := by
  classical
  let T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  let S := hT.toFinset
  let f : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => if v ∈ S then 1 else 0
  have hf : ∀ v, f v ≠ 0 → v ∈ S := by
    intro v hv
    by_contra hnot
    exact hv (by simp [f, hnot])
  let m : RayClassModulus K :=
    { finitePart := Finsupp.onFinset S f hf
      infinitePart := Finset.univ }
  refine ⟨m, ?_⟩
  constructor
  · intro v hv Q hQ hlie
    by_contra hram
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have hunder := hlie.over
      rw [hbot, Ideal.under_bot] at hunder
      exact v.ne_bot hunder
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
      ⟨Q, hQ, hQne⟩
    have hvT : v ∈ T := ⟨w, hlie, hram⟩
    have hvS : v ∈ S := hT.mem_toFinset.mpr hvT
    apply hv
    apply Finsupp.mem_support_iff.mpr
    change (Finsupp.onFinset S f hf) v ≠ 0
    rw [Finsupp.onFinset_apply]
    simpa only [f, hvS, ite_true] using (one_ne_zero : (1 : ℕ) ≠ 0)
  · intro v hv hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- The public narrow modulus whose finite part is the actual norm conductor. -/
noncomputable def normConductorRayClassModulus
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] : RayClassModulus K := by
  classical
  exact
    { finitePart :=
        GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := L)
      infinitePart := Finset.univ }

/-- The public norm-conductor modulus is the original narrow modulus. -/
theorem normConductorRayClassModulus_original
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    rayClassModulusToOriginal K (normConductorRayClassModulus K L) =
      RayClass.Modulus.narrowOfFinite
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := L)) := by
  classical
  apply RayClass.Modulus.ext
  · rfl
  · rfl

open GlobalClassFieldTheory.GlobalClassFields renaming
  ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces →
    ideleClassNorm_conductor_support_eq_ramifiedPlaces in
/-- The actual narrow finite norm conductor, together with every real place,
is a public modulus outside which a finite abelian extension is unramified. -/
theorem normConductorRayClassModulus_unramifiedOutside
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    IsUnramifiedOutsideModulus K L (normConductorRayClassModulus K L) := by
  classical
  have hs :=
    ideleClassNorm_conductor_support_eq_ramifiedPlaces
      (K := K) (L := L)
  constructor
  · intro v hv Q hQ hlie
    by_contra hram
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have hunder := hlie.over
      rw [hbot, Ideal.under_bot] at hunder
      exact v.ne_bot hunder
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
      ⟨Q, hQ, hQne⟩
    have hvram : v ∈ _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      exact ⟨w, hlie, hram⟩
    apply hv
    change v ∈
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support
    rw [hs]
    exact hvram
  · intro v hv hnot
    change (⟨v, hv⟩ : RayClassRealPlace K) ∉ Finset.univ at hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- The norm conductor yields a public modulus outside which the extension
is unramified. -/
theorem unramifiedOutside_normConductorModulus
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    ∃ m : RayClassModulus K,
      m.finitePart =
        GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) ∧
        IsUnramifiedOutsideModulus K L m := by
  refine ⟨normConductorRayClassModulus K L, ?_,
    normConductorRayClassModulus_unramifiedOutside K L⟩
  rfl

/-- The public norm-conductor modulus is a defining modulus for the actual
idèle-class norm subgroup. -/
private theorem normConductorRayClassModulus_isDefining
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    RayClass.Modulus.congruenceSubgroup
        (rayClassModulusToOriginal K (normConductorRayClassModulus K L)) ≤
      (_root_.ideleClassNorm K L).range := by
  rw [normConductorRayClassModulus_original K L]
  exact
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_isDefiningModulus
    (K := K) (L := L)

/-- Arithmetic global reciprocity, descended to the public ray class group
at the actual narrow norm conductor. -/
noncomputable def normConductorArtin
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    RayClassGroup (normConductorRayClassModulus K L) →* (L ≃ₐ[K] L) := by
  let m := normConductorRayClassModulus K L
  let m' := rayClassModulusToOriginal K m
  have hm : RayClass.Modulus.congruenceSubgroup m' ≤
      (_root_.ideleClassNorm K L).range := by
    exact normConductorRayClassModulus_isDefining K L
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv.toMonoidHom.comp
    ((GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap
      m' ((_root_.ideleClassNorm K L).range) hm).comp
        (rayClassGroupEquivOriginal K m).toMonoidHom)

/-- The conductor ray-class Artin map is onto the finite abelian Galois group. -/
theorem normConductorArtin_surjective
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    Function.Surjective (normConductorArtin K L) := by
  unfold normConductorArtin
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
    K L).surjective.comp
      ((GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap_surjective
        (rayClassModulusToOriginal K (normConductorRayClassModulus K L))
        ((_root_.ideleClassNorm K L).range)
        (normConductorRayClassModulus_isDefining K L)).comp
        (rayClassGroupEquivOriginal K (normConductorRayClassModulus K L)).surjective)

open GlobalClassFieldTheory.IdealClassFieldTheory renaming
  arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin →
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin in
/-- At a prime away from the norm conductor, the public Artin map agrees
with the arithmetic prime Artin element of the original idèle theory. -/
theorem normConductorArtin_prime
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (normConductorRayClassModulus K L).finitePart.support) :
    normConductorArtin K L
        (rayClassOfFinitePrime (normConductorRayClassModulus K L) v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v := by
  let m := normConductorRayClassModulus K L
  let m' := rayClassModulusToOriginal K m
  have hm : RayClass.Modulus.congruenceSubgroup m' ≤
      (_root_.ideleClassNorm K L).range := by
    exact normConductorRayClassModulus_isDefining K L
  have hv' : v ∉ m'.finitePart.support := hv
  change
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L)
      (GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap
        m' ((_root_.ideleClassNorm K L).range) hm
        (rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv))) = _
  rw [rayClassGroupEquivOriginal_prime K m v hv]
  change GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m' hm
      (RayClass.primeToModulusIdeal m' v hv') = _
  exact
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin
    (K := K) (L := L) m' hm v hv'

/-- The class field selected from a closed finite-index idèle-class subgroup
has exactly that subgroup as its norm group. -/
theorem classFieldExistence_normSubgroup
    (K : Type) [Field K] [NumberField K]
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
        (GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
          (K := K) H hclosed)).range = H :=
  GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_ideleClassNorm_range
    H hclosed

/-- The degree of the selected class field is the index of its defining
idèle-class subgroup. -/
theorem classFieldExistence_degree
    (K : Type) [Field K] [NumberField K]
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module.finrank K
        (GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField
          (K := K) H hclosed) = H.index :=
  GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_finrank_eq_index
    H hclosed

/-- The implemented arithmetic norm-residue isomorphism proves finite
abelian global reciprocity in quotient form. -/
theorem finiteAbelianGlobalReciprocity
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Nonempty
      ((IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range) ≃ₜ*
        (L ≃ₐ[K] L)) := by
  exact
    ⟨GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L⟩

/-- Maximal abelian reciprocity after quotienting by the identity
component. -/
theorem maximalAbelianGlobalReciprocity
    (K : Type) [Field K] [NumberField K] :
    Nonempty
      (ideleClassComponentQuotient K ≃ₜ*
        (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)) := by
  exact
    ⟨GlobalClassFieldTheory.Reciprocity.ideleClassComponentQuotientEquivMaximalAbelianGalois K⟩

end ClassFieldTheory.GlobalClassFieldComparison
