/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
/-!
# The Herbrand quotient of the global S-unit group

This file computes the Herbrand quotient of the global `S`-unit group. It connects the actual
`S`-unit group to its logarithmic lattice, adds the invariant diagonal
integer direction, and combines the resulting exact sequences with the
permutation-lattice calculation.
-/

@[expose] public section

open scoped BigOperators NumberField nonZeroDivisors Pointwise
open IsDedekindDomain Module

noncomputable
section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LogarithmicQuotient

open scoped Classical in
/-- The additive Galois action restricted to the actual full
logarithmic lattice. -/
@[reducible]
noncomputable def fullLogLatticeDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.fullLogLattice (K := L) S) := by
  letI := sUnitMulDistribMulAction K L S hS
  letI := additiveSUnitDistribMulAction K L S hS
  letI := logPlaceMulAction K L S hS
  letI := fullLogSpaceDistribMulAction K L S hS
  letI := logHyperplaneDistribMulAction K L S hS
  exact
    { smul := fun σ z =>
        ⟨σ • (z :
            SUnitGroup.LogHyperplane (K := L) S),
          fullLogLattice_smul_mem K L hS
            σ z.1 z.2⟩
      one_smul := by
        intro z
        apply Subtype.ext
        exact one_smul (L ≃ₐ[K] L)
          (z : SUnitGroup.LogHyperplane (K := L) S)
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact mul_smul σ τ
          (z : SUnitGroup.LogHyperplane (K := L) S)
      smul_zero := by
        intro σ
        apply Subtype.ext
        exact DistribMulAction.smul_zero σ
      smul_add := by
        intro σ z z'
        apply Subtype.ext
        exact DistribMulAction.smul_add σ
          (z : SUnitGroup.LogHyperplane (K := L) S)
          (z' : SUnitGroup.LogHyperplane (K := L) S) }

open scoped Classical in
/-- The full logarithm as a surjective multiplicative homomorphism
from `S`-units onto the multiplicative logarithmic lattice. -/
noncomputable def sUnitFullLogMulHom
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup (K := L) S →*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S) where
  toFun x :=
    Multiplicative.ofAdd
      ⟨SUnitGroup.fullLog (K := L) S
          (Additive.ofMul x), by
        rw [SUnitGroup.fullLogLattice_eq_range]
        exact ⟨Additive.ofMul x, rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_zero
      (SUnitGroup.fullLog (K := L) S)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_add
      (SUnitGroup.fullLog (K := L) S)
      (Additive.ofMul x) (Additive.ofMul y)

open scoped Classical in
/-- The multiplicative full logarithm is onto its defining lattice. -/
theorem sUnitFullLogMulHom_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective
      (sUnitFullLogMulHom L S) := by
  intro z
  have hz :
      (Multiplicative.toAdd z :
          SUnitGroup.fullLogLattice (K := L) S).1 ∈
        LinearMap.range
          (SUnitGroup.fullLog (K := L) S).toIntLinearMap := by
    rw [← SUnitGroup.fullLogLattice_eq_range]
    exact
      (Multiplicative.toAdd z :
        SUnitGroup.fullLogLattice (K := L) S).2
  obtain ⟨x, hx⟩ := hz
  refine ⟨Additive.toMul x, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change
    SUnitGroup.fullLog (K := L) S x =
      (Multiplicative.toAdd z :
        SUnitGroup.fullLogLattice (K := L) S).1
  exact hx

open scoped Classical in
/-- The kernel of the multiplicative full logarithm is exactly the
torsion subgroup of the `S`-unit group. -/
theorem sUnitFullLogMulHom_ker
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (sUnitFullLogMulHom L S).ker =
      CommGroup.torsion
        (SUnitGroup (K := L) S) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxlog :
        SUnitGroup.fullLog (K := L) S
            (Additive.ofMul x) = 0 := by
      have hx' :=
        congrArg
          (fun z :
              Multiplicative
                (SUnitGroup.fullLogLattice
                  (K := L) S) =>
            ((Multiplicative.toAdd z :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S))
          hx
      exact hx'
    have hxt :=
      (SUnitGroup.fullLog_eq_zero_iff
        (K := L) S (Additive.ofMul x)).mp hxlog
    change IsOfFinOrder x
    exact isOfFinAddOrder_ofMul_iff.mp hxt
  · intro hxt
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply
      (SUnitGroup.fullLog_eq_zero_iff
        (K := L) S (Additive.ofMul x)).mpr
    change IsOfFinAddOrder (Additive.ofMul x)
    exact isOfFinAddOrder_ofMul_iff.mpr hxt

omit [NumberField K] in
open scoped Classical in
/-- The multiplicative full logarithm is equivariant for the actual
Galois actions. -/
theorem sUnitFullLogMulHom_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _sUnitAction :=
      sUnitMulDistribMulAction K L S hS
    letI _latticeAction :=
      fullLogLatticeDistribMulAction K L S hS
    letI _multiplicativeLatticeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (x : SUnitGroup (K := L) S),
      sUnitFullLogMulHom L S (σ • x) =
        σ • sUnitFullLogMulHom L S x := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let multiplicativeLatticeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  intro σ x
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact fullLog_smul K L hS σ (Additive.ofMul x)

open scoped Classical in
/-- Ordinary roots of unity identify with the torsion subgroup of the
`S`-unit group. -/
noncomputable def rootsOfUnityEquivSUnitTorsion
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    NumberField.Units.torsion L ≃*
      CommGroup.torsion
        (SUnitGroup (K := L) S) :=
  ((NumberField.Units.torsion L).equivMapOfInjective
      (SUnitGroup.fromNumberFieldUnits (K := L) S)
      (SUnitGroup.fromNumberFieldUnits_injective
        (K := L) S)).trans
    (MulEquiv.subgroupCongr
      (SUnitGroup.torsion_eq_rootsOfUnity_range
        (K := L) S).symm)

open scoped Classical in
/-- Torsion in an `S`-unit group over a number field is finite. -/
theorem sUnitTorsionFinite
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Finite
      (CommGroup.torsion
        (SUnitGroup (K := L) S)) :=
  Finite.of_equiv
    (NumberField.Units.torsion L)
    (rootsOfUnityEquivSUnitTorsion L S).toEquiv

omit [NumberField K] in
open scoped Classical in
/-- The torsion subgroup is stable under Galois automorphisms. -/
theorem sUnitTorsion_stable
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _sUnitAction :=
      sUnitMulDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (x : SUnitGroup (K := L) S),
      x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) →
        σ • x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  intro σ x hx
  exact
    CommGroup.le_comap_torsion
      (MulDistribMulAction.toMonoidHom
        (SUnitGroup (K := L) S) σ) hx

open scoped Classical in
/-- Exactness of torsion inclusion followed by the full logarithm. -/
theorem sUnitTorsion_fullLog_exact
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    ∀ x : SUnitGroup (K := L) S,
      sUnitFullLogMulHom L S x = 1 ↔
        ∃ t :
            CommGroup.torsion
              (SUnitGroup (K := L) S),
          (CommGroup.torsion
            (SUnitGroup (K := L) S)).subtype t = x := by
  intro x
  constructor
  · intro hx
    have hxt :
        x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) := by
      rw [← sUnitFullLogMulHom_ker L S]
      exact hx
    exact ⟨⟨x, hxt⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    have ht :
        ((t :
            CommGroup.torsion
              (SUnitGroup (K := L) S)) :
          SUnitGroup (K := L) S) ∈
            (sUnitFullLogMulHom L S).ker := by
      rw [sUnitFullLogMulHom_ker L S]
      exact t.2
    exact ht

end LogarithmicQuotient

section DiagonalExtension

open scoped Classical in
/-- Membership in the product lattice is exactly integrality in the
logarithmic lattice and in the diagonal coordinate. -/
theorem mem_fullLogHyperplaneDiagonalLattice_iff
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (z :
      SUnitGroup.LogHyperplane (K := L) S × ℝ) :
    z ∈ fullLogHyperplaneDiagonalLattice L S ↔
      z.1 ∈ SUnitGroup.fullLogLattice (K := L) S ∧
        ∃ n : ℤ, (n : ℝ) = z.2 := by
  let b :=
    fullLogHyperplaneDiagonalBasis L S
  constructor
  · intro hz
    have hzrepr :
        ∀ i, b.repr z i ∈
          Set.range (algebraMap ℤ ℝ) :=
      (b.mem_span_iff_repr_mem ℤ _).mp hz
    have hzfirst :
        z.1 ∈
          SUnitGroup.fullLogLattice (K := L) S := by
      rw [←
        (Module.Free.chooseBasis ℤ
          (SUnitGroup.fullLogLattice
            (K := L) S)).ofZLatticeBasis_span ℝ]
      apply
        ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
          ℤ _).mpr
      intro j
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inl] using hzrepr (Sum.inl j)
    have hzsecond :=
      hzrepr (Sum.inr ())
    simp only [b, fullLogHyperplaneDiagonalBasis,
      Basis.prod_repr_inr, Basis.singleton_repr] at hzsecond
    exact ⟨hzfirst, hzsecond⟩
  · rintro ⟨hzfirst, ⟨n, hn⟩⟩
    apply (b.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    cases i with
    | inl j =>
        have hzspan :
            z.1 ∈
              Submodule.span ℤ
                (Set.range (fullLogLatticeRealBasis L S)) := by
          simpa only [fullLogLatticeRealBasis,
            (Module.Free.chooseBasis ℤ
              (SUnitGroup.fullLogLattice
                (K := L) S)).ofZLatticeBasis_span ℝ] using
            hzfirst
        have hzcoord :=
          ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
            ℤ _).mp hzspan j
        simpa only [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inl] using hzcoord
    | inr j =>
        refine ⟨n, ?_⟩
        simpa [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inr, Basis.singleton_repr,
          RingHom.id_apply] using hn

open scoped Classical in
/-- The natural integral-linear map from the logarithmic lattice and
one diagonal integer coordinate to the extended full logarithmic
lattice. -/
noncomputable def fullLogLatticeProdIntToExtended
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (SUnitGroup.fullLogLattice (K := L) S × ℤ) →ₗ[ℤ]
      extendedFullLogLattice L S := by
  let e :=
    fullLogSpaceEquivHyperplaneProd L S
  refine
    { toFun := fun z =>
        ⟨e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · change
      fullLogSpaceSplit L S
          (e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) ∈
        fullLogHyperplaneDiagonalLattice L S
    rw [show
      fullLogSpaceSplit L S
          (e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
            SUnitGroup.fullLogLattice
              (K := L) S) :
          SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact e.apply_symm_apply _]
    exact
      (mem_fullLogHyperplaneDiagonalLattice_iff
        L S _).mpr ⟨z.1.2, ⟨z.2, rfl⟩⟩
  · intro x y
    apply Subtype.ext
    change
      e.symm
          (((((x + y).1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S)),
            (((x + y).2 : ℤ) : ℝ)) =
        e.symm
            ((((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ))) +
          e.symm
            ((((y.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (y.2 : ℝ)))
    rw [← e.symm.map_add]
    congr 1
    ext <;> simp
  · intro n x
    apply Subtype.ext
    change
      e.symm
          (((((n • x).1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S)),
            ((((n • x).2 : ℤ) : ℝ))) =
        n •
          e.symm
            ((((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ)))
    rw [← map_zsmul]
    congr 1
    ext <;> simp

open scoped Classical in
/-- The preceding map is bijective. -/
theorem fullLogLatticeProdIntToExtended_bijective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Bijective
      (fullLogLatticeProdIntToExtended L S) := by
  let e :=
    fullLogSpaceEquivHyperplaneProd L S
  constructor
  · intro x y hxy
    have hxy' :=
      congrArg
        (fun z : extendedFullLogLattice L S =>
          e (z :
            SUnitGroup.FullLogSpace (K := L) S))
        hxy
    have hpairs :
        (((x.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (x.2 : ℝ)) =
          (((y.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (y.2 : ℝ)) := by
      change
        e (e.symm
            (((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ))) =
          e (e.symm
            (((y.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (y.2 : ℝ))) at hxy'
      simpa only [e, LinearEquiv.apply_symm_apply] using hxy'
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hpairs
    · have hs :
          (x.2 : ℝ) = (y.2 : ℝ) :=
        congrArg Prod.snd hpairs
      exact Int.cast_injective hs
  · intro y
    have hy :
        fullLogSpaceSplit L S
            (y :
              SUnitGroup.FullLogSpace (K := L) S) ∈
          fullLogHyperplaneDiagonalLattice L S :=
      y.2
    obtain ⟨hyfirst, n, hn⟩ :=
      (mem_fullLogHyperplaneDiagonalLattice_iff
        L S _).mp hy
    let x :
        SUnitGroup.fullLogLattice (K := L) S × ℤ :=
      (⟨(fullLogSpaceSplit L S
          (y :
            SUnitGroup.FullLogSpace (K := L) S)).1,
        hyfirst⟩, n)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply e.injective
    change
      e (e.symm
          (((x.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (x.2 : ℝ))) =
        e (y :
          SUnitGroup.FullLogSpace (K := L) S)
    rw [e.apply_symm_apply]
    change
      ((fullLogSpaceSplit L S
          (y :
            SUnitGroup.FullLogSpace (K := L) S)).1,
        (n : ℝ)) =
      fullLogSpaceSplit L S
        (y :
          SUnitGroup.FullLogSpace (K := L) S)
    exact Prod.ext rfl hn

open scoped Classical in
/-- Integral-linear decomposition of the extended lattice into the
logarithmic lattice and one integer diagonal direction. -/
noncomputable def extendedFullLogLatticeEquivProdInt
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    extendedFullLogLattice L S ≃ₗ[ℤ]
      (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
  (LinearEquiv.ofBijective
    (fullLogLatticeProdIntToExtended L S)
    (fullLogLatticeProdIntToExtended_bijective L S)).symm

open scoped Classical in
/-- The componentwise action on the logarithmic lattice paired with
the invariant integer diagonal. -/
@[reducible]
noncomputable def fullLogLatticeProdIntDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.fullLogLattice (K := L) S × ℤ) := by
  letI :=
    fullLogLatticeDistribMulAction K L S hS
  exact
    { smul := fun σ z => (σ • z.1, z.2)
      one_smul := by
        intro z
        apply Prod.ext
        · exact one_smul (L ≃ₐ[K] L) z.1
        · rfl
      mul_smul := by
        intro σ τ z
        apply Prod.ext
        · exact mul_smul σ τ z.1
        · rfl
      smul_zero := by
        intro σ
        apply Prod.ext
        · exact DistribMulAction.smul_zero σ
        · rfl
      smul_add := by
        intro σ z z'
        apply Prod.ext
        · exact DistribMulAction.smul_add σ z.1 z'.1
        · rfl }

omit [NumberField K] in
open scoped Classical in
/-- The map from logarithmic-plus-diagonal coordinates into the
extended lattice is equivariant. -/
theorem fullLogLatticeProdIntToExtended_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        SUnitGroup.fullLogLattice (K := L) S × ℤ),
      fullLogLatticeProdIntToExtended L S
          (_productAction.toMulAction.toSemigroupAction.toSMul.smul
            σ z) =
        _extendedAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (fullLogLatticeProdIntToExtended L S z) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  intro σ z
  apply Subtype.ext
  apply fullLogSpaceSplit_injective L S
  apply Prod.ext
  · change
      (fullLogSpaceSplit L S
        ((fullLogSpaceEquivHyperplaneProd L S).symm
          (((σ • z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)))).1 =
        (fullLogSpaceSplit L S
          (permutationRepresentation ρ σ
            ((fullLogSpaceEquivHyperplaneProd L S).symm
              (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
                (z.2 : ℝ))))).1
    rw [permutationRepresentation_logPlace K L hS,
      fullLogSpaceSplit_fst_smul K L hS]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((σ • z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((σ • z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    change
      σ • (z.1 :
          SUnitGroup.LogHyperplane (K := L) S) =
        σ • (z.1 :
          SUnitGroup.LogHyperplane (K := L) S)
    rfl
  · change
      (fullLogSpaceSplit L S
        ((fullLogSpaceEquivHyperplaneProd L S).symm
          (((σ • z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)))).2 =
        (fullLogSpaceSplit L S
          (permutationRepresentation ρ σ
            ((fullLogSpaceEquivHyperplaneProd L S).symm
              (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
                (z.2 : ℝ))))).2
    rw [permutationRepresentation_logPlace K L hS,
      fullLogSpaceSplit_snd_smul K L hS]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((σ • z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((σ • z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]

omit [NumberField K] in
open scoped Classical in
/-- The integral decomposition of the extended lattice is equivariant. -/
theorem extendedFullLogLatticeEquivProdInt_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (x : extendedFullLogLattice L S),
      extendedFullLogLatticeEquivProdInt L S
          (_extendedAction.toMulAction.toSemigroupAction.toSMul.smul
            σ x) =
        _productAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (extendedFullLogLatticeEquivProdInt L S x) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  intro σ x
  let e :=
    extendedFullLogLatticeEquivProdInt L S
  apply e.symm.injective
  have hmap :=
    fullLogLatticeProdIntToExtended_equivariant
      K L hS σ (e x)
  change
    e.symm
        (productAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (e x)) =
      extendedAction.toMulAction.toSemigroupAction.toSMul.smul
        σ (e.symm (e x)) at hmap
  rw [e.symm_apply_apply, hmap,
    e.symm_apply_apply]

end DiagonalExtension

section LogLatticeHerbrand

open scoped Classical in
/-- Inclusion of the logarithmic lattice as the first factor of the
logarithmic-plus-diagonal lattice, in multiplicative notation. -/
def fullLogLatticeProdIntIncl
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S) →*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) where
  toFun z :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd z, 0)
  map_one' := rfl
  map_mul' _ _ := rfl

open scoped Classical in
/-- Projection from the logarithmic-plus-diagonal lattice to its
integer diagonal coordinate, in multiplicative notation. -/
def fullLogLatticeProdIntProj
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) →*
      Multiplicative ℤ where
  toFun z :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd z).2
  map_one' := rfl
  map_mul' _ _ := rfl

open scoped Classical in
/-- The multiplicative equivalence induced by the integral
decomposition of the extended lattice. -/
noncomputable def extendedFullLogLatticeMulEquivProdInt
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative (extendedFullLogLattice L S) ≃*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
  (extendedFullLogLatticeEquivProdInt L S).toAddEquiv.toMultiplicative

omit [NumberField K] in
open scoped Classical in
/-- The multiplicative form of the integral decomposition is
Galois-equivariant. -/
theorem extendedFullLogLatticeMulEquivProdInt_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _extendedMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) :=
      multiplicativeDistribMulAction
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (x : Multiplicative (extendedFullLogLattice L S)),
      extendedFullLogLatticeMulEquivProdInt L S
          (_extendedMultiplicativeAction.toMulAction.toSemigroupAction.toSMul.smul
            σ x) =
        _productMultiplicativeAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (extendedFullLogLatticeMulEquivProdInt L S x) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let extendedMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (extendedFullLogLattice L S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  intro σ x
  apply Multiplicative.toAdd.injective
  change
    extendedFullLogLatticeEquivProdInt L S
        (extendedAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (Multiplicative.toAdd x)) =
      productAction.toMulAction.toSemigroupAction.toSMul.smul
        σ
        (extendedFullLogLatticeEquivProdInt L S
          (Multiplicative.toAdd x))
  exact
    extendedFullLogLatticeEquivProdInt_equivariant
      K L hS σ (Multiplicative.toAdd x)

omit [NumberField K] in
open scoped Classical in
/-- The first-factor inclusion is Galois-equivariant. -/
theorem fullLogLatticeProdIntIncl_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _latticeMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)),
      fullLogLatticeProdIntIncl L S (σ • z) =
        σ • fullLogLatticeProdIntIncl L S z := by
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  intro σ z
  rfl

omit [NumberField K] in
open scoped Classical in
/-- The diagonal projection is Galois-equivariant for the trivial
action on its integer target. -/
theorem fullLogLatticeProdIntProj_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    letI _integerAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction (L ≃ₐ[K] L)
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)),
      fullLogLatticeProdIntProj L S (σ • z) =
        σ • fullLogLatticeProdIntProj L S z := by
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  let integerAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction (L ≃ₐ[K] L)
  intro σ z
  rfl

open scoped Classical in
/-- Exactness of the first-factor inclusion followed by the diagonal
projection. -/
theorem fullLogLatticeProdInt_exact
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    ∀ z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ),
      fullLogLatticeProdIntProj L S z = 1 ↔
        ∃ x :
            Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S),
          fullLogLatticeProdIntIncl L S x = z := by
  intro z
  constructor
  · intro hz
    refine
      ⟨Multiplicative.ofAdd
          (Multiplicative.toAdd z).1, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · rfl
    · exact (congrArg Multiplicative.toAdd hz).symm
  · rintro ⟨x, rfl⟩
    rfl

open scoped Classical in
/-- The first-factor inclusion is injective. -/
theorem fullLogLatticeProdIntIncl_injective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Injective
      (fullLogLatticeProdIntIncl L S) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  exact
    congrArg
      (fun z :
          Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ) =>
        (Multiplicative.toAdd z).1) hxy

open scoped Classical in
/-- The diagonal projection is surjective. -/
theorem fullLogLatticeProdIntProj_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective
      (fullLogLatticeProdIntProj L S) := by
  intro z
  exact
    ⟨Multiplicative.ofAdd
        (0, Multiplicative.toAdd z), rfl⟩

open scoped Classical in
/-- For the genuine sum-zero logarithmic lattice, adjoining
the invariant diagonal multiplies the Herbrand quotient by `|G|`. -/
theorem fullLogLattice_herbrandQuotient_eq_stabilizerProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _latticeMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let latticeAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S) :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  let integerAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction (L ≃ₐ[K] L)
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let extendedMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (extendedFullLogLattice L S)) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hExtended, hExtendedValue⟩ :=
    extendedFullLogLattice_herbrandQuotient_eq_stabilizerProduct
      K L hS σ hgen
  let extendedH0Finite := hExtended.1
  let extendedHMinusOneFinite := hExtended.2
  let e :=
    extendedFullLogLatticeMulEquivProdInt L S
  have he :
      ∀ (τ : L ≃ₐ[K] L)
        (x : Multiplicative (extendedFullLogLattice L S)),
        e (τ • x) = τ • e x :=
    extendedFullLogLatticeMulEquivProdInt_equivariant
      K L hS
  let hProduct :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) σ :=
    ⟨herbrandH0Finite_of_equivariantMulEquiv e he,
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        e he σ⟩
  let productH0Finite := hProduct.1
  let productHMinusOneFinite := hProduct.2
  let hInteger :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) (Multiplicative ℤ) σ :=
    ⟨trivialIntHerbrandH0Finite,
      trivialIntHerbrandHMinusOneFinite σ⟩
  let integerH0Finite := hInteger.1
  let integerHMinusOneFinite := hInteger.2
  let hLattice :=
    herbrandQuotientDefined_left_of_middle_right
      (fullLogLatticeProdIntIncl L S)
      (fullLogLatticeProdIntProj L S)
      (fullLogLatticeProdIntIncl_equivariant K L hS)
      (fullLogLatticeProdIntProj_equivariant K L hS)
      (fullLogLatticeProdInt_exact L S)
      (fullLogLatticeProdIntIncl_injective L S)
      (fullLogLatticeProdIntProj_surjective L S)
      σ hgen hProduct hInteger
  let latticeH0Finite := hLattice.1
  let latticeHMinusOneFinite := hLattice.2
  have hMultiplicative :=
    herbrandQuotient_multiplicative_of_shortExact
      (fullLogLatticeProdIntIncl L S)
      (fullLogLatticeProdIntProj L S)
      (fullLogLatticeProdIntIncl_equivariant K L hS)
      (fullLogLatticeProdIntProj_equivariant K L hS)
      (fullLogLatticeProdInt_exact L S)
      (fullLogLatticeProdIntIncl_injective L S)
      (fullLogLatticeProdIntProj_surjective L S)
      σ hgen
  have hIntegerValue := trivialInt_herbrandQuotient_eq_card (G := L ≃ₐ[K] L) σ
  have hExtendedProduct := herbrandQuotient_eq_of_equivariantMulEquiv e he σ
  refine ⟨hLattice, ?_⟩
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (L ≃ₐ[K] L) ≠ 0)
  rw [eq_div_iff hcard]
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ *
        (Fintype.card (L ≃ₐ[K] L) : ℚ) =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ))
          _ _ _ _ σ := by
      rw [← hIntegerValue]
      exact hMultiplicative.symm
    _ =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S))
          _ _ _ _ σ :=
      hExtendedProduct.symm
    _ =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      hExtendedValue

end LogLatticeHerbrand

section ActualSUnitHerbrand

open scoped Classical in
/-- For the actual `S`-unit group, the finite
roots-of-unity kernel has Herbrand quotient one, so the logarithmic
lattice formula transfers unchanged. -/
theorem sUnit_herbrandQuotient_eq_stabilizerProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _sUnitAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) :=
      sUnitMulDistribMulAction K L S hS
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) S) :=
    sUnitMulDistribMulAction K L S hS
  let latticeAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S) :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let torsionAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) :=
    stableSubgroupMulDistribMulAction
      (CommGroup.torsion
        (SUnitGroup (K := L) S))
      (sUnitTorsion_stable K L hS)
  let torsionFinite :
      Finite
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) :=
    sUnitTorsionFinite L S
  obtain ⟨hLattice, hLatticeValue⟩ :=
    fullLogLattice_herbrandQuotient_eq_stabilizerProduct_div_card
      K L hS σ hgen
  let latticeH0Finite := hLattice.1
  let latticeHMinusOneFinite := hLattice.2
  let hTorsion :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) σ :=
    ⟨inferInstance, inferInstance⟩
  let torsionH0Finite := hTorsion.1
  let torsionHMinusOneFinite := hTorsion.2
  let hSUnit :=
    herbrandQuotientDefined_middle_of_left_right
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype
      (sUnitFullLogMulHom L S)
      (stableSubgroup_subtype_equivariant
        (CommGroup.torsion
          (SUnitGroup (K := L) S))
        (sUnitTorsion_stable K L hS))
      (sUnitFullLogMulHom_equivariant K L hS)
      (sUnitTorsion_fullLog_exact L S)
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype_injective
      (sUnitFullLogMulHom_surjective L S)
      σ hgen hTorsion hLattice
  let sUnitH0Finite := hSUnit.1
  let sUnitHMinusOneFinite := hSUnit.2
  have hMultiplicative :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L) S) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := CommGroup.torsion
              (SUnitGroup (K := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S)) σ :=
    herbrandQuotient_multiplicative_of_shortExact
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype
      (sUnitFullLogMulHom L S)
      (stableSubgroup_subtype_equivariant
        (CommGroup.torsion
          (SUnitGroup (K := L) S))
        (sUnitTorsion_stable K L hS))
      (sUnitFullLogMulHom_equivariant K L hS)
      (sUnitTorsion_fullLog_exact L S)
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype_injective
      (sUnitFullLogMulHom_surjective L S)
      σ hgen
  have hTorsionValue :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := CommGroup.torsion
            (SUnitGroup (K := L) S)) σ = 1 :=
    herbrandQuotient_eq_one_of_finite_module
      σ hgen
  refine ⟨hSUnit, ?_⟩
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ =
        @herbrandQuotient
            (L ≃ₐ[K] L)
            (CommGroup.torsion
              (SUnitGroup (K := L) S))
            _ _ _ _ σ *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S))
            _ _ _ _ σ :=
      hMultiplicative
    _ =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ := by
      rw [hTorsionValue, one_mul]
    _ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) :=
      hLatticeValue

end ActualSUnitHerbrand

section LocalDegreeInterpretation

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- Stabilizing a finite place is equivalent to stabilizing its
underlying prime ideal. -/
theorem finitePlace_stabilizer_eq_idealStabilizer
    (P : HeightOneSpectrum (𝓞 L)) :
    letI _finitePlaceAction :=
      finitePlaceMulAction K L
    MulAction.stabilizer (L ≃ₐ[K] L) P =
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  let finitePlaceAction :=
    finitePlaceMulAction K L
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  change
    finitePlaceEquiv K L σ P = P ↔
      σ • P.asIdeal = P.asIdeal
  rw [HeightOneSpectrum.ext_iff,
    finitePlaceEquiv_asIdeal,
    Ideal.pointwise_smul_def]
  change
    Ideal.map
          (NumberField.RingOfIntegers.mapAlgEquiv
            σ).toRingEquiv.toRingHom P.asIdeal =
        P.asIdeal ↔
      Ideal.map
          (MulSemiringAction.toRingHom
            (L ≃ₐ[K] L) (𝓞 L) σ) P.asIdeal =
        P.asIdeal
  have hhom :
      (NumberField.RingOfIntegers.mapAlgEquiv
          σ).toRingEquiv.toRingHom =
        MulSemiringAction.toRingHom
          (L ≃ₐ[K] L) (𝓞 L) σ := by
    ext x
    rfl
  rw [hhom]

open scoped Classical in
/-- The finite local degree at the place `P`, in the standard
ramification-index times inertia-degree form
`[L_P : K_p] = e(P/p) f(P/p)`. -/
noncomputable def finiteLogPlaceLocalDegree
    (P : HeightOneSpectrum (𝓞 L)) : ℕ :=
  let p := P.asIdeal.under (𝓞 K)
  p.ramificationIdxIn (𝓞 L) *
    p.inertiaDegIn (𝓞 L)

open scoped Classical in
/-- The stabilizer of a finite place has order equal to its local
degree. -/
theorem finitePlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    (P : HeightOneSpectrum (𝓞 L)) :
    letI _finitePlaceAction :=
      finitePlaceMulAction K L
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) P) =
      finiteLogPlaceLocalDegree K L P := by
  let finitePlaceAction :=
    finitePlaceMulAction K L
  rw [finitePlace_stabilizer_eq_idealStabilizer K L P]
  unfold finiteLogPlaceLocalDegree
  let p := P.asIdeal.under (𝓞 K)
  have hp : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) P.ne_bot
  let quotientFinite : Finite ((𝓞 K) ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp
  let residueFinite : Finite p.ResidueField :=
    inferInstance
  let residuePerfect : PerfectField p.ResidueField :=
    inferInstance
  exact
    Ideal.card_stabilizer_eq p P.asIdeal

open scoped Classical in
/-- Passing to a stable finite set does not change the stabilizer or
the finite local degree of one of its places. -/
theorem stableFinitePlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (v : S) :
    letI _stableAction :=
      stableFinitePlaceMulAction K L S hS
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) v) =
      finiteLogPlaceLocalDegree K L v := by
  let stableAction :=
    stableFinitePlaceMulAction K L S hS
  let finitePlaceAction :=
    finitePlaceMulAction K L
  rw [show
    MulAction.stabilizer (L ≃ₐ[K] L) v =
        MulAction.stabilizer
          (L ≃ₐ[K] L)
          (v : HeightOneSpectrum (𝓞 L)) by
      ext σ
      simp only [MulAction.mem_stabilizer_iff]
      change
        (⟨finitePlaceEquiv K L σ v, _⟩ : S) = v ↔
          finitePlaceEquiv K L σ v = v
      exact Subtype.ext_iff]
  exact
    finitePlace_stabilizer_card_eq_localDegree
      K L v

open scoped Classical in
/-- The local degree attached to a logarithmic place.  At an
archimedean place it is `1` or `2`; at a finite place it is
`e(P/p) f(P/p)`. -/
noncomputable def logPlaceLocalDegree
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (q : SUnitGroup.LogPlace (K := L) S) : ℕ :=
  match q with
  | Sum.inl w =>
      if NumberField.InfinitePlace.IsUnramified K w
      then 1 else 2
  | Sum.inr v =>
      finiteLogPlaceLocalDegree K L v

open scoped Classical in
/-- For every actual logarithmic place, the order of its Galois
stabilizer is its local degree. -/
theorem logPlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (q : SUnitGroup.LogPlace (K := L) S) :
    letI _logPlaceAction :=
      logPlaceMulAction K L S hS
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) q) =
      logPlaceLocalDegree K L S q := by
  let stableAction :=
    stableFinitePlaceMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  cases q with
  | inl w =>
      unfold logPlaceLocalDegree
      rw [show
        MulAction.stabilizer
              (L ≃ₐ[K] L)
              (Sum.inl w :
                SUnitGroup.LogPlace (K := L) S) =
            MulAction.stabilizer (L ≃ₐ[K] L) w by
          ext σ
          simp only [MulAction.mem_stabilizer_iff]
          change Sum.inl (σ • w) = Sum.inl w ↔
            σ • w = w
          simp]
      exact
        NumberField.InfinitePlace.card_stabilizer
  | inr v =>
      unfold logPlaceLocalDegree
      rw [show
        MulAction.stabilizer
              (L ≃ₐ[K] L)
              (Sum.inr v :
                SUnitGroup.LogPlace (K := L) S) =
            MulAction.stabilizer (L ≃ₐ[K] L) v by
          ext σ
          simp only [MulAction.mem_stabilizer_iff]
          change Sum.inr (σ • v) = Sum.inr v ↔
            σ • v = v
          simp]
      exact
        stableFinitePlace_stabilizer_card_eq_localDegree
          K L hS v

open scoped Classical in
/-- The canonical representative of every logarithmic-place orbit has
stabilizer order equal to its local degree. -/
theorem permutationOrbitStabilizer_card_eq_logPlaceLocalDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    ∀ ω :
        MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S),
      Nat.card (permutationOrbitStabilizer ω) =
        logPlaceLocalDegree K L S ω.out := by
  dsimp only
  intro ω
  exact
    logPlace_stabilizer_card_eq_localDegree
      K L hS ω.out

open scoped Classical in
/-- The Herbrand quotient in local-degree form:
`h(G, L^S) = |G|⁻¹ ∏_{p ∈ S} [L_P : K_p]`, with the
archimedean places included in the logarithmic place set. -/
theorem sUnit_herbrandQuotient_eq_localDegreeProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _sUnitAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) :=
      sUnitMulDistribMulAction K L S hS
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (logPlaceLocalDegree K L S ω.out : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) S) :=
    sUnitMulDistribMulAction K L S hS
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hSUnit, hSUnitValue⟩ :=
    sUnit_herbrandQuotient_eq_stabilizerProduct_div_card
      K L hS σ hgen
  refine ⟨hSUnit, ?_⟩
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) :=
      hSUnitValue
    _ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (logPlaceLocalDegree K L S ω.out : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro ω _
      norm_cast
      rw [← Nat.card_eq_fintype_card]
      exact
        permutationOrbitStabilizer_card_eq_logPlaceLocalDegree
          K L hS ω

end LocalDegreeInterpretation
