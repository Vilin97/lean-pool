/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
/-!
# Finite coefficient support for relative ideles

This file supplies the finite-support input for the actual scalar-extension model

`𝔸_K ⊗[K] L`.

Fixing the canonical chosen `K`-basis of `L`, every relative adele has
finitely many base-adele coefficients.  For a relative idele we take
the union of the nonintegral finite places of the coefficients of the
idele and of its inverse.  Outside this finite set both local tensor
components therefore lie in the lattice spanned by that basis over
the local valuation ring.

This produces the finite support from a basis lattice.  Passing from
that lattice to the product of local integer rings additionally requires
integral compatibility of the relative tensor decomposition.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The finite index type of the canonical chosen `K`-basis of `L`. -/
abbrev RelativeAdeleBasisIndex :=
  Module.Free.ChooseBasisIndex K L

/-- The canonical chosen `K`-basis used to extract base-adele
coefficients. -/
noncomputable def relativeExtensionBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  Module.Free.chooseBasis K L

/-- Scalar extension of the chosen basis from `K` to `𝔸_K`. -/
noncomputable def relativeAdeleBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L))
      (NumberField.AdeleRing (𝓞 K) K)
      (RelativeAdeleRing K L) :=
  Algebra.TensorProduct.basis
    (NumberField.AdeleRing (𝓞 K) K)
    (relativeExtensionBasis (K := K) (L := L))

/-- The `i`-th base-adele coefficient of a relative adele. -/
noncomputable def relativeAdeleCoefficient
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  (relativeAdeleBasis (K := K) (L := L)).repr z i

omit [NumberField L] in
/-- Expansion of a relative adele in the chosen extension basis. -/
theorem relativeAdele_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L) :
    z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        relativeAdeleCoefficient
            (K := K) (L := L) z i ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  symm
  simpa [relativeAdeleCoefficient, relativeAdeleBasis,
    relativeExtensionBasis, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def] using
      (relativeAdeleBasis (K := K) (L := L)).sum_repr z

omit [NumberField L] in
/-- Evaluation at a finite place is coefficientwise in the chosen
basis expansion. -/
theorem relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleFiniteComponent_tmul] using h

omit [NumberField L] in
/-- Evaluation at an infinite place is coefficientwise in the chosen
basis expansion. -/
theorem relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).1 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleInfiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleInfiniteComponent_tmul] using h

/-- The set of places at which a base adele is not in the local
valuation ring is finite. -/
theorem finite_adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    {w : HeightOneSpectrum (𝓞 K) |
      a.2 w ∉ w.adicCompletionIntegers K}.Finite :=
  Filter.eventually_cofinite.mp a.2.2

/-- The exceptional finite places at which a base adele is not in the
local valuation ring. -/
noncomputable def adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_adeleNonIntegralPlaces (K := K) a).toFinset

@[simp]
theorem mem_adeleNonIntegralPlaces_iff
    (a : NumberField.AdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ adeleNonIntegralPlaces (K := K) a ↔
      a.2 w ∉ w.adicCompletionIntegers K := by
  exact
    Set.Finite.mem_toFinset
      (finite_adeleNonIntegralPlaces (K := K) a)

/-- Away from its exact exceptional finset, a base adele has integral
finite component. -/
theorem adele_component_mem_integers_of_notMem
    (a : NumberField.AdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ adeleNonIntegralPlaces (K := K) a) :
    a.2 w ∈ w.adicCompletionIntegers K := by
  contrapose! hw
  exact
    (mem_adeleNonIntegralPlaces_iff
      (K := K) a w).2 hw

/-- Exact union of all exceptional coefficient places of a relative
adele. -/
noncomputable def relativeAdeleCoefficientSupport
    (z : RelativeAdeleRing K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion fun i =>
    adeleNonIntegralPlaces
      (K := K)
      (relativeAdeleCoefficient
        (K := K) (L := L) z i)

omit [NumberField L] in
@[simp]
theorem mem_relativeAdeleCoefficientSupport_iff
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeAdeleCoefficientSupport
        (K := K) (L := L) z ↔
      ∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ∉
          w.adicCompletionIntegers K := by
  classical
  simp [relativeAdeleCoefficientSupport]

/-- The exact coefficient support of a relative idele contains the
exceptional places of the idele and its inverse. -/
noncomputable def relativeIdeleCoefficientSupport
    (z : RelativeIdeleGroup K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    relativeAdeleCoefficientSupport
        (K := K) (L := L)
        (z : RelativeAdeleRing K L) ∪
      relativeAdeleCoefficientSupport
        (K := K) (L := L)
        ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L)

omit [NumberField L] in
@[simp]
theorem mem_relativeIdeleCoefficientSupport_iff
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeIdeleCoefficientSupport
        (K := K) (L := L) z ↔
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) ∨
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            ((z⁻¹ : RelativeIdeleGroup K L) :
              RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) := by
  classical
  simp [relativeIdeleCoefficientSupport]

omit [NumberField L] in
/-- Outside the exact coefficient support, every coefficient of both
the relative idele and its inverse is integral at the given finite
place. -/
theorem relativeIdele_coefficients_integral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) ∧
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) := by
  constructor
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inl ⟨i, hi⟩)
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inr ⟨i, hi⟩)

omit [NumberField L] in
/-- The exact support is the least finset outside which all
coefficients of the idele and its inverse are integral. -/
theorem relativeIdeleCoefficientSupport_minimal
    (z : RelativeIdeleGroup K L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ w, w ∉ S →
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              (z : RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K) ∧
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              ((z⁻¹ : RelativeIdeleGroup K L) :
                RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K)) :
    relativeIdeleCoefficientSupport
        (K := K) (L := L) z ⊆ S := by
  intro w hw
  by_contra hwS
  obtain hbad | hbad :=
    (mem_relativeIdeleCoefficientSupport_iff
      (K := K) (L := L) z w).1 hw
  · obtain ⟨i, hi⟩ := hbad
    exact hi ((hS w hwS).1 i)
  · obtain ⟨i, hi⟩ := hbad
    exact hi ((hS w hwS).2 i)

omit [NumberField L] in
/-- Basis-lattice integrality in the local tensor algebra: all
coordinates in the fixed extension basis belong to the valuation
ring of `K_w`. -/
def RelativeBasisIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∃ c :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        w.adicCompletionIntegers K,
    x =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ((c i : w.adicCompletionIntegers K) :
            w.adicCompletion K) ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i

omit [NumberField L] in
/-- A local tensor unit is basis-integral when both it and its inverse
belong to the local valuation-ring coefficient lattice. -/
def RelativeBasisIntegralUnitAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) : Prop :=
  RelativeBasisIntegralAt
      (K := K) (L := L) w
      (x : w.adicCompletion K ⊗[K] L) ∧
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((x⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L)

omit [NumberField L] in
/-- The finite component of a relative idele is given by the evaluated
base-adele coefficients. -/
theorem relativeIdele_finiteComponent_eq_sum_tmul_coefficients
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    ((RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :
        (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L) =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  rw [RelativeIdeleGroup.finiteComponent_coe]
  exact
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z : RelativeAdeleRing K L) w

omit [NumberField L] in
/-- Outside the coefficient support, the actual finite component lies
in the local lattice spanned by the chosen extension basis. -/
theorem relativeIdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).1 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w

omit [NumberField L] in
/-- Outside the same support, the actual finite component of the
inverse lies in the same local basis lattice. -/
theorem relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w
          (z⁻¹ : RelativeIdeleGroup K L) :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).2 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z⁻¹ : RelativeIdeleGroup K L) w

omit [NumberField L] in
/-- Equivalently, the inverse of the actual local unit component lies
in the same basis lattice outside the coefficient support. -/
theorem relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z)⁻¹ :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L)) := by
  simpa using
    relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw

omit [NumberField L] in
/-- Thus the actual local unit component is basis-integral outside the
explicit coefficient support. -/
theorem relativeIdele_finiteComponent_basisIntegralUnit_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralUnitAt
      (K := K) (L := L) w
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z) :=
  ⟨relativeIdele_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw,
    relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
      (K := K) (L := L) z w hw⟩

omit [NumberField L] in
/-- A source-producing finite-support theorem: one explicit
minimal finset simultaneously controls the local basis integrality of
the relative idele and its inverse. -/
theorem exists_relativeIdele_coefficientSupport
    (z : RelativeIdeleGroup K L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ w, w ∉ S →
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              (z : RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K) ∧
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              ((z⁻¹ : RelativeIdeleGroup K L) :
                RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K)) ∧
      (∀ w, w ∉ S →
        RelativeBasisIntegralAt
          (K := K) (L := L) w
          ((RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w z :
              (w.adicCompletion K ⊗[K] L)ˣ) :
              w.adicCompletion K ⊗[K] L) ∧
        RelativeBasisIntegralAt
          (K := K) (L := L) w
          ((((RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w z)⁻¹ :
              (w.adicCompletion K ⊗[K] L)ˣ) :
              w.adicCompletion K ⊗[K] L))) := by
  refine
    ⟨relativeIdeleCoefficientSupport
        (K := K) (L := L) z, ?_, ?_⟩
  · intro w hw
    exact
      relativeIdele_coefficients_integral_of_notMem
        (K := K) (L := L) z w hw
  · intro w hw
    exact
      ⟨relativeIdele_finiteComponent_basisIntegral_of_notMem
          (K := K) (L := L) z w hw,
        relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
          (K := K) (L := L) z w hw⟩
