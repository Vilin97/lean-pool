/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.PolynomialFactors
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
/-!
# Classification of extensions of a completed absolute value

For a simple finite extension `L = K(α)`, the extensions of a nontrivial
absolute value of `K` correspond to the distinct irreducible factors, over
the completion, of an irreducible polynomial having `α` as a root.  The final
theorem below also records the explicit pullback valuation and the extension
of the chosen embedding to the completed field.
-/

@[expose] public section

noncomputable
section

open Polynomial
open scoped Topology
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- Base change of the chosen irreducible polynomial from `K` to its completion `K_v`. -/
abbrev completionExtensionFactorCompletionPolynomial
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (f : K[X]) :
    vK.Completion[X] :=
  f.map (algebraMap K vK.Completion)

/-- The distinct normalized irreducible factors appearing after base change
to the completion. Repeated factors of an inseparable polynomial occur only once. -/
abbrev CompletionExtensionFactorCompletionFactors
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (f : K[X]) :=
  DistinctNormalizedFactors (completionExtensionFactorCompletionPolynomial vK f)

/-- A root of the chosen irreducible polynomial is integral over the base
field.  This is derived from `hf` and `hroot`; it is not an extra hypothesis
of the extension-factor correspondence. -/
theorem completionExtensionFactor_root_isIntegral
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) : IsIntegral K α :=
  (show IsAlgebraic K α from ⟨f, hf.ne_zero, hroot⟩).isIntegral

/-- An irreducible polynomial having `α` as a root is associated to the
minimal polynomial of `α`. -/
theorem completionExtensionFactor_definingPolynomial_associated_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) :
    Associated f (minpoly K α) := by
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
  have hunit : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
    isUnit_C.mpr (IsUnit.mk0 f.leadingCoeff⁻¹ (inv_ne_zero hlead))
  exact (associated_mul_unit_right f (C f.leadingCoeff⁻¹) hunit).trans
    (Associated.of_eq (minpoly.eq_of_irreducible hf hroot))

/-- After base change to the completion, the chosen irreducible polynomial and the minimal
polynomial still have exactly the same normalized irreducible factors. -/
theorem completionExtensionFactor_completionFactors_eq_minpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    polynomialDistinctNormalizedFactors
        (completionExtensionFactorCompletionPolynomial vK f) =
      polynomialDistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) := by
  exact polynomialDistinctNormalizedFactors_eq_of_associated
    (Polynomial.associated_map_map (algebraMap K vK.Completion)
      (completionExtensionFactor_definingPolynomial_associated_minpoly hf hroot))

/-- Transport the factor set of the mapped minimal polynomial to the factor
set of the particular chosen irreducible polynomial. -/
noncomputable def completionExtensionFactorMinpolyFactorsEquivCompletionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  Set.equivOfEq (by
    ext g
    exact Finset.ext_iff.mp
      (completionExtensionFactor_completionFactors_eq_minpolyFactors
        vK hf hroot).symm g)

/-- The root/minimal-polynomial relation transported from roots to simple
`K`-embeddings into the algebraic closure of `K_v`. -/
abbrev CompletionExtensionFactorEmbeddingSetoid
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Setoid (L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :=
  Setoid.comap
    (simpleEmbeddingsEquivMappedMinpolyRoots
      (K' := vK.Completion)
      (E := absoluteValueExtensionAlgebraicCompletionClosure vK)
      α hα hgen)
    (rootMinpolySetoid
      ((minpoly K α).map (algebraMap K vK.Completion)))

/-- Conjugacy classes of simple embeddings are the distinct irreducible
factors of the mapped minimal polynomial. -/
noncomputable def completionExtensionFactorEmbeddingClassesEquivMinpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) ≃
      DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) :=
  let e := simpleEmbeddingsEquivMappedMinpolyRoots
    (K' := vK.Completion)
    (E := absoluteValueExtensionAlgebraicCompletionClosure vK)
    α hα hgen
  (Quotient.congr e (fun _ _ => Iff.rfl)).trans
    (rootClassesEquivDistinctNormalizedFactors
      (E := absoluteValueExtensionAlgebraicCompletionClosure vK)
      ((Polynomial.map_ne_zero_iff
        (algebraMap K vK.Completion).injective).2 (minpoly.ne_zero hα)))

/-- For a simple extension, the relation used in the preceding quotient is
exactly conjugacy of embeddings over `K_v` from the valuation-extension theorem. -/
theorem completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  have hpbgen : pb.gen = α := by simp [pb]
  change IsConjRoot vK.Completion (τ α) (τ' α) ↔ _
  constructor
  · intro hconj
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv hconj.symm
    refine ⟨σ, ?_⟩
    let στ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK :=
      (σ.toAlgHom.restrictScalars K).comp τ
    have heq : τ' = στ := by
      apply pb.algHom_ext
      rw [hpbgen]
      exact hσ.symm
    intro x
    exact DFunLike.congr_fun heq x
  · rintro ⟨σ, hσ⟩
    change minpoly vK.Completion (τ α) = minpoly vK.Completion (τ' α)
    rw [hσ α]
    exact (minpoly.algEquiv_eq σ (τ α)).symm

/-- Regard the pullback attached to an embedding as an exact extension.
The extension property is the one proved in the valuation-extension theorem, rather than an
extra field in the data of the extension-factor correspondence. -/
noncomputable def pullbackAbsoluteValueExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (τ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    AbsoluteValueExtension vK L :=
  ⟨absoluteValueExtensionPullback vK hvK τ,
    absoluteValueExtension_pullback_extends vK hvK τ⟩

/-- In the simple-extension situation, equality of the two pullback
valuations is exactly the factor relation used on embeddings.  The forward
direction is proved by extending both embeddings to the same completion and
comparing minimal polynomials there. -/
theorem completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK) :
    absoluteValueExtensionPullback vK hvK τ =
        absoluteValueExtensionPullback vK hvK τ' ↔
      (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  rw [completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    vK α hα hgen τ τ']
  exact absoluteValueExtension_pullback_eq_iff_conjugate vK hvK τ τ'

/-- The canonical embedding attached to `w` by the valuation-extension theorem pulls `bar v`
back to `w` itself. -/
theorem completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    w.1 = absoluteValueExtensionPullback vK hvK
      (absoluteValueExtensionEmbeddingOfExtension vK w) := by
  exact absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w

/-- Exact extensions are the same as the conjugacy classes of embeddings
used in the factor calculation. -/
noncomputable def completionExtensionFactorExtensionsEquivEmbeddingClasses
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  letI : FiniteDimensional K L := pb.finite
  letI : Algebra.IsAlgebraic K L := inferInstance
  let fromClass :
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) →
        AbsoluteValueExtension vK L :=
    Quotient.lift
      (pullbackAbsoluteValueExtension vK hvK)
      (by
        intro τ τ' hrel
        apply Subtype.ext
        exact (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
          vK hvK α hα hgen τ τ').2 hrel)
  refine
    { toFun := fun w => Quotient.mk
        (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen)
        (absoluteValueExtensionEmbeddingOfExtension vK w)
      invFun := fromClass
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
      vK hvK w).symm
  · intro q
    induction q using Quotient.inductionOn with
    | _ τ =>
      apply Quotient.sound
      let wτ : AbsoluteValueExtension vK L :=
        pullbackAbsoluteValueExtension vK hvK τ
      apply (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
        vK hvK α hα hgen
        (absoluteValueExtensionEmbeddingOfExtension vK wτ) τ).1
      exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
        vK hvK wτ).symm

/-- Auxiliary form of the correspondence, first stated for the mapped
minimal polynomial. -/
noncomputable def completionExtensionFactorExtensionsEquivMinpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) :=
  (completionExtensionFactorExtensionsEquivEmbeddingClasses
      vK hvK α hα hgen).trans
    (completionExtensionFactorEmbeddingClassesEquivMinpolyFactors
      vK α hα hgen)

/-- Auxiliary form with the particular chosen irreducible polynomial `f` as
target. -/
noncomputable def completionExtensionFactorExtensionsEquivCompletionFactorsAux
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  (completionExtensionFactorExtensionsEquivMinpolyFactors
      vK hvK α hα hgen).trans
    (completionExtensionFactorMinpolyFactorsEquivCompletionFactors
      vK hf hroot)

/-- The irreducible factor attached directly to an exact extension `w`: it
is the minimal polynomial over `K_v` of the image of `α` in `L_w`. -/
noncomputable def completionExtensionFactorExtensionFactor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L)
    (w : AbsoluteValueExtension vK L) : vK.Completion[X] := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact minpoly vK.Completion
    (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α)

/-- The directly attached factor is one of the distinct normalized factors
of the chosen irreducible polynomial over the completion. -/
theorem completionExtensionFactor_extensionFactor_mem
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (w : AbsoluteValueExtension vK L) :
    completionExtensionFactorExtensionFactor vK α w ∈
      polynomialDistinctNormalizedFactors
        (completionExtensionFactorCompletionPolynomial vK f) := by
  classical
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let hKv := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have hαalg : IsAlgebraic K α := ⟨f, hf.ne_zero, hroot⟩
  have hα : IsIntegral K α := hαalg.isIntegral
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have hp0 : completionExtensionFactorCompletionPolynomial vK f ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (algebraMap K vK.Completion).injective).2 hf.ne_zero
  have haf : Polynomial.aeval a
      (completionExtensionFactorCompletionPolynomial vK f) = 0 := by
    change Polynomial.aeval (ι α)
      (f.map (algebraMap K vK.Completion)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    rw [Polynomial.aeval_algHom_apply ι α f, hroot, map_zero]
  dsimp [completionExtensionFactorExtensionFactor,
    polynomialDistinctNormalizedFactors, polynomialNormalizedFactors]
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hp0]
  exact ⟨minpoly.irreducible haKv, minpoly.monic haKv,
    minpoly.dvd vK.Completion a haf⟩

/-- The canonical map from exact extensions to completion factors. -/
noncomputable def completionExtensionFactorExtensionToFactor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    AbsoluteValueExtension vK L →
      CompletionExtensionFactorCompletionFactors vK f :=
  fun w => ⟨completionExtensionFactorExtensionFactor vK α w,
    completionExtensionFactor_extensionFactor_mem vK hf hroot w⟩

/-- The factor read from the canonical embedding supplied by the valuation-extension theorem is
the same polynomial as the factor read directly in the metric completion
`L_w`. -/
theorem completionExtensionFactor_embeddingOfExtension_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (α : L)
    (w : AbsoluteValueExtension vK L) :
    minpoly vK.Completion
        (absoluteValueExtensionEmbeddingOfExtension vK w α) =
      completionExtensionFactorExtensionFactor vK α w := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let a := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 α
  calc
    minpoly vK.Completion
        (absoluteValueExtensionEmbeddingOfExtension vK w α) =
        minpoly vK.Completion a :=
      minpoly.algHom_eq
        (absoluteValueExtensionLocalizationEmbedding vK w)
        (absoluteValueExtensionLocalizationEmbedding vK w).injective a
    _ = minpoly vK.Completion
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) := by
      rw [← minpoly.algHom_eq
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val.injective a]
      rfl
    _ = completionExtensionFactorExtensionFactor vK α w := rfl

/-- In a finite simple extension the image of the primitive generator
already generates the whole metric completion over `K_v`.  No separability
hypothesis is used. -/
theorem completionExtensionFactor_completion_adjoin_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Algebra.adjoin vK.Completion
        ({AbsoluteValue.toCompletionAlgHom (K := K) w.1 α} :
          Set w.1.Completion) = ⊤ := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have hrange : Set.range
      (AbsoluteValue.toCompletion w.1) ⊆
      (IntermediateField.adjoin vK.Completion ({a} : Set w.1.Completion) :
        Set w.1.Completion) := by
    rintro _ ⟨x, rfl⟩
    change ι x ∈ IntermediateField.adjoin vK.Completion ({a} : Set _)
    have hx : x ∈ Algebra.adjoin K ({α} : Set L) := by
      rw [hgen]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff.mp hx]
        exact IntermediateField.mem_adjoin_simple_self vK.Completion a
    | algebraMap x =>
        rw [ι.commutes,
          IsScalarTower.algebraMap_apply K vK.Completion w.1.Completion]
        exact (IntermediateField.adjoin vK.Completion ({a} : Set _)).algebraMap_mem _
    | add x y _ _ hx hy =>
        simpa only [map_add] using
          (IntermediateField.adjoin vK.Completion ({a} : Set _)).add_mem hx hy
    | mul x y _ _ hx hy =>
        simpa only [map_mul] using
          (IntermediateField.adjoin vK.Completion ({a} : Set _)).mul_mem hx hy
  have hloc_le : AbsoluteValue.algebraicLocalization vK w.1 w.2 ≤
      IntermediateField.adjoin vK.Completion ({a} : Set _) := by
    exact IntermediateField.adjoin_le_iff.mpr hrange
  have hsimple : IntermediateField.adjoin vK.Completion ({a} : Set _) = ⊤ := by
    apply top_unique
    rw [← absoluteValueExtension_finiteLocalization_eq_top vK hvK w]
    exact hloc_le
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      haKv.isAlgebraic,
    hsimple, IntermediateField.top_toSubalgebra]

/-- The finite simple field cut out by the factor attached to `w` is the
metric completion `L_w`. -/
noncomputable def completionExtensionFactorAdjoinRootEquivCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AdjoinRoot (completionExtensionFactorExtensionFactor vK α w) ≃ₐ[vK.Completion]
      w.1.Completion := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have htop : Algebra.adjoin vK.Completion ({a} : Set w.1.Completion) = ⊤ :=
    completionExtensionFactor_completion_adjoin_eq_top
      vK hvK α hα hgen w
  change AdjoinRoot (minpoly vK.Completion a) ≃ₐ[vK.Completion]
    w.1.Completion
  exact (@minpoly.equivAdjoin vK.Completion w.1.Completion _ _ _ _ _ _
    (Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion w.1.Completion).injective) a haKv).trans
    ((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv)

/-- The preceding equivalence sends the residue class of `X` to the
canonical image of the primitive generator in `L_w`. -/
@[simp]
theorem completionExtensionFactor_adjoinRootEquivCompletion_root
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    completionExtensionFactorAdjoinRootEquivCompletion vK hvK α hα hgen w
        (AdjoinRoot.root (completionExtensionFactorExtensionFactor vK α w)) =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1 α := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  change ((AdjoinRoot.Minpoly.toAdjoin vK.Completion a)
      (AdjoinRoot.root (minpoly vK.Completion a)) : w.1.Completion) = a
  exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X
    (R := vK.Completion) (x := a)

/-- If `w` is presented as the pullback along an embedding `τ`, then the
factor attached to `w` is the minimal polynomial of `τ(α)`. -/
theorem completionExtensionFactor_extensionFactor_eq_minpoly_of_pullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L)
    (τ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hτ : w.1 = absoluteValueExtensionPullback vK hvK τ) :
    completionExtensionFactorExtensionFactor vK α w =
      minpoly vK.Completion (τ α) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  let τw := absoluteValueExtensionEmbeddingOfExtension vK w
  have hpull : absoluteValueExtensionPullback vK hvK τw =
      absoluteValueExtensionPullback vK hvK τ :=
    (absoluteValueExtension_extension_eq_pullback_embeddingOfExtension
      vK hvK w).symm.trans hτ
  have hrel : (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τw τ :=
    (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
      vK hvK α hα hgen τw τ).1 hpull
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  change minpoly vK.Completion
      (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) = _
  calc
    minpoly vK.Completion
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) =
        minpoly vK.Completion (τw α) :=
      (completionExtensionFactor_embeddingOfExtension_minpoly vK α w).symm
    _ = minpoly vK.Completion (τ α) := hrel

/-- The embedding `τ` extends from `L` to an algebraic equivalence from
`L_w` onto the simple field `K_v(τ(α))`.  The compatibility with every
element of `L` is proved below. -/
noncomputable def completionExtensionFactorCompletionEquivSimpleRoot
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L)
    (τ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hτ : w.1 = absoluteValueExtensionPullback vK hvK τ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    w.1.Completion ≃ₐ[vK.Completion]
      IntermediateField.adjoin vK.Completion
        ({τ α} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK)) := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  have hfactor : completionExtensionFactorExtensionFactor vK α w =
      minpoly vK.Completion (τ α) :=
    completionExtensionFactor_extensionFactor_eq_minpoly_of_pullback
      vK hvK α hα hgen w τ hτ
  have hτα : IsIntegral vK.Completion (τ α) :=
    (Algebra.IsAlgebraic.isAlgebraic (τ α)).isIntegral
  exact (completionExtensionFactorAdjoinRootEquivCompletion
      vK hvK α hα hgen w).symm |>.trans
    ((AdjoinRoot.algEquivOfEq vK.Completion _ _ hfactor).trans
      (IntermediateField.adjoinRootEquivAdjoin vK.Completion hτα))

/-- On the primitive generator, the completed embedding has the prescribed
value `τ(α)`. -/
@[simp]
theorem completionExtensionFactor_completionEquivSimpleRoot_gen
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L)
    (τ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hτ : w.1 = absoluteValueExtensionPullback vK hvK τ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    completionExtensionFactorCompletionEquivSimpleRoot
        vK hvK α hα hgen w τ hτ
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) =
      IntermediateField.AdjoinSimple.gen vK.Completion (τ α) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let e0 := completionExtensionFactorAdjoinRootEquivCompletion
    vK hvK α hα hgen w
  let hfactor : completionExtensionFactorExtensionFactor vK α w =
      minpoly vK.Completion (τ α) :=
    completionExtensionFactor_extensionFactor_eq_minpoly_of_pullback
      vK hvK α hα hgen w τ hτ
  let e1 := AdjoinRoot.algEquivOfEq vK.Completion _ _ hfactor
  have hτα : IsIntegral vK.Completion (τ α) :=
    (Algebra.IsAlgebraic.isAlgebraic (τ α)).isIntegral
  let e2 := IntermediateField.adjoinRootEquivAdjoin vK.Completion hτα
  have hinv : e0.symm
      (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) =
      AdjoinRoot.root (completionExtensionFactorExtensionFactor vK α w) := by
    apply e0.injective
    rw [e0.apply_symm_apply,
      completionExtensionFactor_adjoinRootEquivCompletion_root]
  change (e0.symm.trans (e1.trans e2))
      (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) = _
  rw [AlgEquiv.trans_apply, hinv, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]

/-- The equivalence to `K_v(τ(α))` really extends `τ` on every element of
`L`, not merely on the chosen primitive generator. -/
theorem completionExtensionFactor_completionEquivSimpleRoot_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L)
    (τ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hτ : w.1 = absoluteValueExtensionPullback vK hvK τ)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ((completionExtensionFactorCompletionEquivSimpleRoot
        vK hvK α hα hgen w τ hτ
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x) :
      IntermediateField.adjoin vK.Completion
        ({τ α} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK))) :
      absoluteValueExtensionAlgebraicCompletionClosure vK) = τ x := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let E := IntermediateField.adjoin vK.Completion
    ({τ α} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK))
  let e : w.1.Completion ≃ₐ[vK.Completion] E :=
    completionExtensionFactorCompletionEquivSimpleRoot
      vK hvK α hα hgen w τ hτ
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let φ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK :=
    ((E.val.comp e.toAlgHom).restrictScalars K).comp ι
  have hpbgen : pb.gen = α := by simp [pb]
  have hφ : φ = τ := by
    apply pb.algHom_ext
    rw [hpbgen]
    change ((e (ι α) : E) :
      absoluteValueExtensionAlgebraicCompletionClosure vK) = τ α
    rw [completionExtensionFactor_completionEquivSimpleRoot_gen]
    rfl
  exact DFunLike.congr_fun hφ x

/-- On an extension `w`, the auxiliary correspondence is the directly
defined polynomial `minpoly_{K_v}(α in L_w)`. -/
theorem completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    (completionExtensionFactorExtensionsEquivCompletionFactorsAux
        vK hvK hf hroot hgen w).1 =
      completionExtensionFactorExtensionFactor vK α w := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  change minpoly vK.Completion
      (absoluteValueExtensionEmbeddingOfExtension vK w α) =
    completionExtensionFactorExtensionFactor vK α w
  exact completionExtensionFactor_embeddingOfExtension_minpoly vK α w

/-- the extension-factor correspondence, correspondence part: exact extensions of `v` to the
simple extension are in canonical bijection with the distinct normalized
irreducible factors of `f` over `K_v`.  Its forward map is definitionally the
factor obtained from `α` in `L_w`. -/
noncomputable def completionExtensionFactorExtensionEquivFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f := by
  let e := completionExtensionFactorExtensionsEquivCompletionFactorsAux
    vK hvK hf hroot hgen
  apply Equiv.ofBijective
    (completionExtensionFactorExtensionToFactor vK hf hroot)
  have heq : completionExtensionFactorExtensionToFactor vK hf hroot = e := by
    funext w
    apply Subtype.ext
    exact (completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
      vK hvK hf hroot hgen w).symm
  rw [heq]
  exact e.bijective

/-- A factor in the correspondence is monic and irreducible and divides the
mapped minimal polynomial of the primitive generator. -/
theorem completionExtensionFactor_factor_irreducible_monic_dvd_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (g : CompletionExtensionFactorCompletionFactors vK f) :
    Irreducible g.1 ∧ g.1.Monic ∧
      g.1 ∣ (minpoly K α).map (algebraMap K vK.Completion) := by
  classical
  let p := (minpoly K α).map (algebraMap K vK.Completion)
  have hp0 : p ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (algebraMap K vK.Completion).injective).2
      (minpoly.ne_zero (completionExtensionFactor_root_isIntegral hf hroot))
  have hg : g.1 ∈ polynomialDistinctNormalizedFactors p := by
    rw [← completionExtensionFactor_completionFactors_eq_minpolyFactors
      vK hf hroot]
    exact g.2
  dsimp [polynomialDistinctNormalizedFactors,
    polynomialNormalizedFactors] at hg
  rw [Multiset.mem_toFinset,
    Polynomial.mem_normalizedFactors_iff hp0] at hg
  exact hg

/-- A chosen root of a factor is also a root of the mapped minimal
polynomial and hence determines a `K`-embedding of `L`. -/
theorem completionExtensionFactor_factorRoot_mem_mappedMinpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    β ∈ ((minpoly K α).map (algebraMap K vK.Completion)).rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK) := by
  rcases completionExtensionFactor_factor_irreducible_monic_dvd_minpoly
    vK hf hroot g with ⟨_, _, hgdvd⟩
  have hp0 : (minpoly K α).map (algebraMap K vK.Completion) ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (algebraMap K vK.Completion).injective).2
      (minpoly.ne_zero (completionExtensionFactor_root_isIntegral hf hroot))
  rw [Polynomial.mem_rootSet] at hβ ⊢
  exact ⟨hp0, aeval_eq_zero_of_dvd_aeval_eq_zero hgdvd hβ.2⟩

/-- The embedding associated with a factor and a specifically chosen root
of that factor. -/
noncomputable def completionExtensionFactorEmbeddingOfFactorRoot
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK :=
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  (simpleEmbeddingsEquivMappedMinpolyRoots
    (K' := vK.Completion)
    (E := absoluteValueExtensionAlgebraicCompletionClosure vK)
    α hα hgen).symm
      ⟨β, completionExtensionFactor_factorRoot_mem_mappedMinpoly
        vK hf hroot g β hβ⟩

/-- The embedding chosen from the root `β` sends `α` to exactly `β`. -/
theorem completionExtensionFactor_embeddingOfFactorRoot_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    completionExtensionFactorEmbeddingOfFactorRoot
      vK hf hroot hgen g β hβ α = β := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let e := simpleEmbeddingsEquivMappedMinpolyRoots
    (K' := vK.Completion)
    (E := absoluteValueExtensionAlgebraicCompletionClosure vK)
    α hα hgen
  let z : PolynomialRootsIn
      (absoluteValueExtensionAlgebraicCompletionClosure vK)
      ((minpoly K α).map (algebraMap K vK.Completion)) :=
    ⟨β, completionExtensionFactor_factorRoot_mem_mappedMinpoly
      vK hf hroot g β hβ⟩
  change (e.symm z) α = β
  exact congrArg Subtype.val (e.apply_symm_apply z)

/-- The valuation extension attached to the chosen root is the explicit
pullback `bar v ∘ τ`. -/
noncomputable def completionExtensionFactorExtensionOfFactorRoot
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    AbsoluteValueExtension vK L :=
  pullbackAbsoluteValueExtension vK hvK
    (completionExtensionFactorEmbeddingOfFactorRoot
      vK hf hroot hgen g β hβ)

theorem completionExtensionFactor_extensionOfFactorRoot_eq_pullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    (completionExtensionFactorExtensionOfFactorRoot
        vK hvK hf hroot hgen g β hβ).1 =
      absoluteValueExtensionPullback vK hvK
        (completionExtensionFactorEmbeddingOfFactorRoot
          vK hf hroot hgen g β hβ) :=
  rfl

/-- The extension built from a root of `g` is sent back to exactly `g` by
the factor correspondence. -/
theorem completionExtensionFactor_extensionOfFactorRoot_factor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    completionExtensionFactorExtensionFactor vK α
        (completionExtensionFactorExtensionOfFactorRoot
          vK hvK hf hroot hgen g β hβ) = g.1 := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let τ := completionExtensionFactorEmbeddingOfFactorRoot
    vK hf hroot hgen g β hβ
  let w := completionExtensionFactorExtensionOfFactorRoot
    vK hvK hf hroot hgen g β hβ
  rcases completionExtensionFactor_factor_irreducible_monic_dvd_minpoly
    vK hf hroot g with ⟨hgirr, hgmonic, _⟩
  have hβeval : Polynomial.aeval β g.1 = 0 :=
    (Polynomial.mem_rootSet.mp hβ).2
  have hmp : g.1 = minpoly vK.Completion β :=
    minpoly.eq_of_irreducible_of_monic hgirr hβeval hgmonic
  calc
    completionExtensionFactorExtensionFactor vK α w =
        minpoly vK.Completion (τ α) :=
      completionExtensionFactor_extensionFactor_eq_minpoly_of_pullback
        vK hvK α hα hgen w τ rfl
    _ = minpoly vK.Completion β := by
      rw [completionExtensionFactor_embeddingOfFactorRoot_apply]
    _ = g.1 := hmp.symm

/-- Thus the explicitly constructed pullback is the inverse image of `g`
under the canonical correspondence. -/
theorem completionExtensionFactor_extensionOfFactorRoot_eq_equiv_symm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    completionExtensionFactorExtensionOfFactorRoot
        vK hvK hf hroot hgen g β hβ =
      (completionExtensionFactorExtensionEquivFactors
        vK hvK hf hroot hgen).symm g := by
  let e := completionExtensionFactorExtensionEquivFactors
    vK hvK hf hroot hgen
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact completionExtensionFactor_extensionOfFactorRoot_factor
    vK hvK hf hroot hgen g β hβ

/-- A normalized irreducible factor is the minimal polynomial of each of
its roots in the algebraic closure. -/
theorem completionExtensionFactor_factor_eq_minpoly_root
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    g.1 = minpoly vK.Completion β := by
  rcases completionExtensionFactor_factor_irreducible_monic_dvd_minpoly
    vK hf hroot g with ⟨hgirr, hgmonic, _⟩
  exact minpoly.eq_of_irreducible_of_monic hgirr
    (Polynomial.mem_rootSet.mp hβ).2 hgmonic

/-- The completed field belonging to a factor and a chosen root `β` is
canonically `K_v(β)`. -/
noncomputable def completionExtensionFactorFactorRootCompletionEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    let w := completionExtensionFactorExtensionOfFactorRoot
      vK hvK hf hroot hgen g β hβ
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    w.1.Completion ≃ₐ[vK.Completion]
      IntermediateField.adjoin vK.Completion
        ({β} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK)) := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let w := completionExtensionFactorExtensionOfFactorRoot
    vK hvK hf hroot hgen g β hβ
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  have hfactor : completionExtensionFactorExtensionFactor vK α w = g.1 :=
    completionExtensionFactor_extensionOfFactorRoot_factor
      vK hvK hf hroot hgen g β hβ
  have hmp : g.1 = minpoly vK.Completion β :=
    completionExtensionFactor_factor_eq_minpoly_root vK hf hroot g β hβ
  have hβint : IsIntegral vK.Completion β :=
    (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  exact (completionExtensionFactorAdjoinRootEquivCompletion
      vK hvK α hα hgen w).symm |>.trans
    ((AdjoinRoot.algEquivOfEq vK.Completion _ _ (hfactor.trans hmp)).trans
      (IntermediateField.adjoinRootEquivAdjoin vK.Completion hβint))

/-- On `α`, the chosen-root completion equivalence has value exactly `β`. -/
@[simp]
theorem completionExtensionFactor_factorRootCompletionEquiv_gen
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK)) :
    let w := completionExtensionFactorExtensionOfFactorRoot
      vK hvK hf hroot hgen g β hβ
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    completionExtensionFactorFactorRootCompletionEquiv
        vK hvK hf hroot hgen g β hβ
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) =
      IntermediateField.AdjoinSimple.gen vK.Completion β := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let w := completionExtensionFactorExtensionOfFactorRoot
    vK hvK hf hroot hgen g β hβ
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let e0 := completionExtensionFactorAdjoinRootEquivCompletion
    vK hvK α hα hgen w
  let hpoly : completionExtensionFactorExtensionFactor vK α w =
      minpoly vK.Completion β :=
    (completionExtensionFactor_extensionOfFactorRoot_factor
      vK hvK hf hroot hgen g β hβ).trans
      (completionExtensionFactor_factor_eq_minpoly_root vK hf hroot g β hβ)
  let e1 := AdjoinRoot.algEquivOfEq vK.Completion _ _ hpoly
  have hβint : IsIntegral vK.Completion β :=
    (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  let e2 := IntermediateField.adjoinRootEquivAdjoin vK.Completion hβint
  have hinv : e0.symm
      (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) =
      AdjoinRoot.root (completionExtensionFactorExtensionFactor vK α w) := by
    apply e0.injective
    rw [e0.apply_symm_apply,
      completionExtensionFactor_adjoinRootEquivCompletion_root]
  change (e0.symm.trans (e1.trans e2))
      (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) = _
  rw [AlgEquiv.trans_apply, hinv, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]

/-- The chosen-root equivalence extends the chosen embedding on every
element of `L`. -/
theorem completionExtensionFactor_factorRootCompletionEquiv_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (g : CompletionExtensionFactorCompletionFactors vK f)
    (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
    (hβ : β ∈ g.1.rootSet
      (absoluteValueExtensionAlgebraicCompletionClosure vK))
    (x : L) :
    let τ := completionExtensionFactorEmbeddingOfFactorRoot
      vK hf hroot hgen g β hβ
    let w := completionExtensionFactorExtensionOfFactorRoot
      vK hvK hf hroot hgen g β hβ
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ((completionExtensionFactorFactorRootCompletionEquiv
        vK hvK hf hroot hgen g β hβ
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x) :
      IntermediateField.adjoin vK.Completion
        ({β} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK))) :
      absoluteValueExtensionAlgebraicCompletionClosure vK) = τ x := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  let τ := completionExtensionFactorEmbeddingOfFactorRoot
    vK hf hroot hgen g β hβ
  let w := completionExtensionFactorExtensionOfFactorRoot
    vK hvK hf hroot hgen g β hβ
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let E := IntermediateField.adjoin vK.Completion
    ({β} : Set (absoluteValueExtensionAlgebraicCompletionClosure vK))
  let e : w.1.Completion ≃ₐ[vK.Completion] E :=
    completionExtensionFactorFactorRootCompletionEquiv
      vK hvK hf hroot hgen g β hβ
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let φ : L →ₐ[K] absoluteValueExtensionAlgebraicCompletionClosure vK :=
    ((E.val.comp e.toAlgHom).restrictScalars K).comp ι
  have hpbgen : pb.gen = α := by simp [pb]
  have hφ : φ = τ := by
    apply pb.algHom_ext
    rw [hpbgen]
    change ((e (ι α) : E) :
      absoluteValueExtensionAlgebraicCompletionClosure vK) = τ α
    rw [completionExtensionFactor_factorRootCompletionEquiv_gen,
      completionExtensionFactor_embeddingOfFactorRoot_apply]
    rfl
  exact DFunLike.congr_fun hφ x

/-- **Classification of extensions of a completed absolute value.**

For `L = K(α)` and an irreducible polynomial `f` with root `α`, exact
extensions of the nontrivial absolute value `v` are in bijection with the
distinct normalized irreducible factors of `f` over `K_v`.  For every factor
and every chosen root `β` in `bar K_v`, the theorem records the embedding
`τ(α) = β`, the formula `w = bar v ∘ τ`, and an equivalence
`L_w ≃ K_v(β)` which extends `τ` on every element of `L`. -/
theorem completionExtensionFactor_classification
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Function.Bijective (completionExtensionFactorExtensionToFactor vK hf hroot) ∧
      ∀ (g : CompletionExtensionFactorCompletionFactors vK f)
        (β : absoluteValueExtensionAlgebraicCompletionClosure vK)
        (hβ : β ∈ g.1.rootSet
          (absoluteValueExtensionAlgebraicCompletionClosure vK)),
        let τ := completionExtensionFactorEmbeddingOfFactorRoot
          vK hf hroot hgen g β hβ
        let w := completionExtensionFactorExtensionOfFactorRoot
          vK hvK hf hroot hgen g β hβ
        letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
        letI : SMul K w.1.Completion := hK.toSMul
        letI := AbsoluteValue.completionAlgebra vK w.1 w.2
        let e := completionExtensionFactorFactorRootCompletionEquiv
          vK hvK hf hroot hgen g β hβ
        τ α = β ∧
          w.1 = absoluteValueExtensionPullback vK hvK τ ∧
          w = (completionExtensionFactorExtensionEquivFactors
            vK hvK hf hroot hgen).symm g ∧
          completionExtensionFactorExtensionFactor vK α w = g.1 ∧
          ∀ x : L,
            ((e (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x) :
              IntermediateField.adjoin vK.Completion
                ({β} : Set
                  (absoluteValueExtensionAlgebraicCompletionClosure vK))) :
              absoluteValueExtensionAlgebraicCompletionClosure vK) = τ x := by
  constructor
  · exact (completionExtensionFactorExtensionEquivFactors
      vK hvK hf hroot hgen).bijective
  · intro g β hβ
    dsimp only
    refine ⟨completionExtensionFactor_embeddingOfFactorRoot_apply
        vK hf hroot hgen g β hβ,
      completionExtensionFactor_extensionOfFactorRoot_eq_pullback
        vK hvK hf hroot hgen g β hβ,
      completionExtensionFactor_extensionOfFactorRoot_eq_equiv_symm
        vK hvK hf hroot hgen g β hβ,
      completionExtensionFactor_extensionOfFactorRoot_factor
        vK hvK hf hroot hgen g β hβ, ?_⟩
    intro x
    exact completionExtensionFactor_factorRootCompletionEquiv_coe
      vK hvK hf hroot hgen g β hβ x

end Valuations
end AlgebraicNumberTheory

end
