/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
/-!
# Localization and decomposition comparison for decomposition groups

For a possibly infinite Galois extension, this file constructs the canonical
isomorphism between the decomposition group of an exact absolute value and
the Galois group of the localization over the completed base field.  The
localization is algebraic, not the
whole metric completion in infinite degree.
-/

@[expose] public section

noncomputable section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section LocalizationLift

variable (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)

/-- The ring equivalence of the normed copy of `L` attached to an automorphism
which preserves `w`. -/
def valuationPreservingWithAbsRingEquiv
    (σ : L ≃ₐ[K] L) : WithAbs w.1 ≃+* WithAbs w.1 :=
  (WithAbs.equiv w.1).trans
    (σ.toRingEquiv.trans (WithAbs.equiv w.1).symm)

@[simp] theorem valuationPreservingWithAbsRingEquiv_apply
    (σ : L ≃ₐ[K] L) (x : L) :
    WithAbs.equiv w.1
        (valuationPreservingWithAbsRingEquiv vK w σ
          ((WithAbs.equiv w.1).symm x)) = σ x :=
  rfl

theorem valuationPreservingWithAbsRingEquiv_isometry
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    Isometry (valuationPreservingWithAbsRingEquiv vK w σ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  exact hσ (WithAbs.equiv w.1 x)

theorem valuationPreservingWithAbsRingEquiv_symm_isometry
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    Isometry (valuationPreservingWithAbsRingEquiv vK w σ).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  have h := hσ (σ⁻¹ (WithAbs.equiv w.1 x))
  simpa [valuationPreservingWithAbsRingEquiv] using h.symm

/-- A valuation-preserving automorphism of `L` extends functorially to a ring
automorphism of the metric completion of `(L,w)`. -/
def valuationPreservingCompletionRingEquiv
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    w.1.Completion ≃+* w.1.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (valuationPreservingWithAbsRingEquiv vK w σ)
    (valuationPreservingWithAbsRingEquiv_isometry vK w σ hσ).continuous
    (valuationPreservingWithAbsRingEquiv_symm_isometry vK w σ hσ).continuous

theorem valuationPreservingCompletionRingEquiv_toCompletion
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) (x : L) :
    valuationPreservingCompletionRingEquiv vK w σ hσ
        (AbsoluteValue.toCompletion w.1 x) =
      AbsoluteValue.toCompletion w.1 (σ x) := by
  change
    UniformSpace.Completion.mapRingEquiv
          (valuationPreservingWithAbsRingEquiv vK w σ)
          (valuationPreservingWithAbsRingEquiv_isometry vK w σ hσ).continuous
          (valuationPreservingWithAbsRingEquiv_symm_isometry vK w σ hσ).continuous
        (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.1.Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (valuationPreservingWithAbsRingEquiv_isometry
        vK w σ hσ).uniformContinuous]
  rfl

/-- The extended automorphism fixes the embedded completed base field. -/
theorem valuationPreservingCompletionRingEquiv_completionMap
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    (x : vK.Completion) :
    valuationPreservingCompletionRingEquiv vK w σ hσ
        (AbsoluteValue.completionMap vK w.1 w.2 x) =
      AbsoluteValue.completionMap vK w.1 w.2 x := by
  have hfun :
      (fun y : vK.Completion =>
        valuationPreservingCompletionRingEquiv vK w σ hσ
          (AbsoluteValue.completionMap vK w.1 w.2 y)) =
        AbsoluteValue.completionMap vK w.1 w.2 := by
    apply UniformSpace.Completion.ext
    · exact UniformSpace.Completion.continuous_map.comp
        (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
    · exact (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
    · intro y
      have hy : (y : vK.Completion) =
          algebraMap K vK.Completion (WithAbs.equiv vK y) := by
        rw [← AbsoluteValue.toCompletion_eq_algebraMap]
        simp
      rw [hy, AbsoluteValue.completionMap_coe]
      change
        valuationPreservingCompletionRingEquiv vK w σ hσ
            (AbsoluteValue.toCompletion w.1
              (algebraMap K L (WithAbs.equiv vK y))) =
          AbsoluteValue.toCompletion w.1
            (algebraMap K L (WithAbs.equiv vK y))
      rw [valuationPreservingCompletionRingEquiv_toCompletion, σ.commutes]
  exact congrFun hfun x

/-- The completion lift preserves the algebraic localization `L K_v`. -/
theorem valuationPreservingCompletionRingEquiv_mem_localization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    {z : w.1.Completion} (hz : z ∈ AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    valuationPreservingCompletionRingEquiv vK w σ hσ z ∈
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  apply IntermediateField.adjoin_induction
      (p := fun x (_ : x ∈ E) =>
        valuationPreservingCompletionRingEquiv vK w σ hσ x ∈ E)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    rw [valuationPreservingCompletionRingEquiv_toCompletion]
    exact IntermediateField.subset_adjoin vK.Completion _ ⟨σ a, rfl⟩
  · intro x
    change
      valuationPreservingCompletionRingEquiv vK w σ hσ
          (AbsoluteValue.completionMap vK w.1 w.2 x) ∈ E
    rw [valuationPreservingCompletionRingEquiv_completionMap]
    exact E.algebraMap_mem x
  · intro x y hx hy hx' hy'
    simpa only [map_add] using E.add_mem hx' hy'
  · intro x hx hx'
    simpa only [map_inv₀] using E.inv_mem hx'
  · intro x y hx hy hx' hy'
    simpa only [map_mul] using E.mul_mem hx' hy'
  · exact hz

/-- The inverse completion lift also preserves `L K_v`. -/
theorem valuationPreservingCompletionRingEquiv_symm_mem_localization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    {z : w.1.Completion} (hz : z ∈ AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    (valuationPreservingCompletionRingEquiv vK w σ hσ).symm z ∈
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  apply IntermediateField.adjoin_induction
      (p := fun x (_ : x ∈ E) =>
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm x ∈ E)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    have hgen := valuationPreservingCompletionRingEquiv_toCompletion
      vK w σ hσ (σ⁻¹ a)
    have hsymm :
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
            (AbsoluteValue.toCompletion w.1 a) =
          AbsoluteValue.toCompletion w.1 (σ⁻¹ a) := by
      rw [← (valuationPreservingCompletionRingEquiv vK w σ hσ).injective.eq_iff,
        (valuationPreservingCompletionRingEquiv vK w σ hσ).apply_symm_apply]
      simpa using hgen.symm
    rw [hsymm]
    exact IntermediateField.subset_adjoin vK.Completion _ ⟨σ⁻¹ a, rfl⟩
  · intro x
    have hbase := valuationPreservingCompletionRingEquiv_completionMap
      vK w σ hσ x
    have hsymm :
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
            (AbsoluteValue.completionMap vK w.1 w.2 x) =
          AbsoluteValue.completionMap vK w.1 w.2 x := by
      rw [← (valuationPreservingCompletionRingEquiv vK w σ hσ).injective.eq_iff,
        (valuationPreservingCompletionRingEquiv vK w σ hσ).apply_symm_apply]
      exact hbase.symm
    change
      (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
          (AbsoluteValue.completionMap vK w.1 w.2 x) ∈ E
    rw [hsymm]
    exact E.algebraMap_mem x
  · intro x y hx hy hx' hy'
    simpa only [map_add] using E.add_mem hx' hy'
  · intro x hx hx'
    simpa only [map_inv₀] using E.inv_mem hx'
  · intro x y hx hy hx' hy'
    simpa only [map_mul] using E.mul_mem hx' hy'
  · exact hz

/-- A valuation-preserving automorphism of `L` extends to a
`K_v`-automorphism of the algebraic localization. -/
def valuationPreservingLocalizationAlgEquiv
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let e := valuationPreservingCompletionRingEquiv vK w σ hσ
  exact
    { toFun := fun z =>
        ⟨e z, valuationPreservingCompletionRingEquiv_mem_localization
          vK w σ hσ z.property⟩
      invFun := fun z =>
        ⟨e.symm z,
          valuationPreservingCompletionRingEquiv_symm_mem_localization
            vK w σ hσ z.property⟩
      left_inv := fun z => by
        apply Subtype.ext
        exact e.symm_apply_apply z
      right_inv := fun z => by
        apply Subtype.ext
        exact e.apply_symm_apply z
      map_mul' := fun x y => by
        apply Subtype.ext
        exact e.map_mul x y
      map_add' := fun x y => by
        apply Subtype.ext
        exact e.map_add x y
      commutes' := fun x => by
        apply Subtype.ext
        exact valuationPreservingCompletionRingEquiv_completionMap
          vK w σ hσ x }

@[simp] theorem valuationPreservingLocalizationAlgEquiv_toLocalization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    valuationPreservingLocalizationAlgEquiv vK w σ hσ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (σ x) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  apply Subtype.ext
  exact valuationPreservingCompletionRingEquiv_toCompletion vK w σ hσ x

end LocalizationLift

section DecompositionEquiv

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

include hvK

/-- Membership in the decomposition group supplies equality, not merely
equivalence, of the normalized absolute-value representatives. -/
theorem absoluteValueDecompositionGroup_preserves_absoluteValue
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    w.1 ((σ : L ≃ₐ[K] L) x) = w.1 x := by
  have hσ :=
    (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w (σ : L ≃ₐ[K] L)).mp σ.property
  have hx := congrArg (fun q : AbsoluteValueExtension vK L => q.1 x) hσ
  simpa [absoluteValueExtensionConjugate,
    absoluteValueConjugate, AbsoluteValue.comp] using hx

omit hvK

variable [IsGalois K L]

include hvK

/-- Every automorphism of the algebraic localization over `K_v` preserves its
unique extended absolute value. -/
theorem localizationAbsoluteValue_algEquiv
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (x :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 (τ x) =
      AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let vhat := AbsoluteValue.completionAbsoluteValue vK
  let wloc := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  let : Algebra.IsAlgebraic vK.Completion E :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion) (L := E) vhat
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  have hwloc : wloc = R.extension := by
    apply R.unique
    intro y
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y
  let wconj : AbsoluteValue E ℝ :=
    wloc.comp (f := τ.toRingEquiv.toRingHom) τ.injective
  have hwconj : wconj = R.extension := by
    apply R.unique
    intro y
    change wloc (τ (algebraMap vK.Completion E y)) = vhat y
    rw [τ.commutes]
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y
  have h := congrArg (fun q : AbsoluteValue E ℝ => q x)
    (hwconj.trans hwloc.symm)
  exact h

omit hvK

/-- Restrict a local automorphism to `L`.  Normality of `L/K` ensures that
the image of the dense algebraic copy of `L` is again that copy. -/
def localizationAlgEquivRestrict
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) : L ≃ₐ[K] L := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let i : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  letI : Algebra K E := (i.comp (algebraMap K L)).toAlgebra
  let iAlg : L →ₐ[K] E :=
    { __ := i
      commutes' := fun x => by
        change i (algebraMap K L x) = (i.comp (algebraMap K L)) x
        rfl }
  letI : Algebra L E := i.toAlgebra
  letI : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let τK : E ≃ₐ[K] E :=
    { __ := τ.toRingEquiv
      commutes' := fun x => by
        change τ (i (algebraMap K L x)) = i (algebraMap K L x)
        rw [AbsoluteValue.toAlgebraicLocalization_algebraMap, τ.commutes] }
  exact Normal.algHomEquivAut K E L (τK.toAlgHom.comp iAlg)

/-- The normality restriction is characterized by its action on the embedded
copy of `L`. -/
theorem localizationAlgEquivRestrict_toLocalization
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        (localizationAlgEquivRestrict vK w τ x) =
      τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let i : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let : Algebra K E := (i.comp (algebraMap K L)).toAlgebra
  let iAlg : L →ₐ[K] E :=
    { __ := i
      commutes' := fun x => by
        change i (algebraMap K L x) = (i.comp (algebraMap K L)) x
        rfl }
  let : Algebra L E := i.toAlgebra
  let : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let τK : E ≃ₐ[K] E :=
    { __ := τ.toRingEquiv
      commutes' := fun y => by
        change τ (i (algebraMap K L y)) = i (algebraMap K L y)
        rw [AbsoluteValue.toAlgebraicLocalization_algebraMap, τ.commutes] }
  change i (Normal.algHomEquivAut K E L (τK.toAlgHom.comp iAlg) x) =
    τ (i x)
  simpa [iAlg, τK, AlgHom.restrictNormal', RingHom.algebraMap_toAlgebra] using
    ((τK.toAlgHom.comp iAlg).restrictNormal_commutes L x)

/-- Restriction of a local automorphism belongs to the decomposition group. -/
def localizationToDecompositionGroup
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    absoluteValueDecompositionGroup K w.1 := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let σ := localizationAlgEquivRestrict vK w τ
  refine ⟨σ, ?_⟩
  intro x
  have habs : w.1 (σ x) = w.1 x := by
    calc
      w.1 (σ x) = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (σ x)) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 (σ
          x)).symm
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) := by
        rw [localizationAlgEquivRestrict_toLocalization]
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
        localizationAbsoluteValue_algEquiv vK hvK w τ _
      _ = w.1 x :=
        AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x
  rw [habs]

include hvK

/-- Extend an element of the decomposition group from `L` to the algebraic
localization `L_w`. -/
def decompositionGroupToLocalization
    (σ : absoluteValueDecompositionGroup K w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
      AbsoluteValue.algebraicLocalization vK w.1 w.2 :=
  valuationPreservingLocalizationAlgEquiv vK w (σ : L ≃ₐ[K] L)
    (absoluteValueDecompositionGroup_preserves_absoluteValue vK hvK w σ)

omit [IsGalois K L] in
@[simp] theorem decompositionGroupToLocalization_toLocalization
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w σ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 ((σ : L ≃ₐ[K] L) x) :=
  valuationPreservingLocalizationAlgEquiv_toLocalization vK w
    (σ : L ≃ₐ[K] L)
    (absoluteValueDecompositionGroup_preserves_absoluteValue vK hvK w σ) x

omit hvK

include hvK

/-- Restriction after extension is the original element of the decomposition
group. -/
theorem localizationToDecompositionGroup_decompositionGroupToLocalization
    (σ : absoluteValueDecompositionGroup K w.1) :
    localizationToDecompositionGroup vK hvK w
        (decompositionGroupToLocalization vK hvK w σ) = σ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  apply i.injective
  calc
    i ((localizationToDecompositionGroup vK hvK w
          (decompositionGroupToLocalization vK hvK w σ) :
        L ≃ₐ[K] L) x) =
        decompositionGroupToLocalization vK hvK w σ (i x) :=
      localizationAlgEquivRestrict_toLocalization vK w
        (decompositionGroupToLocalization vK hvK w σ) x
    _ = i ((σ : L ≃ₐ[K] L) x) :=
      decompositionGroupToLocalization_toLocalization vK hvK w σ x

/-- Extension after restriction is the original local automorphism. -/
theorem decompositionGroupToLocalization_localizationToDecompositionGroup
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w
        (localizationToDecompositionGroup vK hvK w τ) = τ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let ρ := decompositionGroupToLocalization vK hvK w
    (localizationToDecompositionGroup vK hvK w τ)
  have hρ : ρ.toAlgHom = τ.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change ρ (i x) = τ (i x)
    rw [decompositionGroupToLocalization_toLocalization]
    change i (localizationAlgEquivRestrict vK w τ x) = τ (i x)
    exact localizationAlgEquivRestrict_toLocalization vK w τ x
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hρ x

omit hvK

include hvK

omit [IsGalois K L] in
/-- Extension from the decomposition group respects composition. -/
theorem decompositionGroupToLocalization_mul
    (σ τ : absoluteValueDecompositionGroup K w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w (σ * τ) =
      decompositionGroupToLocalization vK hvK w σ *
        decompositionGroupToLocalization vK hvK w τ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let ρL := decompositionGroupToLocalization vK hvK w (σ * τ)
  let ρR := decompositionGroupToLocalization vK hvK w σ *
    decompositionGroupToLocalization vK hvK w τ
  have hρ : ρL.toAlgHom = ρR.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change ρL (i x) = ρR (i x)
    calc
      ρL (i x) = i (((σ * τ : absoluteValueDecompositionGroup K w.1) :
          L ≃ₐ[K] L) x) :=
        decompositionGroupToLocalization_toLocalization vK hvK w (σ * τ) x
      _ = i ((σ : L ≃ₐ[K] L) ((τ : L ≃ₐ[K] L) x)) := rfl
      _ = decompositionGroupToLocalization vK hvK w σ
          (i ((τ : L ≃ₐ[K] L) x)) :=
        (decompositionGroupToLocalization_toLocalization
          vK hvK w σ ((τ : L ≃ₐ[K] L) x)).symm
      _ = decompositionGroupToLocalization vK hvK w σ
          (decompositionGroupToLocalization vK hvK w τ (i x)) := by
        exact congrArg (decompositionGroupToLocalization vK hvK w σ)
          (decompositionGroupToLocalization_toLocalization
            vK hvK w τ x).symm
      _ = ρR (i x) := rfl
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hρ x

omit hvK

include hvK

/-- The localization and decomposition comparison (decomposition groups): for a possibly
infinite Galois
extension, the decomposition group at `w` is canonically isomorphic to the
Galois group of the algebraic localization over `K_v`. -/
def decompositionGroupEquivAlgebraicLocalizationAut :
    absoluteValueDecompositionGroup K w.1 ≃*
      (letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
       letI : SMul K w.1.Completion := hK.toSMul
       letI := AbsoluteValue.completionAlgebra vK w.1 w.2
       AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
         AbsoluteValue.algebraicLocalization vK w.1 w.2) where
  toFun := decompositionGroupToLocalization vK hvK w
  invFun := localizationToDecompositionGroup vK hvK w
  left_inv := localizationToDecompositionGroup_decompositionGroupToLocalization
    vK hvK w
  right_inv :=
    decompositionGroupToLocalization_localizationToDecompositionGroup vK hvK w
  map_mul' := decompositionGroupToLocalization_mul vK hvK w

@[simp] theorem localizationRamificationGroups_decompositionGroupEquiv_apply
    (σ : absoluteValueDecompositionGroup K w.1) :
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w σ =
      decompositionGroupToLocalization vK hvK w σ :=
  rfl

@[simp] theorem localizationRamificationGroups_decompositionGroupEquiv_symm_apply
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm τ =
      localizationToDecompositionGroup vK hvK w τ :=
  rfl

theorem localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w σ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 ((σ : L ≃ₐ[K] L) x) :=
  decompositionGroupToLocalization_toLocalization vK hvK w σ x

omit hvK

end DecompositionEquiv

end HilbertRamification
