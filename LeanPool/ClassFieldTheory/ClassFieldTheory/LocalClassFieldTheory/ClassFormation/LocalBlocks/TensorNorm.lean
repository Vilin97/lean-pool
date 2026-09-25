/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
/-!
# The norm image of a local tensor factor

For a finite Galois extension `L / K`, the completion tensor-product theorem decomposes

`K_v ⊗[K] L`

as the product of the completions above `v`.  After choosing one extension
`w`, Galois conjugation identifies every factor with `L_w`.  Consequently
the image of the determinant norm on the tensor algebra is exactly the field
norm subgroup of `L_w / K_v`.

This is the concrete norm-subgroup form of the local calculation used in
the local-block norm calculation, and it is also the bridge between the local cohomology
calculation and multiplicative weak approximation.
-/

@[expose] public section

open scoped BigOperators TensorProduct

noncomputable
section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open ValuationTheory.Completion

universe u

variable {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The determinant norm on the unit group of a local tensor algebra. -/
def localTensorDetNorm
    (vK : AbsoluteValue K ℝ) :
    (LocalTensorAlgebra (L := L) vK)ˣ →*
      vK.Completionˣ :=
  Units.map (Algebra.norm vK.Completion)

/-- The image of the determinant norm on a local tensor algebra. -/
def localTensorNormSubgroup
    (vK : AbsoluteValue K ℝ) :
    Subgroup vK.Completionˣ :=
  (localTensorDetNorm (K := K) (L := L) vK).range

section ChosenCompletion

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- For a right coset of the decomposition group, conjugation followed by
the localization/completion equivalence identifies the corresponding
completion with the chosen algebraic localization. -/
noncomputable def rightCosetCompletionAlgEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :
        Algebra vK.Completion
          (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (rightCosetExtensionEquiv vK hvK w q).1
        (rightCosetExtensionEquiv vK hvK w q).2
    (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃ₐ[vK.Completion] LocalizedCompletion vK
      w := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI :
      Algebra vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    AbsoluteValue.completionAlgebra vK
      (rightCosetExtensionEquiv vK hvK w q).1
      (rightCosetExtensionEquiv vK hvK w q).2
  let eConj :
      (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃ₐ[vK.Completion] w.1.Completion :=
    { conjugateExtensionCompletionRingEquiv
        vK w (Quotient.out q) with
      commutes' :=
        conjugateExtensionCompletionRingEquiv_algebraMap
          vK w (Quotient.out q) }
  exact eConj.trans
    (localizedCompletionEquivCompletion vK hvK w).symm

/-- Transporting a completion unit to the chosen localization preserves
its determinant norm over the completed base field. -/
theorem normUnits_rightCosetCompletionAlgEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1))
    (z :
      ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :
        Algebra vK.Completion
          (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (rightCosetExtensionEquiv vK hvK w q).1
        (rightCosetExtensionEquiv vK hvK w q).2
    letI : Module.Finite vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      completionModuleFinite vK hvK
        (rightCosetExtensionEquiv vK hvK w q)
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    normUnits vK.Completion (LocalizedCompletion vK w)
        (Units.mapEquiv
          (rightCosetCompletionAlgEquiv
            vK hvK w q).toMulEquiv z) =
      Units.map (Algebra.norm vK.Completion) z := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ :
      Algebra vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    AbsoluteValue.completionAlgebra vK
      (rightCosetExtensionEquiv vK hvK w q).1
      (rightCosetExtensionEquiv vK hvK w q).2
  let _ : Module.Finite vK.Completion
      (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    completionModuleFinite vK hvK
      (rightCosetExtensionEquiv vK hvK w q)
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  apply Units.ext
  change
    Algebra.norm vK.Completion
        (rightCosetCompletionAlgEquiv vK hvK w q
          (z :
            (rightCosetExtensionEquiv
              vK hvK w q).1.Completion)) =
      Algebra.norm vK.Completion
        (z :
          (rightCosetExtensionEquiv
            vK hvK w q).1.Completion)
  exact Algebra.norm_eq_of_algEquiv
    (rightCosetCompletionAlgEquiv vK hvK w q) _

/-- The completion tensor-product decomposition, with all factors transported to the one
chosen algebraic localization. -/
noncomputable def localTensorUnitsEquivChosenCoordinates :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (LocalTensorAlgebra (L := L) vK)ˣ ≃*
      (InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) →
        (LocalizedCompletion vK w)ˣ) := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (localTensorUnitsEquivCompletionProduct
      vK hvK).trans
      (completionProductUnitsEquivRightCosets
        vK hvK w)

/-- The finite set of right cosets of the decomposition group.  It is
packaged explicitly so statements about products do not depend on a chosen
`Fintype` structure for the quotient. -/
noncomputable def decompositionRightCosetsFinset :
    Finset
      (InducedRightCosets
        (absoluteValueDecompositionGroup K w.1)) :=
  @Finset.univ _ (Fintype.ofFinite _)

omit [IsGalois K L] in
@[simp]
theorem mem_decompositionRightCosetsFinset
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    q ∈ decompositionRightCosetsFinset
      (K := K) (vK := vK) (w := w) := by
  simp [decompositionRightCosetsFinset]

/-- The field norm of a transported coordinate is the determinant norm
of the original completion coordinate. -/
theorem normUnits_completionProductUnitsEquivRightCosets
    (p : ∀ w' : AbsoluteValueExtension vK L,
      w'.1.Completionˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w'.1.Completion :=
      fun w' ↦ completionModuleFinite vK hvK w'
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    normUnits vK.Completion (LocalizedCompletion vK w)
        (completionProductUnitsEquivRightCosets
          vK hvK w p q) =
      Units.map (Algebra.norm vK.Completion)
        (p (rightCosetExtensionEquiv vK hvK w q)) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  rw [← normUnits_rightCosetCompletionAlgEquiv
    vK hvK w q
      (p (rightCosetExtensionEquiv vK hvK w q))]
  congr 1

/-- The determinant norm on `K_v ⊗[K] L` is the product of the field
norms of its coordinates after all factors have been transported to the
chosen localization. -/
theorem localTensorDetNorm_eq_prod_chosenCoordinates
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w'.1.Completion :=
      fun w' ↦ completionModuleFinite vK hvK w'
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    localTensorDetNorm (K := K) (L := L) vK z =
      ∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q) := by
  classical
  let _ :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  apply Units.ext
  change
    Algebra.norm vK.Completion
        (z : LocalTensorAlgebra (L := L) vK) =
      ((∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q) : vK.Completionˣ) :
        vK.Completion)
  have hnorm :=
    RelativeIdeleGroup.localNorm_units_eq_prod
      vK hvK z
  change
    Algebra.norm vK.Completion
        (z : LocalTensorAlgebra (L := L) vK) =
      ∏ w' : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecompositionLeft
            (K := K) (L := L) vK hvK
            (z : LocalTensorAlgebra (L := L) vK) w')
    at hnorm
  rw [hnorm]
  change
    (∏ w' : AbsoluteValueExtension vK L,
      Algebra.norm vK.Completion
        (completionTensorDecompositionLeft
          (K := K) (L := L) vK hvK
          (z : LocalTensorAlgebra (L := L) vK) w')) =
      Units.coeHom vK.Completion
        (∏ q ∈ decompositionRightCosetsFinset
            (K := K) (vK := vK) (w := w),
          normUnits vK.Completion
            (LocalizedCompletion vK w)
            (localTensorUnitsEquivChosenCoordinates
              vK hvK w z q))
  rw [map_prod]
  rw [show decompositionRightCosetsFinset
      (K := K) (vK := vK) (w := w) =
      Finset.univ by
    ext q
    simp]
  rw [← (rightCosetExtensionEquiv
    vK hvK w).prod_comp]
  apply Finset.prod_congr rfl
  intro q _
  have h :=
    normUnits_completionProductUnitsEquivRightCosets
      vK hvK w
      (localTensorUnitsEquivCompletionProduct vK hvK z) q
  exact (congrArg (fun x : vK.Completionˣ ↦
    (x : vK.Completion)) h).symm

/-- **Local tensor norm image.**  The determinant norm image of the local
tensor algebra is exactly the field-norm subgroup of any chosen completion
above `v`. -/
theorem localTensorNormSubgroup_eq_localNormSubgroup
    (hvK : vK.IsNontrivial) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    localTensorNormSubgroup (K := K) (L := L) vK =
      localNormSubgroup vK.Completion
        (LocalizedCompletion vK w) := by
  classical
  let _ :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
  ext x
  change
    (∃ z : (LocalTensorAlgebra (L := L) vK)ˣ,
      localTensorDetNorm (K := K) (L := L) vK z = x) ↔
      ∃ y : (LocalizedCompletion vK w)ˣ,
        normUnits vK.Completion
          (LocalizedCompletion vK w) y = x
  constructor
  · rintro ⟨z, rfl⟩
    refine
      ⟨∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        localTensorUnitsEquivChosenCoordinates
          vK hvK w z q, ?_⟩
    rw [map_prod,
      localTensorDetNorm_eq_prod_chosenCoordinates
        vK hvK w z]
  · rintro ⟨y, rfl⟩
    let q₀ : InducedRightCosets
        (absoluteValueDecompositionGroup K w.1) :=
      Quotient.mk'' (1 : L ≃ₐ[K] L)
    let f :
        InducedRightCosets
            (absoluteValueDecompositionGroup K w.1) →
          (LocalizedCompletion vK w)ˣ :=
      fun q ↦ if q₀ = q then y else 1
    let z : (LocalTensorAlgebra (L := L) vK)ˣ :=
      (localTensorUnitsEquivChosenCoordinates
        vK hvK w).symm f
    refine ⟨z, ?_⟩
    rw [localTensorDetNorm_eq_prod_chosenCoordinates
      vK hvK w z]
    change
      (∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q)) =
        normUnits vK.Completion
          (LocalizedCompletion vK w) y
    rw [(localTensorUnitsEquivChosenCoordinates
      vK hvK w).apply_symm_apply f]
    have hq₀ :
        q₀ ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w) :=
      mem_decompositionRightCosetsFinset
        (K := K) (vK := vK) (w := w) q₀
    simpa only [f, apply_ite, map_one] using
      Finset.prod_ite_eq_of_mem
        (decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w))
        q₀
        (fun _ ↦
          normUnits vK.Completion
            (LocalizedCompletion vK w) y)
        hq₀

end ChosenCompletion

end LocalClassFieldTheory
