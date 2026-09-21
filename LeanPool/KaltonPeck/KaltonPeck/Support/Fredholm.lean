/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Fredholm operator calculus

This file develops quotient-by-kernel descriptions of ranges and proves invariance, composition,
index, and range results for Fredholm operators.
-/

namespace KaltonPeck.Support.Fredholm

noncomputable section

/-- The canonical linear equivalence from a quotient by a kernel onto the range.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
def quotientKernelRangeEquiv {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y) :
    (X ⧸ A.toLinearMap.ker) ≃ₗ[ℝ] A.toLinearMap.range := by
  exact A.toLinearMap.quotKerEquivRange

/-- Evaluation formula for the quotient-by-kernel equivalence.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
theorem quotientKernelRangeEquiv_apply_mk {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y)
    (x : X) :
    ((quotientKernelRangeEquiv A (Submodule.Quotient.mk x) : A.toLinearMap.range) : Y) =
      A x := by
  rfl

/-- Finite-rank consequences of the quotient-by-kernel equivalence.

Blueprint: `lem:quotient-range`; audit: `COV-QUOT-KER-RANGE`. -/
theorem quotientKernelRange {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y)
    (hA : HasFiniteRank A) :
    IsClosed (A.toLinearMap.ker : Set X) ∧
      FiniteDimensional ℝ (X ⧸ A.toLinearMap.ker) ∧
        Module.finrank ℝ (X ⧸ A.toLinearMap.ker) =
          Module.finrank ℝ A.toLinearMap.range ∧
            Module.finrank ℝ (X ⧸ A.toLinearMap.ker) = operatorRank A := by
  letI : FiniteDimensional ℝ A.toLinearMap.range := hA
  exact
    ⟨A.isClosed_ker, (quotientKernelRangeEquiv A).symm.finiteDimensional,
      (quotientKernelRangeEquiv A).finrank_eq,
      (quotientKernelRangeEquiv A).finrank_eq⟩

/-- Fredholmness is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem isFredholm_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup X'] [NormedSpace ℝ X'] [CompleteSpace X']
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [CompleteSpace Y'] (A : X →L[ℝ] Y)
    (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    IsFredholm A ↔
      IsFredholm (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) := by
  let T := U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)
  let kMap : T.toLinearMap.ker →ₗ[ℝ] A.toLinearMap.ker :=
    { toFun := fun x => ⟨V.toLinearEquiv x, by
        have hx := x.property
        change U.toLinearEquiv (A.toLinearMap (V.toLinearEquiv x)) = 0 at hx
        apply U.toLinearEquiv.injective
        simpa only [map_zero] using hx⟩
      map_add' := by
        intro x y
        exact Subtype.ext (V.toLinearEquiv.map_add x y)
      map_smul' := by
        intro c x
        exact Subtype.ext (V.toLinearEquiv.map_smul c x) }
  have hkMap : Function.Bijective kMap := by
    constructor
    · intro x y h
      exact Subtype.ext (V.toLinearEquiv.injective (congrArg Subtype.val h))
    · intro y
      refine ⟨⟨V.symm.toLinearEquiv y, ?_⟩, ?_⟩
      · change U (A (V (V.symm y))) = 0
        rw [V.apply_symm_apply]
        have hy := y.property
        change A y = 0 at hy
        rw [hy, map_zero]
      · exact Subtype.ext (V.apply_symm_apply (y : X))
  let kEquiv : T.toLinearMap.ker ≃ₗ[ℝ] A.toLinearMap.ker :=
    LinearEquiv.ofBijective kMap hkMap
  let cEquiv : (Y' ⧸ T.toLinearMap.range) ≃ₗ[ℝ] (Y ⧸ A.toLinearMap.range) := by
    refine Submodule.Quotient.equiv T.toLinearMap.range A.toLinearMap.range
      U.symm.toLinearEquiv ?_
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx⟩, hz⟩
      subst z
      subst y
      refine ⟨V x, ?_⟩
      simp [T]
    · rintro ⟨x, rfl⟩
      refine ⟨U (A x), ?_, U.symm_apply_apply (A x)⟩
      refine ⟨V.symm x, ?_⟩
      simp [T]
  have hclosed :
      IsClosed (A.toLinearMap.range : Set Y) ↔
        IsClosed (T.toLinearMap.range : Set Y') := by
    have hrange :
        (T.toLinearMap.range : Set Y') = U '' (A.toLinearMap.range : Set Y) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨A (V x), ⟨V x, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨V.symm x, by simp [T]⟩
    rw [hrange]
    constructor
    · exact U.toHomeomorph.isClosedMap _
    · intro h
      have h' :=
        U.symm.toHomeomorph.isClosedMap (U '' (A.toLinearMap.range : Set Y)) h
      have himage :
          U.symm.toHomeomorph '' (U '' (A.toLinearMap.range : Set Y)) =
            (A.toLinearMap.range : Set Y) := by
        ext y
        simp
      rw [himage] at h'
      exact h'
  change IsFredholm A ↔ IsFredholm T
  constructor
  · rintro ⟨hker, hrange, hcoker⟩
    exact ⟨kEquiv.symm.finiteDimensional, hclosed.mp hrange,
      cEquiv.symm.finiteDimensional⟩
  · rintro ⟨hker, hrange, hcoker⟩
    exact ⟨kEquiv.finiteDimensional, hclosed.mpr hrange,
      cEquiv.finiteDimensional⟩

/-- The kernel equivalence induced by bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
def kernelEquivOfEquivComp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)).toLinearMap.ker
      ≃ₗ[ℝ] A.toLinearMap.ker := by
  let f :
      (U.toContinuousLinearMap.comp
        (A.comp V.toContinuousLinearMap)).toLinearMap.ker →ₗ[ℝ]
        A.toLinearMap.ker :=
    { toFun := fun x => ⟨V.toLinearEquiv x, by
        have hx := x.property
        change U.toLinearEquiv (A.toLinearMap (V.toLinearEquiv x)) = 0 at hx
        apply U.toLinearEquiv.injective
        simpa only [map_zero] using hx⟩
      map_add' := by
        intro x y
        exact Subtype.ext (V.toLinearEquiv.map_add x y)
      map_smul' := by
        intro c x
        exact Subtype.ext (V.toLinearEquiv.map_smul c x) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (V.toLinearEquiv.injective (congrArg Subtype.val h))
  · intro y
    refine ⟨⟨V.symm.toLinearEquiv y, ?_⟩, ?_⟩
    · change U (A (V (V.symm y))) = 0
      rw [V.apply_symm_apply]
      have hy := y.property
      change A y = 0 at hy
      rw [hy, map_zero]
    · exact Subtype.ext (V.apply_symm_apply (y : X))

/-- The cokernel equivalence induced by bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
def cokernelEquivOfEquivComp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    (Y' ⧸ (U.toContinuousLinearMap.comp
      (A.comp V.toContinuousLinearMap)).toLinearMap.range) ≃ₗ[ℝ]
        (Y ⧸ A.toLinearMap.range) := by
  refine Submodule.Quotient.equiv
    (U.toContinuousLinearMap.comp
      (A.comp V.toContinuousLinearMap)).toLinearMap.range
    A.toLinearMap.range U.symm.toLinearEquiv ?_
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, hz⟩
    subst z
    subst y
    refine ⟨V x, ?_⟩
    simp
  · rintro ⟨x, rfl⟩
    refine ⟨U (A x), ?_, U.symm_apply_apply (A x)⟩
    refine ⟨V.symm x, ?_⟩
    simp

/-- Nullity is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem nullity_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    nullity (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) = nullity A := by
  exact (kernelEquivOfEquivComp A U V).finrank_eq

/-- Cokernel dimension is invariant under bounded equivalences on source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem cokernelFinrank_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    Module.finrank ℝ
        (Y' ⧸ (U.toContinuousLinearMap.comp
          (A.comp V.toContinuousLinearMap)).toLinearMap.range) =
      Module.finrank ℝ (Y ⧸ A.toLinearMap.range) := by
  exact (cokernelEquivOfEquivComp A U V).finrank_eq

/-- Fredholm index is invariant under bounded equivalences on the source and target.

Blueprint: `lem:fredholm-calculus`, item 1; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholmIndex_equiv_comp {X Y X' Y' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] (A : X →L[ℝ] Y) (U : Y ≃L[ℝ] Y') (V : X' ≃L[ℝ] X) :
    fredholmIndex (U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap)) =
      fredholmIndex A := by
  unfold fredholmIndex
  rw [nullity_equiv_comp, cokernelFinrank_equiv_comp]

/-- Multiplication by a nonzero real scalar preserves Fredholmness and index.

Blueprint: `lem:fredholm-calculus`, item 2; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholm_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (a : ℝ) (ha : a ≠ 0) :
    (IsFredholm (a • A) ↔ IsFredholm A) ∧ fredholmIndex (a • A) = fredholmIndex A := by
  have hker : (a • A).toLinearMap.ker = A.toLinearMap.ker := by
    change (a • A.toLinearMap).ker = A.toLinearMap.ker
    exact LinearMap.ker_smul _ _ ha
  have hrange : (a • A).toLinearMap.range = A.toLinearMap.range := by
    change (a • A.toLinearMap).range = A.toLinearMap.range
    exact LinearMap.range_smul _ _ ha
  unfold IsFredholm fredholmIndex nullity
  rw [hker, hrange]
  constructor <;> rfl

/-- Injective postcomposition does not change the kernel.

Blueprint: `lem:fredholm-calculus`, item 2; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem ker_comp_of_injective {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z)
    (hC : Function.Injective C) :
    (C.comp A).toLinearMap.ker = A.toLinearMap.ker := by
  ext x
  constructor
  · intro hx
    change C (A x) = 0 at hx
    change A x = 0
    apply hC
    simpa using hx
  · intro hx
    change A x = 0 at hx
    change C (A x) = 0
    rw [hx, map_zero]

/-- A composition of Fredholm maps is Fredholm.

Blueprint: `lem:fredholm-calculus`, item 3; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem isFredholm_comp {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) (hA : IsFredholm A) (hB : IsFredholm B) :
    IsFredholm (B.comp A) := by
  letI : FiniteDimensional ℝ A.toLinearMap.ker := hA.1
  letI : FiniteDimensional ℝ B.toLinearMap.ker := hB.1
  letI : FiniteDimensional ℝ (Y ⧸ A.toLinearMap.range) := hA.2.2
  letI : FiniteDimensional ℝ (Z ⧸ B.toLinearMap.range) := hB.2.2
  have hker : FiniteDimensional ℝ (B.comp A).toLinearMap.ker := by
    change FiniteDimensional ℝ (B.toLinearMap.comp A.toLinearMap).ker
    rw [LinearMap.ker_comp]
    infer_instance
  have hcoker : FiniteDimensional ℝ (Z ⧸ (B.comp A).toLinearMap.range) := by
    change FiniteDimensional ℝ (Z ⧸ (B.toLinearMap.comp A.toLinearMap).range)
    rw [LinearMap.range_comp]
    infer_instance
  refine ⟨hker, ?_, hcoker⟩
  letI : CompleteSpace B.toLinearMap.range := hB.2.1.completeSpace_coe
  let f : Y →L[ℝ] B.toLinearMap.range := B.rangeRestrict
  have hfq : Topology.IsQuotientMap f :=
    f.isQuotientMap B.toLinearMap.surjective_rangeRestrict
  have himage : IsClosed
      ((Submodule.map f.toLinearMap A.toLinearMap.range :
        Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range) := by
    apply hfq.isClosed_preimage.mp
    change IsClosed
      ((Submodule.comap f.toLinearMap
        (Submodule.map f.toLinearMap A.toLinearMap.range) : Submodule ℝ Y) : Set Y)
    rw [Submodule.comap_map_eq]
    have hfker : f.toLinearMap.ker = B.toLinearMap.ker := by
      simp [f]
    rw [hfker]
    exact Submodule.isClosed_sup_finiteDimensional _ _ hA.2.1
  have hclosed : IsClosed
      ((fun y : B.toLinearMap.range => (y : Z)) ''
        ((Submodule.map f.toLinearMap A.toLinearMap.range :
          Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range)) :=
    hB.2.1.isClosedMap_subtype_val _ himage
  rw [show ((B.comp A).toLinearMap.range : Set Z) =
      (fun y : B.toLinearMap.range => (y : Z)) ''
        ((Submodule.map f.toLinearMap A.toLinearMap.range :
          Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range) by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨f (A x), ?_, rfl⟩
      exact ⟨A x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, ⟨x, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩]
  exact hclosed

/-- Fredholm index is additive under composition.

Blueprint: `lem:fredholm-calculus`, item 3; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem fredholmIndex_comp {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z) (hA : IsFredholm A) (hB : IsFredholm B) :
    fredholmIndex (B.comp A) = fredholmIndex B + fredholmIndex A := by
  letI : FiniteDimensional ℝ A.toLinearMap.ker := hA.1
  letI : FiniteDimensional ℝ B.toLinearMap.ker := hB.1
  letI : FiniteDimensional ℝ (Y ⧸ A.toLinearMap.range) := hA.2.2
  letI : FiniteDimensional ℝ (Z ⧸ B.toLinearMap.range) := hB.2.2
  change (B.toLinearMap.comp A.toLinearMap).index =
    B.toLinearMap.index + A.toLinearMap.index
  exact LinearMap.index_comp B.toLinearMap

/-- A bounded left inverse gives zero kernel, finite-dimensional kernel, and closed range.

Blueprint: `lem:fredholm-calculus`, item 4; audit: `INF-FREDHOLM-CALCULUS`. -/
theorem leftInverseKernelRange {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] (A : X →L[ℝ] Y) (hA : A.HasLeftInverse) :
    A.toLinearMap.ker = ⊥ ∧
      FiniteDimensional ℝ A.toLinearMap.ker ∧ IsClosed (A.toLinearMap.range : Set Y) := by
  have hker : A.toLinearMap.ker = ⊥ := A.ker_eq_bot_of_injective hA.injective
  refine ⟨hker, ?_, hA.isClosed_range⟩
  rw [hker]
  infer_instance

/-- Range and index theorem for a skew Fredholm operator into the strong dual.

Blueprint: `lem:skew-fredholm-range`; audit: `AUX-SKEW-FREDHOLM-INDEX-RANGE`. -/
theorem skewFredholmRange {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (S : X →L[ℝ] StrongDual ℝ X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm S)
    (hSkew : (transpose S).comp (NormedSpace.inclusionInDoubleDual ℝ X) = -S) :
    fredholmIndex S = 0 ∧
      S.toLinearMap.range = Forms.continuousAnnihilator S.toLinearMap.ker ∧
        IsClosed (S.toLinearMap.range : Set (StrongDual ℝ X)) := by
  have hskew_eval (x y : X) : S y x = -S x y := by
    have h := congrArg (fun T : X →L[ℝ] StrongDual ℝ X => T x) hSkew
    have h' := congrArg (fun f : StrongDual ℝ X => f y) h
    change S y x = -S x y at h'
    exact h'
  have hrange :
      S.toLinearMap.range = Forms.continuousAnnihilator S.toLinearMap.ker := by
    apply le_antisymm
    · intro f hf
      rcases hf with ⟨x, rfl⟩
      change ((ContinuousLinearMap.compL ℝ S.toLinearMap.ker X ℝ).flip
        S.toLinearMap.ker.subtypeL) (S x) = 0
      apply ContinuousLinearMap.ext
      intro n
      change S x (n : X) = 0
      rw [hskew_eval n x]
      have hn : S (n : X) = 0 := n.property
      rw [hn]
      simp
    · intro f hf
      have hf_double : f ∈ {g : StrongDual ℝ X |
          ∀ G : Forms.continuousAnnihilator S.toLinearMap.range,
            (G : StrongDual ℝ (StrongDual ℝ X)) g = 0} := by
        intro G
        obtain ⟨x, hx⟩ := hReflexive (G : StrongDual ℝ (StrongDual ℝ X))
        have hxker : x ∈ S.toLinearMap.ker := by
          change S x = 0
          apply ContinuousLinearMap.ext
          intro y
          have hG := G.property
          change ((ContinuousLinearMap.compL ℝ S.toLinearMap.range
            (StrongDual ℝ X) ℝ).flip S.toLinearMap.range.subtypeL)
              (G : StrongDual ℝ (StrongDual ℝ X)) = 0 at hG
          have hGy := DFunLike.congr_fun hG
            (⟨S y, ⟨y, rfl⟩⟩ : S.toLinearMap.range)
          change (G : StrongDual ℝ (StrongDual ℝ X)) (S y) = 0 at hGy
          rw [← hx] at hGy
          change S y x = 0 at hGy
          rw [hskew_eval x y] at hGy
          exact neg_eq_zero.mp hGy
        have hf0 := hf
        change ((ContinuousLinearMap.compL ℝ S.toLinearMap.ker X ℝ).flip
          S.toLinearMap.ker.subtypeL) f = 0 at hf0
        have hfx := DFunLike.congr_fun hf0
          (⟨x, hxker⟩ : S.toLinearMap.ker)
        change f x = 0 at hfx
        change (G : StrongDual ℝ (StrongDual ℝ X)) f = 0
        rw [← hx]
        exact hfx
      have hdouble :=
        Forms.continuousDoubleAnnihilator S.toLinearMap.range hFredholm.2.1
      have hmem := congrArg
        (fun A : Set (StrongDual ℝ X) => f ∈ A) hdouble
      exact hmem.mp hf_double
  let kernelToRangeAnnihilator :
      S.toLinearMap.ker →ₗ[ℝ]
        Forms.continuousAnnihilator S.toLinearMap.range :=
    { toFun := fun x => ⟨NormedSpace.inclusionInDoubleDual ℝ X x, by
          change ((ContinuousLinearMap.compL ℝ S.toLinearMap.range
            (StrongDual ℝ X) ℝ).flip S.toLinearMap.range.subtypeL)
              (NormedSpace.inclusionInDoubleDual ℝ X x) = 0
          apply ContinuousLinearMap.ext
          rintro ⟨f, y, rfl⟩
          change S y (x : X) = 0
          rw [hskew_eval (x : X) y]
          have hx : S (x : X) = 0 := x.property
          rw [hx]
          simp⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }
  have hkernelToRangeAnnihilator_injective :
      Function.Injective kernelToRangeAnnihilator := by
    intro x y hxy
    apply Subtype.ext
    apply (NormedSpace.inclusionInDoubleDualLi ℝ).injective
    exact congrArg Subtype.val hxy
  have hkernelToRangeAnnihilator_surjective :
      Function.Surjective kernelToRangeAnnihilator := by
    intro G
    obtain ⟨x, hx⟩ := hReflexive (G : StrongDual ℝ (StrongDual ℝ X))
    have hxker : x ∈ S.toLinearMap.ker := by
      change S x = 0
      apply ContinuousLinearMap.ext
      intro y
      have hG := G.property
      change ((ContinuousLinearMap.compL ℝ S.toLinearMap.range
        (StrongDual ℝ X) ℝ).flip S.toLinearMap.range.subtypeL)
          (G : StrongDual ℝ (StrongDual ℝ X)) = 0 at hG
      have hGy := DFunLike.congr_fun hG
        (⟨S y, ⟨y, rfl⟩⟩ : S.toLinearMap.range)
      change (G : StrongDual ℝ (StrongDual ℝ X)) (S y) = 0 at hGy
      rw [← hx] at hGy
      change S y x = 0 at hGy
      rw [hskew_eval x y] at hGy
      exact neg_eq_zero.mp hGy
    refine ⟨⟨x, hxker⟩, ?_⟩
    apply Subtype.ext
    exact hx
  let kernelEquivRangeAnnihilator :
      S.toLinearMap.ker ≃ₗ[ℝ]
        Forms.continuousAnnihilator S.toLinearMap.range :=
    LinearEquiv.ofBijective kernelToRangeAnnihilator
      ⟨hkernelToRangeAnnihilator_injective,
        hkernelToRangeAnnihilator_surjective⟩
  letI : FiniteDimensional ℝ S.toLinearMap.ker := hFredholm.1
  letI : FiniteDimensional ℝ
      (StrongDual ℝ X ⧸ S.toLinearMap.range) := hFredholm.2.2
  letI : IsClosed (S.toLinearMap.range : Set (StrongDual ℝ X)) := hFredholm.2.1
  have hkernel_annihilator_dim :
      Module.finrank ℝ S.toLinearMap.ker =
        Module.finrank ℝ
          (Forms.continuousAnnihilator S.toLinearMap.range) :=
    kernelEquivRangeAnnihilator.finrank_eq
  have hquotient_annihilator_dim :
      Module.finrank ℝ
          (StrongDual ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range)) =
        Module.finrank ℝ
          (Forms.continuousAnnihilator S.toLinearMap.range) :=
    (Forms.quotientDualEquivAnnihilator
      S.toLinearMap.range).toLinearEquiv.finrank_eq
  have hcontinuousDual_dim :
      Module.finrank ℝ
          (StrongDual ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range)) =
        Module.finrank ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range) := by
    have hcont :
        Module.finrank ℝ
            (Module.Dual ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range)) =
          Module.finrank ℝ
            (StrongDual ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range)) :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
        (E := StrongDual ℝ X ⧸ S.toLinearMap.range) (F' := ℝ)).finrank_eq
    rw [← hcont]
    exact Subspace.dual_finrank_eq
  have hdim :
      Module.finrank ℝ S.toLinearMap.ker =
        Module.finrank ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range) := by
    calc
      Module.finrank ℝ S.toLinearMap.ker =
          Module.finrank ℝ
            (Forms.continuousAnnihilator S.toLinearMap.range) :=
        hkernel_annihilator_dim
      _ = Module.finrank ℝ
          (StrongDual ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range)) :=
        hquotient_annihilator_dim.symm
      _ = Module.finrank ℝ (StrongDual ℝ X ⧸ S.toLinearMap.range) :=
        hcontinuousDual_dim
  refine ⟨?_, hrange, hFredholm.2.1⟩
  simp [fredholmIndex, nullity, hdim]

end

end KaltonPeck.Support.Fredholm

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
