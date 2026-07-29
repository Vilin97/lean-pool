/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.PoissonSummation
public import LeanPool.Odlyzko.Theta.TraceDualIdeal
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Trace.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An euclidean ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (mixedEmbedding.euclidean.toMixed K).toLinearMap

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
theorem covolume_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [euclideanIdealLattice,
    ZLattice.covolume_comap (mixedEmbedding.idealLattice K I)
      MeasureTheory.volume MeasureTheory.volume
      (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    mixedEmbedding.covolume_idealLattice]

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped ComplexConjugate

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A mixed trace pairing used in the Odlyzko-bound argument. -/
noncomputable def mixedTracePairing
    (x y : mixedEmbedding.mixedSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w}, x.1 w * y.1 w) +
    ∑ w : {w : InfinitePlace K // IsComplex w},
      2 * (x.2 w * y.2 w).re

open Classical in
private theorem sum_embeddings_eq_sum_places (z : K) :
    (∑ φ : K →+* ℂ, φ z) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          ((embedding_of_isReal w.2 z : ℝ) : ℂ)) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (w.1.embedding z + conj (w.1.embedding z)) := by
  have hfiber (w : InfinitePlace K) :
      ∑ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ ↦
        InfinitePlace.mk φ = w), φ z =
        if hw : IsReal w then
          w.embedding z
        else
          w.embedding z + conj (w.embedding z) := by
    have hmk (φ : K →+* ℂ) :
        InfinitePlace.mk φ = w ↔
          φ = w.embedding ∨
            ComplexEmbedding.conjugate φ = w.embedding := by
      constructor
      · intro h
        apply mk_eq_iff.mp
        simp_all
      · intro h
        exact (mk_eq_iff.mpr h).trans (mk_embedding w)
    by_cases hw : IsReal w
    · have hconj :
          ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw)
      have hfilter :
          Finset.univ.filter (fun φ : K →+* ℂ ↦
            InfinitePlace.mk φ = w) =
            {w.embedding} := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        rw [hmk]
        constructor
        · rintro (h | h)
          · simp_all
          · have hc := congrArg ComplexEmbedding.conjugate h
            simpa [hconj] using hc
        · simp_all
      simp_all
    · have hne :
          ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
        rwa [Ne, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      have hfilter :
          Finset.univ.filter (fun φ : K →+* ℂ ↦
            InfinitePlace.mk φ = w) =
            {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        rw [hmk]
        constructor
        · rintro (rfl | h)
          · simp
          · right
            have hc := congrArg ComplexEmbedding.conjugate h
            simpa using hc
        · rintro (rfl | rfl) <;> simp
      simp [hfilter, hne.symm, hw,
        ComplexEmbedding.conjugate_coe_eq]
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk
    (fun φ : K →+* ℂ ↦ φ z)]
  simp_rw [hfiber]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (p := fun w : InfinitePlace K ↦ IsReal w)]
  apply congrArg₂
  · apply Finset.sum_congr rfl
    simp_all
  · rw [Fintype.sum_equiv
      (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K ↦ not_isReal_iff_isComplex))]
    simp_all

open Classical in
theorem mixedTracePairing_mixedEmbedding (x y : K) :
    mixedTracePairing K (mixedEmbedding K x) (mixedEmbedding K y) =
      Algebra.trace ℚ K (x * y) := by
  have hemb :
      (∑ σ : K →ₐ[ℚ] ℂ, σ (x * y)) =
        ∑ φ : K →+* ℂ, φ (x * y) := by
    rw [Fintype.sum_equiv RingHom.equivRatAlgHom]
    simp
  have htrace :
      ((Algebra.trace ℚ K (x * y) : ℚ) : ℂ) =
        (∑ w : {w : InfinitePlace K // IsReal w},
            ((embedding_of_isReal w.2 (x * y) : ℝ) : ℂ)) +
          ∑ w : {w : InfinitePlace K // IsComplex w},
            (w.1.embedding (x * y) +
              conj (w.1.embedding (x * y))) := by
    rw [← sum_embeddings_eq_sum_places K (x * y), ← hemb]
    exact trace_eq_sum_embeddings
      (K := ℚ) (L := K) (E := ℂ) (x := x * y)
  have hre :
      Algebra.trace ℚ K (x * y) =
        (∑ w : {w : InfinitePlace K // IsReal w},
            embedding_of_isReal w.2 (x * y)) +
          ∑ w : {w : InfinitePlace K // IsComplex w},
            (w.1.embedding (x * y) +
              conj (w.1.embedding (x * y))).re := by
    simpa only [Complex.add_re, Complex.re_sum, Complex.ofReal_re,
      Complex.ratCast_re] using congrArg Complex.re htrace
  have hreal (w : {w : InfinitePlace K // IsReal w}) :
      embedding_of_isReal w.2 (x * y) =
        embedding_of_isReal w.2 x * embedding_of_isReal w.2 y := by simp
  have hcomplex (w : {w : InfinitePlace K // IsComplex w}) :
      (w.1.embedding (x * y) + conj (w.1.embedding (x * y))).re =
        2 * (w.1.embedding x * w.1.embedding y).re := by
    rw [map_mul]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  simp_rw [hreal, hcomplex] at hre
  simpa only [mixedTracePairing, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex] using hre.symm

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A divide by sqrt two used in the Odlyzko-bound argument. -/
noncomputable def divideBySqrtTwo : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (Real.sqrt 2)⁻¹
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))))

open Classical in
@[simp]
theorem divideBySqrtTwo_symm_apply (z : ℂ) :
    divideBySqrtTwo.symm z = Real.sqrt 2 • z := by
  apply divideBySqrtTwo.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change z = ((Real.sqrt 2)⁻¹ : ℝ) • (Real.sqrt 2 • z)
  simp

open Classical in
/-- An unscale complex coordinates used in the Odlyzko-bound argument. -/
noncomputable def unscaleComplexCoordinates :
    ({w : InfinitePlace K // IsComplex w} → ℂ) ≃L[ℝ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  ContinuousLinearEquiv.piCongrRight fun _ ↦ divideBySqrtTwo

open Classical in
/-- A trace to mixed used in the Odlyzko-bound argument. -/
noncomputable def traceToMixed :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.mixedSpace K :=
  (mixedEmbedding.euclidean.toMixed K).trans
    ((ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K))

open Classical in
/-- A trace embedding used in the Odlyzko-bound argument. -/
noncomputable def traceEmbedding (x : K) :
    mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).symm (mixedEmbedding K x)

open Classical in
/-- A trace ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (traceToMixed K).toLinearMap

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

open Classical in
theorem traceEmbedding_mem_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} :
    traceEmbedding K x ∈ traceIdealLattice K I ↔
      x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  change
    traceToMixed K (traceEmbedding K x) ∈
        mixedEmbedding.idealLattice K I ↔ _
  rw [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply,
    mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (mixedEmbedding_injective K hxy).symm ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

open Classical in
theorem exists_traceEmbedding_eq_of_mem_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {v : mixedEmbedding.euclidean.mixedSpace K}
    (hv : v ∈ traceIdealLattice K I) :
    ∃ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K),
      traceEmbedding K x = v := by
  change traceToMixed K v ∈ mixedEmbedding.idealLattice K I at hv
  rw [mixedEmbedding.mem_idealLattice] at hv
  obtain ⟨x, hx, hvx⟩ := hv
  refine ⟨x, hx, ?_⟩
  apply (traceToMixed K).injective
  rw [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
  simp_all

open Classical in
/-- A trace conjugation used in the Odlyzko-bound argument. -/
noncomputable def traceConjugation :
    mixedEmbedding.euclidean.mixedSpace K ≃ₗᵢ[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ
      (EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}))
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ ↦ Complex.conjLIE)

open Classical in
@[simp]
theorem traceConjugation_involutive
    (x : mixedEmbedding.euclidean.mixedSpace K) :
    traceConjugation K (traceConjugation K x) = x := by
  -- `WithLp.ext_iff` postdates v4.32; `ofLp` injectivity says the same thing.
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · apply WithLp.ofLp_injective
    funext w
    simp [traceConjugation]

open Classical in
theorem inner_traceEmbedding_traceConjugation (x y : K) :
    inner ℝ (traceEmbedding K x)
        (traceConjugation K (traceEmbedding K y)) =
      Algebra.trace ℚ K (x * y) := by
  rw [← mixedTracePairing_mixedEmbedding K x y]
  suffices
    (∑ w : {w : InfinitePlace K // IsReal w},
        embedding_of_isReal w.2 y * embedding_of_isReal w.2 x) +
      ((∑ w : {w : InfinitePlace K // IsComplex w},
          Real.sqrt 2 * (w.1.embedding y).re *
            (Real.sqrt 2 * (w.1.embedding x).re)) -
        ∑ w : {w : InfinitePlace K // IsComplex w},
          Real.sqrt 2 * (w.1.embedding y).im *
            (Real.sqrt 2 * (w.1.embedding x).im)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          embedding_of_isReal w.2 x * embedding_of_isReal w.2 y) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          2 * ((w.1.embedding x).re * (w.1.embedding y).re -
            (w.1.embedding x).im * (w.1.embedding y).im) by
    -- The extra lemmas unfold the `WithLp.linearEquiv` / `prodCongr` wrappers,
    -- which v4.32's default simp set leaves in place.
    simpa [traceEmbedding, traceToMixed, unscaleComplexCoordinates,
      mixedEmbedding.euclidean.toMixed, traceConjugation, mixedTracePairing,
      WithLp.prod_inner_apply, PiLp.inner_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply,
      mixedEmbedding.mixedEmbedding_apply_isReal,
      mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hmul (a b : ℝ) :
      Real.sqrt 2 * a * (Real.sqrt 2 * b) = 2 * (a * b) := by grind
  simp_rw [hmul, mul_sub, Finset.sum_sub_distrib]
  grind

end NumberField.Odlyzko

end

section

open Complex Module NumberField NumberField.InfinitePlace Submodule
open scoped nonZeroDivisors RealInnerProductSpace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A trace ideal real basis used in the Odlyzko-bound argument. -/
noncomputable def traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℝ
      (mixedEmbedding.euclidean.mixedSpace K) :=
  (mixedEmbedding.fractionalIdealLatticeBasis K I).map
    (traceToMixed K).symm.toLinearEquiv

open Classical in
@[simp]
theorem traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    traceIdealRealBasis K I i =
      traceEmbedding K (basisOfFractionalIdeal K I i) := by
  rw [traceIdealRealBasis, Basis.map_apply,
    mixedEmbedding.fractionalIdealLatticeBasis_apply]
  rfl

open Classical in
theorem span_traceIdealRealBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range (traceIdealRealBasis K I)) =
      traceIdealLattice K I := by
  rw [traceIdealLattice]
  let eZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
        mixedEmbedding.mixedSpace K :=
    (traceToMixed K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (traceIdealRealBasis K I) =
        eZ.symm '' Set.range
          (mixedEmbedding.fractionalIdealLatticeBasis K I) := by
    ext x
    simp [eZ, traceIdealRealBasis]
  calc
    span ℤ (Set.range (traceIdealRealBasis K I)) =
        (span ℤ
          (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I))).map
            eZ.symm.toLinearMap := by simp_all
    _ = (mixedEmbedding.idealLattice K I).map
          eZ.symm.toLinearMap := by
      rw [mixedEmbedding.span_idealLatticeBasis]
    _ = ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
          (traceToMixed K).toLinearMap := by
      change (mixedEmbedding.idealLattice K I).map eZ.symm.toLinearMap =
        (mixedEmbedding.idealLattice K I).comap eZ.toLinearMap
      exact Submodule.map_equiv_eq_comap_symm eZ.symm _

open Classical in
theorem innerDualBasis_traceIdealRealBasis_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I) i =
      traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual i)) := by
  have h :
      LinearMap.BilinForm.dualBasis
          (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
          innerBilin_nondegenerate (traceIdealRealBasis K I) =
        fun i ↦ traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i)) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro a b
    rw [traceIdealRealBasis_apply]
    change inner ℝ
      (traceConjugation K
        (traceEmbedding K
          ((basisOfFractionalIdeal K I).traceDual a)))
      (traceEmbedding K (basisOfFractionalIdeal K I b)) = _
    rw [real_inner_comm,
      inner_traceEmbedding_traceConjugation K]
    rw [Module.Basis.trace_mul_traceDual]
    split_ifs <;> norm_num
  exact congrFun h i

open Classical in
theorem span_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range
        (basisOfFractionalIdeal K I).traceDual) =
      ((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.coe_dual (A := ℤ) (K := ℚ)
      (Units.ne_zero I)]
  symm
  apply Submodule.traceDual_span_of_basis ℤ
  ext x
  exact (mem_span_basisOfFractionalIdeal K).symm

open Classical in
/-- A trace embedding int linear map used in the Odlyzko-bound argument. -/
noncomputable def traceEmbeddingIntLinearMap :
    K →ₗ[ℤ] mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).symm.toLinearEquiv.toLinearMap.restrictScalars ℤ).comp
    (mixedEmbedding K).toIntAlgHom.toLinearMap

open Classical in
@[simp]
theorem traceEmbeddingIntLinearMap_apply (x : K) :
    traceEmbeddingIntLinearMap K x = traceEmbedding K x :=
  rfl

open Classical in
/-- A conjugate trace ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def conjugateTraceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (traceIdealLattice K I).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem map_traceEmbeddingIntLinearMap_fractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I : Submodule (𝓞 K) K).restrictScalars ℤ).map
        (traceEmbeddingIntLinearMap K) =
      traceIdealLattice K I := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (traceEmbedding_mem_traceIdealLattice K I).2 hx
  · intro hv
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    exact ⟨x, hx, by simpa using hxv⟩

open Classical in
theorem span_conjugate_traceDual_basisOfFractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  let cZ :
      mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℤ]
      mixedEmbedding.euclidean.mixedSpace K :=
    (traceConjugation K).toLinearEquiv.restrictScalars ℤ
  have hrange :
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) ''
          Set.range (basisOfFractionalIdeal K I).traceDual := by
    ext x
    simp [cZ]
  calc
    span ℤ (Set.range fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) =
        (span ℤ (Set.range
          (basisOfFractionalIdeal K I).traceDual)).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [hrange, Submodule.map_span]
    _ = (((traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).restrictScalars ℤ).map
            (cZ.toLinearMap.comp (traceEmbeddingIntLinearMap K)) := by
      rw [span_traceDual_basisOfFractionalIdeal]
    _ = conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
      rw [Submodule.map_comp, map_traceEmbeddingIntLinearMap_fractionalIdeal]
      rfl

open Classical in
theorem dualLattice_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (traceIdealLattice K I) =
      conjugateTraceIdealLattice K (traceDualIdealUnit K I) := by
  rw [dualLattice, ← span_traceIdealRealBasis K I]
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis
    (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
    innerBilin_nondegenerate (traceIdealRealBasis K I)]
  rw [show Set.range
      (LinearMap.BilinForm.dualBasis
        (innerₗ (mixedEmbedding.euclidean.mixedSpace K))
        innerBilin_nondegenerate (traceIdealRealBasis K I)) =
      Set.range (fun i : Free.ChooseBasisIndex ℤ I ↦
        traceConjugation K
          (traceEmbedding K
            ((basisOfFractionalIdeal K I).traceDual i))) by
    congr 1
    funext i
    exact innerDualBasis_traceIdealRealBasis_apply K I i]
  exact span_conjugate_traceDual_basisOfFractionalIdeal K I

end NumberField.Odlyzko

end
