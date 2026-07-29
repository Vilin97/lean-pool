/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.TraceDualIdeal
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.Trace.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

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
