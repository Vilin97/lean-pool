/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.NumberField
public import LeanPool.Odlyzko.Theta.TracePairing

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

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
