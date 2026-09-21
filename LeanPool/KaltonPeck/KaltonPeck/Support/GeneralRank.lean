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
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim
import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity
import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm

/-!
# General rank-parity reduction

This file analyzes the kernel of a finite-rank polynomial defect, constructs the associated
rank-parity form, and proves evenness of its restricted radical.
-/

namespace KaltonPeck.Support.GeneralRank

noncomputable
section

/-- The kernel of `T ² + I` is closed, finite-codimensional, invariant under `T`, and carries
the restricted complex structure.

Blueprint: `lem:finite-rank-kernel`; audit: `AUX-FINITE-RANK-KERNEL-CODIM`. -/
theorem finiteRankPolynomialKernel {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (T : X →L[ℝ] X)
    (hFiniteRank : HasFiniteRank (T ^ 2 + 1)) :
    IsClosed ((T ^ 2 + 1).toLinearMap.ker : Set X) ∧
      FiniteDimensional ℝ (X ⧸ (T ^ 2 + 1).toLinearMap.ker) ∧
      Module.finrank ℝ (X ⧸ (T ^ 2 + 1).toLinearMap.ker) =
        operatorRank (T ^ 2 + 1) ∧
      (∀ x : (T ^ 2 + 1).toLinearMap.ker,
        T (x : X) ∈ (T ^ 2 + 1).toLinearMap.ker) ∧
      ∀ x : (T ^ 2 + 1).toLinearMap.ker, T (T (x : X)) = -(x : X) := by
  obtain ⟨hclosed, hfinite, hdim, _⟩ :=
    Fredholm.quotientKernelRange (T ^ 2 + 1) hFiniteRank
  refine ⟨hclosed, hfinite, hdim, ?_, ?_⟩
  · intro x
    have hx := x.property
    change T (T (T (x : X))) + T (x : X) = 0
    change T (T (x : X)) + (x : X) = 0 at hx
    rw [← map_add]
    rw [hx, map_zero]
  · intro x
    have hx := x.property
    change T (T (x : X)) + (x : X) = 0 at hx
    exact eq_neg_of_add_eq_zero_left hx

/-- The auxiliary alternating Fredholm form, together with every identity used downstream.

Blueprint: `lem:rank-parity-form`; audit: `AUX-RANK-PARITY-FORM`. -/
structure RankParityFormData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (omega : StrongSymplecticForm X) (T : X →L[ℝ] X) where
  /-- The auxiliary alternating form associated to `I + T⁺T`. -/
  form : ContinuousAlternatingForm X
  form_apply (x y : X) :
    form.toDual x y = omega.toDual ((1 + omega.adjoint T * T) x) y
  form_apply_expanded (x y : X) :
    form.toDual x y = omega.toDual x y + omega.toDual (T x) (T y)
  inducedOperator :
    form.toDual =
      omega.toDual.toContinuousLinearMap.comp (1 + omega.adjoint T * T)
  radical_eq_kernel :
    form.radical = (1 + omega.adjoint T * T).toLinearMap.ker
  isFredholm (hFredholm : IsFredholm (1 + omega.adjoint T * T)) :
    IsFredholm form.toDual

/-- The auxiliary form `eta(x,y) = omega((I + T⁺T)x,y)` and its structural identities.

Blueprint: `lem:rank-parity-form`. -/
def rankParityForm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (T : X →L[ℝ] X) :
    RankParityFormData omega T := by
  let G : X →L[ℝ] X := 1 + omega.adjoint T * T
  have hadjoint (x y : X) :
      omega.toDual (omega.adjoint T x) y = omega.toDual x (T y) := by
    simp [StrongSymplecticForm.adjoint, transpose]
  let eta : ContinuousAlternatingForm X :=
    { toDual := omega.toDual.toContinuousLinearMap.comp G
      alternating := by
        intro x
        change omega.toDual (G x) x = 0
        rw [show G x = x + omega.adjoint T (T x) by simp [G]]
        rw [map_add, add_apply, hadjoint]
        simp [omega.alternating] }
  refine
    { form := eta
      form_apply := ?_
      form_apply_expanded := ?_
      inducedOperator := ?_
      radical_eq_kernel := ?_
      isFredholm := ?_ }
  · intro x y
    change omega.toDual (G x) y = _
    rfl
  · intro x y
    change omega.toDual (G x) y = _
    rw [show G x = x + omega.adjoint T (T x) by simp [G]]
    rw [map_add, add_apply, hadjoint]
  · change omega.toDual.toContinuousLinearMap.comp G = _
    rfl
  · ext x
    simp only [eta, ContinuousAlternatingForm.radical, LinearMap.mem_ker]
    change omega.toDual (G x) = 0 ↔ G x = 0
    constructor
    · intro hx
      apply omega.toDual.injective
      simpa using hx
    · intro hx
      rw [hx, map_zero]
  · intro hFredholm
    rcases hFredholm with ⟨hKernel, hRange, hCokernel⟩
    have hKernelEq :
        (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.ker =
          G.toLinearMap.ker := by
      ext x
      simp only [LinearMap.mem_ker]
      change omega.toDual (G x) = 0 ↔ G x = 0
      constructor
      · intro hx
        apply omega.toDual.injective
        simpa using hx
      · intro hx
        rw [hx, map_zero]
    have hRangeEq :
        (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.range =
          G.toLinearMap.range.map omega.toDual.toLinearEquiv.toLinearMap := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨G x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hKernelEq]
      exact hKernel
    · rw [hRangeEq]
      apply IsComplete.isClosed
      change IsComplete (omega.toDual '' (G.toLinearMap.range : Set X))
      exact omega.toDual.isUniformEmbedding.isComplete_iff.mpr hRange.isComplete
    · let eCoker :
          (X ⧸ G.toLinearMap.range) ≃ₗ[ℝ]
            (StrongDual ℝ X ⧸
              (omega.toDual.toContinuousLinearMap.comp G).toLinearMap.range) :=
        Submodule.Quotient.equiv _ _ omega.toDual.toLinearEquiv hRangeEq.symm
      let : FiniteDimensional ℝ (X ⧸ G.toLinearMap.range) := hCokernel
      exact FiniteDimensional.of_surjective eCoker.toLinearMap eCoker.surjective

/-- The restricted radical is `T`-invariant and has even real dimension.

Blueprint: `lem:restricted-radical-even`; audit: `AUX-ETA-T-INVARIANT-ON-E`,
`AUX-ETA-T-SKEW-ON-E`, `AUX-RESTRICTED-RADICAL-T-INVARIANT`, and
`LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem restrictedRadicalEven {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (omega : StrongSymplecticForm X)
    (T : X →L[ℝ] X) (hFiniteRank : HasFiniteRank (T ^ 2 + 1)) :
    (∀ x : (rankParityForm omega T).form.restrictedRadical
        (T ^ 2 + 1).toLinearMap.ker,
      T (x : X) ∈
        (rankParityForm omega T).form.restrictedRadical (T ^ 2 + 1).toLinearMap.ker) ∧
      Even (Module.finrank ℝ
        ((rankParityForm omega T).form.restrictedRadical
          (T ^ 2 + 1).toLinearMap.ker)) := by
  let E := (T ^ 2 + 1).toLinearMap.ker
  let eta := (rankParityForm omega T).form
  let R := eta.restrictedRadical E
  change (∀ x : R, T (x : X) ∈ R) ∧ Even (Module.finrank ℝ R)
  obtain ⟨_, _, _, hTE, hT2⟩ := finiteRankPolynomialKernel T hFiniteRank
  have hRE (x : R) : (x : X) ∈ E := by
    have hx := x.property
    change (x : X) ∈ E ⊓ eta.orthogonal E at hx
    exact hx.1
  have hR : ∀ x : R, T (x : X) ∈ R := by
    intro x
    have hx := x.property
    change (x : X) ∈ E ⊓ eta.orthogonal E at hx
    change T (x : X) ∈ E ⊓ eta.orthogonal E
    refine ⟨hTE ⟨x, hx.1⟩, ?_⟩
    have hxZero (z : E) : eta.toDual (x : X) (z : X) = 0 := by
      have hxOrth := hx.2
      change
        (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ E X ℝ))
          E.subtypeL).comp eta.toDual).toLinearMap (x : X) = 0 at hxOrth
      exact DFunLike.congr_fun hxOrth z
    change
      (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ E X ℝ))
        E.subtypeL).comp eta.toDual).toLinearMap (T (x : X)) = 0
    apply ContinuousLinearMap.ext
    intro y
    change eta.toDual (T (x : X)) (y : X) = 0
    let Ty : E := ⟨T (y : X), hTE y⟩
    have hxy : eta.toDual (x : X) (T (y : X)) = 0 := hxZero Ty
    have hx2 : T (T (x : X)) = -(x : X) := hT2 ⟨x, hx.1⟩
    have hy2 : T (T (y : X)) = -(y : X) := hT2 y
    have h1 := (rankParityForm omega T).form_apply_expanded (T (x : X)) (y : X)
    have h2 := (rankParityForm omega T).form_apply_expanded (x : X) (T (y : X))
    change eta.toDual (T (x : X)) (y : X) =
      omega.toDual (T (x : X)) (y : X) +
        omega.toDual (T (T (x : X))) (T (y : X)) at h1
    change eta.toDual (x : X) (T (y : X)) =
      omega.toDual (x : X) (T (y : X)) +
        omega.toDual (T (x : X)) (T (T (y : X))) at h2
    rw [hx2] at h1
    rw [hy2] at h2
    simp only [map_neg, neg_apply] at h1 h2
    linarith
  refine ⟨hR, ?_⟩
  apply FiniteParity.finiteInvariantSubmoduleComplexDimensionEven T.toLinearMap R hR
  intro x
  exact hT2 ⟨x, hRE x⟩

end

end KaltonPeck.Support.GeneralRank

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
