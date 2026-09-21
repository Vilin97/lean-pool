/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81ApproximationReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81Majorization

/-! # Theorem81Majorization Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1(iii) over a REAL Hilbert space

The printed clause is, for every symmetric gauge `Φ`,

  `Φ(α₁ - α, …, αₙ - α) ≤ Φ((λ₁ - α) cos²θ₁, …, (λₙ - α) cos²θₙ)`,

and the printed standing assumption is that the Hilbert space is real *or*
complex.  `Section8PartIII.lean` proves it over `ℂ`; this module proves it over
`ℝ`.

## Not a descent

Unlike part (ii), nothing here is transported.  Both links of the two-link chain
are already available over `ℝ`:

* the pointwise Weyl step is `theorem8_1_upperSandwichApproximation_real`, which
  *is* the descended one; and
* the second link,
  `TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized`, is stated for
  an arbitrary `RCLike` field, so it applies at `ℝ` directly.

In particular the finite-rank reindex is done over `Fin (Module.finrank ℝ E)`
natively, with no appeal to `Module.finrank ℂ (RealComplexification E)`.

## The finite-dimensional hypothesis

`[FiniteDimensional ℝ E]` is **the paper's own restriction in this clause** -- a
symmetric gauge is a function of a finite sequence -- and is not a narrowing
introduced by the formalization.  Parts (i) and (ii), and the whole of 8.1(a)
and 8.1(b), are dimension-free over `ℝ` as well as over `ℂ`.

## Both blocks

The printed "with a similar relation for `Λ₀`" is
`theorem8_1_lowerWeightedWeakMajorization_real` and its symmetric-gauge
corollary, against the mirrored objects `lowerBlockShift` and
`lowerCosineBlock`.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Davis--Kahan 1970, Theorem 8.1(iii), upper block, over a REAL Hilbert
space: the weak-majorization core.**

  `a(A₁ - α)  ≺w  (i ↦ aᵢ(Λ₁ - α) · aᵢ(C₁)²)`.

Same two links as the complex proof: the pointwise real Weyl step, packaged by
`FiniteVector.WeaklyMajorized.of_pointwise`, then the `RCLike`-generic
positive-sandwich weak majorization, whose middle factor is positive by
`theorem8_1_perturbedUpperBlockShift_nonneg_real`. -/
theorem theorem8_1_upperWeightedWeakMajorization_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) := by
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp
    with hQdef
  -- The perturbed upper block is the positive middle factor of the sandwich.
  have hM : (0 : E →L[ℝ] E) ≤ upperBlockShift (A + K) Q alpha :=
    theorem8_1_perturbedUpperBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  -- Link one: the real Weyl step, promoted from pointwise domination.
  have hstep1 : FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℝ E) =>
        (ContinuousLinearMap.adjoint (cosineBlock P Q) ∘L
          upperBlockShift (A + K) Q alpha ∘L
          cosineBlock P Q).approximationNumber (i : ℕ)) :=
    FiniteVector.WeaklyMajorized.of_pointwise
      (fun i j hij =>
        (upperBlockShift A P alpha).approximationNumber_antitone (Fin.le_def.mp hij))
      (fun i j hij =>
        (ContinuousLinearMap.adjoint (cosineBlock P Q) ∘L
          upperBlockShift (A + K) Q alpha ∘L
          cosineBlock P Q).approximationNumber_antitone (Fin.le_def.mp hij))
      (fun i => (upperBlockShift A P alpha).approximationNumber_nonneg _)
      (fun i => (ContinuousLinearMap.adjoint (cosineBlock P Q) ∘L
        upperBlockShift (A + K) Q alpha ∘L
        cosineBlock P Q).approximationNumber_nonneg _)
      (fun i => theorem8_1_upperSandwichApproximation_real A K P hdelta hA hK
        hAP hPlow hPhigh hKP hKPperp (i : ℕ))
  -- Link two: the generic positive-sandwich weak majorization, at `𝕜 = ℝ`.
  exact hstep1.trans
    (approximationNumber_adjoint_sandwich_weaklyMajorized hM (cosineBlock P Q))

/-- **Davis--Kahan 1970, Theorem 8.1(iii), upper block, over a REAL Hilbert
space: the printed every-symmetric-gauge form.**

  `Φ(α₁ - α, …) ≤ Φ((λ₁ - α) cos²θ₁, …)`   for every symmetric gauge `Φ`.

Immediate from the weak majorization above and Fan dominance. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) :=
  Phi.mono_weaklyMajorized
    (theorem8_1_upperWeightedWeakMajorization_real A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp)

/-! ### The lower block -/

/-- **Davis--Kahan 1970, Theorem 8.1(iii), lower block, over a REAL Hilbert
space: the weak-majorization core.**

  `a((α + δ) - A₀)  ≺w  (i ↦ aᵢ((α + δ) - Λ₀) · aᵢ(C₀)²)`,

the printed lower companion, by the same two links against the mirrored
objects.  No `‖C₀‖²` relaxation is used: the whole cosine sequence is retained,
weight by weight. -/
theorem theorem8_1_lowerWeightedWeakMajorization_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) := by
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp
    with hQdef
  have hM : (0 : E →L[ℝ] E) ≤ lowerBlockShift (A + K) Q alpha delta :=
    theorem8_1_perturbedLowerBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  have hstep1 : FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℝ E) =>
        (ContinuousLinearMap.adjoint (lowerCosineBlock P Q) ∘L
          lowerBlockShift (A + K) Q alpha delta ∘L
          lowerCosineBlock P Q).approximationNumber (i : ℕ)) :=
    FiniteVector.WeaklyMajorized.of_pointwise
      (fun i j hij =>
        (lowerBlockShift A P alpha delta).approximationNumber_antitone
          (Fin.le_def.mp hij))
      (fun i j hij =>
        (ContinuousLinearMap.adjoint (lowerCosineBlock P Q) ∘L
          lowerBlockShift (A + K) Q alpha delta ∘L
          lowerCosineBlock P Q).approximationNumber_antitone (Fin.le_def.mp hij))
      (fun i => (lowerBlockShift A P alpha delta).approximationNumber_nonneg _)
      (fun i => (ContinuousLinearMap.adjoint (lowerCosineBlock P Q) ∘L
        lowerBlockShift (A + K) Q alpha delta ∘L
        lowerCosineBlock P Q).approximationNumber_nonneg _)
      (fun i => theorem8_1_lowerSandwichApproximation_real A K P hdelta hA hK
        hAP hPlow hPhigh hKP hKPperp (i : ℕ))
  exact hstep1.trans
    (approximationNumber_adjoint_sandwich_weaklyMajorized hM (lowerCosineBlock P Q))

/-- **Davis--Kahan 1970, Theorem 8.1(iii), lower block, over a REAL Hilbert
space: the printed every-symmetric-gauge form.**

  `Φ((α + δ) - α₁, …) ≤ Φ(((α + δ) - λ₁) cos²θ₁, …)`   for every symmetric
gauge. -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) :=
  Phi.mono_weaklyMajorized
    (theorem8_1_lowerWeightedWeakMajorization_real A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp)

end

end Section8
end DavisKahan1970
end TauCeti
