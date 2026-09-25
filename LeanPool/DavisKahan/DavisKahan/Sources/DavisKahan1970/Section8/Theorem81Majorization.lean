/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81Approximation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SandwichMajorization

/-!
# Davis--Kahan 1970, Theorem 8.1(iii), both blocks

The printed clause is, for every symmetric gauge `Φ`,

  `Φ(α₁ - α, …, αₙ - α) ≤ Φ((λ₁ - α) cos²θ₁, …, (λₙ - α) cos²θₙ)`,

with `αᵢ` the eigenvalues of the unperturbed compression `A₁`, `λᵢ` those of the
perturbed compression `Λ₁`, and `θᵢ` the principal angles, so that the cosine
block `C₁` has singular values `cos θᵢ`.

## Why this is not part (ii)

Part (ii) is the single-index estimate

  `aₙ(A₁ - α) ≤ ‖C₁‖² aₙ(Λ₁ - α)`,

which replaces every `cos²θᵢ` by the largest one.  Part (iii) keeps the *whole*
cosine sequence, weight by weight, and can therefore not be derived from part
(ii)'s conclusion.  What the two clauses genuinely share is the earlier Weyl
step, `theorem8_1_upperSandwichApproximation`:

  `aₙ(A₁ - α) ≤ aₙ(C₁⋆ (Λ₁ - α) C₁)`,

which is part (i) plus form monotonicity, before any estimate on `C₁`.  Part
(ii) follows it with the coarse `‖C₁‖²` sandwich bound; part (iii) follows it
with the weak-majorization sandwich theorem
`TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized`,

  `a(D⋆ M D) ≺w (i ↦ aᵢ(M) aᵢ(D)²)`   for `0 ≤ M`,

which is the generalized von Neumann / rearrangement content of the paper's
proof: the alignment of `Λ₁` with the angle eigenvectors, the rearrangement
comparison and the Ky Fan dominance step are all absorbed there.

## Source dictionary

The statement below is about ambient operators, and reads back to the printed
sequences as follows.

* `upperBlockShift A P alpha = P_{Pᗮ}(A - α)P_{Pᗮ}` is positive here (the form
  of `A` on `Pᗮ` is at least `α + δ`), so its approximation numbers are its
  eigenvalues: the nonzero ones are exactly the `αᵢ - α`, the rest zeros
  contributed by the extension by zero off `Pᗮ`.
* `upperBlockShift (A + K) Q alpha = P_{Qᗮ}(A + K - α)P_{Qᗮ}` is positive for the
  same reason on the canonical branch `Q`, and its nonzero eigenvalues are the
  `λᵢ - α`.
* `cosineBlock P Q = P_{Qᗮ} P_{Pᗮ}` is the ambient `C₁`, whose nonzero singular
  values are the cosines `cos θᵢ` of the principal angles between `Pᗮ` and `Qᗮ`.

So the right-hand sequence below is `(λᵢ - α) cos²θᵢ`, zero-padded, and the
left-hand one is `αᵢ - α`, zero-padded.  Both paddings are by zeros at the tail
of a decreasing nonnegative sequence, which changes neither a prefix sum nor a
symmetric gauge.

`ContinuousLinearMap.approximationNumber` is indexed in **decreasing** order
while the paper prints `λ₁ ≤ λ₂ ≤ ⋯` increasing.  As already recorded for part
(ii), reversing both lists together is a global reindex, and a symmetric gauge
is permutation invariant, so this is the printed statement and not a reordering
of it.

Finite dimension is an explicit hypothesis, matching the printed clause: a
symmetric gauge is a function of a finite sequence.

## Both blocks

The paper's "with a similar relation for `Λ₀`" is
`theorem8_1_lowerWeightedWeakMajorization` and its symmetric-gauge
corollary, proved below by the same two-link chain against the mirrored objects
`lowerBlockShift` and `lowerCosineBlock` of `Section8PartII.lean`.

## Not in this module

No eigenvalue/angle facade is assembled here; that dictionary is
`Section8SourceDictionary.lean`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 8.1(iii), upper block: the weak-majorization
core.**

  `a(A₁ - α)  ≺w  (i ↦ aᵢ(Λ₁ - α) · aᵢ(C₁)²)`,

i.e. every prefix sum of the approximation numbers of the unperturbed upper
block is dominated by the corresponding prefix sum of the cosine-weighted
approximation numbers of the perturbed upper block.  In the printed reading
(see the module docstring) this is

  `(α₁ - α, …)  ≺w  ((λ₁ - α) cos²θ₁, …)`.

The proof is the two-step chain

  `a(S)  ≺w  a(C₁⋆ M C₁)  ≺w  (i ↦ aᵢ(M) aᵢ(C₁)²)`,

whose first link is the pointwise Weyl step of part (i)
(`theorem8_1_upperSandwichApproximation`, packaged by
`FiniteVector.WeaklyMajorized.of_pointwise`) and whose second link is the
generic sandwich majorization for a positive middle factor.  The middle factor
is positive by `theorem8_1_perturbedUpperBlockShift_nonneg`. -/
theorem theorem8_1_upperWeightedWeakMajorization [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) := by
  set Q : Submodule ℂ H := canonicalLowBranch (A + K)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha
    with hQdef
  have : Q.HasOrthogonalProjection := by rw [hQdef]; infer_instance
  -- The perturbed upper block is the positive middle factor of the sandwich.
  have hM : (0 : H →L[ℂ] H) ≤ upperBlockShift (A + K) Q alpha :=
    theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  -- Link one: the Weyl step of part (i), promoted from pointwise domination.
  have hstep1 : FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℂ H) =>
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
      (fun i => theorem8_1_upperSandwichApproximation A K P hdelta hA hK
        hAP hPlow hPhigh hKP hKPperp (i : ℕ))
  -- Link two: the generic positive-sandwich weak majorization.
  exact hstep1.trans
    (approximationNumber_adjoint_sandwich_weaklyMajorized hM (cosineBlock P Q))

/-- **Davis--Kahan 1970, Theorem 8.1(iii), upper block: the printed
every-symmetric-gauge form.**

  `Φ(α₁ - α, …) ≤ Φ((λ₁ - α) cos²θ₁, …)`   for every symmetric gauge `Φ`.

Immediate from the weak majorization above and Fan dominance
(`FiniteSymmetricGauge.mono_weaklyMajorized`): a symmetric gauge is monotone
under weak majorization, so no convexity, permutation-invariance or dominance
argument has to be repeated here. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (Module.finrank ℂ H))
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) :=
  Phi.mono_weaklyMajorized
    (theorem8_1_upperWeightedWeakMajorization A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp)

/-! ### The lower block

The printed "with a similar relation for `Λ₀`" is the same two-link chain, run
through the mirrored objects of `Section8PartII.lean`.  Under the reflection
`A ↦ -A`, `α ↦ -(α + δ)` the upper data becomes the lower data, so no new
majorization theorem appears here: `theorem8_1_lowerSandwichApproximation`
replaces its upper namesake and everything else is unchanged. -/

/-- **Davis--Kahan 1970, Theorem 8.1(iii), lower block: the weak-majorization
core.**

  `a((α + δ) - A₀)  ≺w  (i ↦ aᵢ((α + δ) - Λ₀) · aᵢ(C₀)²)`,

the printed lower companion of `theorem8_1_upperWeightedWeakMajorization`.
Same two links: the pointwise lower Weyl step of part (i), packaged by
`FiniteVector.WeaklyMajorized.of_pointwise`, then the generic positive-sandwich
weak majorization with `theorem8_1_perturbedLowerBlockShift_nonneg` supplying
positivity of the middle factor.  No `‖C₀‖²` relaxation is used: the whole cosine
sequence is retained, weight by weight. -/
theorem theorem8_1_lowerWeightedWeakMajorization [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) := by
  set Q : Submodule ℂ H := canonicalLowBranch (A + K)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha
    with hQdef
  have : Q.HasOrthogonalProjection := by rw [hQdef]; infer_instance
  -- The perturbed lower block is the positive middle factor of the sandwich.
  have hM : (0 : H →L[ℂ] H) ≤ lowerBlockShift (A + K) Q alpha delta :=
    theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  -- Link one: the lower Weyl step of part (i), promoted from pointwise domination.
  have hstep1 : FiniteVector.WeaklyMajorized
      (fun i : Fin (Module.finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      (fun i : Fin (Module.finrank ℂ H) =>
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
      (fun i => theorem8_1_lowerSandwichApproximation A K P hdelta hA hK
        hAP hPlow hPhigh hKP hKPperp (i : ℕ))
  -- Link two: the generic positive-sandwich weak majorization.
  exact hstep1.trans
    (approximationNumber_adjoint_sandwich_weaklyMajorized hM (lowerCosineBlock P Q))

/-- **Davis--Kahan 1970, Theorem 8.1(iii), lower block: the printed
every-symmetric-gauge form.**

  `Φ((α + δ) - α₁, …) ≤ Φ(((α + δ) - λ₁) cos²θ₁, …)`   for every symmetric gauge.

Immediate from the lower weak majorization and Fan dominance, exactly as in the
upper block. -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (Module.finrank ℂ H))
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) :=
  Phi.mono_weaklyMajorized
    (theorem8_1_lowerWeightedWeakMajorization A K P hdelta hA hK hAP
      hPlow hPhigh hKP hKPperp)

end Section8
end DavisKahan1970
end TauCeti
