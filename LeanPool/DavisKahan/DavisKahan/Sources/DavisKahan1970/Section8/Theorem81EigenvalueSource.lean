/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81AngleForms

/-!
# Theorem 8.1 (ii) and (iii) on the printed eigenvalue sequences

Parts (ii) and (iii) are printed on *eigenvalues*: `λ_k` are the ordered
eigenvalues of `Λ₁`, `α_k` those of `A₁`, and the clauses read

  (ii)   `α_k − α ≤ ‖C₁‖₁² (λ_k − α)`                    in finite dimensions,
  (iii)  `Φ(α₁ − α, …) ≤ Φ((λ₁ − α)cos²θ₁, …)`           in finite dimensions.

`Theorem81Approximation` and `Theorem81AngleForms` prove them on approximation
numbers, which is the right shape for the mathematics — that reading is
dimension-free, and it is what discharges the printed clause's "and natural
infinite-dimensional extensions".  It is not the printed reading.

`approximationNumber_eq_eigenvalues_of_isPositive` is the correspondence: in
finite dimensions the approximation numbers of a positive operator are its
sorted eigenvalues, and every block appearing in (ii) and (iii) is positive
under Theorem 8.1's hypotheses.  These eight declarations compose that
correspondence into the printed sequences, in both scalar fields.  They are
façades; nothing is proved here.

The symmetry that names the eigenvalue sequences is *derived* here, from `A`
Hermitian, and not asked of the caller: Davis and Kahan do not assume it, so it
must not appear as a hypothesis.
-/

open TauCeti.DavisKahan.Angle
open TauCeti.DavisKahan.Sylvester

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan
open Module (finrank)

noncomputable section

universe u v

/-! ### Symmetry of the blocks, derived rather than assumed

Davis and Kahan do not assume the blocks are symmetric; it follows from `A`
being Hermitian, and it is what names the eigenvalue sequences.  These two
lemmas supply the proof term the printed statements below need, so that no
caller has to. -/

section Symmetry

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type u} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **`A₁ − α` is symmetric**, from `A` Hermitian. -/
theorem isSymmetric_upperBlockShift {A : G →L[𝕜] G} (hA : IsSelfAdjoint A)
    (P : Submodule 𝕜 G) [P.HasOrthogonalProjection] (alpha : ℝ) :
    (upperBlockShift A P alpha : G →ₗ[𝕜] G).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (upperBlockShift_isSelfAdjoint A P alpha hA)

/-- **`(α + δ) − A₀` is symmetric**, from `A` Hermitian. -/
theorem isSymmetric_lowerBlockShift {A : G →L[𝕜] G} (hA : IsSelfAdjoint A)
    (P : Submodule 𝕜 G) [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    (lowerBlockShift A P alpha delta : G →ₗ[𝕜] G).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (lowerBlockShift_isSelfAdjoint A P alpha delta hA)

end Symmetry

section Complex

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 8.1 (ii), upper block, on the printed eigenvalue
sequences.**  `α_k − α ≤ ‖C₁‖₁² (λ_k − α)`, in finite dimensions, with `‖C₁‖₁`
the largest principal cosine of `(Pᗮ, Qᗮ)`. -/
theorem theorem8_1_upperEigenvalueRepulsion_sourceExact [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℂ H)) :
    (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl i ≤
      TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)ᗮ 0 ^ 2 *
          (isSymmetric_upperBlockShift (hA.add hK) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
          alpha).eigenvalues rfl i := by
  have hposA : (upperBlockShift A P alpha : H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg (upperBlockShift_nonneg A P hdelta.le hA hPhigh)
  have hposQ : (upperBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha : H
          →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
  have h := theorem8_1_upperApproximationRepulsion_angle A K P hdelta hA hK hAP hPlow hPhigh hKP
    hKPperp (i : ℕ)
  rw [approximationNumber_eq_eigenvalues_of_isPositive hposA i,
    approximationNumber_eq_eigenvalues_of_isPositive hposQ i] at h
  exact h

/-- **Theorem 8.1 (ii), lower block, on the printed eigenvalue sequences.** -/
theorem theorem8_1_lowerEigenvalueRepulsion_sourceExact [FiniteDimensional ℂ H]
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℂ H)) :
    (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues rfl i ≤
      TauCeti.principalCosines P (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) 0 ^ 2 *
          (isSymmetric_lowerBlockShift (hA.add hK) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha
          delta).eigenvalues rfl i := by
  have hposA : (lowerBlockShift A P alpha delta : H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg (lowerBlockShift_nonneg A P hdelta.le hA hPlow)
  have hposQ : (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha delta :
          H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
  have h := theorem8_1_lowerApproximationRepulsion_angle A K P hdelta hA hK hAP hPlow hPhigh hKP
    hKPperp (i : ℕ)
  rw [approximationNumber_eq_eigenvalues_of_isPositive hposA i,
    approximationNumber_eq_eigenvalues_of_isPositive hposQ i] at h
  exact h
/-- **Davis--Kahan 1970, Theorem 8.1 (iii), upper block, on the printed eigenvalue
sequences.**  `Φ(α₁ − α, …, α_n − α) ≤ Φ((λ₁ − α)cos²θ₁, …, (λ_n − α)cos²θ_n)`,
for every symmetric gauge, in finite dimensions, in the paper's index order. -/
theorem theorem8_1_upperSymmetricGaugeEigenvalue_sourceExact [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) => (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl
      i.rev)
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (isSymmetric_upperBlockShift (hA.add hK) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
          alpha).eigenvalues rfl i.rev *
          TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)ᗮ (i.rev : ℕ) ^
          2) := by
  have hposA : (upperBlockShift A P alpha : H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg (upperBlockShift_nonneg A P hdelta.le hA hPhigh)
  have hposQ : (upperBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha : H
          →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
  have h := theorem8_1_upperSymmetricGaugeRepulsion_angle_rev A K P Phi hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp
  have hfA : (fun i : Fin (finrank ℂ H) =>
      (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ))
      = fun i : Fin (finrank ℂ H) => (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl
        i.rev := by
    funext i
    exact approximationNumber_eq_eigenvalues_of_isPositive hposA i.rev
  have hfQ : (fun i : Fin (finrank ℂ H) =>
      (upperBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
          alpha).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)ᗮ (i.rev : ℕ) ^ 2)
      = fun i : Fin (finrank ℂ H) => (isSymmetric_upperBlockShift (hA.add hK)
        (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
          alpha).eigenvalues rfl i.rev *
        TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)ᗮ (i.rev : ℕ) ^
          2 := by
    funext i
    rw [approximationNumber_eq_eigenvalues_of_isPositive hposQ i.rev]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le (h.trans_eq (congrArg (fun f => Phi f) hfQ))
/-- **Theorem 8.1 (iii), lower block, on the printed eigenvalue sequences.** -/
theorem theorem8_1_lowerSymmetricGaugeEigenvalue_sourceExact [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) => (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues
      rfl i.rev)
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (isSymmetric_lowerBlockShift (hA.add hK) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha
          delta).eigenvalues rfl i.rev *
          TauCeti.principalCosines P (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) (i.rev : ℕ) ^
          2) := by
  have hposA : (lowerBlockShift A P alpha delta : H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg (lowerBlockShift_nonneg A P hdelta.le hA hPlow)
  have hposQ : (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha delta :
          H →ₗ[ℂ] H).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
  have h := theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev A K P Phi hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp
  have hfA : (fun i : Fin (finrank ℂ H) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ))
      = fun i : Fin (finrank ℂ H) => (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues
        rfl i.rev := by
    funext i
    exact approximationNumber_eq_eigenvalues_of_isPositive hposA i.rev
  have hfQ : (fun i : Fin (finrank ℂ H) =>
      (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha
          delta).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines P (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) (i.rev : ℕ) ^ 2)
      = fun i : Fin (finrank ℂ H) => (isSymmetric_lowerBlockShift (hA.add hK)
        (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) alpha
          delta).eigenvalues rfl i.rev *
        TauCeti.principalCosines P (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha) (i.rev : ℕ) ^
          2 := by
    funext i
    rw [approximationNumber_eq_eigenvalues_of_isPositive hposQ i.rev]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le (h.trans_eq (congrArg (fun f => Phi f) hfQ))

end Complex

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Theorem 8.1 (ii), upper block, on the printed eigenvalue sequences, over a
real Hilbert space.** -/
theorem theorem8_1_upperEigenvalueRepulsion_sourceExact_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℝ E)) :
    (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl i ≤
      TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
        hKP hKPperp)ᗮ 0 ^ 2 * (isSymmetric_upperBlockShift (hA.add hK) (canonicalLowBranchReal A
        K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha).eigenvalues rfl i := by
  have hposA : (upperBlockShift A P alpha : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg (upperBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPhigh))
  have hposQ : (upperBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp) alpha : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedUpperBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp)
  have h := theorem8_1_upperApproximationRepulsion_angle_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp (i : ℕ)
  rw [approximationNumber_eq_eigenvalues_of_isPositive hposA i,
    approximationNumber_eq_eigenvalues_of_isPositive hposQ i] at h
  exact h

/-- **Theorem 8.1 (ii), lower block, on the printed eigenvalue sequences, over a
real Hilbert space.** -/
theorem theorem8_1_lowerEigenvalueRepulsion_sourceExact_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (i : Fin (finrank ℝ E)) :
    (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues rfl i ≤
      TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp) 0 ^ 2 * (isSymmetric_lowerBlockShift (hA.add hK) (canonicalLowBranchReal A K P
        hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha delta).eigenvalues rfl i := by
  have hposA : (lowerBlockShift A P alpha delta : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg (lowerBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPlow))
  have hposQ : (lowerBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp) alpha delta : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedLowerBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp)
  have h := theorem8_1_lowerApproximationRepulsion_angle_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp (i : ℕ)
  rw [approximationNumber_eq_eigenvalues_of_isPositive hposA i,
    approximationNumber_eq_eigenvalues_of_isPositive hposQ i] at h
  exact h
/-- **Theorem 8.1 (iii), upper block, on the printed eigenvalue sequences, over a
real Hilbert space.** -/
theorem theorem8_1_upperSymmetricGaugeEigenvalue_sourceExact_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℝ E) => (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl
      i.rev)
      ≤ Phi (fun i : Fin (finrank ℝ E) =>
        (isSymmetric_upperBlockShift (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp) alpha).eigenvalues rfl i.rev *
          TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
            hPhigh hKP hKPperp)ᗮ (i.rev : ℕ) ^ 2) := by
  have hposA : (upperBlockShift A P alpha : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg (upperBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPhigh))
  have hposQ : (upperBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp) alpha : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedUpperBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp)
  have h := theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp
  have hfA : (fun i : Fin (finrank ℝ E) =>
      (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ))
      = fun i : Fin (finrank ℝ E) => (isSymmetric_upperBlockShift hA P alpha).eigenvalues rfl
        i.rev := by
    funext i
    exact approximationNumber_eq_eigenvalues_of_isPositive hposA i.rev
  have hfQ : (fun i : Fin (finrank ℝ E) =>
      (upperBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp) alpha).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
          hKP hKPperp)ᗮ (i.rev : ℕ) ^ 2)
      = fun i : Fin (finrank ℝ E) => (isSymmetric_upperBlockShift (hA.add hK)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
        alpha).eigenvalues rfl i.rev *
        TauCeti.principalCosines Pᗮ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
          hKP hKPperp)ᗮ (i.rev : ℕ) ^ 2 := by
    funext i
    rw [approximationNumber_eq_eigenvalues_of_isPositive hposQ i.rev]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le (h.trans_eq (congrArg (fun f => Phi f) hfQ))
/-- **Theorem 8.1 (iii), lower block, on the printed eigenvalue sequences, over a
real Hilbert space.** -/
theorem theorem8_1_lowerSymmetricGaugeEigenvalue_sourceExact_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℝ E) => (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues
      rfl i.rev)
      ≤ Phi (fun i : Fin (finrank ℝ E) =>
        (isSymmetric_lowerBlockShift (hA.add hK) (canonicalLowBranchReal A K P hdelta hA hK hAP
          hPlow hPhigh hKP hKPperp) alpha delta).eigenvalues rfl i.rev *
          TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
            hKP hKPperp) (i.rev : ℕ) ^ 2) := by
  have hposA : (lowerBlockShift A P alpha delta : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg (lowerBlockShift_nonneg A P hdelta.le hA
      (by simpa only [RCLike.re_to_real] using hPlow))
  have hposQ : (lowerBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp) alpha delta : E →ₗ[ℝ] E).IsPositive :=
    isPositive_toLinearMap_of_nonneg
      (theorem8_1_perturbedLowerBlockShift_nonneg_real A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp)
  have h := theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp
  have hfA : (fun i : Fin (finrank ℝ E) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ))
      = fun i : Fin (finrank ℝ E) => (isSymmetric_lowerBlockShift hA P alpha delta).eigenvalues
        rfl i.rev := by
    funext i
    exact approximationNumber_eq_eigenvalues_of_isPositive hposA i.rev
  have hfQ : (fun i : Fin (finrank ℝ E) =>
      (lowerBlockShift (A + K) (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp) alpha delta).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
          hKP hKPperp) (i.rev : ℕ) ^ 2)
      = fun i : Fin (finrank ℝ E) => (isSymmetric_lowerBlockShift (hA.add hK)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) alpha
        delta).eigenvalues rfl i.rev *
        TauCeti.principalCosines P (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
          hKP hKPperp) (i.rev : ℕ) ^ 2 := by
    funext i
    rw [approximationNumber_eq_eigenvalues_of_isPositive hposQ i.rev]
  exact (congrArg (fun f => Phi f) hfA.symm).trans_le (h.trans_eq (congrArg (fun f => Phi f) hfQ))

end Real

end

end Section8
end DavisKahan1970
end TauCeti
