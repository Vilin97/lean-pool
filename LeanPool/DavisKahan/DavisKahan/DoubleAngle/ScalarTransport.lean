/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.SymmetricNormingScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.UnboundedReflection
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace

/-!
# Scalar transport for the unbounded double-angle hypotheses

The `tan 2Θ` source theorem is built from three pieces of scalar-independent
data: a reducing subspace, an off-diagonal bounded perturbation, and ordered
quadratic-form bounds on the two reducing summands.  This file records that each
piece is invariant under `RCLikeIso` transport.
-/

open scoped InnerProductSpace TauCeti.CompleteSubspace

namespace TauCeti
namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Off-diagonality with respect to a closed splitting is scalar invariant. -/
theorem isOddFor_clm_iff (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (B : E →L[𝕜] E) :
    TauCeti.IsOddFor (submodule (e := e) U) (clm (e := e) B) ↔
      TauCeti.IsOddFor U B := by
  constructor
  · rintro ⟨hUV, hVU⟩
    constructor
    · intro x hx
      have h := hUV (of (e := e) x) ((mem_submodule (e := e)).2 hx)
      rw [submodule_orthogonal] at h
      exact (mem_submodule (e := e)).1 h
    · intro x hx
      have hx' : of (e := e) x ∈ (submodule (e := e) U)ᗮ := by
        rw [submodule_orthogonal]
        exact (mem_submodule (e := e)).2 hx
      exact (mem_submodule (e := e)).1 (hVU (of (e := e) x) hx')
  · rintro ⟨hUV, hVU⟩
    constructor
    · intro x hx
      rw [submodule_orthogonal]
      exact (mem_submodule (e := e)).2
        (hUV (out (e := e) x) ((mem_submodule (e := e)).1 hx))
    · intro x hx
      have hx0 : out (e := e) x ∈ Uᗮ := by
        rw [submodule_orthogonal] at hx
        exact (mem_submodule (e := e)).1 hx
      exact (mem_submodule (e := e)).2 (hVU (out (e := e) x) hx0)

omit [CompleteSpace E] in
/-- A quadratic-form upper bound on a reducing subspace transports unchanged. -/
theorem formUpperOnSubspace_pmap
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} {a : ℝ}
    (h : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ a * ‖(x : E)‖ ^ 2) :
    ∀ x : (pmap (e := e) A).domain,
      (x : ScalarTransport e E) ∈ submodule (e := e) U →
      RCLike.re ⟪pmap (e := e) A x, (x : ScalarTransport e E)⟫_𝕂 ≤
        a * ‖(x : ScalarTransport e E)‖ ^ 2 := by
  intro x hx
  let x0 := domainOut (e := e) A x
  have hx0 : (x0 : E) ∈ U := (mem_submodule (e := e)).1 hx
  have h0 := h x0 hx0
  change RCLike.re (e (⟪A x0, (x0 : E)⟫_𝕜)) ≤ a * ‖(x0 : E)‖ ^ 2
  rwa [e.re_map]

omit [CompleteSpace E] in
/-- A quadratic-form lower bound on the orthogonal summand transports unchanged. -/
theorem formLowerOnOrthogonal_pmap
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} {b : ℝ}
    (h : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜) :
    ∀ x : (pmap (e := e) A).domain,
      (x : ScalarTransport e E) ∈ (submodule (e := e) U)ᗮ →
      b * ‖(x : ScalarTransport e E)‖ ^ 2 ≤
        RCLike.re ⟪pmap (e := e) A x, (x : ScalarTransport e E)⟫_𝕂 := by
  intro x hx
  let x0 := domainOut (e := e) A x
  have hx0 : (x0 : E) ∈ Uᗮ := by
    rw [submodule_orthogonal] at hx
    exact (mem_submodule (e := e)).1 hx
  have h0 := h x0 hx0
  change b * ‖(x0 : E)‖ ^ 2 ≤ RCLike.re (e (⟪A x0, (x0 : E)⟫_𝕜))
  rwa [e.re_map]

omit [CompleteSpace E] in
/-- Ambient projection blocks commute with scalar transport. -/
theorem projectionBlock_clm
    (Ω Γ : Submodule 𝕜 E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    clm (e := e) (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Ω Γ K) =
      TauCeti.DavisKahan.ExactSinTheta.projectionBlock
        (submodule (e := e) Ω) (submodule (e := e) Γ) (clm (e := e) K) := by
  change clm (e := e) (Ω.starProjection * K * Γ.starProjection) =
    (submodule (e := e) Ω).starProjection * clm (e := e) K *
      (submodule (e := e) Γ).starProjection
  rw [clm_mul, clm_mul, starProjection_clm, starProjection_clm]

/-- Symmetric-norm extended gauges of block compressions are scalar invariant. -/
theorem extendedGauge_blockCompression_transport
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    (Ω Γ : Submodule 𝕜 E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.extendedGauge
        (TauCeti.DavisKahan.ExactSinTheta.blockCompression
          (submodule (e := e) Ω) (submodule (e := e) Γ) (clm (e := e) K)) =
      N.extendedGauge (TauCeti.DavisKahan.ExactSinTheta.blockCompression Ω Γ K) := by
  rw [← N.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression
        (submodule (e := e) Ω) (submodule (e := e) Γ) (clm (e := e) K)),
    ← projectionBlock_clm,
    TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge_clm,
    N.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression Ω Γ K)]

/-- Ideal membership of block compressions is scalar invariant. -/
theorem mem_blockCompression_transport_iff
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    (Ω Γ : Submodule 𝕜 E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.Mem (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (submodule (e := e) Ω) (submodule (e := e) Γ) (clm (e := e) K)) ↔
      N.Mem (TauCeti.DavisKahan.ExactSinTheta.blockCompression Ω Γ K) := by
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem
  rw [extendedGauge_blockCompression_transport]

/-- Ordinary symmetric-norm gauges of block compressions are scalar invariant. -/
theorem gauge_blockCompression_transport
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    (Ω Γ : Submodule 𝕜 E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.gauge (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (submodule (e := e) Ω) (submodule (e := e) Γ) (clm (e := e) K)) =
      N.gauge (TauCeti.DavisKahan.ExactSinTheta.blockCompression Ω Γ K) := by
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
  rw [extendedGauge_blockCompression_transport]

/-- The two coordinate presentations of a transported complementary block have the
same approximation-number sequence.  This avoids rewriting the equality
`submodule (Uᗮ) = (submodule U)ᗮ` through dependent subtype instances. -/
theorem blockCompression_orthogonal_transport_hasSameApproximationNumbers
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    (TauCeti.DavisKahan.ExactSinTheta.blockCompression
      (submodule (e := e) U)ᗮ (submodule (e := e) U) (clm (e := e) K)).HasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (submodule (e := e) Uᗮ) (submodule (e := e) U) (clm (e := e) K)) := by
  let P₁ := TauCeti.DavisKahan.ExactSinTheta.projectionBlock
    (submodule (e := e) U)ᗮ (submodule (e := e) U) (clm (e := e) K)
  let P₂ := TauCeti.DavisKahan.ExactSinTheta.projectionBlock
    (submodule (e := e) Uᗮ) (submodule (e := e) U) (clm (e := e) K)
  have hperp : (submodule (e := e) U)ᗮ = submodule (e := e) Uᗮ :=
    submodule_orthogonal (e := e) U
  have hP : P₁ = P₂ := by
    dsimp [P₁, P₂, TauCeti.DavisKahan.ExactSinTheta.projectionBlock]
    rw [Submodule.starProjection_congr hperp]
  have h₁ := TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression
    (submodule (e := e) U)ᗮ (submodule (e := e) U) (clm (e := e) K)
  have h₂ := TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression
    (submodule (e := e) Uᗮ) (submodule (e := e) U) (clm (e := e) K)
  have hPseq : P₁.HasSameApproximationNumbers P₂ := by
    rw [hP]
  exact ContinuousLinearMap.HasSameApproximationNumbers.trans
    (ContinuousLinearMap.HasSameApproximationNumbers.symm h₁)
    (ContinuousLinearMap.HasSameApproximationNumbers.trans hPseq h₂)

/-- Symmetric-norm ideal membership for the transported complementary block can be
stated directly with `(submodule U)ᗮ`, without dependent rewriting. -/
theorem mem_blockCompression_orthogonal_transport_iff
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.Mem (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (submodule (e := e) U)ᗮ (submodule (e := e) U) (clm (e := e) K)) ↔
      N.Mem (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U K) := by
  have hcoord := blockCompression_orthogonal_transport_hasSameApproximationNumbers
    (e := e) U K
  have htransport := extendedGauge_blockCompression_transport (e := e) N Uᗮ U K
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem
  rw [N.extendedGauge_eq_of_hasSameApproximationNumbers hcoord, htransport]

/-- Symmetric-norm gauges of the transported complementary block can likewise be
stated directly with `(submodule U)ᗮ`. -/
theorem gauge_blockCompression_orthogonal_transport
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.gauge (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (submodule (e := e) U)ᗮ (submodule (e := e) U) (clm (e := e) K)) =
      N.gauge (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U K) := by
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
  have hcoord := blockCompression_orthogonal_transport_hasSameApproximationNumbers
    (e := e) U K
  have htransport := extendedGauge_blockCompression_transport (e := e) N Uᗮ U K
  rw [N.extendedGauge_eq_of_hasSameApproximationNumbers hcoord, htransport]

omit [CompleteSpace E] in
/-- Reduction of `A + B` is scalar invariant, in the spelling consumed by the
source-facing `tan 2Θ` theorem. -/
theorem reducesSubspace_addBounded_pmap_iff
    {A : E →ₗ.[𝕜] E} (B : E →L[𝕜] E)
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    TauCeti.LinearPMap.ReducesSubspace
        (TauCeti.LinearPMap.addBounded (pmap (e := e) A) (clm (e := e) B))
        (submodule (e := e) V) ↔
      TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V := by
  rw [← pmap_addBounded]
  exact reducesSubspace_pmap_iff (e := e) V

end ScalarTransport
end TauCeti
