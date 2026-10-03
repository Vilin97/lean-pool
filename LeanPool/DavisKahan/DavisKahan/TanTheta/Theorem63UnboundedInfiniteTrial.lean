/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrialData
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63Unbounded

/-! # Theorem63Unbounded Infinite Trial -/

@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 for an unbounded operator and an arbitrary trial space

Davis--Kahan's Appendix removes the finite-dimensional trial-space hypothesis from the
single-angle tangent theorem by finite-projector approximation.  Two halves of that
argument already existed separately:

* `Theorem63Unbounded.lean` proves the printed unbounded theorem for a finite trial space;
* `Theorem63InfiniteTrial.lean` proves the Appendix finite-projector passage for a bounded
  ambient operator and an arbitrary complete trial space.

The finite-projector passage only uses bounded trial-block data: the self-adjoint Ritz
compression, the residual, and the action on the trial space.  Those are precisely the
fields of `Theorem63TrialData`, including for an `BoundedCompressionTrialBlock`.  This module lifts
the Appendix argument to that data abstraction and then instantiates it at the unbounded
trial block.

No doubled-angle theorem enters this proof.  The only approximation operator used to find
finite almost-invariant subspaces is the bounded self-adjoint Ritz compression.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TanTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Infinite-trial passage over abstract trial-block data -/

namespace Theorem63TrialData

variable {Z V : Submodule ℂ H}
  [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]

section InfiniteCore

variable (data : Theorem63TrialData Z V)

/-- Fan-dominance endpoint for arbitrary complete trial-block data. -/
theorem ideal_of_formBounds_infinite
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem data.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  refine ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N.toFanDominantIdealFamily hdelta hResidual fun k => ?_
  have hcore := data.all_kyFan_core_of_formBounds_infinite hdelta hMupper hcross k
  have hKyTan : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  rw [hKyTan]
  exact hcore

/-- Unconditional infinite-trial endpoint over abstract trial-block data: the tangent
representative is constructed with exactly the approximation numbers prescribed by the
paper. -/
theorem ideal_of_formBounds_infinite_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (hResidual : N.Mem data.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (fun n => data.approximationSingularValue_sineBlock_lt_one_infiniteData
        hdelta hMupper hcross n)
  obtain ⟨hmem, hbound⟩ := data.ideal_of_formBounds_infinite N hdelta
    hMupper hcross tanTheta0 htan hResidual
  exact ⟨tanTheta0, htan, hmem, hbound⟩

end InfiniteCore

end Theorem63TrialData

/-! ## The Appendix endpoint for an unbounded self-adjoint operator -/

/-- **Davis--Kahan Theorem 6.3, unbounded ambient operator and arbitrary complete trial
space, under the printed reducing-subspace hypotheses.**

This is the Appendix dimension-removal endpoint.  There is no finite-dimensionality or
compactness hypothesis on `Z`.  The tangent representative is exhibited, and every
Fan-dominant unitarily invariant ideal gauge satisfies the printed residual bound. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite_exists N hdelta hCompression
    (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted) hResidual

/-- Same arbitrary-trial unbounded theorem when a tangent representative with the paper's
approximation numbers is supplied explicitly. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite N hdelta hCompression
    (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted)
    tanTheta0 htan hResidual

/-- Spectral-gap specialization of the arbitrary-trial unbounded theorem. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z
        (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let V := selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite_exists N hdelta hCompression
    (crossed_lower_of_spectralGap A hA D hgap) hResidual

/-- Spectral-gap specialization with the tangent representative supplied explicitly.

`theorem6_3_unbounded_infiniteTrial_ideal_exists` produces a representative; a
source-facing statement at an arbitrary unitarily invariant norm cannot use that
form, because the existential would hand back a possibly different witness at
each Ky Fan index.  Taking the representative as a parameter is what lets the
paper-norm promotion quantify one operator over all indices. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z
      (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  let V := selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic
  let data := Theorem63TrialData.ofUnbounded D V
  exact data.ideal_of_formBounds_infinite N hdelta hCompression
    (crossed_lower_of_spectralGap A hA D hgap) tanTheta0 htan hResidual

end TanTheta
end DavisKahan
end TauCeti
