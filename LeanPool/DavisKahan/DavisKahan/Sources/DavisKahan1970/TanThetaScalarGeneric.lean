/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaDirectedUnbounded
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TangentOperatorGeneric
import LeanPool.DavisKahan.DavisKahan.TanTheta.ScalarTransport

/-!
# Scalar-generic unbounded `tan Θ`

The Appendix-complete single-angle tangent theorems were already proved at both
`ℝ` and `ℂ`; the missing public API was the scalar-generic front door.  This
module transports only the boundary data of those proofs.  The unbounded Ritz
compression remains a partial self-adjoint operator, the residual remains a
bounded rectangular operator, and every approximation number and
symmetric-norming gauge is preserved exactly.

The foundational result is `UnboundedCompressionTrialData.all_kyFan_core_rclike`.
The strong symmetric-norming endpoints and the source-shaped Ritz wrappers are
corollaries of that transport, just as the scalar-generic sine theorem is built
on its Ky Fan majorization core.
-/

open scoped InnerProductSpace BigOperators TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TauCeti.ScalarTransport

section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The directed sine block entering Theorem 6.3, at an arbitrary `RCLike` field. -/
noncomputable def directedSineBlock
    (Z V : Submodule 𝕜 H)  [V.HasOrthogonalProjection] :
    Z →L[𝕜] H :=
  Vᗮ.starProjection ∘L Z.subtypeL

/-- A directed tangent representative has exactly the singular values `tan θⱼ`. -/
noncomputable def HasDirectedTangentApproximationNumbers
    (Z V : Submodule 𝕜 H)  [V.HasOrthogonalProjection]
    (tanTheta0 : Z →L[𝕜] H) : Prop :=
  ∀ n, tanTheta0.approximationNumber n =
    Real.tan (Real.arcsin ((directedSineBlock Z V).approximationNumber n))

section Transport

universe w
variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

omit [CompleteSpace H] in
/-- Scalar transport carries the directed sine block into the canonical transported
subspace coordinates. -/
theorem scalarTransport_directedSineBlock
    (Z V : Submodule 𝕜 H)  [V.HasOrthogonalProjection]
     :
    scalarTransportSubspaceCLM (e := e) Z (directedSineBlock Z V) =
      directedSineBlock (ScalarTransport.submodule (e := e) Z)
        (ScalarTransport.submodule (e := e) V) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [scalarTransportSubspaceCLM, directedSineBlock, ContinuousLinearMap.comp_apply]
  let z0 : Z :=
    ScalarTransport.out (e := e)
      ((ScalarTransport.submoduleSubtypeEquiv (e := e) Z).symm z)
  let x : ScalarTransport e H := (z : ScalarTransport e H)
  have hx : x = ScalarTransport.of (e := e) ((z0 : Z) : H) := by
    change x = ScalarTransport.of (e := e)
      (ScalarTransport.out (e := e) x)
    exact (ScalarTransport.of_out x).symm
  change ScalarTransport.of (e := e) (Vᗮ.starProjection ((z0 : Z) : H)) =
    (ScalarTransport.submodule (e := e) V)ᗮ.starProjection x
  rw [hx]
  exact (ScalarTransport.starProjection_orthogonal_of (e := e) V _).symm

omit [CompleteSpace H] in
/-- Approximation numbers of the directed sine block are scalar invariant. -/
theorem approximationNumber_directedSineBlock_transport
    (Z V : Submodule 𝕜 H)  [V.HasOrthogonalProjection]
     (n : ℕ) :
    (directedSineBlock (ScalarTransport.submodule (e := e) Z)
      (ScalarTransport.submodule (e := e) V)).approximationNumber n =
      (directedSineBlock Z V).approximationNumber n := by
  rw [← scalarTransport_directedSineBlock (e := e) Z V]
  exact approximationNumber_scalarTransportSubspaceCLM (e := e) Z
    (directedSineBlock Z V) n

omit [CompleteSpace H] in
/-- Legacy Appendix spelling of the same scalar-invariance fact. -/
theorem approximationSingularValue_directedSineBlock_transport
    (Z V : Submodule 𝕜 H)  [V.HasOrthogonalProjection]
     (n : ℕ) :
    approximationSingularValue n
        (directedSineBlock (ScalarTransport.submodule (e := e) Z)
          (ScalarTransport.submodule (e := e) V)) =
      approximationSingularValue n (directedSineBlock Z V) := by
  simpa only [approximationSingularValue] using
    approximationNumber_directedSineBlock_transport (e := e) Z V n

end Transport

namespace UnboundedCompressionTrialData

variable {Z V : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  [CompleteSpace Z]

/-- **The Appendix Ky Fan core at every `RCLike` field.**

This is the scalar-generic analytic invariant behind the unbounded directed
`tangent` theorem.  The proof dispatches to the already established real or
complex cutoff engine after transporting the unbounded compression data. -/
theorem all_kyFan_core_rclike
    (D : UnboundedCompressionTrialData Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_𝕜)
    (k : ℕ) :
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (directedSineBlock Z V))) ≤
      kyFanApproximationGauge k D.residual := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let D' := D.scalarTransport (e := e)
    let V' := ScalarTransport.submodule (e := e) V
    have hupper' : TauCeti.LinearPMap.SemiboundedAbove D'.compression alpha :=
      (D.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hc := TauCeti.DavisKahan1970.all_kyFan_core_unboundedCompression_real D' V' hdelta hupper'
      hcross' k
    have hsine : ∀ n : ℕ,
        approximationSingularValue n
            (TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal
              (ScalarTransport.submodule (e := e) Z) V') =
          approximationSingularValue n (directedSineBlock Z V) := by
      intro n
      change approximationSingularValue n
          (directedSineBlock (ScalarTransport.submodule (e := e) Z) V') = _
      exact approximationSingularValue_directedSineBlock_transport (e := e) Z V n
    rw [D.kyFanApproximationGauge_scalarTransport_residual (e := e)] at hc
    simpa only [hsine] using hc
  · let e := RCLikeIso.complex h
    let D' := D.scalarTransport (e := e)
    let V' := ScalarTransport.submodule (e := e) V
    have hupper' : TauCeti.LinearPMap.SemiboundedAbove D'.compression alpha :=
      (D.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hc := D'.all_kyFan_core V' hdelta hupper' hcross' k
    have hsine : ∀ n : ℕ,
        approximationSingularValue n
            (TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock
              (ScalarTransport.submodule (e := e) Z) V') =
          approximationSingularValue n (directedSineBlock Z V) := by
      intro n
      change approximationSingularValue n
          (directedSineBlock (ScalarTransport.submodule (e := e) Z) V') = _
      exact approximationSingularValue_directedSineBlock_transport (e := e) Z V n
    rw [D.kyFanApproximationGauge_scalarTransport_residual (e := e)] at hc
    simpa only [hsine] using hc

/-- The source gap excludes the single-angle tangent pole at every `RCLike` field. -/
theorem approximationNumber_directedSineBlock_lt_one_rclike
    (D : UnboundedCompressionTrialData Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_𝕜)
    (n : ℕ) :
    (directedSineBlock Z V).approximationNumber n < 1 := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let D' := D.scalarTransport (e := e)
    let V' := ScalarTransport.submodule (e := e) V
    have hupper' : TauCeti.LinearPMap.SemiboundedAbove D'.compression alpha :=
      (D.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hc := TauCeti.DavisKahan1970.approximationSingularValue_sineBlockReal_lt_one_unboundedCompression
      D' V' hdelta hupper' hcross' n
    change approximationSingularValue n
        (directedSineBlock (ScalarTransport.submodule (e := e) Z) V') < 1 at hc
    rw [approximationSingularValue_directedSineBlock_transport (e := e) Z V n] at hc
    simpa only [approximationSingularValue] using hc
  · let e := RCLikeIso.complex h
    let D' := D.scalarTransport (e := e)
    let V' := ScalarTransport.submodule (e := e) V
    have hupper' : TauCeti.LinearPMap.SemiboundedAbove D'.compression alpha :=
      (D.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hc := D'.approximationSingularValue_sineBlock_lt_one V' hdelta hupper' hcross' n
    change approximationSingularValue n
        (directedSineBlock (ScalarTransport.submodule (e := e) Z) V') < 1 at hc
    rw [approximationSingularValue_directedSineBlock_transport (e := e) Z V n] at hc
    simpa only [approximationSingularValue] using hc

/-- **Strong unbounded directed `tan Θ₀`, scalar-generic over `RCLike`.** -/
theorem symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    (D : UnboundedCompressionTrialData Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_𝕜)
    (tanTheta0 : Z →L[𝕜] H)
    (htan : HasDirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  have hcore := D.all_kyFan_core_rclike (V := V) hdelta hupper hcross k
  have htanKy : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (directedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact Finset.sum_congr rfl fun n _ => by
      simpa only [approximationSingularValue] using htan n
  rwa [htanKy]

end UnboundedCompressionTrialData

end
end TanTheta
end DavisKahan

namespace DavisKahan1970

section

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ScalarTransport

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Davis--Kahan `tan Θ`, directed clause, full unbounded scope, scalar-generic.** -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {Z V : Submodule 𝕜 E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (tanTheta0 : Z →L[𝕜] E)
    (htan : TanTheta.HasDirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem D.trial.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  exact D.trial.symmetricNorming_rclike (V := V) N hdelta hupper hcross
    tanTheta0 htan hResidual

/-- **Davis--Kahan `tan Θ₀`, full unbounded directed clause, scalar-generic,
with the tangent representative constructed.** -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {Z V : Submodule 𝕜 E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (hResidual : N.Mem D.trial.residual) :
    (∀ n, (TanTheta.directedSineBlock Z V).approximationNumber n < 1) ∧
      ∃ tanTheta0 : Z →L[𝕜] E,
        TanTheta.HasDirectedTangentApproximationNumbers Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  have hlt : ∀ n, (TanTheta.directedSineBlock Z V).approximationNumber n < 1 :=
    fun n => D.trial.approximationNumber_directedSineBlock_lt_one_rclike
      (V := V) hdelta hupper hcross n
  refine ⟨hlt, ?_⟩
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let Z' := ScalarTransport.submodule (e := e) Z
    let V' := ScalarTransport.submodule (e := e) V
    have hlt' : ∀ n,
        approximationSingularValue n
          (TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal Z' V') < 1 := by
      intro n
      change approximationSingularValue n (TanTheta.directedSineBlock Z' V') < 1
      rw [TanTheta.approximationSingularValue_directedSineBlock_transport (e := e) Z V n]
      simpa only [approximationSingularValue] using hlt n
    obtain ⟨T', hT'⟩ :=
      TauCeti.DavisKahan1970.exists_hasTheorem63DirectedTangentApproximationNumbersReal Z' V' hlt'
    let T : Z →L[𝕜] E :=
      (TanTheta.scalarTransportSubspaceCLMEquiv (e := e) Z).symm T'
    have htransport : TanTheta.scalarTransportSubspaceCLM (e := e) Z T = T' :=
      Equiv.apply_symm_apply (TanTheta.scalarTransportSubspaceCLMEquiv (e := e) Z) T'
    have htan : TanTheta.HasDirectedTangentApproximationNumbers Z V T := by
      intro n
      have hTn := TanTheta.approximationNumber_scalarTransportSubspaceCLM
        (e := e) Z T n
      rw [htransport] at hTn
      have hTshape : T'.approximationNumber n =
          Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z' V').approximationNumber n)) := by
        simpa only [approximationSingularValue,
          TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal,
          TanTheta.directedSineBlock] using hT' n
      calc
        T.approximationNumber n = T'.approximationNumber n := hTn.symm
        _ = Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z' V').approximationNumber n)) := hTshape
        _ = Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z V).approximationNumber n)) := by
          rw [TanTheta.approximationNumber_directedSineBlock_transport (e := e) Z V n]
    obtain ⟨hmem, hbound⟩ :=
      tanTheta_directed_unboundedRitz_symmetricNorming_rclike N D hV
        hdelta hupper hUnwanted T htan hResidual
    exact ⟨T, htan, hmem, hbound⟩
  · let e := RCLikeIso.complex h
    let Z' := ScalarTransport.submodule (e := e) Z
    let V' := ScalarTransport.submodule (e := e) V
    have hlt' : ∀ n,
        approximationSingularValue n
          (TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock Z' V') < 1 := by
      intro n
      change approximationSingularValue n (TanTheta.directedSineBlock Z' V') < 1
      rw [TanTheta.approximationSingularValue_directedSineBlock_transport (e := e) Z V n]
      simpa only [approximationSingularValue] using hlt n
    obtain ⟨T', hT'⟩ :=
      TauCeti.DavisKahan.TanTheta.exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z' V' hlt'
    let T : Z →L[𝕜] E :=
      (TanTheta.scalarTransportSubspaceCLMEquiv (e := e) Z).symm T'
    have htransport : TanTheta.scalarTransportSubspaceCLM (e := e) Z T = T' :=
      Equiv.apply_symm_apply (TanTheta.scalarTransportSubspaceCLMEquiv (e := e) Z) T'
    have htan : TanTheta.HasDirectedTangentApproximationNumbers Z V T := by
      intro n
      have hTn := TanTheta.approximationNumber_scalarTransportSubspaceCLM
        (e := e) Z T n
      rw [htransport] at hTn
      have hTshape : T'.approximationNumber n =
          Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z' V').approximationNumber n)) := by
        simpa only [approximationSingularValue,
          TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock,
          TanTheta.directedSineBlock] using hT' n
      calc
        T.approximationNumber n = T'.approximationNumber n := hTn.symm
        _ = Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z' V').approximationNumber n)) := hTshape
        _ = Real.tan (Real.arcsin ((TanTheta.directedSineBlock Z V).approximationNumber n)) := by
          rw [TanTheta.approximationNumber_directedSineBlock_transport (e := e) Z V n]
    obtain ⟨hmem, hbound⟩ :=
      tanTheta_directed_unboundedRitz_symmetricNorming_rclike N D hV
        hdelta hupper hUnwanted T htan hResidual
    exact ⟨T, htan, hmem, hbound⟩

/-- **Davis--Kahan `tan Θ`, ambient clause, full unbounded scope, scalar-generic.** -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (hdefined : Angle.HasDefinedTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (Angle.tanAngleOperator U V) ∧
      delta * N.gauge (Angle.tanAngleOperator U V) ≤ N.gauge H := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let D' := D.trial.scalarTransport (e := e)
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let H' := ScalarTransport.clm (e := e) H
    have hupper' := (D.trial.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.trial.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hdefined' : Angle.HasDefinedTangent U' V' :=
      (Angle.hasDefinedTangent_submodule (e := e) U V).2 hdefined
    have h35' : DavisKahan.CrossedDefectsEquivalent U' V' :=
      DavisKahan.crossedDefectsEquivalent_of_isAcute U' V'
        (TauCeti.isAcute_of_projectionGap_lt_one hdefined')
    have hResidual' := D.trial.scalarTransport_residual_eq_projectionBlock
      (e := e) H hResidual
    have hMem' : N.Mem H' := (SymmetricNormingFunction.mem_clm_iff N H).2 hMem
    have hc := TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitzData_symmetricNorming_real
      (E := ScalarTransport e E) (U := U') (V := V') N D' H'
      ((ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hH) hdelta hupper'
      (by
        intro z
        have hz := hcross' z
        simpa [D', V', Submodule.starProjection_orthogonal_apply] using hz)
      h35' hResidual' hMem'
    have hm : N.Mem (Angle.tanAngleOperator U' V') := by
      rw [Angle.tanAngleOperator_real U' V' hdefined']
      exact hc.2.1
    have hb : delta * N.gauge (Angle.tanAngleOperator U' V') ≤ N.gauge H' := by
      rw [Angle.tanAngleOperator_real U' V' hdefined']
      exact hc.2.2
    rw [← Angle.clm_tanAngleOperator (e := e) U V hdefined] at hm hb
    exact ⟨(SymmetricNormingFunction.mem_clm_iff N _).1 hm, by
      rwa [SymmetricNormingFunction.gauge_clm, SymmetricNormingFunction.gauge_clm] at hb⟩
  · let e := RCLikeIso.complex h
    let D' := D.trial.scalarTransport (e := e)
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let H' := ScalarTransport.clm (e := e) H
    have hupper' := (D.trial.semiboundedAbove_scalarTransport_iff (e := e)).2 hupper
    have hcross' := D.trial.crossedLower_scalarTransport (e := e) (V := V) hcross
    have hdefined' : Angle.HasDefinedTangent U' V' :=
      (Angle.hasDefinedTangent_submodule (e := e) U V).2 hdefined
    have h35' : DavisKahan.CrossedDefectsEquivalent U' V' :=
      DavisKahan.crossedDefectsEquivalent_of_isAcute U' V'
        (TauCeti.isAcute_of_projectionGap_lt_one hdefined')
    have hResidual' := D.trial.scalarTransport_residual_eq_projectionBlock
      (e := e) H hResidual
    have hMem' : N.Mem H' := (SymmetricNormingFunction.mem_clm_iff N H).2 hMem
    have hc := TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitzData_symmetricNorming_complex
      (E := ScalarTransport e E) N D' H'
      ((ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hH) hdelta hupper'
      hcross' h35' hResidual' hMem'
    have hm : N.Mem (Angle.tanAngleOperator U' V') := by
      simpa using hc.2.1
    have hb : delta * N.gauge (Angle.tanAngleOperator U' V') ≤ N.gauge H' := by
      simpa using hc.2.2
    rw [← Angle.clm_tanAngleOperator (e := e) U V hdefined] at hm hb
    exact ⟨(SymmetricNormingFunction.mem_clm_iff N _).1 hm, by
      rwa [SymmetricNormingFunction.gauge_clm, SymmetricNormingFunction.gauge_clm] at hb⟩

end
end DavisKahan1970
end TauCeti
