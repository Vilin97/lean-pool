/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedReducingReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedReducing
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TangentOperatorGeneric
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleGeneric
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.TanTheta.ScalarTransport

/-!
# Scalar-generic unbounded `tan 2Θ`

The unbounded double-angle tangent theorem had complete real and complex
endpoints but no common `RCLike` front door.  This module transports only the
source data and the final singular-value objects, leaving the fixed-field
spectral-cutoff proofs untouched.

The ambient endpoint is canonical: it bounds the scalar-generic
`absTanTwoAngleOperator`.  The directed endpoint returns a bounded corner whose
complete approximation-number sequence is `tan (arcsin a_n(sin 2Θ₀))`; this is
the invariant content of the directed tangent in every source unitarily
invariant norm and avoids exposing field-specific inverse machinery.
-/

open scoped InnerProductSpace TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.Angle
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ScalarTransport

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A directed doubled-tangent representative has exactly the singular values
obtained by applying `tan ∘ arcsin` to the directed doubled-sine sequence. -/
def HasDirectedDoubleTangentApproximationNumbers
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (T : U →L[𝕜] Uᗮ) : Prop :=
  ∀ n, T.approximationNumber n =
    Real.tan (Real.arcsin ((DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))

/-- **Davis--Kahan `tan 2Θ₀`, full unbounded directed residual form, scalar-generic.**

The source gap itself excludes the quarter-turn pole.  The theorem constructs a
bounded directed tangent representative, identifies every approximation number,
and gives the strong symmetric-norming membership and estimate

`(b-a) N(tan 2Θ₀) ≤ 2 N(P_{U⊥} B P_U)`.
-/
theorem tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {B : E →L[𝕜] E} {a b : ℝ}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    (∀ n : ℕ, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      ∃ T : U →L[𝕜] Uᗮ,
        HasDirectedDoubleTangentApproximationNumbers U V T ∧
        N.Mem T ∧
        (b - a) * N.gauge T ≤ 2 * N.gauge (blockCompression Uᗮ U B) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let A' := ScalarTransport.pmap (e := e) A
    let B' := ScalarTransport.clm (e := e) B
    have hA' : IsSelfAdjoint A' := (ScalarTransport.isSelfAdjoint_pmap_iff e).2 hA
    have hred' : TauCeti.LinearPMap.ReducesSubspace A' U' :=
      (ScalarTransport.reducesSubspace_pmap_iff (e := e) U).2 hred
    have hB' : TauCeti.IsOddFor U' B' :=
      (ScalarTransport.isOddFor_clm_iff (e := e) U B).2 hB
    have hVred' : TauCeti.LinearPMap.ReducesSubspace
        (TauCeti.LinearPMap.addBounded A' B') V' :=
      (ScalarTransport.reducesSubspace_addBounded_pmap_iff (e := e) B V).2 hV
    let hV' : DavisKahan.ReflectionIntertwines A' B' V' :=
      DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred'
    have hUa' := ScalarTransport.formUpperOnSubspace_pmap (e := e) hUa
    have hUb' := ScalarTransport.formLowerOnOrthogonal_pmap (e := e) hUb
    have hRmem' : N.Mem (blockCompression U'ᗮ U' B') := by
      dsimp [U', B']
      exact (ScalarTransport.mem_blockCompression_orthogonal_transport_iff
        (e := e) N U B).2 hRmem
    obtain ⟨hlt', hseq', hmem', hbound'⟩ :=
      tanTwoTheta_directed_unboundedResidual_reducing_sineSequence_symmetricNorming_real
        (E := ScalarTransport e E) (U := U') (A := A') (B := B') (a := a) (b := b)
        N V' hA' hred' hB' hV' hUa' hUb' hab hRmem'
    let T' : U' →L[ℝ] U'ᗮ := reflectionTangentCorner U' V'.reflectionOperator
    let T : U →L[𝕜] Uᗮ :=
      DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) U T'
    have hsine : ∀ n : ℕ,
        (DavisKahan.sinTwoThetaIdealBlock U' V').approximationNumber n =
          (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n := by
      intro n
      rw [← Angle.clm_sinTwoThetaIdealBlock (e := e) U V]
      exact ScalarTransport.approximationNumber_clm (e := e)
        (DavisKahan.sinTwoThetaIdealBlock U V) n
    have hlt : ∀ n : ℕ,
        (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1 := by
      intro n
      rw [← hsine n]
      exact hlt' n
    have hseq : HasDirectedDoubleTangentApproximationNumbers U V T := by
      intro n
      have hTn :=
        DavisKahan.TanTheta.approximationNumber_scalarTransportOrthogonalSubspaceBlockCLMInv
          (e := e) U T' n
      change T.approximationNumber n = _
      rw [hTn]
      change T'.approximationNumber n = _
      dsimp [T']
      rw [hseq' n, hsine n]
    have hmem : N.Mem T := by
      change N.Mem
        (DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) U T')
      exact (DavisKahan.TanTheta.mem_scalarTransportOrthogonalSubspaceBlockCLMInv_iff
        (e := e) N U T').2 hmem'
    have hTgauge : N.gauge T' = N.gauge T := by
      change N.gauge T' =
        N.gauge (DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv
          (e := e) U T')
      exact (DavisKahan.TanTheta.gauge_scalarTransportOrthogonalSubspaceBlockCLMInv
        (e := e) N U T').symm
    have hRgauge : N.gauge (blockCompression U'ᗮ U' B') =
        N.gauge (blockCompression Uᗮ U B) := by
      dsimp [U', B']
      exact ScalarTransport.gauge_blockCompression_orthogonal_transport
        (e := e) N U B
    refine ⟨hlt, T, hseq, hmem, ?_⟩
    rw [← hTgauge, ← hRgauge]
    exact hbound'
  · let e := RCLikeIso.complex h
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let A' := ScalarTransport.pmap (e := e) A
    let B' := ScalarTransport.clm (e := e) B
    have hA' : IsSelfAdjoint A' := (ScalarTransport.isSelfAdjoint_pmap_iff e).2 hA
    have hred' : TauCeti.LinearPMap.ReducesSubspace A' U' :=
      (ScalarTransport.reducesSubspace_pmap_iff (e := e) U).2 hred
    have hB' : TauCeti.IsOddFor U' B' :=
      (ScalarTransport.isOddFor_clm_iff (e := e) U B).2 hB
    have hVred' : TauCeti.LinearPMap.ReducesSubspace
        (TauCeti.LinearPMap.addBounded A' B') V' :=
      (ScalarTransport.reducesSubspace_addBounded_pmap_iff (e := e) B V).2 hV
    let hV' : DavisKahan.ReflectionIntertwines A' B' V' :=
      DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred'
    have hUa' := ScalarTransport.formUpperOnSubspace_pmap (e := e) hUa
    have hUb' := ScalarTransport.formLowerOnOrthogonal_pmap (e := e) hUb
    have hRmem' : N.Mem (blockCompression U'ᗮ U' B') := by
      dsimp [U', B']
      exact (ScalarTransport.mem_blockCompression_orthogonal_transport_iff
        (e := e) N U B).2 hRmem
    obtain ⟨hlt', hseq', hmem', hbound'⟩ :=
      tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex
        (G := ScalarTransport e E) (U := U') (A := A') (B := B') (a := a) (b := b)
        N V' hA' hred' hB' hV' hUa' hUb' hab hRmem'
    let T' : U' →L[ℂ] U'ᗮ := reflectionTangentCorner U' V'.reflectionOperator
    let T : U →L[𝕜] Uᗮ :=
      DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) U T'
    have hsine : ∀ n : ℕ,
        (DavisKahan.sinTwoThetaIdealBlock U' V').approximationNumber n =
          (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n := by
      intro n
      rw [← Angle.clm_sinTwoThetaIdealBlock (e := e) U V]
      exact ScalarTransport.approximationNumber_clm (e := e)
        (DavisKahan.sinTwoThetaIdealBlock U V) n
    have hlt : ∀ n : ℕ,
        (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1 := by
      intro n
      rw [← hsine n]
      exact hlt' n
    have hseq : HasDirectedDoubleTangentApproximationNumbers U V T := by
      intro n
      have hTn :=
        DavisKahan.TanTheta.approximationNumber_scalarTransportOrthogonalSubspaceBlockCLMInv
          (e := e) U T' n
      change T.approximationNumber n = _
      rw [hTn]
      change T'.approximationNumber n = _
      dsimp [T']
      rw [hseq' n, hsine n]
    have hmem : N.Mem T := by
      change N.Mem
        (DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) U T')
      exact (DavisKahan.TanTheta.mem_scalarTransportOrthogonalSubspaceBlockCLMInv_iff
        (e := e) N U T').2 hmem'
    have hTgauge : N.gauge T' = N.gauge T := by
      change N.gauge T' =
        N.gauge (DavisKahan.TanTheta.scalarTransportOrthogonalSubspaceBlockCLMInv
          (e := e) U T')
      exact (DavisKahan.TanTheta.gauge_scalarTransportOrthogonalSubspaceBlockCLMInv
        (e := e) N U T').symm
    have hRgauge : N.gauge (blockCompression U'ᗮ U' B') =
        N.gauge (blockCompression Uᗮ U B) := by
      dsimp [U', B']
      exact ScalarTransport.gauge_blockCompression_orthogonal_transport
        (e := e) N U B
    refine ⟨hlt, T, hseq, hmem, ?_⟩
    rw [← hTgauge, ← hRgauge]
    exact hbound'

/-- **Davis--Kahan `tan 2Θ`, full unbounded ambient form, scalar-generic.**

The ordered form gap derives its own pole exclusion.  The conclusion is on the
canonical branch-free ambient operator `|tan 2Θ|`, with strong symmetric-norming
membership and the sharp factor two. -/
theorem tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {B : E →L[𝕜] E} {a b : ℝ}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    (hab : a < b)
    (hBmem : N.Mem B) :
    Angle.HasDefinedDoubleTangent U V ∧
      N.Mem (Angle.absTanTwoAngleOperator U V) ∧
      (b - a) * N.gauge (Angle.absTanTwoAngleOperator U V) ≤ 2 * N.gauge B := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLikeIso.real h
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let A' := ScalarTransport.pmap (e := e) A
    let B' := ScalarTransport.clm (e := e) B
    have hA' : IsSelfAdjoint A' := (ScalarTransport.isSelfAdjoint_pmap_iff e).2 hA
    have hred' : TauCeti.LinearPMap.ReducesSubspace A' U' :=
      (ScalarTransport.reducesSubspace_pmap_iff (e := e) U).2 hred
    have hBsa' : IsSelfAdjoint B' := (ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hBsa
    have hB' : TauCeti.IsOddFor U' B' :=
      (ScalarTransport.isOddFor_clm_iff (e := e) U B).2 hB
    have hVred' : TauCeti.LinearPMap.ReducesSubspace
        (TauCeti.LinearPMap.addBounded A' B') V' :=
      (ScalarTransport.reducesSubspace_addBounded_pmap_iff (e := e) B V).2 hV
    let hV' : DavisKahan.ReflectionIntertwines A' B' V' :=
      DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred'
    have hUa' := ScalarTransport.formUpperOnSubspace_pmap (e := e) hUa
    have hUb' := ScalarTransport.formLowerOnOrthogonal_pmap (e := e) hUb
    have hBmem' : N.Mem B' :=
      (SymmetricNormingFunction.mem_clm_iff N B).2 hBmem
    obtain ⟨hlt', _hseq', hmem', hbound'⟩ :=
      tanTwoTheta_ambient_unbounded_reducing_sineSequence_symmetricNorming_real
        (E := ScalarTransport e E) (U := U') (A := A') (B := B') (a := a) (b := b)
        hA' hred' hB' hUa' hUb' hab N V' hBsa' hV' hBmem'
    have hsinApprox : ∀ n : ℕ,
        (Angle.sinTwoAngleOperator U' V').approximationNumber n < 1 := by
      intro n
      have hs := Angle.sinTwoAngleOperator_hasSameApproximationNumbers
        (U := U') (V := V') n
      rw [hs]
      exact hlt' n
    have hnorm : ‖Angle.sinTwoAngleOperator U' V'‖ < 1 := by
      rw [← (Angle.sinTwoAngleOperator U' V').approximationNumber_index_zero]
      exact hsinApprox 0
    have hdefined' : Angle.HasDefinedDoubleTangent U' V' :=
      Angle.hasDefinedDoubleTangent_of_norm_sinTwoAngleOperator_lt_one U' V' hnorm
    have hmemGeneric' : N.Mem (Angle.absTanTwoAngleOperator U' V') := by
      rw [Angle.absTanTwoAngleOperator_real U' V' hdefined']
      exact hmem'
    have hboundGeneric' :
        (b - a) * N.gauge (Angle.absTanTwoAngleOperator U' V') ≤ 2 * N.gauge B' := by
      rw [Angle.absTanTwoAngleOperator_real U' V' hdefined']
      exact hbound'
    have hdefined : Angle.HasDefinedDoubleTangent U V :=
      (Angle.hasDefinedDoubleTangent_submodule (e := e) U V).1 hdefined'
    rw [← Angle.clm_absTanTwoAngleOperator (e := e) U V hdefined] at hmemGeneric' hboundGeneric'
    refine ⟨hdefined, (SymmetricNormingFunction.mem_clm_iff N _).1 hmemGeneric', ?_⟩
    rwa [SymmetricNormingFunction.gauge_clm,
      SymmetricNormingFunction.gauge_clm] at hboundGeneric'
  · let e := RCLikeIso.complex h
    let U' := ScalarTransport.submodule (e := e) U
    let V' := ScalarTransport.submodule (e := e) V
    let A' := ScalarTransport.pmap (e := e) A
    let B' := ScalarTransport.clm (e := e) B
    have hA' : IsSelfAdjoint A' := (ScalarTransport.isSelfAdjoint_pmap_iff e).2 hA
    have hred' : TauCeti.LinearPMap.ReducesSubspace A' U' :=
      (ScalarTransport.reducesSubspace_pmap_iff (e := e) U).2 hred
    have hBsa' : IsSelfAdjoint B' := (ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hBsa
    have hB' : TauCeti.IsOddFor U' B' :=
      (ScalarTransport.isOddFor_clm_iff (e := e) U B).2 hB
    have hVred' : TauCeti.LinearPMap.ReducesSubspace
        (TauCeti.LinearPMap.addBounded A' B') V' :=
      (ScalarTransport.reducesSubspace_addBounded_pmap_iff (e := e) B V).2 hV
    let hV' : DavisKahan.ReflectionIntertwines A' B' V' :=
      DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred'
    have hUa' := ScalarTransport.formUpperOnSubspace_pmap (e := e) hUa
    have hUb' := ScalarTransport.formLowerOnOrthogonal_pmap (e := e) hUb
    have hBmem' : N.Mem B' :=
      (SymmetricNormingFunction.mem_clm_iff N B).2 hBmem
    obtain ⟨hdefined', hmem', hbound'⟩ :=
      tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex
        (G := ScalarTransport e E) N V' hA' hred' hBsa' hB' hV'
        hUa' hUb' hab hBmem'
    have hdefinedGeneric' : Angle.HasDefinedDoubleTangent U' V' := by
      simpa only [Angle.HasDefinedDoubleTangent, Angle.angleOperator_complex] using hdefined'
    have hmemGeneric' : N.Mem (Angle.absTanTwoAngleOperator U' V') := by
      simpa using hmem'
    have hboundGeneric' :
        (b - a) * N.gauge (Angle.absTanTwoAngleOperator U' V') ≤ 2 * N.gauge B' := by
      simpa using hbound'
    have hdefined : Angle.HasDefinedDoubleTangent U V :=
      (Angle.hasDefinedDoubleTangent_submodule (e := e) U V).1 hdefinedGeneric'
    rw [← Angle.clm_absTanTwoAngleOperator (e := e) U V hdefined] at hmemGeneric' hboundGeneric'
    refine ⟨hdefined, (SymmetricNormingFunction.mem_clm_iff N _).1 hmemGeneric', ?_⟩
    rwa [SymmetricNormingFunction.gauge_clm,
      SymmetricNormingFunction.gauge_clm] at hboundGeneric'

end

end DavisKahan1970
end TauCeti
