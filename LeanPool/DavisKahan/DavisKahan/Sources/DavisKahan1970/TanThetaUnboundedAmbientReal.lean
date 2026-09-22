/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DirectedUnboundedReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.UnboundedCompressionReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Tan Theta Unbounded Ambient Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The unbounded ambient `tan Theta` theorem over a **real** Hilbert space

`DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean` proves the ambient
(whole-space) half of the Section 2 tangent theorem for an unbounded self-adjoint operator
over a complex Hilbert space, at every source unitarily invariant norm.  Standing
assumption 1 of Davis--Kahan 1970 is that the space is "real or complex", so the printed
scope also carries the real case; this module supplies it, with no loss of constant, norm
class, or generality.

## What descends, and what does not

There are two real routes.  The older specialization, inherited from
`DirectedUnboundedReal.lean`, passes through bounded `Theorem63TrialData`.  The Appendix
route uses `UnboundedCompressionTrialData`, whose Ritz compression is itself a closed
unbounded self-adjoint operator.  Its data are complexified by
`complexifyUnboundedCompressionTrialData`, the existing complex Appendix cutoff/Ky-Fan
argument supplies the sharp lower corner, and the complex ambient assembly is applied
unchanged.  The conclusion is read back by `SymmetricNormingFunction.gauge_complexify`.
No complexification of the source ambient closed operator is required.

The printed standing assumption (3.5) is consumed entirely on the real side.
`norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent` derives real uniform
transversality from the real directed no-pole estimate and (3.5); only its consequence
`‖sin Θ‖ < 1` crosses to the complexification.  That is why the crossed-defect condition
itself never has to be transported.

## Main results

* `norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent`: real ambient
  uniform transversality from real trial-block form bounds and the printed (3.5);
* `tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_real`: the ambient estimate over real
  trial-block data;
* `tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_real`: the specialization with an
  unbounded ambient operator but bounded Ritz compression;
* `tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real`: the Appendix-complete
  endpoint in which the Ritz compression itself may be unbounded.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*, SIAM J.
  Numer. Anal. 7 (1970), 1--46: standing assumption 1, the Section 2 `tan Θ` theorem, the
  standing assumption (3.5) of Section 3, and the Section 6 ambient assembly.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The paper's real `tan Θ` exists as a bounded operator**: no principal angle reaches
`π/2`.  The real reading of `HasDefinedAmbientTangent`. -/
def HasDefinedAmbientTangentReal (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < 1

/-- `HasDefinedAmbientTangentReal` is exactly `‖sin Θ‖ < 1`; the projection gap and the real
ambient sine are the same number. -/
theorem hasDefinedAmbientTangentReal_iff_norm_sinAngleOperatorR_lt_one
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    HasDefinedAmbientTangentReal U V ↔ ‖sinAngleOperatorR U V‖ < 1 := by
  rw [HasDefinedAmbientTangentReal, norm_sinAngleOperatorR U V]


/-! ## Real uniform transversality from real trial-block data -/

/-- **Uniform transversality over a real Hilbert space, from unbounded trial data.**

`‖sin Θ‖ < 1` is a consequence of the tangent theorem's own form bounds together with the
printed standing assumption (3.5); it is never a hypothesis supplied by the caller.  The
ambient directed block `P_{V^⊥} P_U` factors through the trial block `P_{V^⊥} P_U|_U`,
whose real approximation singular values are already known to be strictly below one at
every trial dimension, and (3.5) identifies the symmetric gap with the directed one.

This is the trial-data twin of
`norm_sinAngleOperatorR_lt_one_of_crossedDefectsEquivalent`, which takes its no-pole
input from the *bounded* ambient hypotheses instead. -/
theorem norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent
    (data : Theorem63TrialData U V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U, (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : U) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ‖sinAngleOperatorR U V‖ < 1 := by
  have hdirected := approximationSingularValue_sineBlockReal_lt_one_infiniteData
    data hdelta hCompression hcross 0
  rw [approximationSingularValue_zero] at hdirected
  have hfactor : Vᗮ.starProjection ∘L U.starProjection =
      theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto := rfl
  have hnorm : ‖Vᗮ.starProjection ∘L U.starProjection‖ < 1 := by
    rw [hfactor]
    calc ‖theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto‖
        ≤ ‖theorem63DirectedSineBlockReal U V‖ * ‖U.orthogonalProjectionOnto‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖theorem63DirectedSineBlockReal U V‖ * 1 :=
          mul_le_mul_of_nonneg_left U.orthogonalProjectionOnto_norm_le
            (ContinuousLinearMap.opNorm_nonneg (theorem63DirectedSineBlockReal U V))
      _ < 1 := by rwa [mul_one]
  rw [norm_sinAngleOperatorR,
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent U V h35]
  exact hnorm

/-! ## Transporting the Rayleigh--Ritz residual block -/

omit [CompleteSpace E] in
/-- The printed Rayleigh--Ritz condition `H₀ = 0`, in the operator form used by the ambient
assembly, transports to the complexified trial data.  Nothing is assumed beyond the real
identity itself. -/
theorem complexifyTrialData_residual_eq_projectionBlock
    (data : Theorem63TrialData U V) (H : E →L[ℝ] E)
    (hResidual : data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL) :
    (complexifyTrialData data).residual =
      (complexifySubmodule U)ᗮ.starProjection ∘L complexify H ∘L
        (complexifySubmodule U).subtypeL := by
  apply ContinuousLinearMap.ext
  intro z
  set e := complexifySubmoduleEquiv U with he
  set u := e.symm z with hu
  have hz : e u = z := e.apply_symm_apply z
  have hcoe : ((complexifySubmodule U).subtypeL z : RealComplexification E) =
      complexify U.subtypeL u := by
    rw [← hz]
    rfl
  rw [complexifyTrialData_residual_apply, hResidual, complexify_comp, complexify_comp]
  simp only [ContinuousLinearMap.comp_apply, starProjection_complexifySubmodule_orthogonal,
    hcoe]
  rfl

/-! ## The ambient theorem over real trial-block data -/

/-- **Unbounded-data ambient `tan Theta` theorem over a REAL Hilbert space, at every source
unitarily invariant norm.**

`data` is the bounded trial-block data extracted from an unbounded real self-adjoint
problem; its residual is exactly the lower `U → U^⊥` block of the bounded perturbation `H`,
which is the operator form of the printed Rayleigh--Ritz condition `H₀ = 0`.  The two form
bounds are the printed ones, and the crossed-defect condition (3.5) is the printed standing
assumption of Section 3.

Uniform transversality is derived, not assumed, and membership of `tan Θ` in the norm's
ideal is concluded rather than hypothesised.  No dimension hypothesis, no compactness
hypothesis, and the constant is the printed `δ`. -/
theorem tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (data : Theorem63TrialData U V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U, (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : U) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangentReal U V ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H := by
  refine ⟨(hasDefinedAmbientTangentReal_iff_norm_sinAngleOperatorR_lt_one U V).2
    (norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent
      data hdelta hCompression hcross h35), ?_⟩
  have htrC : ‖sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)‖ < 1 := by
    rw [← complexify_sinAngleOperatorR U V, norm_complexify]
    exact norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent
      data hdelta hCompression hcross h35
  have hMemC : N.Mem (complexify H) :=
    (SymmetricNormingFunction.mem_complexify_iff N H).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex_of_transversality
      (E := RealComplexification E) N (complexifyTrialData data) (complexify H)
      ((complexify_isSelfAdjoint_iff H).2 hH) hdelta
      (complexifyTrialData_compression_upper data hCompression)
      (complexifyTrialData_crossed_lower data hcross)
      htrC (complexifyTrialData_residual_eq_projectionBlock data H hResidual) hMemC
  rw [← complexify_tanAngleOperatorR U V] at hmemC hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, the whole-space `tan Θ` theorem for an unbounded self-adjoint
operator over a REAL Hilbert space, at every source unitarily invariant norm.**

This is the real-scalar endpoint of the Section 2 ambient tangent statement: `A` is a
closed unbounded real self-adjoint operator, `U` is an arbitrary closed real trial subspace
contained in its domain, `V` is an arbitrary chosen reducing subspace, `H` is the bounded
perturbation, and the conclusion is the printed `δ N(tan Θ) ≤ N(H)` with `tan Θ` the real
ambient angle operator of the pair `(U, V)`.

The hypotheses are the printed ones: `hVdom`/`hVcomm` say `V` reduces the operator,
`hCompression` is the upper end `A₀ ≤ α`, `hUnwanted` is `α + δ ≤ Λ₁`, `hResidual` is the
Rayleigh--Ritz condition `H₀ = 0`, and `h35` is the standing assumption (3.5) of Section 3,
which the source assumes for the remainder of the paper and under which it proves this
theorem in Section 6.

Nothing here is a complex theorem with real hypotheses: the space, the operator, the
subspaces, the perturbation, the angle operator and the gauge are all real.  Only the
Appendix Ky Fan passage is proved by complexification, at the finite Ky Fan level where
approximation numbers are preserved exactly. -/
theorem tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E)
    (D : BoundedCompressionTrialBlock A U)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : U, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangentReal U V ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H :=
  tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_real N
    (Theorem63TrialData.ofUnbounded D V) H hH hdelta hCompression
    (fun z => by
      simpa using crossed_lower_of_reducing (𝕜 := ℝ) A D V hVdom hVcomm
        (fun y hy hydom => by simpa using hUnwanted y hy hydom) z)
    h35 hResidual hMem


/-! ## Appendix scope: real unbounded Ritz compression -/

/-- **Uniform transversality over a real Hilbert space with an unbounded Ritz
compression.**

This is the Appendix-scope twin of
`norm_sinAngleOperatorR_lt_one_of_data_crossedDefectsEquivalent`.  The no-pole
input is the real unbounded-compression theorem; the standing crossed-defect
condition (3.5) then converts the directed gap into the ambient gap. -/
theorem norm_sinAngleOperatorR_lt_one_of_unboundedCompression_crossedDefectsEquivalent
    (D : UnboundedCompressionTrialData U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : U) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ‖sinAngleOperatorR U V‖ < 1 := by
  have hdirected := approximationSingularValue_sineBlockReal_lt_one_unboundedCompression
    D V hdelta hupper hcross 0
  rw [approximationSingularValue_zero] at hdirected
  have hfactor : Vᗮ.starProjection ∘L U.starProjection =
      theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto := rfl
  have hnorm : ‖Vᗮ.starProjection ∘L U.starProjection‖ < 1 := by
    rw [hfactor]
    calc
      ‖theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto‖
          ≤ ‖theorem63DirectedSineBlockReal U V‖ * ‖U.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖theorem63DirectedSineBlockReal U V‖ * 1 :=
        mul_le_mul_of_nonneg_left U.orthogonalProjectionOnto_norm_le
          (ContinuousLinearMap.opNorm_nonneg (theorem63DirectedSineBlockReal U V))
      _ < 1 := by rwa [mul_one]
  rw [norm_sinAngleOperatorR,
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent U V h35]
  exact hnorm

/-- The Rayleigh--Ritz residual-block identity for real unbounded-compression data
commutes with complexification. -/
theorem complexifyUnboundedCompressionTrialData_residual_eq_projectionBlock
    (D : UnboundedCompressionTrialData U) (H : E →L[ℝ] E)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL) :
    (complexifyUnboundedCompressionTrialData D).residual =
      (complexifySubmodule U)ᗮ.starProjection ∘L complexify H ∘L
        (complexifySubmodule U).subtypeL := by
  apply ContinuousLinearMap.ext
  intro z
  set e := complexifySubmoduleEquiv U with he
  set u := e.symm z with hu
  have hz : e u = z := e.apply_symm_apply z
  have hcoe : ((complexifySubmodule U).subtypeL z : RealComplexification E) =
      complexify U.subtypeL u := by
    rw [← hz]
    rfl
  rw [complexifyUnboundedCompressionTrialData_residual_apply, hResidual,
    complexify_comp, complexify_comp]
  simp only [ContinuousLinearMap.comp_apply, starProjection_complexifySubmodule_orthogonal,
    hcoe]
  rfl

/-- **Davis--Kahan's Appendix ambient `tan Theta` theorem over a REAL Hilbert
space, with a genuinely unbounded Ritz compression.**

The unbounded compression is transported only as trial data.  The source
operator `tanAngleOperatorR U V`, perturbation `H`, and final norm statement
remain genuinely real.  The complex proof performs the spectral cutoff on the
complexified Ritz compression and the bounded two-corner ambient assembly; exact
complexification identities then descend the result without changing the
constant or norm class. -/
theorem tanTheta_ambient_unboundedRitzData_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (D : UnboundedCompressionTrialData U)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : U) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangentReal U V ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H := by
  refine ⟨(hasDefinedAmbientTangentReal_iff_norm_sinAngleOperatorR_lt_one U V).2
    (norm_sinAngleOperatorR_lt_one_of_unboundedCompression_crossedDefectsEquivalent
      D hdelta hupper hcross h35), ?_⟩
  have htrC :
      ‖sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)‖ < 1 := by
    rw [← complexify_sinAngleOperatorR U V, norm_complexify]
    exact norm_sinAngleOperatorR_lt_one_of_unboundedCompression_crossedDefectsEquivalent
      D hdelta hupper hcross h35
  have hMemC : N.Mem (complexify H) :=
    (SymmetricNormingFunction.mem_complexify_iff N H).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    tanTheta_ambient_unboundedRitzData_symmetricNorming_complex_of_transversality
      (E := RealComplexification E) N (complexifyUnboundedCompressionTrialData D)
      (complexify H) ((complexify_isSelfAdjoint_iff H).2 hH) hdelta
      (complexifyUnboundedCompressionTrialData_compression_upper D hupper)
      (complexifyUnboundedCompressionTrialData_crossed_lower D hcross)
      htrC (complexifyUnboundedCompressionTrialData_residual_eq_projectionBlock D H hResidual)
      hMemC
  rw [← complexify_tanAngleOperatorR U V] at hmemC hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, Appendix-complete real ambient `tan Theta` theorem.**

Both the ambient self-adjoint operator and the Ritz compression may be
unbounded.  The residual and perturbation remain bounded, exactly as required
for the displayed unitary-invariant norm inequality. -/
theorem tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (D : UnboundedCompressionTrialData U)
    (A : E →ₗ.[ℝ] E)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZA : ∀ z : D.compression.domain, ((z : U) : E) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : U) : E), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangentReal U V ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H := by
  refine tanTheta_ambient_unboundedRitzData_symmetricNorming_real
    N D H hH hdelta hupper ?_ h35 hResidual hMem
  intro z
  simpa using D.crossed_lower_of_reducing V A hZA haction hVdom hVcomm
    (fun y hy hydom => by simpa using hUnwanted y hy hydom) z

/-! ### The constructor-first interface, over `ℝ`

The real mirror of `tanTheta_ambient_unboundedRitz_symmetricNorming_complex`.  The four
structural facts that tie the compression data to the ambient operator and say
that `Vᗮ` reduces it are replaced by the two objects that carry them,
`DavisKahan.UnboundedRitzPair` and `DavisKahan.ReducingComplement`; both are
scalar-generic, so no real-specific vocabulary is introduced. -/

/-- **Davis--Kahan 1970, `tan Θ`, unbounded ambient form over `ℝ`, taking the Ritz
pair and the reducing complement as objects.**

`tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real` with its four
structural arguments replaced by `DavisKahan.UnboundedRitzPair A U` and
`DavisKahan.ReducingComplement A V`.  The mathematics -- semiboundedness of the
compression, coercivity on the unwanted subspace, and the crossed-defect standing
condition (3.5) -- is unchanged and still supplied by the caller.

Everything here is real: the space, the operator, the subspaces, the
perturbation, the ambient tangent `tanAngleOperatorR U V`, and the gauge. -/
theorem tanTheta_ambient_unboundedRitz_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangentReal U V ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H :=
  tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real N D.trial A H hH
    hdelta D.mem_domain D.action_eq hV.mapsDomain hV.commutes hupper hUnwanted h35
    hResidual hMem

/-! ## The printed `tan Θ` hypotheses over `ℝ`, with the source's own vacuity convention

The real mirror of the `DefinedTangent` section in `TanThetaUnboundedAmbient.lean`; see its
note for why condition (3.5) is not a hypothesis of the Section 2 theorem and what replaces
it. -/

section DefinedTangent

omit [CompleteSpace E] in
/-- A defined real tangent implies condition (3.5), for the same reason as over `ℂ`. -/
theorem crossedDefectsEquivalent_of_hasDefinedAmbientTangentReal
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : HasDefinedAmbientTangentReal U V) : DavisKahan.CrossedDefectsEquivalent U V :=
  DavisKahan.crossedDefectsEquivalent_of_isAcute U V (TauCeti.isAcute_of_projectionGap_lt_one h)

/-- **Davis--Kahan 1970, the `tan Θ` theorem, ambient clause, over `ℝ`, at the printed
hypotheses**, with the source's vacuity convention in place of condition (3.5). -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hdefined : HasDefinedAmbientTangentReal U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H :=
  (tanTheta_ambient_unboundedRitz_symmetricNorming_real N D hV H hH hdelta hupper hUnwanted
    (crossedDefectsEquivalent_of_hasDefinedAmbientTangentReal hdefined) hResidual hMem).2

/-- **Davis--Kahan 1970, the ambient `tan Θ` theorem at the printed source scope
over `ℝ`.**

Separable ambient Hilbert space and normalized unitarily invariant norm.  The
definedness hypothesis stays exactly as printed; the estimate goes through the
Fan-dominance bridge. -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_real
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E}
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hdefined : HasDefinedAmbientTangentReal U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H :=
  normalizedUnitaryInvariant_of_symmetricNorming N hdelta hMem fun M hM =>
    tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_real M D hV H hH
      hdelta hupper hUnwanted hdefined hResidual hM

end DefinedTangent

end

end DavisKahan1970
end TauCeti
