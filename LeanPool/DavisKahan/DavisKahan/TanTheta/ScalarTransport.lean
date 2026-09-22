/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.SymmetricNormingScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportIsometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.UnitaryTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace

/-!
# Scalar transport for unbounded Ritz-compression data

The hard Appendix proof of the unbounded tangent theorem is implemented once over
`ℂ` and descended to `ℝ`.  To expose the accepted real/complex endpoints through
one `RCLike` API we only have to transport the data at the boundary of that
proof.  This file does exactly that.

The important point is that the transport does **not** replace an unbounded
compression by a bounded one.  The compression remains a self-adjoint partial
map, conjugated by the canonical isometry between the transport of a subspace
subtype and the subtype of the transported subspace.  The bounded residual is
transported in the same coordinates, so its complete approximation-number
sequence and every symmetric-norming gauge are unchanged.
-/

open scoped InnerProductSpace TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TauCeti.ScalarTransport

noncomputable section

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]
variable {e : RCLikeIso 𝕜 𝕂}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {Z V : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  [CompleteSpace Z]

/-- Transport a bounded operator whose domain is a closed subspace into the
canonical transported-subspace coordinates. -/
noncomputable def scalarTransportSubspaceCLM (Z : Submodule 𝕜 H)
    (T : Z →L[𝕜] H) :
    ScalarTransport.submodule (e := e) Z →L[𝕂] ScalarTransport e H :=
  ScalarTransport.clm (e := e) T ∘L
    (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Scalar transport is a bijection on bounded maps out of a closed subspace. -/
noncomputable def scalarTransportSubspaceCLMEquiv (Z : Submodule 𝕜 H) :
    (Z →L[𝕜] H) ≃
      (ScalarTransport.submodule (e := e) Z →L[𝕂] ScalarTransport e H) where
  toFun := scalarTransportSubspaceCLM (e := e) Z
  invFun T := (ScalarTransport.clmEquiv (e := e)).symm
    (T ∘L (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).toContinuousLinearEquiv.toContinuousLinearMap)
  left_inv T := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  right_inv T := by
    apply ContinuousLinearMap.ext
    intro z
    rfl

omit [CompleteSpace H] in
/-- Transporting a subspace-domain operator preserves every approximation number. -/
theorem approximationNumber_scalarTransportSubspaceCLM
    (Z : Submodule 𝕜 H)
    (T : Z →L[𝕜] H) (n : ℕ) :
    (scalarTransportSubspaceCLM (e := e) Z T).approximationNumber n =
      T.approximationNumber n := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  let I := LinearIsometryEquiv.refl 𝕂 (ScalarTransport e H)
  have hsame :
      (ScalarTransport.clm (e := e) T).HasSameApproximationNumbers
        (scalarTransportSubspaceCLM (e := e) Z T) := by
    refine SameApproximationSingularValues.of_isometricEquiv_comp I W ?_
    ext z
    rfl
  rw [← hsame n]
  exact ScalarTransport.approximationNumber_clm (e := e) T n

/-- Every finite source gauge is unchanged for a transported subspace-domain map. -/
theorem prefixGauge_scalarTransportSubspaceCLM
    (N : SymmetricNormingFunction) (n : ℕ)
    (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection] (T : Z →L[𝕜] H) :
    N.prefixGauge n (scalarTransportSubspaceCLM (e := e) Z T) =
      N.prefixGauge n T := by
  unfold SymmetricNormingFunction.prefixGauge
  apply congrArg (N.finiteGauge n)
  funext i
  exact approximationNumber_scalarTransportSubspaceCLM (e := e) Z T i

/-- The extended source gauge is unchanged for a transported subspace-domain map. -/
theorem extendedGauge_scalarTransportSubspaceCLM
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] H) :
    N.extendedGauge (scalarTransportSubspaceCLM (e := e) Z T) =
      N.extendedGauge T := by
  unfold SymmetricNormingFunction.extendedGauge
  exact iSup_congr fun n => by
    rw [prefixGauge_scalarTransportSubspaceCLM (e := e) N n Z T]

/-- Symmetric-norm ideal membership is unchanged for a transported subspace-domain map. -/
theorem mem_scalarTransportSubspaceCLM_iff
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] H) :
    N.Mem (scalarTransportSubspaceCLM (e := e) Z T) ↔ N.Mem T := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_scalarTransportSubspaceCLM]

/-- Every symmetric-norming gauge is unchanged for a transported subspace-domain map. -/
theorem gauge_scalarTransportSubspaceCLM
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] H) :
    N.gauge (scalarTransportSubspaceCLM (e := e) Z T) = N.gauge T := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_scalarTransportSubspaceCLM]


/-- Transport a bounded operator between two closed subspaces, using the canonical
transported-subspace coordinates on both sides. -/
noncomputable def scalarTransportSubspaceBlockCLM
    (Z W : Submodule 𝕜 H)
    (T : Z →L[𝕜] W) :
    ScalarTransport.submodule (e := e) Z →L[𝕂]
      ScalarTransport.submodule (e := e) W :=
  (ScalarTransport.submoduleSubtypeEquiv (e := e) W).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ScalarTransport.clm (e := e) T ∘L
      (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Scalar transport is a bijection on bounded maps between closed subspaces. -/
noncomputable def scalarTransportSubspaceBlockCLMEquiv
    (Z W : Submodule 𝕜 H)  :
    (Z →L[𝕜] W) ≃
      (ScalarTransport.submodule (e := e) Z →L[𝕂]
        ScalarTransport.submodule (e := e) W) where
  toFun := scalarTransportSubspaceBlockCLM (e := e) Z W
  invFun T := (ScalarTransport.clmEquiv (e := e)).symm
    ((ScalarTransport.submoduleSubtypeEquiv (e := e) W).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).toContinuousLinearEquiv.toContinuousLinearMap)
  left_inv T := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  right_inv T := by
    apply ContinuousLinearMap.ext
    intro z
    rfl

omit [CompleteSpace H] in
/-- Two-sided transported subspace coordinates preserve every approximation number. -/
theorem approximationNumber_scalarTransportSubspaceBlockCLM
    (Z W : Submodule 𝕜 H)
    (T : Z →L[𝕜] W) (n : ℕ) :
    (scalarTransportSubspaceBlockCLM (e := e) Z W T).approximationNumber n =
      T.approximationNumber n := by
  let U := ScalarTransport.submoduleSubtypeEquiv (e := e) W
  let V := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  have hsame :
      (ScalarTransport.clm (e := e) T).HasSameApproximationNumbers
        (scalarTransportSubspaceBlockCLM (e := e) Z W T) := by
    refine SameApproximationSingularValues.of_isometricEquiv_comp U V ?_
    rfl
  rw [← hsame n]
  exact ScalarTransport.approximationNumber_clm (e := e) T n

/-- Transport a bounded operator from a closed subspace to its orthogonal complement.

The codomain adapter is the canonical isometry from the transport of `Zᗮ` to
the orthogonal complement of the transported `Z`.  Thus the result has exactly
the type used by the fixed-field directed tangent-corner theorems, without any
submodule equality casts. -/
noncomputable def scalarTransportOrthogonalSubspaceBlockCLM
    (Z : Submodule 𝕜 H)
    (T : Z →L[𝕜] Zᗮ) :
    ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ :=
  (ScalarTransport.orthogonalSubmoduleSubtypeEquiv (e := e) Z).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ScalarTransport.clm (e := e) T ∘L
      (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Transport a bounded operator from the transported subspace and its orthogonal
complement back to the original scalar field.  This is deliberately a named inverse
transport rather than an `Equiv`: the orthogonal-complement adapter contains a proof of
`submodule (Zᗮ) = (submodule Z)ᗮ`, so asking Lean for definitional inverse laws exposes
irrelevant equality casts.  The approximation-number theorems below are the invariant
actually needed by the source layer. -/
noncomputable def scalarTransportOrthogonalSubspaceBlockCLMInv
    (Z : Submodule 𝕜 H)
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ) :
    Z →L[𝕜] Zᗮ :=
  (ScalarTransport.clmEquiv (e := e)).symm
    ((ScalarTransport.orthogonalSubmoduleSubtypeEquiv (e := e) Z).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      T ∘L
      (ScalarTransport.submoduleSubtypeEquiv (e := e) Z).toContinuousLinearEquiv.toContinuousLinearMap)

omit [CompleteSpace H] in
/-- Orthogonal-corner transport preserves every approximation number. -/
theorem approximationNumber_scalarTransportOrthogonalSubspaceBlockCLM
    (Z : Submodule 𝕜 H)
    (T : Z →L[𝕜] Zᗮ) (n : ℕ) :
    (scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T).approximationNumber n =
      T.approximationNumber n := by
  let U := ScalarTransport.orthogonalSubmoduleSubtypeEquiv (e := e) Z
  let V := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  have hsame :
      (ScalarTransport.clm (e := e) T).HasSameApproximationNumbers
        (scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T) := by
    refine SameApproximationSingularValues.of_isometricEquiv_comp U V ?_
    rfl
  rw [← hsame n]
  exact ScalarTransport.approximationNumber_clm (e := e) T n

omit [CompleteSpace H] in
/-- Inverse orthogonal-corner transport also preserves every approximation number. -/
theorem approximationNumber_scalarTransportOrthogonalSubspaceBlockCLMInv
    (Z : Submodule 𝕜 H)
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ) (n : ℕ) :
    (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T).approximationNumber n =
      T.approximationNumber n := by
  let U := ScalarTransport.orthogonalSubmoduleSubtypeEquiv (e := e) Z
  let V := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  let X : ScalarTransport e Z →L[𝕂] ScalarTransport e Zᗮ :=
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      V.toContinuousLinearEquiv.toContinuousLinearMap
  have hcoord : T.HasSameApproximationNumbers X := by
    refine SameApproximationSingularValues.of_isometricEquiv_comp U.symm V.symm ?_
    rfl
  have hclm :
      ScalarTransport.clm (e := e)
          (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T) = X := by
    change (ScalarTransport.clmEquiv (e := e))
        ((ScalarTransport.clmEquiv (e := e)).symm X) = X
    exact Equiv.apply_symm_apply (ScalarTransport.clmEquiv (e := e)) X
  calc
    (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T).approximationNumber n =
        (ScalarTransport.clm (e := e)
          (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T)).approximationNumber n :=
      (ScalarTransport.approximationNumber_clm (e := e)
        (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T) n).symm
    _ = X.approximationNumber n := by rw [hclm]
    _ = T.approximationNumber n := (hcoord n).symm

/-- The extended symmetric-norming gauge is unchanged by orthogonal-corner
transport.  This is proved directly from the cross-field approximation-number
identity: `HasSameApproximationNumbers` itself is intentionally same-field. -/
theorem extendedGauge_scalarTransportOrthogonalSubspaceBlockCLM
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] Zᗮ) :
    N.extendedGauge (scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T) =
      N.extendedGauge T := by
  unfold SymmetricNormingFunction.extendedGauge
  exact iSup_congr fun n => by
    apply congrArg ENNReal.ofReal
    unfold SymmetricNormingFunction.prefixGauge
    apply congrArg (N.finiteGauge n)
    funext i
    exact approximationNumber_scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T i

/-- Symmetric-norm ideal membership is unchanged by orthogonal-corner transport. -/
theorem mem_scalarTransportOrthogonalSubspaceBlockCLM_iff
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] Zᗮ) :
    N.Mem (scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T) ↔ N.Mem T := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_scalarTransportOrthogonalSubspaceBlockCLM]

/-- Symmetric-norm gauges are unchanged by orthogonal-corner transport. -/
theorem gauge_scalarTransportOrthogonalSubspaceBlockCLM
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : Z →L[𝕜] Zᗮ) :
    N.gauge (scalarTransportOrthogonalSubspaceBlockCLM (e := e) Z T) = N.gauge T := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_scalarTransportOrthogonalSubspaceBlockCLM]

/-- The extended symmetric-norming gauge is unchanged by inverse
orthogonal-corner transport. -/
theorem extendedGauge_scalarTransportOrthogonalSubspaceBlockCLMInv
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ) :
    N.extendedGauge (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T) =
      N.extendedGauge T := by
  unfold SymmetricNormingFunction.extendedGauge
  exact iSup_congr fun n => by
    apply congrArg ENNReal.ofReal
    unfold SymmetricNormingFunction.prefixGauge
    apply congrArg (N.finiteGauge n)
    funext i
    exact approximationNumber_scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T i

/-- Symmetric-norm ideal membership is unchanged by inverse orthogonal-corner transport. -/
theorem mem_scalarTransportOrthogonalSubspaceBlockCLMInv_iff
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ) :
    N.Mem (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T) ↔ N.Mem T := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_scalarTransportOrthogonalSubspaceBlockCLMInv]

/-- Symmetric-norm gauges are unchanged by inverse orthogonal-corner transport. -/
theorem gauge_scalarTransportOrthogonalSubspaceBlockCLMInv
    (N : SymmetricNormingFunction) (Z : Submodule 𝕜 H) [Z.HasOrthogonalProjection]
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      (ScalarTransport.submodule (e := e) Z)ᗮ) :
    N.gauge (scalarTransportOrthogonalSubspaceBlockCLMInv (e := e) Z T) = N.gauge T := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_scalarTransportOrthogonalSubspaceBlockCLMInv]

/-- Approximation numbers of the inverse transported coordinates are unchanged. -/
theorem approximationNumber_scalarTransportSubspaceBlockCLMEquiv_symm
    (Z W : Submodule 𝕜 H) [Z.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (T : ScalarTransport.submodule (e := e) Z →L[𝕂]
      ScalarTransport.submodule (e := e) W) (n : ℕ) :
    ((scalarTransportSubspaceBlockCLMEquiv (e := e) Z W).symm T).approximationNumber n =
      T.approximationNumber n := by
  have h := approximationNumber_scalarTransportSubspaceBlockCLM (e := e) Z W
    ((scalarTransportSubspaceBlockCLMEquiv (e := e) Z W).symm T) n
  change (((scalarTransportSubspaceBlockCLMEquiv (e := e) Z W)
      ((scalarTransportSubspaceBlockCLMEquiv (e := e) Z W).symm T)).approximationNumber n) =
    ((scalarTransportSubspaceBlockCLMEquiv (e := e) Z W).symm T).approximationNumber n at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The extended source gauge is unchanged by two-sided subspace transport. -/
theorem extendedGauge_scalarTransportSubspaceBlockCLM
    (N : SymmetricNormingFunction) (Z W : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (T : Z →L[𝕜] W) :
    N.extendedGauge (scalarTransportSubspaceBlockCLM (e := e) Z W T) =
      N.extendedGauge T := by
  unfold SymmetricNormingFunction.extendedGauge
  exact iSup_congr fun n => by
    apply congrArg ENNReal.ofReal
    unfold SymmetricNormingFunction.prefixGauge
    apply congrArg (N.finiteGauge n)
    funext i
    exact approximationNumber_scalarTransportSubspaceBlockCLM (e := e) Z W T i

/-- Symmetric-norm ideal membership is unchanged by two-sided subspace transport. -/
theorem mem_scalarTransportSubspaceBlockCLM_iff
    (N : SymmetricNormingFunction) (Z W : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (T : Z →L[𝕜] W) :
    N.Mem (scalarTransportSubspaceBlockCLM (e := e) Z W T) ↔ N.Mem T := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_scalarTransportSubspaceBlockCLM]

/-- Symmetric-norm gauges are unchanged by two-sided subspace transport. -/
theorem gauge_scalarTransportSubspaceBlockCLM
    (N : SymmetricNormingFunction) (Z W : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (T : Z →L[𝕜] W) :
    N.gauge (scalarTransportSubspaceBlockCLM (e := e) Z W T) = N.gauge T := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_scalarTransportSubspaceBlockCLM]

namespace UnboundedCompressionTrialData

/-- The original subspace coordinate represented by a vector of the transported
subspace. -/
private def subspaceOut (Z : Submodule 𝕜 H)
    (z : ScalarTransport.submodule (e := e) Z) : Z :=
  ⟨ScalarTransport.out (e := e) (z : ScalarTransport e H), z.2⟩

/-- **Transport an unbounded Ritz-compression bundle across an isomorphism of
`RCLike` fields.**

The partial compression is transported and then conjugated into the canonical
transported-subspace subtype.  The residual is transported and precomposed by
the same coordinate isometry. -/
noncomputable def scalarTransport (D : UnboundedCompressionTrialData Z) :
    UnboundedCompressionTrialData (ScalarTransport.submodule (e := e) Z) := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  refine
    { compression := TauCeti.LinearPMap.unitaryConj W
        (ScalarTransport.pmap (e := e) D.compression)
      compression_isSelfAdjoint :=
        TauCeti.LinearPMap.isSelfAdjoint_unitaryConj
          ((ScalarTransport.isSelfAdjoint_pmap_iff e).2 D.compression_isSelfAdjoint)
      residual := scalarTransportSubspaceCLM (e := e) Z D.residual
      residual_orthogonal := ?_ }
  intro z z'
  change e (⟪D.residual (subspaceOut (e := e) Z z),
    ((subspaceOut (e := e) Z z' : Z) : H)⟫_𝕜) = 0
  rw [D.residual_orthogonal, map_zero]

/-- The transported residual is the scalar transport of the original residual,
up to the canonical isometry of the domain coordinates. -/
theorem scalarTransport_residual_eq (D : UnboundedCompressionTrialData Z) :
    (D.scalarTransport (e := e)).residual =
      scalarTransportSubspaceCLM (e := e) Z D.residual := rfl

/-- The transported residual has exactly the approximation singular values of
the scalar-transported residual before the harmless domain-coordinate change. -/
theorem scalarTransport_residual_sameApproximationNumbers_clm
    (D : UnboundedCompressionTrialData Z) :
    (ScalarTransport.clm (e := e) D.residual).HasSameApproximationNumbers
      (D.scalarTransport (e := e)).residual := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  let I := LinearIsometryEquiv.refl 𝕂 (ScalarTransport e H)
  refine SameApproximationSingularValues.of_isometricEquiv_comp I W ?_
  ext z
  rfl

/-- The transported residual has the same finite Ky Fan gauges as the original. -/
theorem kyFanApproximationGauge_scalarTransport_residual
    (D : UnboundedCompressionTrialData Z) (k : ℕ) :
    kyFanApproximationGauge k (D.scalarTransport (e := e)).residual =
      kyFanApproximationGauge k D.residual := by
  have hcoord := D.scalarTransport_residual_sameApproximationNumbers_clm (e := e)
  calc
    kyFanApproximationGauge k (D.scalarTransport (e := e)).residual =
        kyFanApproximationGauge k (ScalarTransport.clm (e := e) D.residual) := by
      change ((D.scalarTransport (e := e)).residual).kyFanGauge k =
        (ScalarTransport.clm (e := e) D.residual).kyFanGauge k
      exact ContinuousLinearMap.HasSameApproximationNumbers.kyFanGauge_eq
        (ContinuousLinearMap.HasSameApproximationNumbers.symm hcoord) k
    _ = kyFanApproximationGauge k D.residual :=
      ScalarTransport.kyFanApproximationGauge_clm k D.residual

/-- Source ideal membership of the residual is invariant under transport. -/
theorem mem_scalarTransport_residual_iff
    (N : SymmetricNormingFunction) (D : UnboundedCompressionTrialData Z) :
    N.Mem (D.scalarTransport (e := e)).residual ↔ N.Mem D.residual := by
  unfold SymmetricNormingFunction.Mem
  rw [N.extendedGauge_eq_of_hasSameApproximationNumbers
      (D.scalarTransport_residual_sameApproximationNumbers_clm (e := e)).symm,
    SymmetricNormingFunction.extendedGauge_clm]

/-- Every source symmetric-norming gauge of the residual is invariant under transport. -/
theorem gauge_scalarTransport_residual
    (N : SymmetricNormingFunction) (D : UnboundedCompressionTrialData Z) :
    N.gauge (D.scalarTransport (e := e)).residual = N.gauge D.residual := by
  unfold SymmetricNormingFunction.gauge
  rw [N.extendedGauge_eq_of_hasSameApproximationNumbers
      (D.scalarTransport_residual_sameApproximationNumbers_clm (e := e)).symm,
    SymmetricNormingFunction.extendedGauge_clm]

/-- Operator-form upper bounds on the unbounded compression are invariant under
scalar transport. -/
theorem semiboundedAbove_scalarTransport_iff
    (D : UnboundedCompressionTrialData Z) {alpha : ℝ} :
    TauCeti.LinearPMap.SemiboundedAbove (D.scalarTransport (e := e)).compression alpha ↔
      TauCeti.LinearPMap.SemiboundedAbove D.compression alpha := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  change TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.unitaryConj W (ScalarTransport.pmap (e := e) D.compression)) alpha ↔ _
  rw [TauCeti.LinearPMap.semiboundedAbove_unitaryConj_iff,
    ScalarTransport.semiboundedAbove_pmap_iff]

/-- A vector in the transported compression domain, read in the original
subspace coordinates. -/
private def compressionDomainOut (D : UnboundedCompressionTrialData Z)
    (z : (D.scalarTransport (e := e)).compression.domain) : D.compression.domain := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  refine ⟨subspaceOut (e := e) Z (z : ScalarTransport.submodule (e := e) Z), ?_⟩
  change ScalarTransport.out (e := e)
      (W.symm (z : ScalarTransport.submodule (e := e) Z)) ∈ D.compression.domain
  exact (ScalarTransport.mem_pmap_domain_iff (e := e)
    (A := D.compression) (W.symm (z : ScalarTransport.submodule (e := e) Z))).mp z.2

/-- The ambient action attached to transported trial data is exactly the
transport of the original ambient action. -/
theorem scalarTransport_action (D : UnboundedCompressionTrialData Z)
    (z : (D.scalarTransport (e := e)).compression.domain) :
    (D.scalarTransport (e := e)).action z =
      ScalarTransport.of (e := e) (D.action (compressionDomainOut (e := e) D z)) := by
  let W := ScalarTransport.submoduleSubtypeEquiv (e := e) Z
  change W (ScalarTransport.pmap (e := e) D.compression
        ⟨W.symm (z : ScalarTransport.submodule (e := e) Z), z.2⟩) +
      ScalarTransport.clm (e := e) D.residual
        (W.symm (z : ScalarTransport.submodule (e := e) Z)) = _
  rfl

/-- **The crossed lower form bound used by the Appendix tangent argument is
invariant under scalar transport.** -/
theorem crossedLower_scalarTransport
    (D : UnboundedCompressionTrialData Z) {alpha delta : ℝ}
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_𝕜) :
    ∀ z : (D.scalarTransport (e := e)).compression.domain,
      (alpha + delta) *
          ‖(ScalarTransport.submodule (e := e) V)ᗮ.starProjection
            (((z : ScalarTransport.submodule (e := e) Z) : ScalarTransport e H))‖ ^ 2 ≤
        RCLike.re ⟪
          (ScalarTransport.submodule (e := e) V)ᗮ.starProjection
            (((z : ScalarTransport.submodule (e := e) Z) : ScalarTransport e H)),
          (ScalarTransport.submodule (e := e) V)ᗮ.starProjection
            ((D.scalarTransport (e := e)).action z)⟫_𝕂 := by
  intro z
  let z0 := compressionDomainOut (e := e) D z
  let x : ScalarTransport e H :=
    ((z : ScalarTransport.submodule (e := e) Z) : ScalarTransport e H)
  have hz0 : (((z0 : D.compression.domain) : Z) : H) =
      ScalarTransport.out (e := e) x := rfl
  have hx : x = ScalarTransport.of (e := e) (((z0 : D.compression.domain) : Z) : H) := by
    rw [hz0]
    exact (ScalarTransport.of_out x).symm
  have hproj :
      (ScalarTransport.submodule (e := e) V)ᗮ.starProjection x =
        ScalarTransport.of (e := e)
          (Vᗮ.starProjection (((z0 : D.compression.domain) : Z) : H)) := by
    rw [hx]
    exact ScalarTransport.starProjection_orthogonal_of (e := e) V _
  have haction :
      (D.scalarTransport (e := e)).action z =
        ScalarTransport.of (e := e) (D.action z0) :=
    scalarTransport_action (e := e) D z
  have hprojAction :
      (ScalarTransport.submodule (e := e) V)ᗮ.starProjection
          ((D.scalarTransport (e := e)).action z) =
        ScalarTransport.of (e := e) (Vᗮ.starProjection (D.action z0)) := by
    rw [haction]
    exact ScalarTransport.starProjection_orthogonal_of (e := e) V _
  have h := hcross z0
  change (alpha + delta) *
      ‖(ScalarTransport.submodule (e := e) V)ᗮ.starProjection x‖ ^ 2 ≤
    RCLike.re ⟪(ScalarTransport.submodule (e := e) V)ᗮ.starProjection x,
      (ScalarTransport.submodule (e := e) V)ᗮ.starProjection
        ((D.scalarTransport (e := e)).action z)⟫_𝕂
  rw [hproj, hprojAction, ScalarTransport.norm_of, ScalarTransport.re_inner_of]
  exact h

/-- A residual identity against an ambient bounded operator transports exactly. -/
theorem scalarTransport_residual_eq_projectionBlock
    (D : UnboundedCompressionTrialData Z) (H0 : H →L[𝕜] H)
    (hResidual : D.residual = Zᗮ.starProjection ∘L H0 ∘L Z.subtypeL) :
    (D.scalarTransport (e := e)).residual =
      (ScalarTransport.submodule (e := e) Z)ᗮ.starProjection ∘L
        ScalarTransport.clm (e := e) H0 ∘L
          (ScalarTransport.submodule (e := e) Z).subtypeL := by
  apply ContinuousLinearMap.ext
  intro z
  let z0 : Z := subspaceOut (e := e) Z z
  let x : ScalarTransport e H := (z : ScalarTransport e H)
  have hz0 : ((z0 : Z) : H) = ScalarTransport.out (e := e) x := rfl
  have hx : x = ScalarTransport.of (e := e) ((z0 : Z) : H) := by
    rw [hz0]
    exact (ScalarTransport.of_out x).symm
  change ScalarTransport.of (e := e) (D.residual z0) = _
  rw [hResidual]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show Z.subtypeL z0 = ((z0 : Z) : H) from rfl]
  rw [show (ScalarTransport.submodule (e := e) Z).subtypeL z = x from rfl, hx,
    ScalarTransport.clm_apply, ScalarTransport.starProjection_orthogonal_of]

end UnboundedCompressionTrialData

end
end TanTheta
end DavisKahan
end TauCeti
