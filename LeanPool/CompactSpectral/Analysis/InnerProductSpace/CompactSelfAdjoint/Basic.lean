/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Compact self-adjoint operators: compression / restriction helpers

This file provides small lemmas that make it convenient to *iterate* the Rayleigh-extremum
eigenvector construction for compact self-adjoint operators by passing to orthogonal complements.

The key technical device is to **compress** a bounded operator `T` to a complete submodule `V`
using the orthogonal projection `E →L[𝕜] V`. When `V` is invariant under `T`, this compression
agrees with the naive restriction and eigenvectors lift back to eigenvectors of `T`.

## Main definitions

- `CompactSelfAdjoint.compress`: compression of `T` to a complete submodule `V`.

## Main results

- `CompactSelfAdjoint.isSelfAdjoint_compress`
- `CompactSelfAdjoint.isCompactOperator_compress`
- `CompactSelfAdjoint.hasEigenvector_of_hasEigenvector_compress_of_invariant`
- `CompactSelfAdjoint.invariant_orthogonalComplement_eigenspace_of_isSelfAdjoint`
-/

namespace CompactSelfAdjoint

open scoped InnerProduct
open scoped Topology

open ContinuousLinearMap

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Compress a bounded operator `T` to a complete submodule `V` using the orthogonal projection. -/
noncomputable def compress (T : E →L[𝕜] E) (V : Submodule 𝕜 E) [CompleteSpace V] : V →L[𝕜] V :=
  V.orthogonalProjectionOnto ∘L T ∘L V.subtypeL

lemma coe_compress_apply_of_invariant (T : E →L[𝕜] E) (V : Submodule 𝕜 E) [CompleteSpace V]
    (hV : ∀ v ∈ V, T v ∈ V) (v : V) :
    (compress (T := T) (V := V) v : E) = T v := by
  classical
  have hTv : T (v : E) ∈ V := hV (v : E) v.property
  let w : V := ⟨T (v : E), hTv⟩
  have hw : V.orthogonalProjectionOnto (T (v : E)) = w := by
    simpa [w] using (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := V) w)
  have hw' : (V.orthogonalProjectionOnto (T (v : E)) : E) = T v := by
    simpa [w] using congrArg (fun x : V => (x : E)) hw
  simpa [compress, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hw'
lemma hasEigenvector_of_hasEigenvector_compress_of_invariant
    (T : E →L[𝕜] E) (V : Submodule 𝕜 E) [CompleteSpace V]
    (hV : ∀ v ∈ V, T v ∈ V) {μ : 𝕜} {v : V}
    (hv : Module.End.HasEigenvector ((compress (T := T) (V := V)) : V →ₗ[𝕜] V) μ v) :
    Module.End.HasEigenvector (T : E →ₗ[𝕜] E) μ (v : E) := by
  rcases (Module.End.hasEigenvector_iff.mp hv) with ⟨hv_mem, hv_ne0⟩
  have hv_ne0' : (v : E) ≠ 0 := by
    simp_all
  refine Module.End.hasEigenvector_iff.mpr ?_
  refine ⟨?_, hv_ne0'⟩
  rw [Module.End.mem_eigenspace_iff]
  have hv_eq : (compress (T := T) (V := V) v : E) = μ • (v : E) := by
    simp_all
  have hproj : (compress (T := T) (V := V) v : E) = T v :=
    coe_compress_apply_of_invariant (T := T) (V := V) hV v
  simpa [hproj] using hv_eq
lemma isCompactOperator_compress (T : E →L[𝕜] E) (hTc : IsCompactOperator (T : E → E))
    (V : Submodule 𝕜 E) [CompleteSpace V] :
    IsCompactOperator (compress (T := T) (V := V) : V → V) := by
  have h1 : IsCompactOperator (fun v : V => T (V.subtypeL v)) :=
    hTc.comp_clm V.subtypeL
  have h2 : IsCompactOperator (fun v : V => V.orthogonalProjectionOnto (T (V.subtypeL v))) :=
    h1.clm_comp V.orthogonalProjectionOnto
  exact h2
section CompleteSpace

variable [CompleteSpace E]

lemma isSelfAdjoint_compress (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (V : Submodule 𝕜 E) [CompleteSpace V] :
    IsSelfAdjoint (compress (T := T) (V := V)) := by
  have hT' : T† = T := ContinuousLinearMap.isSelfAdjoint_iff'.mp hT
  refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
  simp [compress, ContinuousLinearMap.adjoint_comp, hT', Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]
lemma invariant_orthogonalComplement_eigenspace_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (μ : 𝕜) :
    ∀ v : E,
      v ∈ (Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ →
        T v ∈ (Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ := by
  have hSymm : (T : E →ₗ[𝕜] E).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  intro v hv
  simpa using
    LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace
      (T := (T : E →ₗ[𝕜] E)) hSymm μ v hv
end CompleteSpace
end

end CompactSelfAdjoint
