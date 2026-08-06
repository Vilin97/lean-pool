/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Data.Fintype.Lattice
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.SpectralFiniteness

/-!
# Compact self-adjoint operators: large-eigenspace cutoff projectors

This file defines the “large-eigenvalue” spectral cutoff subspace for a compact self-adjoint
operator and packages its orthogonal projector, together with basic algebraic properties.

The key downstream use is to build finite-dimensional (hence finite-rank) approximations and to
enable spectral iteration by compressing to invariant orthogonal complements.

## Main definitions

- `CompactSelfAdjoint.largeEigenspace`
- `CompactSelfAdjoint.largeEigenspaceProjector`

## Main results

- `CompactSelfAdjoint.finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint`
- `CompactSelfAdjoint.isStarProjection_largeEigenspaceProjector`
- `CompactSelfAdjoint.range_largeEigenspaceProjector`
- `CompactSelfAdjoint.largeEigenspaceProjector_comp`
-/

namespace CompactSelfAdjoint

open Filter Topology Metric
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ### Large-eigenspace cutoff subspace and projector -/

/-- The spectral cutoff subspace spanned by all eigenspaces with `‖μ‖ ≥ ε`. -/
noncomputable def largeEigenspace (T : E →L[𝕜] E) (ε : ℝ) : Submodule 𝕜 E :=
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  (⨆ i : {μ : 𝕜 // ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}, t.eigenspace i.1)

/-- For a compact self-adjoint operator, `largeEigenspace` is finite-dimensional
(hence complete). -/
lemma finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    FiniteDimensional 𝕜 (largeEigenspace (𝕜 := 𝕜) (E := E) T ε) := by
  classical
  -- Reuse `finiteDimensional_iSup_eigenspace_norm_ge`.
  exact finiteDimensional_iSup_eigenspace_norm_ge (𝕜 := 𝕜) (E := E) T hT hTc hε
/-- The orthogonal projector onto the `largeEigenspace` cutoff subspace. -/
noncomputable def largeEigenspaceProjector
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) : E →L[𝕜] E := by
  classical
  haveI :
      FiniteDimensional 𝕜 (largeEigenspace (𝕜 := 𝕜) (E := E) T ε) :=
    finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) T hT hTc hε
  exact (largeEigenspace (𝕜 := 𝕜) (E := E) T ε).starProjection
lemma isStarProjection_largeEigenspaceProjector
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    IsStarProjection (largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε) := by
  classical
  simp [largeEigenspaceProjector, isStarProjection_starProjection]
lemma isSelfAdjoint_largeEigenspaceProjector
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    IsSelfAdjoint (largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε) := by
  exact (isStarProjection_largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε).isSelfAdjoint
lemma largeEigenspaceProjector_idem
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε ∘L
        largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε =
      largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε := by
  have h :=
    (isStarProjection_largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε).isIdempotentElem
  exact h
lemma range_largeEigenspaceProjector
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    LinearMap.range (largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε).toLinearMap =
      largeEigenspace (𝕜 := 𝕜) (E := E) T ε := by
  classical
  have :
      FiniteDimensional 𝕜 (largeEigenspace (𝕜 := 𝕜) (E := E) T ε) :=
    finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) T hT hTc hε
  simp only [largeEigenspaceProjector]
  exact Submodule.range_starProjection (U := largeEigenspace (𝕜 := 𝕜) (E := E) T ε)
/-! ### Cutoff projectors commute with the operator -/
lemma largeEigenspaceProjector_comp
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε ∘L T =
      T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  let ι := {μ : 𝕜 // ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}
  have hsFin :
      {μ : 𝕜 | ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}.Finite := by
    simpa [t] using
      finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc hε
  let : Fintype ι := hsFin.fintype
  let U : Submodule 𝕜 E := largeEigenspace (𝕜 := 𝕜) (E := E) T ε
  have : FiniteDimensional 𝕜 U :=
    finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) T hT hTc hε
  -- Unfold the cutoff projector as the orthogonal projection onto `U`.
  simp only [largeEigenspaceProjector]
  have hU_invt : U ∈ t.invtSubmodule := by
    have h_each : ∀ i : ι, t.eigenspace i.1 ∈ t.invtSubmodule := by
      intro i
      change t.eigenspace i.1 ≤ (t.eigenspace i.1).comap t
      intro x hx
      simp_all
    have h_sup : (Finset.univ.sup fun i : ι => t.eigenspace i.1) ∈ t.invtSubmodule := by
      classical
      refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
      · simp
      · intro a s ha hs
        simpa [Finset.sup_insert] using
          Module.End.invtSubmodule.sup_mem (f := t) (h_each a) hs
    have hU' :
        (⨆ i : ι, t.eigenspace i.1) ∈ t.invtSubmodule := by
      simpa [Finset.sup_univ_eq_iSup] using h_sup
    simpa [U, largeEigenspace, t, ι] using hU'
  have hSymm : t.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  have hU_orth_invt : U.orthogonal ∈ t.invtSubmodule :=
    hSymm.orthogonalComplement_mem_invtSubmodule (p := U) hU_invt
  have hU_forall : ∀ x ∈ U, t x ∈ U :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := t) (p := U)).1 hU_invt
  have hU_orth_forall : ∀ x ∈ U.orthogonal, t x ∈ U.orthogonal :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := t) (p := U.orthogonal)).1 hU_orth_invt
  ext x
  let P : E →L[𝕜] E := U.starProjection
  have hxP : P x ∈ U := Submodule.starProjection_apply_mem (U := U) x
  have hx_orth : x - P x ∈ U.orthogonal := Submodule.sub_starProjection_mem_orthogonal (K := U) x
  have hTP_mem : T (P x) ∈ U := by simpa [t] using hU_forall (P x) hxP
  have hTorth_mem : T (x - P x) ∈ U.orthogonal := by
    simpa [t] using hU_orth_forall (x - P x) hx_orth
  have hx_decomp : x = P x + (x - P x) := by
    simp_all
  have hP_TPx : P (T (P x)) = T (P x) :=
    (Submodule.starProjection_eq_self_iff (K := U)).2 hTP_mem
  have hP_Torth : P (T (x - P x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := U)).2 hTorth_mem
  have hPTx : P (T x) = T (P x) := by
    calc
      P (T x) = P (T (P x + (x - P x))) := by
            exact congrArg (fun y => P (T y)) hx_decomp
      _ = P (T (P x) + T (x - P x)) := by
            exact congrArg P (T.map_add (P x) (x - P x))
      _ = P (T (P x)) + P (T (x - P x)) := by
            exact P.map_add (T (P x)) (T (x - P x))
      _ = T (P x) := by
            rw [hP_TPx, hP_Torth]
            simp
  simpa [ContinuousLinearMap.comp_apply] using hPTx
end CompactSelfAdjoint
