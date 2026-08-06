/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Module.Submodule.Invariant
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.Basic
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.CutoffProjector
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.OpNormEigenvalue

/-!
# Compact self-adjoint operators: large-eigenspace approximation in operator norm

For a compact self-adjoint operator `T` and `ε > 0`, the “large-eigenvalue” cutoff projector
`largeEigenspaceProjector T ε` yields a finite-dimensional approximation:

* `T ∘ largeEigenspaceProjector T ε` has finite-dimensional range, and
* `‖T - T ∘ largeEigenspaceProjector T ε‖ ≤ ε`.
-/

namespace CompactSelfAdjoint

open Filter Topology Metric
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]


lemma largeEigenspace_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
    largeEigenspace (𝕜 := 𝕜) (E := E) T ε ∈ t.invtSubmodule := by
  classical
  intro t
  let s : Set 𝕜 := {μ : 𝕜 | ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}
  have hsFin : s.Finite := by
    simpa [s, t] using
      finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc hε
  let : Fintype s.Elem := hsFin.fintype
  have h_each : ∀ i : s.Elem, t.eigenspace i.1 ∈ t.invtSubmodule := by
    intro i
    change t.eigenspace i.1 ≤ (t.eigenspace i.1).comap t
    intro x hx
    simp_all
  have h_sup : (Finset.univ.sup fun i : s.Elem => t.eigenspace i.1) ∈ t.invtSubmodule := by
    classical
    refine Finset.induction_on (Finset.univ : Finset s.Elem) ?_ ?_
    · simp
    · intro a S ha hS
      simpa [Finset.sup_insert] using Module.End.invtSubmodule.sup_mem (f := t) (h_each a) hS
  have hU' : (⨆ i : s.Elem, t.eigenspace i.1) ∈ t.invtSubmodule := by
    simpa [Finset.sup_univ_eq_iSup] using h_sup
  -- `s.Elem` and `largeEigenspace`'s index subtype are definitionally, but not
  -- syntactically, equal.
  exact hU'
lemma largeEigenspace_orthogonal_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
    (largeEigenspace (𝕜 := 𝕜) (E := E) T ε).orthogonal ∈ t.invtSubmodule := by
  classical
  intro t
  have hU :
      largeEigenspace (𝕜 := 𝕜) (E := E) T ε ∈ t.invtSubmodule :=
    largeEigenspace_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) T hT hTc hε
  have hSymm : t.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  exact hSymm.orthogonalComplement_mem_invtSubmodule (p := largeEigenspace (𝕜 := 𝕜) (E := E) T ε) hU
/-! ### Finite-rank approximation in operator norm -/
lemma finiteDimensional_range_comp_largeEigenspaceProjector
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    FiniteDimensional 𝕜
      (LinearMap.range
        ((T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε : E →L[𝕜] E) :
          E →ₗ[𝕜] E)) := by
  classical
  let U : Submodule 𝕜 E := largeEigenspace (𝕜 := 𝕜) (E := E) T ε
  have : FiniteDimensional 𝕜 U :=
    finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) T hT hTc hε
  let P : E →L[𝕜] E := largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  have hU_invt :
      U ∈ t.invtSubmodule := by
    simpa [U, t] using
      largeEigenspace_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc (ε := ε) hε
  have hU_forall : ∀ x ∈ U, (T : E →ₗ[𝕜] E) x ∈ U :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := (T : E →ₗ[𝕜] E)) (p := U)).1 hU_invt
  have hPdef : P = U.starProjection := by
    simp [P, largeEigenspaceProjector, U]
  have hrange_le : LinearMap.range ((T ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E) ≤ U := by
    rintro y ⟨x, rfl⟩
    simp_all
  -- A submodule of a finite-dimensional submodule is finite-dimensional.
  exact Submodule.finiteDimensional_of_le
    (S₁ := LinearMap.range ((T ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E)) (S₂ := U) hrange_le
lemma opNorm_sub_comp_largeEigenspaceProjector_le
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    ‖T - T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε‖ ≤ ε := by
  classical
  by_cases hE : Nontrivial E
  · have : Nontrivial E := hE
    let U : Submodule 𝕜 E := largeEigenspace (𝕜 := 𝕜) (E := E) T ε
    have : FiniteDimensional 𝕜 U :=
      finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc hε
    let P0 : E →L[𝕜] E := U.starProjection
    have hP0 : largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε = P0 := by
      simp [P0, largeEigenspaceProjector, U]
    -- Work in terms of `P0`.
    let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
    have hU_invt : U ∈ t.invtSubmodule := by
      simpa [U, t] using
        CompactSelfAdjoint.largeEigenspace_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
          (𝕜 := 𝕜) (E := E) T hT hTc (ε := ε) hε
    have hU_orth_invt : U.orthogonal ∈ t.invtSubmodule := by
      have :=
        largeEigenspace_orthogonal_mem_invtSubmodule_of_isCompactOperator_of_isSelfAdjoint
          (𝕜 := 𝕜) (E := E) T hT hTc (ε := ε) hε
      simpa [U, t] using this
    have hV : ∀ v ∈ U.orthogonal, T v ∈ U.orthogonal :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := t) (p := U.orthogonal)).1 hU_orth_invt
    -- Consider the compression of `T` to `Uᗮ`.
    let V : Submodule 𝕜 E := U.orthogonal
    let S : V →L[𝕜] V := compress (𝕜 := 𝕜) (E := E) (T := T) (V := V)
    have hS_self : IsSelfAdjoint S := by
      simpa [S, V] using isSelfAdjoint_compress (𝕜 := 𝕜) (E := E) (T := T) hT (V := V)
    have hS_compact : IsCompactOperator (S : V → V) := by
      simpa [S, V] using isCompactOperator_compress (𝕜 := 𝕜) (E := E) (T := T) hTc (V := V)
    have hS_le : ‖S‖ ≤ ε := by
      by_contra hlt
      have hlt' : ε < ‖S‖ := lt_of_not_ge hlt
      by_cases hVsub : Subsingleton V
      · have : Subsingleton V := hVsub
        have : ‖S‖ = 0 := ContinuousLinearMap.opNorm_subsingleton (f := S)
        exact (not_lt_of_ge (le_of_lt hε)) (by simpa [this] using hlt')
      · have : Nontrivial V := (not_subsingleton_iff_nontrivial).1 hVsub
        obtain ⟨μ, v, hv, hμ⟩ :=
          exists_hasEigenvector_norm_eq_opNorm_of_isCompactOperator_of_isSelfAdjoint
            (𝕜 := 𝕜) (E := V) S hS_self hS_compact
        have hμ' : ε ≤ ‖μ‖ := le_of_lt (by simpa [hμ] using hlt')
        have hvT : Module.End.HasEigenvector (T : E →ₗ[𝕜] E) μ (v : E) := by
          -- Lift the eigenvector from the compression using invariance of `V`.
          exact
            hasEigenvector_of_hasEigenvector_compress_of_invariant
              (𝕜 := 𝕜) (E := E) (T := T) (V := V) (hV := hV) (μ := μ) (v := v) hv
        rcases (Module.End.hasEigenvector_iff.mp hvT) with ⟨hv_mem, hv_ne0⟩
        have hμeig : t.HasEigenvalue μ :=
          Module.End.hasEigenvalue_of_hasEigenvector (f := t) hvT
        -- The eigenvector lies in the large-eigenspace cutoff by construction.
        have hvU : (v : E) ∈ U := by
          let i0 : {μ : 𝕜 // ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ} := ⟨μ, ⟨hμ', hμeig⟩⟩
          have hle : t.eigenspace μ ≤ U := by
            -- `eigenspace μ` is one summand in the defining `iSup`.
            simpa [U, largeEigenspace, t] using
              (le_iSup (fun i : {μ : 𝕜 // ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ} => t.eigenspace i.1) i0)
          exact hle hv_mem
        have hvV : (v : E) ∈ U.orthogonal := v.property
        have hdisj : Disjoint U U.orthogonal := Submodule.orthogonal_disjoint U
        have hv0 : (v : E) = 0 := by
          have : (v : E) ∈ (⊥ : Submodule 𝕜 E) := by
            have : (v : E) ∈ U ⊓ U.orthogonal := ⟨hvU, hvV⟩
            simpa [hdisj.eq_bot] using this
          simpa using this
        exact hv_ne0 hv0
    -- Use the compression bound pointwise on `x - P0 x ∈ Uᗮ`, then deduce an op-norm bound.
    have hboundV : ∀ y : V, ‖T (y : E)‖ ≤ ε * ‖(y : E)‖ := by
      intro y
      have hy : (compress (𝕜 := 𝕜) (E := E) (T := T) (V := V) y : E) = T y :=
        coe_compress_apply_of_invariant (𝕜 := 𝕜) (E := E) (T := T) (V := V) (hV := hV) y
      have hle : ‖(compress (𝕜 := 𝕜) (E := E) (T := T) (V := V) y : V)‖ ≤ ‖S‖ * ‖y‖ := by
        simpa [S] using (ContinuousLinearMap.le_opNorm S y)
      have hle' : ‖(compress (𝕜 := 𝕜) (E := E) (T := T) (V := V) y : V)‖ ≤ ε * ‖y‖ := by
        have : ‖S‖ * ‖y‖ ≤ ε * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right hS_le (norm_nonneg y)
        exact le_trans hle this
      -- Rewrite in `E` and use that `‖(y : E)‖ = ‖y‖`.
      simpa [hy, S] using hle'
    have hmain :
        ‖T - T ∘L P0‖ ≤ ε := by
      refine ContinuousLinearMap.opNorm_le_bound (T - T ∘L P0) (le_of_lt hε) ?_
      intro x
      -- Write the error as `T (x - P0 x)`.
      have hxV : x - P0 x ∈ V := by
        dsimp [V, P0]
        exact Submodule.sub_starProjection_mem_orthogonal (K := U) x
      let y : V := ⟨x - P0 x, hxV⟩
      have hy_bound : ‖T (x - P0 x)‖ ≤ ε * ‖x - P0 x‖ := by
        simpa [y] using (hboundV y)
      have hnorm_sub : ‖x - P0 x‖ ≤ ‖x‖ := by
        -- `x - P0 x = Uᗮ.starProjection x`, and star projections are contractive.
        have horth : V.starProjection x = x - P0 x := by
          dsimp [V, P0]
          exact Submodule.starProjection_orthogonal_val (K := U) x
        -- Take norms.
        have : ‖x - P0 x‖ = ‖V.starProjection x‖ := (congrArg norm horth).symm
        calc
          ‖x - P0 x‖ = ‖V.starProjection x‖ := this
          _ ≤ ‖x‖ := by simpa [V] using Submodule.norm_starProjection_apply_le (K := V) x
      -- Finish.
      have : ‖(T - T ∘L P0) x‖ ≤ ε * ‖x‖ := by
        have hx : (T - T ∘L P0) x = T (x - P0 x) := by
          simp
        calc
          ‖(T - T ∘L P0) x‖ = ‖T (x - P0 x)‖ := congrArg norm hx
          _ ≤ ε * ‖x - P0 x‖ := hy_bound
          _ ≤ ε * ‖x‖ := by gcongr
      exact this
    -- Rewrite back to the canonical projector.
    simpa [hP0] using hmain
  · -- If `E` is trivial, all operator norms are `0`.
    have : Subsingleton E := (not_nontrivial_iff_subsingleton).1 hE
    simpa using (le_of_lt hε)
end CompactSelfAdjoint
