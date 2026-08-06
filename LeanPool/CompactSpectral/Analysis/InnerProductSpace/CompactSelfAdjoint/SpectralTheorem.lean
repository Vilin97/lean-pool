/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.Approximation

/-!
# Compact self-adjoint operators: spectral theorem (Hilbert basis of eigenvectors)

This file proves the spectral theorem for **compact self-adjoint** operators on a
Hilbert space.

## Main results

- `iSup_eigenspace_orthogonal_eq_bot_of_isCompactOperator_of_isSelfAdjoint`:
  the (possibly infinite) supremum of eigenspaces is dense (its orthogonal complement is `⊥`).
- `exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint`:
  a compact self-adjoint operator admits a `HilbertBasis` consisting of eigenvectors.
-/

namespace CompactSelfAdjoint

open scoped Topology

open Filter Topology

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]


theorem iSup_eigenspace_orthogonal_eq_bot_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    (⨆ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ = ⊥ := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  ext x
  constructor
  · intro hx
    -- Reduce to showing `T x = 0`; then `x` lies in the kernel and its orthogonal complement.
    have hxU :
        ∀ {ε : ℝ} (hε : 0 < ε),
          x ∈ (largeEigenspace (𝕜 := 𝕜) (E := E) T ε)ᗮ := by
      intro ε hε
      -- `largeEigenspace T ε ≤ ⨆ μ, t.eigenspace μ`
      have hle :
          largeEigenspace (𝕜 := 𝕜) (E := E) T ε ≤ ⨆ μ : 𝕜, t.eigenspace μ := by
        classical
        -- Unfold and compare `iSup`s.
        refine iSup_le ?_
        intro i
        exact le_trans (le_iSup (fun μ : 𝕜 => t.eigenspace μ) i.1) le_rfl
      exact Submodule.orthogonal_le hle hx
    have hTx : T x = 0 := by
      by_contra hTx0
      have hx_ne : x ≠ 0 := by
        intro hx0
        exact hTx0 (by simp [hx0])
      have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx_ne
      have hntx : 0 < ‖T x‖ := norm_pos_iff.2 (by
        simp_all)
      -- Use the approximation estimate with `ε = ‖T x‖ / (2 * ‖x‖)`.
      set ε : ℝ := ‖T x‖ / (2 * ‖x‖) with hεdef
      have hε : 0 < ε := by
        simp_all
      have : FiniteDimensional 𝕜 (largeEigenspace (𝕜 := 𝕜) (E := E) T ε) :=
        finiteDimensional_largeEigenspace_of_isCompactOperator_of_isSelfAdjoint
          (𝕜 := 𝕜) (E := E) T hT hTc (ε := ε) hε
      let P : E →L[𝕜] E :=
        largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε
      have hxP : P x = 0 := by
        -- `x ∈ (largeEigenspace T ε)ᗮ` implies `U.starProjection x = 0`.
        have : x ∈ (largeEigenspace (𝕜 := 𝕜) (E := E) T ε)ᗮ := hxU hε
        -- `P` is the `starProjection` to `largeEigenspace`.
        have hP : P = (largeEigenspace (𝕜 := 𝕜) (E := E) T ε).starProjection := by
          simp [P, largeEigenspaceProjector]
        -- Convert membership in the orthogonal complement to a `starProjection` equation.
        have :
            (largeEigenspace (𝕜 := 𝕜) (E := E) T ε).starProjection x = 0 := by
          simpa using
            (Submodule.starProjection_apply_eq_zero_iff
                (K := largeEigenspace (𝕜 := 𝕜) (E := E) T ε) (v := x)).2 this
        simpa [hP] using this
      have hOp :
          ‖T - T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε‖ ≤ ε :=
        opNorm_sub_comp_largeEigenspaceProjector_le (𝕜 := 𝕜) (E := E) T hT hTc hε
      have hxP' :
          largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε x = 0 := by
        simpa [P] using hxP
      have hnorm :
          ‖T x‖ ≤ ε * ‖x‖ := by
        have hx' : (T - T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε) x = T x := by
          simp [hxP']
        calc
          ‖T x‖ = ‖(T - T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε) x‖ := by
            simp [hx']
          _ ≤ ‖T - T ∘L largeEigenspaceProjector (𝕜 := 𝕜) (E := E) T hT hTc hε‖ * ‖x‖ := by
            simpa using (ContinuousLinearMap.le_opNorm (T - T ∘L largeEigenspaceProjector
              (𝕜 := 𝕜) (E := E) T hT hTc hε) x)
          _ ≤ ε * ‖x‖ := by gcongr
      have hxne' : (‖x‖ : ℝ) ≠ 0 := (ne_of_gt hnx)
      have hnorm' : (‖T x‖ : ℝ) ≤ ‖T x‖ / 2 := by
        have : ‖T x‖ ≤ (‖T x‖ / (2 * ‖x‖)) * ‖x‖ := by
          simpa [hεdef] using hnorm
        have hmul : (‖T x‖ / (2 * ‖x‖)) * ‖x‖ = ‖T x‖ / 2 := by
          field_simp [hxne']
        simpa [hmul] using this
      have hlt : ‖T x‖ / 2 < ‖T x‖ := by nlinarith [hntx]
      exact (not_lt_of_ge hnorm' hlt)
    -- Now `x ∈ ker t` and `x ∈ (ker t)ᗮ`, so `x = 0`.
    have hxker : x ∈ LinearMap.ker t := by
      simpa [t] using hTx
    have hxker_orth : x ∈ (LinearMap.ker t : Submodule 𝕜 E)ᗮ := by
      -- `ker t = t.eigenspace 0 ≤ ⨆ μ, t.eigenspace μ`.
      have hle : (LinearMap.ker t : Submodule 𝕜 E) ≤ ⨆ μ : 𝕜, t.eigenspace μ := by
        simpa [Module.End.eigenspace_zero] using (le_iSup (fun μ : 𝕜 => t.eigenspace μ) (0 : 𝕜))
      exact Submodule.orthogonal_le hle hx
    have hdisj : Disjoint (LinearMap.ker t : Submodule 𝕜 E) (LinearMap.ker t : Submodule 𝕜 E)ᗮ :=
      Submodule.orthogonal_disjoint _
    have : x ∈ (⊥ : Submodule 𝕜 E) := by
      have : x ∈ (LinearMap.ker t : Submodule 𝕜 E) ⊓ (LinearMap.ker t : Submodule 𝕜 E)ᗮ :=
        ⟨hxker, hxker_orth⟩
      simpa [hdisj.eq_bot] using this
    simpa using this
  · simp_all
theorem exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    ∃ (ι : Type (max u v)) (μ : ι → 𝕜) (b : HilbertBasis ι 𝕜 E),
      (∀ i, Module.End.HasEigenvector (T : E →ₗ[𝕜] E) (μ i) (b i)) := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  have hSymm : t.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  -- Each eigenspace is closed (as a kernel), hence complete.
  have complete_eigenspace : ∀ μ : 𝕜, CompleteSpace (t.eigenspace μ) := by
    intro μ
    have hClosed : IsClosed ((t.eigenspace μ : Submodule 𝕜 E) : Set E) := by
      have :
          ((t.eigenspace μ : Submodule 𝕜 E) : Set E) =
            (LinearMap.ker ((T - μ • ContinuousLinearMap.id 𝕜 E : E →L[𝕜] E) :
              E →ₗ[𝕜] E) : Set E) := by
        ext x
        simp [t, LinearMap.mem_ker, sub_eq_zero]
      simpa [this] using
        (ContinuousLinearMap.isClosed_ker (f := (T - μ • ContinuousLinearMap.id 𝕜 E)))
    have : CompleteSpace ((t.eigenspace μ : Submodule 𝕜 E) : Set E) := hClosed.completeSpace_coe
    simpa using (inferInstance : CompleteSpace (t.eigenspace μ))
  -- Choose a Hilbert basis for each eigenspace, indexed by a set of vectors.
  classical
  choose w b hb using (fun μ : 𝕜 =>
    @exists_hilbertBasis 𝕜 _ (t.eigenspace μ) _ _ (complete_eigenspace μ))
  let ι : Type _ := Σ μ : 𝕜, w μ
  let μ' : ι → 𝕜 := fun i => i.1
  let v : ι → E := fun i => ((b i.1 i.2 : t.eigenspace i.1) : E)
  have hv_orthonormal : Orthonormal 𝕜 v := by
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨μi, vi⟩
      -- `b μi` is orthonormal in the eigenspace.
      have h' : ‖(b μi vi : t.eigenspace μi)‖ = 1 := by
        have : Orthonormal 𝕜 (b μi) := (b μi).orthonormal
        exact this.norm_eq_one vi
      -- Coercion to `E` does not change the norm.
      simpa [v] using h'
    · intro i j hij
      rcases i with ⟨μi, vi⟩
      rcases j with ⟨μj, vj⟩
      by_cases hμ : μi = μj
      · subst hμ
        have hv' : Orthonormal 𝕜 (b μi) := (b μi).orthonormal
        have hij' : vi ≠ vj := by
          intro h
          exact hij (by simp [h])
        -- Orthonormality within one eigenspace.
        have : inner 𝕜 (b μi vi : t.eigenspace μi) (b μi vj : t.eigenspace μi) = 0 :=
          hv'.2 hij'
        simpa [v] using this
      · -- Distinct eigenspaces are orthogonal for symmetric operators.
        have hOrtho : t.eigenspace μi ⟂ t.eigenspace μj :=
          (hSymm.orthogonalFamily_eigenspaces).isOrtho hμ
        have : inner 𝕜 (b μi vi : E) (b μj vj : E) = 0 := by
          have hmem : (b μi vi : E) ∈ (t.eigenspace μj)ᗮ :=
            hOrtho (b μi vi).property
          have : inner 𝕜 (b μj vj : E) (b μi vi : E) = 0 :=
            (Submodule.mem_orthogonal (K := t.eigenspace μj) (v := (b μi vi : E))).1 hmem
              (b μj vj : E) (b μj vj).property
          simpa using (inner_eq_zero_symm.mp this)
        simpa [v] using this
  have hv_span_orth : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    -- If `x` is orthogonal to the span of all basis vectors in all eigenspaces,
    -- then `x` is orthogonal to every eigenspace, hence zero by compactness.
    ext x
    constructor
    · intro hx
      have hxv : ∀ i : ι, inner 𝕜 (v i) x = 0 := by
        have hx' : ∀ y, y ∈ Submodule.span 𝕜 (Set.range v) → inner 𝕜 y x = 0 :=
          (Submodule.mem_orthogonal (K := Submodule.span 𝕜 (Set.range v)) (v := x)).1 hx
        intro i
        exact hx' (v i) (Submodule.subset_span ⟨i, rfl⟩)
      have hx_eigs : x ∈ (⨆ μ : 𝕜, t.eigenspace μ)ᗮ := by
        -- Use `iInf_orthogonal` to show orthogonality to each eigenspace.
        have hx_each : ∀ μ : 𝕜, x ∈ (t.eigenspace μ)ᗮ := by
          intro μ
          -- Let `f : t.eigenspace μ →L[𝕜] 𝕜` be `y ↦ ⟪x, y⟫`.
          let f : (t.eigenspace μ) →L[𝕜] 𝕜 := (innerSL 𝕜 x).comp (t.eigenspace μ).subtypeL
          have hspan_le : Submodule.span 𝕜 (Set.range (b μ)) ≤ LinearMap.ker f.toLinearMap := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨i, rfl⟩
            change f (b μ i) = 0
            -- `x` is orthogonal to `b μ i`, since it appears among the `v`'s.
            have : inner 𝕜 x (b μ i : E) = 0 := by
              have : inner 𝕜 (b μ i : E) x = 0 := by
                -- This is `hxv` at index `⟨μ, i⟩`.
                simpa [v] using hxv ⟨μ, i⟩
              simpa using (inner_eq_zero_symm.mp this)
            simpa [f, ContinuousLinearMap.comp_apply] using this
          have hker_closed : IsClosed ((LinearMap.ker f.toLinearMap : Set (t.eigenspace μ))) := by
            simpa using (ContinuousLinearMap.isClosed_ker (f := f))
          have htop :
              (Submodule.span 𝕜 (Set.range (b μ))).topologicalClosure = ⊤ :=
            HilbertBasis.dense_span (b μ)
          have htop_le :
              (⊤ : Submodule 𝕜 (t.eigenspace μ)) ≤ LinearMap.ker f.toLinearMap := by
            -- The kernel is closed and contains a dense submodule, hence is `⊤`.
            have :
                (Submodule.span 𝕜 (Set.range (b μ))).topologicalClosure ≤
                  LinearMap.ker f.toLinearMap :=
              Submodule.topologicalClosure_minimal
                (Submodule.span 𝕜 (Set.range (b μ))) hspan_le hker_closed
            simpa [htop] using this
          have hf0 : ∀ y, f y = 0 := by
            intro y
            have : y ∈ LinearMap.ker f.toLinearMap := htop_le (by simp)
            simpa [LinearMap.mem_ker] using this
          -- Conclude `x` is orthogonal to the whole eigenspace.
          refine (Submodule.mem_orthogonal (K := t.eigenspace μ) (v := x)).2 ?_
          intro y hy
          have : inner 𝕜 x y = 0 := by
            -- `y` is a vector in the eigenspace, viewed as a subtype element.
            have : f ⟨y, hy⟩ = 0 := hf0 ⟨y, hy⟩
            simpa [f, ContinuousLinearMap.comp_apply] using this
          simpa using (inner_eq_zero_symm.mp this)
        -- Now package the pointwise orthogonality.
        have hx_inf : x ∈ ⨅ μ : 𝕜, (t.eigenspace μ)ᗮ := by
          simp_all
        simpa [Submodule.iInf_orthogonal] using hx_inf
      have hx0 : x = 0 := by
        have hxbot : x ∈ (⊥ : Submodule 𝕜 E) := by
          have :
              (⨆ μ : 𝕜, t.eigenspace μ)ᗮ = (⊥ : Submodule 𝕜 E) :=
            iSup_eigenspace_orthogonal_eq_bot_of_isCompactOperator_of_isSelfAdjoint
              (𝕜 := 𝕜) (E := E) T hT hTc
          simpa [this] using hx_eigs
        simpa using hxbot
      simp [hx0]
    · simp_all
  refine ⟨ι, μ', HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth, ?_⟩
  intro i
  rcases i with ⟨μi, vi⟩
  -- Show each basis vector is a nonzero vector in the `μi`-eigenspace.
  have hmem : (v ⟨μi, vi⟩) ∈ t.eigenspace μi := by
    -- `b μi vi` is an element of the eigenspace subtype.
    simp [v]
  have hne0 : v ⟨μi, vi⟩ ≠ 0 := by
    have hv' : Orthonormal 𝕜 v := hv_orthonormal
    have hv_norm : ‖v ⟨μi, vi⟩‖ = 1 := hv'.1 ⟨μi, vi⟩
    have hv_norm_ne : ‖v ⟨μi, vi⟩‖ ≠ 0 := by
      simp [hv_norm]
    exact (norm_ne_zero_iff.1 hv_norm_ne)
  -- Identify `b`'s coerced family with `v`.
  have hb' :
      (HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth) ⟨μi, vi⟩ = v ⟨μi, vi⟩ := by
    simp_all
  -- Conclude.
  refine (Module.End.hasEigenvector_iff.mpr ?_)
  refine ⟨?_, ?_⟩
  · rw [hb']
    exact hmem
  · simpa [hb'] using hne0
end
end CompactSelfAdjoint
