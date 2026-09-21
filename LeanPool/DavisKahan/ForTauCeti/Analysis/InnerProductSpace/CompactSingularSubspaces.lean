/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSpectralDecomposition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint

/-!
# Singular eigenspaces of compact operators

For a bounded operator `T : E →L[𝕜] F`, a right singular eigenspace at squared singular value
`μ` is an eigenspace of `T⋆T`, and the corresponding left singular eigenspace is the
`μ`-eigenspace of `TT⋆`. For `μ ≠ 0`, `T` carries the right eigenspace isomorphically onto the
left eigenspace,
with inverse `μ⁻¹ T⋆`.

This formulation is valid in arbitrary Hilbert dimension.  For a compact operator the nonzero
singular eigenspaces are finite-dimensional, while the kernels may have arbitrary dimension.
It is the basis-free core of the Schmidt decomposition; orthonormal singular systems can be
chosen independently inside each finite-dimensional nonzero block.

## Main results

* `TauCeti.apply_mem_leftGram_eigenspace`: `T` maps a right Gram eigenspace into the matching left
  Gram eigenspace.
* `TauCeti.adjoint_apply_mem_rightGram_eigenspace`: `T⋆` maps a left Gram eigenspace into the
  matching right Gram eigenspace.
* `TauCeti.nonzeroGramEigenspaceEquiv`: the algebraic equivalence between corresponding nonzero
  Gram eigenspaces.
* `TauCeti.finiteDimensional_rightGram_eigenspace` and
  `TauCeti.finiteDimensional_leftGram_eigenspace`: compactness makes every nonzero singular block
  finite-dimensional.
* `TauCeti.finrank_rightGram_eigenspace_eq_leftGram_eigenspace`: corresponding nonzero singular
  blocks have equal multiplicity.
* `TauCeti.hasEigenvalue_rightGram_iff_leftGram`: the two Gram operators of any bounded map have
  the same nonzero eigenvalues.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable (T : E →L[𝕜] F)

/-- `T` maps each eigenspace of `T⋆T` into the same eigenspace of `TT⋆`. -/
theorem apply_mem_leftGram_eigenspace {μ : 𝕜} {x : E}
    (hx : x ∈ eigenspace (T.adjoint ∘L T).toLinearMap μ) :
    T x ∈ eigenspace (T ∘L T.adjoint).toLinearMap μ := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  calc
    (T ∘L T.adjoint) (T x) = T ((T.adjoint ∘L T) x) := rfl
    _ = T (μ • x) := congrArg T hx
    _ = μ • T x := map_smul T μ x

/-- `T⋆` maps each eigenspace of `TT⋆` into the same eigenspace of `T⋆T`. -/
theorem adjoint_apply_mem_rightGram_eigenspace {μ : 𝕜} {y : F}
    (hy : y ∈ eigenspace (T ∘L T.adjoint).toLinearMap μ) :
    T.adjoint y ∈ eigenspace (T.adjoint ∘L T).toLinearMap μ := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  calc
    (T.adjoint ∘L T) (T.adjoint y) = T.adjoint ((T ∘L T.adjoint) y) := rfl
    _ = T.adjoint (μ • y) := congrArg T.adjoint hy
    _ = μ • T.adjoint y := map_smul T.adjoint μ y

/-- The nonzero `μ`-eigenspaces of `T⋆T` and `TT⋆` are linearly equivalent via `x ↦ T x`,
with inverse `y ↦ μ⁻¹ • T⋆ y`. -/
noncomputable def nonzeroGramEigenspaceEquiv (μ : 𝕜) (hμ : μ ≠ 0) :
    eigenspace (T.adjoint ∘L T).toLinearMap μ ≃ₗ[𝕜]
      eigenspace (T ∘L T.adjoint).toLinearMap μ := by
  refine LinearEquiv.ofLinearMap
    (T.toLinearMap.restrict fun x hx => apply_mem_leftGram_eigenspace T hx)
    ((μ⁻¹ • T.adjoint.toLinearMap).restrict fun y hy =>
      Submodule.smul_mem _ _ (adjoint_apply_mem_rightGram_eigenspace T hy)) ?_ ?_
  · ext y
    have hy := y.2
    rw [Module.End.mem_eigenspace_iff] at hy
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply]
    calc
      T (μ⁻¹ • T.adjoint y.1) = μ⁻¹ • (T ∘L T.adjoint) y.1 := by
        rw [map_smul]
        rfl
      _ = μ⁻¹ • (μ • y.1) := congrArg (fun z => μ⁻¹ • z) hy
      _ = μ⁻¹ • μ • y.1 := by rw [smul_smul]
      _ = y.1 := inv_smul_smul₀ hμ y.1
  · ext x
    have hx := x.2
    rw [Module.End.mem_eigenspace_iff] at hx
    simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply]
    calc
      μ⁻¹ • T.adjoint (T x.1) = μ⁻¹ • (T.adjoint ∘L T) x.1 := rfl
      _ = μ⁻¹ • (μ • x.1) := congrArg (fun z => μ⁻¹ • z) hx
      _ = μ⁻¹ • μ • x.1 := by rw [smul_smul]
      _ = x.1 := inv_smul_smul₀ hμ x.1

/-- If `T` is compact, every nonzero eigenspace of `T⋆T` is finite-dimensional. -/
theorem finiteDimensional_rightGram_eigenspace (hT : IsCompactOperator T) (μ : 𝕜)
    (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace (T.adjoint ∘L T).toLinearMap μ) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace (hT.clm_comp T.adjoint) μ hμ

/-- If `T` is compact, every nonzero eigenspace of `TT⋆` is finite-dimensional. -/
theorem finiteDimensional_leftGram_eigenspace (hT : IsCompactOperator T) (μ : 𝕜)
    (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace (T ∘L T.adjoint).toLinearMap μ) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace (hT.comp_clm T.adjoint) μ hμ

/-- Corresponding nonzero Gram eigenspaces of a compact operator have the same finite
multiplicity. -/
theorem finrank_rightGram_eigenspace_eq_leftGram_eigenspace
    (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    finrank 𝕜 (eigenspace (T.adjoint ∘L T).toLinearMap μ) =
      finrank 𝕜 (eigenspace (T ∘L T.adjoint).toLinearMap μ) := by
  have hfdRight : FiniteDimensional 𝕜 (eigenspace (T.adjoint ∘L T).toLinearMap μ) :=
    finiteDimensional_rightGram_eigenspace T hT μ hμ
  have hfdLeft : FiniteDimensional 𝕜 (eigenspace (T ∘L T.adjoint).toLinearMap μ) :=
    finiteDimensional_leftGram_eigenspace T hT μ hμ
  exact (nonzeroGramEigenspaceEquiv T μ hμ).finrank_eq

/-- The two Gram operators of a bounded operator have the same nonzero eigenvalues. -/
theorem hasEigenvalue_rightGram_iff_leftGram (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T.adjoint ∘L T).toLinearMap μ ↔
      Module.End.HasEigenvalue (T ∘L T.adjoint).toLinearMap μ := by
  let e := nonzeroGramEigenspaceEquiv T μ hμ
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := h.exists_hasEigenvector
    let xs : eigenspace (T.adjoint ∘L T).toLinearMap μ := ⟨x, hx⟩
    let ys : eigenspace (T ∘L T.adjoint).toLinearMap μ := e xs
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨ys.property, ?_⟩
    intro hy0
    have hys0 : ys = 0 := by
      apply Subtype.ext
      exact hy0
    have hxs0 : xs = 0 := e.injective (by simpa only [ys, map_zero] using hys0)
    exact hx0 (congrArg Subtype.val hxs0)
  · intro h
    obtain ⟨y, hy, hy0⟩ := h.exists_hasEigenvector
    let ys : eigenspace (T ∘L T.adjoint).toLinearMap μ := ⟨y, hy⟩
    let xs : eigenspace (T.adjoint ∘L T).toLinearMap μ := e.symm ys
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨xs.property, ?_⟩
    intro hx0
    have hxs0 : xs = 0 := by
      apply Subtype.ext
      exact hx0
    have hys0 : ys = 0 := e.symm.injective (by simpa only [xs, map_zero] using hxs0)
    exact hy0 (congrArg Subtype.val hys0)

end

end TauCeti
