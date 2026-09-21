/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Ritz compression and residual

Finite-dimensional compressions, invariant-pair residuals, Galerkin
orthogonality, covariance, and Frobenius minimality.

## Sources

Ritz compressions and their residuals are the numerical-analysis form of the
Davis--Kahan `sin Θ` theorem; the source argument is distilled in
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex` and
`prose/distilled_literature/DavisKahan1970_part_III.tex`.  The generic-trial-map
shape here is this library's, not the paper's.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Residual/Ritz.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Compression of `A` to the isometric coordinate space of `X`. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap

/-- Residual of an approximate invariant pair represented by an isometric
embedding. -/
@[expose]
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M


/-- Galerkin/Ritz residual. -/
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)

/-- The represented approximate subspace. -/
@[expose]
def approximateSubspace (X : F →ₗᵢ[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.range X.toLinearMap

/-- Compression of a symmetric operator is symmetric.
-/
theorem isSymmetric_compression {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (X : F →ₗᵢ[𝕜] E) : (compression A X).IsSymmetric := by
  intro p q
  simp only [compression, LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left, hA, ← LinearMap.adjoint_inner_right]

/-- The adjoint of an isometric embedding is a left inverse. -/
 theorem adjoint_comp_linearIsometry_eq_id (X : F →ₗᵢ[𝕜] E) :
    X.toLinearMap.adjoint ∘ₗ X.toLinearMap = LinearMap.id := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [LinearMap.adjoint_inner_left]
  -- states the goal as the inner-product identity the isometry/adjoint lemma
  -- expects, rather than through the bundled map.
  change ⟪X x, X y⟫_𝕜 = ⟪x, y⟫_𝕜
  exact X.inner_map_map x y

/-- The Ritz residual is orthogonal to the trial subspace.
-/
theorem adjoint_comp_ritzResidual_eq_zero (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) :
    X.toLinearMap.adjoint ∘ₗ ritzResidual A X = 0 := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, ritzResidual, residual, compression,
    LinearMap.sub_apply, LinearMap.zero_apply, inner_zero_left]
  rw [LinearMap.adjoint_inner_left, inner_sub_left]
  -- states the goal as the inner-product identity the isometry/adjoint lemma
  -- expects, rather than through the bundled map.
  change ⟪A (X x), X y⟫_𝕜 -
      ⟪X (X.toLinearMap.adjoint (A (X x))), X y⟫_𝕜 = 0
  apply sub_eq_zero.mpr
  exact (LinearMap.adjoint_inner_left X.toLinearMap y (A (X x))).symm |>.trans
    (X.inner_map_map (X.toLinearMap.adjoint (A (X x))) y).symm

/-- Vanishing Ritz residual is equivalent to invariance of the represented
subspace.
-/
theorem ritzResidual_eq_zero_iff_reduces {A : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) :
    ritzResidual A X = 0 ↔ IsInvariant A (approximateSubspace X) := by
  constructor
  · intro hR x hx
    rcases hx with ⟨y, rfl⟩
    have hpoint := LinearMap.congr_fun hR y
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change A (X y) - X (compression A X y) = 0 at hpoint
    exact ⟨compression A X y, (sub_eq_zero.mp hpoint).symm⟩
  · intro hred
    ext y
    have hmem : A (X y) ∈ approximateSubspace X :=
      hred (X y) ⟨y, rfl⟩
    rcases hmem with ⟨z, hz⟩
    have hz' : A (X.toLinearMap y) = X.toLinearMap z := hz.symm
    have hcomp : compression A X y = z := by
      -- states the goal with the definition unfolded, in the shape the next step needs.
      change X.toLinearMap.adjoint (A (X.toLinearMap y)) = z
      rw [hz']
      have hleft := LinearMap.congr_fun (adjoint_comp_linearIsometry_eq_id X) z
      -- restates the hypothesis with the definition unfolded, which is the form the
      -- following step matches against.
      change X.toLinearMap.adjoint (X.toLinearMap z) = z at hleft
      exact hleft
    -- unfolds the named residual/compression so the following rewrite sees its
    -- definition; there is no `_apply` lemma for it to route through.
    change A (X.toLinearMap y) - X.toLinearMap (compression A X y) = 0
    rw [hcomp, hz', sub_self]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Residuals transform naturally under a unitary change of approximate
coordinates.
-/
theorem residual_comp_unitary (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) (V : F ≃ₗᵢ[𝕜] F) :
    residual A (X.comp V.toLinearIsometry)
        (V.symm.toLinearMap ∘ₗ M ∘ₗ V.toLinearMap) =
      residual A X M ∘ₗ V.toLinearMap := by
  ext x
  simp [residual, LinearMap.comp_apply]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- If `(X,M)` is invariant for `B`, its residual for `A` is exactly the
perturbation applied to `X`.
-/
theorem residual_eq_perturbation_comp {A B : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    residual A X M = (A - B) ∘ₗ X.toLinearMap := by
  -- states the goal with the definition unfolded, in the shape the next step needs.
  change A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M = (A - B) ∘ₗ X.toLinearMap
  rw [LinearMap.sub_comp, hBX]

/-- A unitarily invariant norm of the invariant-pair residual is bounded by
that of the ambient perturbation.
-/
theorem opNorm_residual_le_perturbation
    {A B : E →ₗ[𝕜] E} (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    UnitarilyInvariantSeminorm.opNorm (residual A X M) ≤
      ‖(A - B).toContinuousLinearMap‖ := by
  rw [residual_eq_perturbation_comp X M hBX,
    UnitarilyInvariantSeminorm.opNorm_apply]
  have hcomp :
      ((A - B) ∘ₗ X.toLinearMap).toContinuousLinearMap =
        (A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap := by
    ext x
    rfl
  have hX : ‖X.toLinearMap.toContinuousLinearMap‖ ≤ 1 := by
    refine X.toLinearMap.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (X.norm_map x)
  rw [hcomp]
  calc
    ‖(A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap‖
        ≤ ‖(A - B).toContinuousLinearMap‖ *
            ‖X.toLinearMap.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(A - B).toContinuousLinearMap‖ * 1 :=
      mul_le_mul_of_nonneg_left hX (norm_nonneg _)
    _ = ‖(A - B).toContinuousLinearMap‖ := mul_one _

/-- Orthogonal decomposition of a general residual into the Ritz residual and
compression error.
-/
theorem residual_frobenius_pythagoras (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (residual A X M) ^ 2 =
      UnitarilyInvariantSeminorm.frobenius (ritzResidual A X) ^ 2 +
      UnitarilyInvariantSeminorm.frobenius (compression A X - M) ^ 2 := by
  let b := stdOrthonormalBasis 𝕜 F
  have hdecomp : residual A X M =
      ritzResidual A X + X.toLinearMap ∘ₗ (compression A X - M) := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change A (X x) - X (M x) =
      (A (X x) - X ((compression A X) x)) +
        X (((compression A X) x) - M x)
    rw [map_sub]
    abel
  have hpoint : ∀ i, ‖residual A X M (b i)‖ ^ 2 =
      ‖ritzResidual A X (b i)‖ ^ 2 +
        ‖(compression A X - M) (b i)‖ ^ 2 := by
    intro i
    have hgal := LinearMap.congr_fun (adjoint_comp_ritzResidual_eq_zero A X) (b i)
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change X.toLinearMap.adjoint (ritzResidual A X (b i)) = 0 at hgal
    have horth :
        ⟪ritzResidual A X (b i),
            X.toLinearMap ((compression A X - M) (b i))⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_left, hgal, inner_zero_left]
    let d := (compression A X - M) (b i)
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change ⟪ritzResidual A X (b i), X d⟫_𝕜 = 0 at horth
    rw [LinearMap.congr_fun hdecomp (b i)]
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change
      ‖ritzResidual A X (b i) + X d‖ ^ 2 =
        ‖ritzResidual A X (b i)‖ ^ 2 + ‖d‖ ^ 2
    have hpythCodomain :
        ‖ritzResidual A X (b i) + X d‖ *
            ‖ritzResidual A X (b i) + X d‖ =
          ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
            ‖X d‖ * ‖X d‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (ritzResidual A X (b i)) (X d) horth
    have hnorm : ‖X d‖ = ‖d‖ := X.norm_map d
    rw [pow_two, pow_two, pow_two]
    calc
      ‖ritzResidual A X (b i) + X d‖ *
          ‖ritzResidual A X (b i) + X d‖ =
        ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
          ‖X d‖ * ‖X d‖ := hpythCodomain
      _ = ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
          ‖d‖ * ‖d‖ := by rw [hnorm]
  rw [UnitarilyInvariantSeminorm.frobenius_apply_basis (residual A X M) rfl b,
    UnitarilyInvariantSeminorm.frobenius_apply_basis (ritzResidual A X) rfl b,
    UnitarilyInvariantSeminorm.frobenius_apply_basis (compression A X - M) rfl b,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hpoint i


/-- The Ritz compression minimizes the Frobenius residual over all coordinate
operators.
-/
theorem ritzResidual_frobenius_minimal (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (ritzResidual A X) ≤
      UnitarilyInvariantSeminorm.frobenius (residual A X M) := by
  have hpyth := residual_frobenius_pythagoras A X M
  have hsq :
      UnitarilyInvariantSeminorm.frobenius (ritzResidual A X) ^ 2 ≤
        UnitarilyInvariantSeminorm.frobenius (residual A X M) ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact le_of_sq_le_sq hsq
    (UnitarilyInvariantSeminorm.frobenius.nonneg _)


end TauCeti
