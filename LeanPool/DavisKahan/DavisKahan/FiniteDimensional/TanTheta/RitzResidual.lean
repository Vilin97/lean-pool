/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace

/-!
# The paper-exact finite Davis--Kahan `tan Θ` theorem

This module records the finite residual theorem in the exact orientation used
in Davis--Kahan (1970), Section 2 and equation (6.6): the Ritz compression lies
in a finite interval, while the unwanted exact spectrum lies above that
interval by `δ`.  The conclusion controls every unitarily invariant norm.

The proof is organized around the source argument.  The hard root is a family
of Ky Fan prefix inequalities obtained from singular vectors of the sine block;
Fan dominance then gives every rectangular unitarily invariant norm.  This is
intentionally separate from the later relaxed spectral-norm theorem and from
an ordered graph-Sylvester formulation.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The one-sided interval hypothesis in the original `tan Θ` theorem.

The Ritz compression of `A` to the trial coordinates is contained in
`[β, α]`, while the spectrum of `A` carried by the orthogonal complement of
the exact subspace is contained in `[α + δ, ∞)`. -/
def TanThetaIntervalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (β α δ : ℝ) : Prop :=
  PointSpectrumIn (compression A X) ⊤ (Set.Icc β α) ∧
    PointSpectrumIn A Uᗮ (Set.Ici (α + δ))

/-- The paper's interval hypotheses force the trial and exact subspaces to be
transverse.  Thus the tangent has no `π/2` pole; this is a conclusion, not an
extra hypothesis. -/
theorem isTransverse_of_tanThetaIntervalGap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ) :
    IsTransverse (approximateSubspace X) U := by
  intro x hx hPx
  rcases hx with ⟨y, rfl⟩
  have hUperpRed : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hxyUperp : X.toLinearMap y ∈ Uᗮ := by
    have horth :
        X.toLinearMap y - U.starProjection (X.toLinearMap y) ∈ Uᗮ :=
      U.sub_starProjection_mem_orthogonal (X.toLinearMap y)
    rw [hPx, sub_zero] at horth
    exact horth
  have hTopRed : IsInvariant (compression A X) ⊤ := by
    intro z _
    exact Submodule.mem_top
  have hMspec : PointSpectrumIn (compression A X) ⊤ (Set.Iic α) := by
    intro lam hlam
    exact (hgap.1 hlam).2
  have hMupper :
      RCLike.re ⟪compression A X y, y⟫_𝕜 ≤ α * ‖y‖ ^ 2 :=
    upperFormBound_of_pointSpectrumIn (isSymmetric_compression hA X)
      hTopRed hMspec y Submodule.mem_top
  have hAlower :
      (α + δ) * ‖X.toLinearMap y‖ ^ 2 ≤
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 :=
    lowerFormBound_of_pointSpectrumIn hA hUperpRed hgap.2 (X.toLinearMap y) hxyUperp
  have hinner :
      RCLike.re ⟪compression A X y, y⟫_𝕜 =
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 := by
    simp only [compression, LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left]
  have hnorm : ‖X.toLinearMap y‖ = ‖y‖ := X.norm_map y
  have hyzero : y = 0 := by
    by_contra hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [← hinner, hnorm] at hAlower
    nlinarith [sq_pos_of_pos hynorm]
  simp [hyzero]


/-- The principal tangent at an index is `tan (arcsin σ)` for the directed sine block. -/
theorem principalTangents_approximateSubspace_apply
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (i : ℕ) :
    principalTangents (approximateSubspace X) U i =
      Real.tan (Real.arcsin ((sinThetaEmbedding U X).singularValues i)) := by
  simp only [principalTangents, principalAngles, Finsupp.mapRange_apply]
  rw [← singularValues_sinThetaEmbedding U X]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
private theorem sinThetaEmbedding_contraction
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (x : F) :
    ‖sinThetaEmbedding U X x‖ ≤ ‖x‖ := by
  calc
    ‖sinThetaEmbedding U X x‖ = ‖Uᗮ.starProjection (X x)‖ := rfl
    _ ≤ ‖X x‖ := Uᗮ.norm_starProjection_apply_le _
    _ = ‖x‖ := X.norm_map x

/-- Transversality makes every singular value of the directed sine block strictly less than one. -/
theorem singularValues_sinThetaEmbedding_lt_one_of_isTransverse
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U)
    (i : Fin (finrank 𝕜 F)) :
    (sinThetaEmbedding U X).singularValues i < 1 := by
  let S := sinThetaEmbedding U X
  let v := rightSingularBasis S i
  have hle : S.singularValues i ≤ 1 :=
    singularValues_le_one_of_contraction
      (sinThetaEmbedding_contraction U X) rfl i
  by_contra hlt
  have hσ : S.singularValues i = 1 := le_antisymm hle (not_lt.mp hlt)
  have hvnorm : ‖v‖ = 1 := (rightSingularBasis S).orthonormal.norm_eq_one i
  have hSnorm : ‖S v‖ = 1 := by
    rw [norm_apply_rightSingularBasis, hσ]
  have hperpnorm : ‖Uᗮ.starProjection (X v)‖ = 1 := by
    change ‖Uᗮ.starProjection (X v)‖ = 1 at hSnorm
    exact hSnorm
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (X v) U
  have hXnorm : ‖X v‖ = 1 := by rw [X.norm_map, hvnorm]
  have hprojnorm : ‖U.starProjection (X v)‖ = 0 := by
    nlinarith [norm_nonneg (U.starProjection (X v))]
  have hprojzero : U.starProjection (X v) = 0 := norm_eq_zero.mp hprojnorm
  have hXzero : X v = 0 := htrans (X v) ⟨v, rfl⟩ hprojzero
  have : ‖X v‖ = 0 := by rw [hXzero, norm_zero]
  linarith


/-- The ambient adjoint of the trial isometry acts on a nonzero sine left singular vector
by the same singular relation. -/
theorem adjoint_apply_sinTheta_leftSingularVector
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) {i : Fin (finrank 𝕜 F)}
    (hi : (sinThetaEmbedding U X).singularValues i ≠ 0) :
    X.toLinearMap.adjoint
        (leftSingularVector (sinThetaEmbedding U X) i) =
      ((((sinThetaEmbedding U X).singularValues i : ℝ) : 𝕜) •
        rightSingularBasis (sinThetaEmbedding U X) i) := by
  let S := sinThetaEmbedding U X
  let y := leftSingularVector S i
  have hSadj : S.adjoint y = ((S.singularValues i : ℝ) : 𝕜) •
      rightSingularBasis S i := adjoint_apply_leftSingularVector S hi
  have hyUperp : y ∈ Uᗮ := by
    dsimp [y]
    rw [leftSingularVector]
    exact Uᗮ.smul_mem _
      (Uᗮ.starProjection_apply_mem (X (rightSingularBasis S i)))
  apply ext_inner_right 𝕜
  intro z
  calc
    ⟪X.toLinearMap.adjoint y, z⟫_𝕜 = ⟪y, X z⟫_𝕜 :=
      LinearMap.adjoint_inner_left X.toLinearMap z y
    _ = ⟪y, Uᗮ.starProjection (X z)⟫_𝕜 := by
      rw [← Uᗮ.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hyUperp]
    _ = ⟪S.adjoint y, z⟫_𝕜 := by
      rw [LinearMap.adjoint_inner_left]
      rfl
    _ = ⟪((S.singularValues i : ℝ) : 𝕜) •
          rightSingularBasis S i, z⟫_𝕜 := by rw [hSadj]

/-- The normalized residual-side witness attached to a sine singular vector.

At a zero singular value the tangent contribution is zero, so the corresponding Ritz-space
basis vector is used.  At a positive singular value, the left singular vector is projected
away from the Ritz space and normalized by the complementary cosine. -/
noncomputable def tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (i : Fin (finrank 𝕜 F)) : E :=
  let S := sinThetaEmbedding U X
  let σ := S.singularValues i
  let v := rightSingularBasis S i
  if σ = 0 then X v else
    (((Real.sqrt (1 - σ ^ 2) : ℝ) : 𝕜)⁻¹) •
      (leftSingularVector S i - ((σ : ℝ) : 𝕜) • X v)

/-- **Adjoint transfer along a real singular relation.**

If `X⋆ y = σ • v` with `σ` real, then testing `X w` against `y` is testing `w`
against `v`, scaled by `σ`.  Two lines, and
`orthonormal_tanThetaResidualWitness` below proves an instance of it **three
times**: twice at `⟪X vi, yj⟫` in two different branches, once at `⟪yi, X vj⟫`
in the mirrored form.  See `{lane:DK-LONGPROOF-7}`. -/
theorem inner_apply_right_of_adjoint_eq_smul {X : E →ₗ[𝕜] F} {y : F} {v : E} {σ : ℝ}
    (h : X.adjoint y = ((σ : ℝ) : 𝕜) • v) (w : E) :
    ⟪X w, y⟫_𝕜 = ((σ : ℝ) : 𝕜) * ⟪w, v⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, h, inner_smul_right]

/-- The mirrored form of `inner_apply_right_of_adjoint_eq_smul`, with the
singular vector on the left.  `σ` being real is what makes the conjugate
disappear. -/
theorem inner_apply_left_of_adjoint_eq_smul {X : E →ₗ[𝕜] F} {y : F} {v : E} {σ : ℝ}
    (h : X.adjoint y = ((σ : ℝ) : 𝕜) • v) (w : E) :
    ⟪y, X w⟫_𝕜 = ((σ : ℝ) : 𝕜) * ⟪v, w⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_left, h, inner_smul_left, RCLike.conj_ofReal]

/-- The residual witnesses form an orthonormal family once the tangent has no pole. -/
theorem orthonormal_tanThetaResidualWitness
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    Orthonormal 𝕜 (tanThetaResidualWitness U X) := by
  classical
  let S := sinThetaEmbedding U X
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    let σ := S.singularValues i
    let v := rightSingularBasis S i
    have hvv : ⟪v, v⟫_𝕜 = 1 := by
      simp [v]
    by_cases hσ : σ = 0
    · have hw : tanThetaResidualWitness U X i = X.toLinearMap v := by
        simp [tanThetaResidualWitness, S, σ, v, hσ]
      rw [hw]
      calc
        ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = ⟪v, v⟫_𝕜 :=
          X.inner_map_map v v
        _ = 1 := hvv
    · let y := leftSingularVector S i
      have hXadj : X.toLinearMap.adjoint y = ((σ : ℝ) : 𝕜) • v := by
        simpa [S, σ, v, y] using
          adjoint_apply_sinTheta_leftSingularVector U X hσ
      have hyy : ⟪y, y⟫_𝕜 = 1 := by
        simpa [y] using
          (orthonormal_iff_ite.mp (orthonormal_leftSingularVector_subtype S)
            ⟨i, hσ⟩ ⟨i, hσ⟩)
      have hXv_y : ⟪X.toLinearMap v, y⟫_𝕜 = ((σ : ℝ) : 𝕜) := by
        calc
          ⟪X.toLinearMap v, y⟫_𝕜 = ⟪v, X.toLinearMap.adjoint y⟫_𝕜 :=
            (LinearMap.adjoint_inner_right X.toLinearMap v y).symm
          _ = ⟪v, ((σ : ℝ) : 𝕜) • v⟫_𝕜 := by rw [hXadj]
          _ = ((σ : ℝ) : 𝕜) := by rw [inner_smul_right, hvv, mul_one]
      have hy_Xv : ⟪y, X.toLinearMap v⟫_𝕜 = ((σ : ℝ) : 𝕜) := by
        calc
          ⟪y, X.toLinearMap v⟫_𝕜 = ⟪X.toLinearMap.adjoint y, v⟫_𝕜 :=
            (LinearMap.adjoint_inner_left X.toLinearMap v y).symm
          _ = ⟪((σ : ℝ) : 𝕜) • v, v⟫_𝕜 := by rw [hXadj]
          _ = ((σ : ℝ) : 𝕜) := by
            rw [inner_smul_left, RCLike.conj_ofReal, hvv, mul_one]
      have hXX : ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = 1 := by
        calc
          ⟪X.toLinearMap v, X.toLinearMap v⟫_𝕜 = ⟪v, v⟫_𝕜 :=
            X.inner_map_map v v
          _ = 1 := hvv
      have hraw :
          ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v,
            y - ((σ : ℝ) : 𝕜) • X.toLinearMap v⟫_𝕜 =
            (((1 - σ ^ 2 : ℝ) : 𝕜)) := by
        simp only [inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, RCLike.conj_ofReal, hyy, hy_Xv, hXv_y, hXX]
        push_cast
        ring
      have hσnonneg : 0 ≤ σ := S.singularValues_nonneg i
      have hσlt : σ < 1 := by
        simpa [S, σ] using
          singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i
      let c := Real.sqrt (1 - σ ^ 2)
      have hcpos : 0 < c := by
        dsimp [c]
        exact Real.sqrt_pos.2 (by nlinarith)
      have hcne : c ≠ 0 := ne_of_gt hcpos
      have hw :
          tanThetaResidualWitness U X i =
            ((((c : ℝ) : 𝕜)⁻¹) •
              (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)) := by
        simp [tanThetaResidualWitness, S, σ, v, y, c, hσ]
      have hc_sq : c ^ 2 = 1 - σ ^ 2 := by
        dsimp [c]
        exact Real.sq_sqrt (by nlinarith)
      have hnormalize : c⁻¹ * (c⁻¹ * (1 - σ ^ 2)) = 1 := by
        field_simp [hcne]
        nlinarith
      rw [hw]
      simp only [inner_smul_left, inner_smul_right, map_inv₀,
        RCLike.conj_ofReal, hraw]
      exact_mod_cast hnormalize
  · rw [ite_eq_right hij]
    let σi := S.singularValues i
    let σj := S.singularValues j
    let vi := rightSingularBasis S i
    let vj := rightSingularBasis S j
    have hvv : ⟪vi, vj⟫_𝕜 = 0 := by
      simp [vi, vj, hij,
        orthonormal_iff_ite.mp (rightSingularBasis S).orthonormal i j]
    have hXX : ⟪X.toLinearMap vi, X.toLinearMap vj⟫_𝕜 = 0 := by
      calc
        ⟪X.toLinearMap vi, X.toLinearMap vj⟫_𝕜 = ⟪vi, vj⟫_𝕜 :=
          X.inner_map_map vi vj
        _ = 0 := hvv
    by_cases hi : σi = 0
    · have hwi : tanThetaResidualWitness U X i = X.toLinearMap vi := by
        simp [tanThetaResidualWitness, S, σi, vi, hi]
      by_cases hj : σj = 0
      · have hwj : tanThetaResidualWitness U X j = X.toLinearMap vj := by
          simp [tanThetaResidualWitness, S, σj, vj, hj]
        rw [hwi, hwj, hXX]
      · let yj := leftSingularVector S j
        have hXadjj : X.toLinearMap.adjoint yj = ((σj : ℝ) : 𝕜) • vj := by
          simpa [S, σj, vj, yj] using
            adjoint_apply_sinTheta_leftSingularVector U X hj
        have hXvi_yj :
            ⟪X.toLinearMap vi, yj⟫_𝕜 = ((σj : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          inner_apply_right_of_adjoint_eq_smul hXadjj vi
        have hraw :
            ⟪X.toLinearMap vi,
              yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj⟫_𝕜 = 0 := by
          rw [inner_sub_right, inner_smul_right, hXvi_yj, hXX, hvv]
          simp
        let cj := Real.sqrt (1 - σj ^ 2)
        have hwj :
            tanThetaResidualWitness U X j =
              ((((cj : ℝ) : 𝕜)⁻¹) •
                (yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj)) := by
          simp [tanThetaResidualWitness, S, σj, vj, yj, cj, hj]
        rw [hwi, hwj, inner_smul_right, hraw, mul_zero]
    · let yi := leftSingularVector S i
      have hXadji : X.toLinearMap.adjoint yi = ((σi : ℝ) : 𝕜) • vi := by
        simpa [S, σi, vi, yi] using
          adjoint_apply_sinTheta_leftSingularVector U X hi
      by_cases hj : σj = 0
      · have hyi_Xvj :
            ⟪yi, X.toLinearMap vj⟫_𝕜 = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 := by
          calc
            ⟪yi, X.toLinearMap vj⟫_𝕜 =
                ⟪X.toLinearMap.adjoint yi, vj⟫_𝕜 :=
              (LinearMap.adjoint_inner_left X.toLinearMap vj yi).symm
            _ = ⟪((σi : ℝ) : 𝕜) • vi, vj⟫_𝕜 := by rw [hXadji]
            _ = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 := by
              rw [inner_smul_left, RCLike.conj_ofReal]
        have hraw :
            ⟪yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi,
              X.toLinearMap vj⟫_𝕜 = 0 := by
          rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
            hyi_Xvj, hXX, hvv]
          simp
        let ci := Real.sqrt (1 - σi ^ 2)
        have hwi :
            tanThetaResidualWitness U X i =
              ((((ci : ℝ) : 𝕜)⁻¹) •
                (yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi)) := by
          simp [tanThetaResidualWitness, S, σi, vi, yi, ci, hi]
        have hwj : tanThetaResidualWitness U X j = X.toLinearMap vj := by
          simp [tanThetaResidualWitness, S, σj, vj, hj]
        rw [hwi, hwj, inner_smul_left, hraw, mul_zero]
      · let yj := leftSingularVector S j
        have hXadjj : X.toLinearMap.adjoint yj = ((σj : ℝ) : 𝕜) • vj := by
          simpa [S, σj, vj, yj] using
            adjoint_apply_sinTheta_leftSingularVector U X hj
        have hyy : ⟪yi, yj⟫_𝕜 = 0 := by
          simpa [yi, yj, hij] using
            (orthonormal_iff_ite.mp (orthonormal_leftSingularVector_subtype S)
              ⟨i, hi⟩ ⟨j, hj⟩)
        have hyi_Xvj :
            ⟪yi, X.toLinearMap vj⟫_𝕜 = ((σi : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          inner_apply_left_of_adjoint_eq_smul hXadji vj
        have hXvi_yj :
            ⟪X.toLinearMap vi, yj⟫_𝕜 = ((σj : ℝ) : 𝕜) * ⟪vi, vj⟫_𝕜 :=
          inner_apply_right_of_adjoint_eq_smul hXadjj vi
        have hraw :
            ⟪yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi,
              yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj⟫_𝕜 = 0 := by
          simp only [inner_sub_left, inner_sub_right, inner_smul_left,
            inner_smul_right, RCLike.conj_ofReal,
            hyy, hyi_Xvj, hXvi_yj, hXX, hvv]
          ring
        let ci := Real.sqrt (1 - σi ^ 2)
        let cj := Real.sqrt (1 - σj ^ 2)
        have hwi :
            tanThetaResidualWitness U X i =
              ((((ci : ℝ) : 𝕜)⁻¹) •
                (yi - ((σi : ℝ) : 𝕜) • X.toLinearMap vi)) := by
          simp [tanThetaResidualWitness, S, σi, vi, yi, ci, hi]
        have hwj :
            tanThetaResidualWitness U X j =
              ((((cj : ℝ) : 𝕜)⁻¹) •
                (yj - ((σj : ℝ) : 𝕜) • X.toLinearMap vj)) := by
          simp [tanThetaResidualWitness, S, σj, vj, yj, cj, hj]
        simp only [hwi, hwj, inner_smul_left, inner_smul_right,
          hraw, mul_zero, mul_zero]

/-- The scalar spectral-gap estimate for one principal tangent.

This is the analytic core of equation (6.6), expressed without direct-rotation coordinates.
The left singular vector of the sine block is projected away from the Ritz space; Galerkin
orthogonality removes that projection from the residual pairing, while its norm supplies the
cosine denominator. -/
theorem tanThetaResidualWitness_scalar
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    (i : Fin (finrank 𝕜 F)) :
    δ * tanTheta0.singularValues i ≤
      RCLike.re ⟪tanThetaResidualWitness U X i,
        ritzResidual A X (rightSingularBasis (sinThetaEmbedding U X) i)⟫_𝕜 := by
  let S := sinThetaEmbedding U X
  let M := compression A X
  let R := ritzResidual A X
  let σ := S.singularValues i
  let v := rightSingularBasis S i
  have hvnorm : ‖v‖ = 1 := (rightSingularBasis S).orthonormal.norm_eq_one i
  have hσnonneg : 0 ≤ σ := S.singularValues_nonneg i
  have htrans := isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have hσlt : σ < 1 := singularValues_sinThetaEmbedding_lt_one_of_isTransverse U X htrans i
  have hcpos : 0 < Real.sqrt (1 - σ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have htan_i : tanTheta0.singularValues i = σ / Real.sqrt (1 - σ ^ 2) := by
    calc
      tanTheta0.singularValues i = principalTangents (approximateSubspace X) U i :=
        congrArg (fun z : ℕ →₀ ℝ => z (i : ℕ)) htan
      _ = Real.tan (Real.arcsin σ) := by
        simpa [S, σ] using principalTangents_approximateSubspace_apply U X (i : ℕ)
      _ = σ / Real.sqrt (1 - σ ^ 2) := Real.tan_arcsin σ
  by_cases hσzero : σ = 0
  · have hgal := LinearMap.congr_fun (adjoint_comp_ritzResidual_eq_zero A X) v
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have horth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hwitness : tanThetaResidualWitness U X i = X.toLinearMap v := by
      simp [tanThetaResidualWitness, S, σ, v, hσzero]
    rw [htan_i, hσzero, zero_div, mul_zero, hwitness]
    change 0 ≤ RCLike.re ⟪X.toLinearMap v, R v⟫_𝕜
    rw [horth]
    simp
  · let y := leftSingularVector S i
    have hynorm : ‖y‖ = 1 := by
      simpa [y] using (orthonormal_leftSingularVector_subtype S).norm_eq_one ⟨i, hσzero⟩
    have hSv : S v = ((σ : ℝ) : 𝕜) • y := by
      simpa [S, σ, v, y] using apply_rightSingularBasis_eq_smul_leftSingularVector S i
    have hSadj : S.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa [S, σ, v, y] using adjoint_apply_leftSingularVector S hσzero
    have hyUperp : y ∈ Uᗮ := by
      dsimp [y]
      rw [leftSingularVector]
      exact Uᗮ.smul_mem _ (Uᗮ.starProjection_apply_mem (X v))
    have hXadj : X.toLinearMap.adjoint y = ((σ : ℝ) : 𝕜) • v := by
      simpa [S, σ, v, y] using
        adjoint_apply_sinTheta_leftSingularVector U X hσzero
    have hMupper : RCLike.re ⟪M v, v⟫_𝕜 ≤ α := by
      have hTopRed : IsInvariant M ⊤ := fun z _ => Submodule.mem_top
      have hspec : PointSpectrumIn M ⊤ (Set.Iic α) := by
        intro lam hlam
        exact (hgap.1 hlam).2
      have hbound : RCLike.re ⟪M v, v⟫_𝕜 ≤ α * ‖v‖ ^ 2 :=
        upperFormBound_of_pointSpectrumIn (isSymmetric_compression hA X)
          hTopRed hspec v Submodule.mem_top
      simpa [hvnorm] using hbound
    have hAlower : α + δ ≤ RCLike.re ⟪A y, y⟫_𝕜 := by
      have hUperpRed : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
      have hbound : (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
        lowerFormBound_of_pointSpectrumIn hA hUperpRed hgap.2 y hyUperp
      simpa [hynorm] using hbound
    have hSyl := LinearMap.congr_fun
      (sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) v
    have hpair :
        RCLike.re ⟪y, R v⟫_𝕜 =
          σ * (RCLike.re ⟪A y, y⟫_𝕜 - RCLike.re ⟪M v, v⟫_𝕜) := by
      have hright :
          ⟪y, complementaryProjection U (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜 := by
        change ⟪y, Uᗮ.starProjection (R v)⟫_𝕜 = ⟪y, R v⟫_𝕜
        rw [← Uᗮ.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hyUperp]
      have hsyl' : A (S v) - S (M v) = complementaryProjection U (R v) := by
        simpa [S, M, R, ritzResidual] using hSyl
      have hSM : ⟪y, S (M v)⟫_𝕜 = ⟪S.adjoint y, M v⟫_𝕜 := by
        exact (LinearMap.adjoint_inner_left S (M v) y).symm
      have hpairComplex :
          ⟪y, R v⟫_𝕜 =
            (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by
        calc
          ⟪y, R v⟫_𝕜 = ⟪y, complementaryProjection U (R v)⟫_𝕜 := hright.symm
          _ = ⟪y, A (S v) - S (M v)⟫_𝕜 := by rw [hsyl']
          _ = ⟪y, A (S v)⟫_𝕜 - ⟪y, S (M v)⟫_𝕜 := inner_sub_right _ _ _
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) - ⟪y, S (M v)⟫_𝕜 := by
            rw [hSv, map_smul, inner_smul_right]
          _ = (((σ : ℝ) : 𝕜) * ⟪y, A y⟫_𝕜) -
              (((σ : ℝ) : 𝕜) * ⟪v, M v⟫_𝕜) := by
            rw [hSM, hSadj, inner_smul_left, RCLike.conj_ofReal]
          _ = (((σ : ℝ) : 𝕜) * (⟪y, A y⟫_𝕜 - ⟪v, M v⟫_𝕜)) := by ring
      have hAy : RCLike.re ⟪y, A y⟫_𝕜 = RCLike.re ⟪A y, y⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      have hMv : RCLike.re ⟪v, M v⟫_𝕜 = RCLike.re ⟪M v, v⟫_𝕜 := by
        rw [← inner_conj_symm, RCLike.conj_re]
      rw [hpairComplex, RCLike.re_ofReal_mul, map_sub, hAy, hMv]
    have hpair_lower : δ * σ ≤ RCLike.re ⟪y, R v⟫_𝕜 := by
      rw [hpair]
      nlinarith
    have hgal := LinearMap.congr_fun (adjoint_comp_ritzResidual_eq_zero A X) v
    change X.toLinearMap.adjoint (R v) = 0 at hgal
    have hXorth : ⟪X.toLinearMap v, R v⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_right, hgal, inner_zero_right]
    have hrawComplex :
        ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          ⟪y, R v⟫_𝕜 := by
      rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, hXorth,
        mul_zero, sub_zero]
    have hraw :
        RCLike.re ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 := congrArg RCLike.re hrawComplex
    let c := Real.sqrt (1 - σ ^ 2)
    have hcpos' : 0 < c := by simpa [c] using hcpos
    have hscale :
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
          RCLike.re ⟪y, R v⟫_𝕜 / c := by
      calc
        RCLike.re ⟪((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v)), R v⟫_𝕜 =
            c⁻¹ * RCLike.re
              ⟪y - ((σ : ℝ) : 𝕜) • X.toLinearMap v, R v⟫_𝕜 := by
                rw [inner_smul_left, map_inv₀, RCLike.conj_ofReal,
                  ← RCLike.ofReal_inv, RCLike.re_ofReal_mul]
        _ = c⁻¹ * RCLike.re ⟪y, R v⟫_𝕜 := by rw [hraw]
        _ = RCLike.re ⟪y, R v⟫_𝕜 / c := by
          simp [div_eq_mul_inv, mul_comm]
    rw [htan_i]
    change δ * (σ / c) ≤
      RCLike.re ⟪
        (if σ = 0 then X.toLinearMap v else
          ((((c : ℝ) : 𝕜)⁻¹) •
            (y - ((σ : ℝ) : 𝕜) • X.toLinearMap v))),
        R v⟫_𝕜
    rw [ite_eq_right hσzero, hscale]
    simpa [div_eq_mul_inv, mul_assoc] using
      (div_le_div_iff_of_pos_right hcpos').2 hpair_lower

/-- Ky Fan domination up to the full trial-space dimension. -/
private theorem kyFan_tanTheta0_ritzResidual_le_of_le_finrank
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    {k : ℕ} (hk : k ≤ finrank 𝕜 F) :
    δ * TauCeti.kyFanSum k tanTheta0 ≤
      TauCeti.kyFanSum k
        (ritzResidual A X) := by
  let S := sinThetaEmbedding U X
  let castIndex : Fin k → Fin (finrank 𝕜 F) := fun i => Fin.castLE hk i
  have htrans := isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have huFull := orthonormal_tanThetaResidualWitness U X htrans
  have hu : Orthonormal 𝕜
      (fun i : Fin k => tanThetaResidualWitness U X (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp huFull (castIndex i) (castIndex j))
  have hv : Orthonormal 𝕜
      (fun i : Fin k => rightSingularBasis S (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp (rightSingularBasis S).orthonormal
        (castIndex i) (castIndex j))
  have hsum := TauCeti.sum_le_kyFanSum_of_orthonormal
    hk hu hv (fun i =>
      tanThetaResidualWitness_scalar hA hU X hδ hgap tanTheta0 htan (castIndex i))
  unfold TauCeti.kyFanSum
  rw [Finset.mul_sum]
  exact hsum

/-- **The source Ky Fan root for the finite `tan Θ` theorem.**

For every prefix length, the sum of the first principal tangents is bounded by
the corresponding singular-value prefix of the Ritz residual.  The proof is
the finite version of Davis--Kahan equation (6.6): choose singular vectors of
the directed sine block, construct the complementary cosine vectors, derive
the scalar gap inequalities, sum, and invoke the rectangular Ky Fan
variational principle.

The operator `tanTheta0` is intentionally arbitrary, as in the paper; only its
singular values are prescribed.  This theorem is the single hard
geometric/majorization seam. -/
theorem kyFan_tanTheta0_ritzResidual_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (_hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) (k : ℕ) :
    δ * TauCeti.kyFanSum k tanTheta0 ≤
      TauCeti.kyFanSum k
        (ritzResidual A X) := by
  by_cases hk : k ≤ finrank 𝕜 F
  · exact kyFan_tanTheta0_ritzResidual_le_of_le_finrank hA hU X hδ hgap
      tanTheta0 htan hk
  · have hk' : finrank 𝕜 F ≤ k := Nat.le_of_not_ge hk
    rw [TauCeti.kyFanSum_eq_of_finrank_le hk' tanTheta0,
      TauCeti.kyFanSum_eq_of_finrank_le hk' (ritzResidual A X)]
    exact kyFan_tanTheta0_ritzResidual_le_of_le_finrank hA hU X hδ hgap
      tanTheta0 htan le_rfl

/-- **Paper-exact Davis--Kahan `tan Θ`, residual form, every UI norm.**

This is the first conclusion in the 1970 theorem:

`δ * N (tan Θ₀) ≤ N R`.

As in the paper, `tanTheta0` may be any rectangular operator whose singular
values are the principal tangents.  The spectral assumptions themselves force
transversality. -/
theorem tanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  have hprefix : ∀ k,
      TauCeti.kyFanSum k
          (((δ : ℝ) : 𝕜) • tanTheta0) ≤
        TauCeti.kyFanSum k
          (ritzResidual A X) := by
    intro k
    rw [TauCeti.kyFanSum_real_smul
      k tanTheta0 hδ.le]
    exact kyFan_tanTheta0_ritzResidual_le hA hU X hβα hδ hgap
      tanTheta0 htan k
  have hN := N.apply_le_of_kyFanSum_le hprefix
  rw [N.smul_eq] at hN
  simpa [RCLike.norm_ofReal, abs_of_pos hδ] using hN

/-- **The residual conclusion of the 1970 `tan Θ` theorem.**

This wrapper retains the equal-dimension hypothesis that is part of the global
setup of Sections 1--2 of Davis--Kahan.  The Ritz choice
`compression A X = X⋆ A X` is exactly the paper's condition `H₀ = 0`.
The tangent sequence is directed from the trial space `range X` toward the
exact invariant subspace `U`. -/
theorem davisKahan1970_tanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F = finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- **Davis--Kahan Theorem 6.3, generalized `tan Θ`, residual conclusion.**

This wrapper retains the paper's strict dimension hypothesis: the trial space
has smaller dimension than the exact invariant subspace being approximated.
All other assumptions and the conclusion are identical to the source theorem
in the finite-dimensional setting. -/
theorem davisKahan1970_generalizedTanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F < finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- The exact theorem also records explicitly that no principal tangent has a
pole. -/
theorem tanTheta0_ritzResidual_le_and_isTransverse
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    IsTransverse (approximateSubspace X) U ∧
      δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact ⟨isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap,
    tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan⟩

end DavisKahan.FiniteDimensional
end TauCeti
