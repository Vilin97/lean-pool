/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.UnboundedCentralBand
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.UnboundedDirectedGapBound

/-!
# The moving band is Lipschitz in the perturbation, with no Riesz projector

Step (c) of the unbounded Theorem 8.2 path.  Two self-adjoint partial maps
differing by a bounded `K`, each with real spectrum in `[l, r] ∪ exterior`, have
band subspaces at projection distance at most `‖K‖ / d`.

The estimate is the unbounded `sin Θ` theorem read at the operator norm
(`directedGap_le_of_reducingGap_unbounded_complex`), applied once in each
orientation and combined by `projectionGap_eq_max_directedProjectionGap`.  The
separation it consumes is `formBoundedSylvesterGap_band_exterior`.

This is what replaces the bounded proof's Riesz-projection continuity: no
contour, no continuation API, and the constant depends only on the gap.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open DavisKahan.Sylvester

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The band subspace of a self-adjoint partial map: the spectral range of the
closed interval `[l, r]`. -/
def bandSubspace {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (l r : ℝ) :
    Submodule ℂ H :=
  TauCeti.LinearPMap.specRange hA (Set.Icc l r) measurableSet_Icc

/-- The band subspace is a spectral range, hence orthogonally complemented. -/
instance bandSubspace_hasOrthogonalProjection {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (l r : ℝ) : (bandSubspace hA l r).HasOrthogonalProjection :=
  TauCeti.LinearPMap.instHasOrthogonalProjection_specRange hA _ _

/-- The band subspace reduces the operator. -/
theorem reducesSubspace_bandSubspace {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (l r : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace A (bandSubspace hA l r) :=
  TauCeti.LinearPMap.reducesSubspace_specRange hA _ _

/-- **The directed half of the Lipschitz estimate.**

`d · directedGap (band of A) (band of A + K) ≤ ‖K‖`, from the unbounded `sin Θ`
theorem at the operator norm. -/
theorem directedGap_bandSubspace_le
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (K : H →L[ℂ] H) (hK : K.IsSymmetric)
    (hAB : B = TauCeti.LinearPMap.addBounded A K)
    {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (_hAspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ bandExterior l r d)
    (hBspec : TauCeti.LinearPMap.realSpectrum B ⊆
      Set.Icc l r ∪ bandExterior l r d) :
    d * Submodule.directedProjectionGap (bandSubspace hA l r) (bandSubspace hB l r) ≤ ‖K‖ := by
  subst hAB
  have hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A K)
      (bandSubspace hB l r) := reducesSubspace_bandSubspace hB l r
  have hperp : (bandSubspace hB l r)ᗮ =
      TauCeti.LinearPMap.specRange hB (bandExterior l r d)
        (measurableSet_bandExterior l r d) :=
    (specRange_bandExterior_eq_orthogonal hB hlr hd hBspec).symm
  have hgap := formBoundedSylvesterGap_band_exterior (A := A)
    (B := TauCeti.LinearPMap.addBounded A K) hA hB hlr
    (W := bandSubspace hA l r) (W' := (bandSubspace hB l r)ᗮ)
    rfl hperp (reducesSubspace_bandSubspace hA l r) hQred.orthogonal
  exact TauCeti.DavisKahan1970.Section8.directedGap_le_of_reducingGap_unbounded_complex
    hA K hK (reducesSubspace_bandSubspace hA l r) hQred hd hgap

/-- **The moving band is Lipschitz in the perturbation.**

`d · ‖P_{band A} − P_{band B}‖ ≤ ‖K‖` when `B = A + K`.  The two directed
estimates come from the unbounded `sin Θ` theorem in each orientation; the
reverse one is the same theorem applied to `A = B + (−K)`. -/
theorem subspaceGap_bandSubspace_le
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (K : H →L[ℂ] H) (hK : K.IsSymmetric)
    (hAB : B = TauCeti.LinearPMap.addBounded A K)
    {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hAspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ bandExterior l r d)
    (hBspec : TauCeti.LinearPMap.realSpectrum B ⊆
      Set.Icc l r ∪ bandExterior l r d) :
    d * Submodule.projectionGap (bandSubspace hA l r) (bandSubspace hB l r) ≤ ‖K‖ := by
  have hnegK : (-K).IsSymmetric := by
    intro x y
    have h : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    change ⟪-(K x), y⟫_ℂ = ⟪x, -(K y)⟫_ℂ
    rw [inner_neg_left, inner_neg_right, h]
  have hBA : A = TauCeti.LinearPMap.addBounded B (-K) := by
    rw [hAB]
    exact (TauCeti.LinearPMap.addBounded_neg_cancel A K).symm
  have h1 := directedGap_bandSubspace_le hA hB K hK hAB hlr hd hAspec hBspec
  have h2 := directedGap_bandSubspace_le hB hA (-K) hnegK hBA hlr hd hBspec hAspec
  rw [norm_neg] at h2
  have hmax := Submodule.projectionGap_eq_max_directedProjectionGap
    (bandSubspace hA l r) (bandSubspace hB l r)
  change d * (bandSubspace hA l r).projectionGap (bandSubspace hB l r) ≤ ‖K‖
  rw [hmax]
  rcases max_cases ((bandSubspace hA l r).directedProjectionGap (bandSubspace hB l r))
    ((bandSubspace hB l r).directedProjectionGap (bandSubspace hA l r)) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he]; exact h1
  · rw [he]; exact h2

/-! ## The directed gap to a fixed subspace is 1-Lipschitz in the moving one -/

omit [CompleteSpace H] in
/-- **Moving one subspace moves the directed gap by no more.**

`|directedGap U W − directedGap V W| ≤ subspaceGap U V`, because both are the
norm of the same contraction composed with the moving projection.  This is what
turns the band's Lipschitz estimate into continuity of the quantity the
bootstrap tracks. -/
theorem abs_directedGap_sub_directedGap_le
    (U V W : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] :
    |U.directedProjectionGap W - V.directedProjectionGap W| ≤
      U.projectionGap V := by
  have hX : ‖(Wᗮ.starProjection : H →L[ℂ] H)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa using Wᗮ.norm_starProjection_apply_le y
  have hsub : ‖Wᗮ.starProjection ∘L U.starProjection‖ -
      ‖Wᗮ.starProjection ∘L V.starProjection‖ ≤
      ‖U.starProjection - V.starProjection‖ := by
    have h1 : ‖Wᗮ.starProjection ∘L U.starProjection‖ -
        ‖Wᗮ.starProjection ∘L V.starProjection‖ ≤
        ‖Wᗮ.starProjection ∘L U.starProjection -
          Wᗮ.starProjection ∘L V.starProjection‖ := by
      have := norm_sub_norm_le (Wᗮ.starProjection ∘L U.starProjection)
        (Wᗮ.starProjection ∘L V.starProjection)
      linarith
    have h2 : Wᗮ.starProjection ∘L U.starProjection -
        Wᗮ.starProjection ∘L V.starProjection
        = Wᗮ.starProjection ∘L (U.starProjection - V.starProjection) := by
      ext y
      simp
    rw [h2] at h1
    refine h1.trans ?_
    calc ‖Wᗮ.starProjection ∘L (U.starProjection - V.starProjection)‖
        ≤ ‖(Wᗮ.starProjection : H →L[ℂ] H)‖ * ‖U.starProjection - V.starProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖U.starProjection - V.starProjection‖ := by
          refine mul_le_mul_of_nonneg_right hX (norm_nonneg _)
      _ = ‖U.starProjection - V.starProjection‖ := one_mul _
  have hsub' : ‖Wᗮ.starProjection ∘L V.starProjection‖ -
      ‖Wᗮ.starProjection ∘L U.starProjection‖ ≤
      ‖V.starProjection - U.starProjection‖ := by
    have h1 : ‖Wᗮ.starProjection ∘L V.starProjection‖ -
        ‖Wᗮ.starProjection ∘L U.starProjection‖ ≤
        ‖Wᗮ.starProjection ∘L V.starProjection -
          Wᗮ.starProjection ∘L U.starProjection‖ := by
      have := norm_sub_norm_le (Wᗮ.starProjection ∘L V.starProjection)
        (Wᗮ.starProjection ∘L U.starProjection)
      linarith
    have h2 : Wᗮ.starProjection ∘L V.starProjection -
        Wᗮ.starProjection ∘L U.starProjection
        = Wᗮ.starProjection ∘L (V.starProjection - U.starProjection) := by
      ext y
      simp
    rw [h2] at h1
    refine h1.trans ?_
    calc ‖Wᗮ.starProjection ∘L (V.starProjection - U.starProjection)‖
        ≤ ‖(Wᗮ.starProjection : H →L[ℂ] H)‖ * ‖V.starProjection - U.starProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖V.starProjection - U.starProjection‖ := by
          refine mul_le_mul_of_nonneg_right hX (norm_nonneg _)
      _ = ‖V.starProjection - U.starProjection‖ := one_mul _
  have hsymm : ‖V.starProjection - U.starProjection‖ =
      ‖U.starProjection - V.starProjection‖ := by
    rw [show V.starProjection - U.starProjection =
      -(U.starProjection - V.starProjection) by abel, norm_neg]
  rw [hsymm] at hsub'
  change |‖Wᗮ.starProjection ∘L U.starProjection‖ -
    ‖Wᗮ.starProjection ∘L V.starProjection‖| ≤ ‖U.starProjection - V.starProjection‖
  rw [abs_sub_le_iff]
  exact ⟨hsub, by linarith [hsub']⟩

/-! ## The endpoints, from the `sin Θ` estimate at zero perturbation

The two endpoint inclusions the bootstrap needs are the *same* estimate with
`K = 0`.  Two reducing subspaces of one self-adjoint partial map, one carrying
band spectrum and the other's complement carrying exterior spectrum, are already
a `FormBoundedSylvesterGap` configuration, so the directed gap between them is at
most `‖0‖ / d`, hence zero.

This is why the commutation of `specProjection` with the projection onto a
reducing subspace -- which an earlier plan named as the missing prerequisite --
is not needed: the uniqueness of the spectral splitting is delivered by the
`sin Θ` theorem itself. -/

omit [CompleteSpace H] in
/-- Adding the zero perturbation changes nothing. -/
theorem addBounded_zero (A : H →ₗ.[ℂ] H) :
    TauCeti.LinearPMap.addBounded A (0 : H →L[ℂ] H) = A := by
  refine LinearPMap.ext rfl ?_
  intro x y hxy
  simp only [TauCeti.LinearPMap.addBounded_apply, zero_apply, add_zero]
  rfl

omit [CompleteSpace H] in
/-- A vanishing directed gap is a subspace inclusion. -/
theorem le_of_directedGap_eq_zero (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U.directedProjectionGap V = 0) : U ≤ V := by
  intro u hu
  have h0 : Vᗮ.starProjection ((U.starProjection) u) = 0 := by
    have hle : ‖(Vᗮ.starProjection ∘L U.starProjection) u‖ ≤
        ‖Vᗮ.starProjection ∘L U.starProjection‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hz : ‖Vᗮ.starProjection ∘L U.starProjection‖ = 0 := h
    rw [hz, zero_mul] at hle
    simpa using norm_le_zero_iff.mp hle
  rw [Submodule.starProjection_eq_self_iff.mpr hu] at h0
  rw [Submodule.starProjection_orthogonal_apply, sub_eq_zero] at h0
  exact h0 ▸ V.starProjection_apply_mem u

/-- **Band spectrum and exterior spectrum on one operator force an inclusion.**

`P` reduces `A` with band spectrum, `W` reduces `A` with exterior spectrum on its
complement; then `P ≤ W`.  The proof is the unbounded `sin Θ` theorem at zero
perturbation.

`B` and `hAB` are the standard device for feeding `A` to a theorem stated about
`addBounded A K`: a caller passes `B := A` and `(addBounded_zero A).symm`, and
`subst` puts the goal in the shape the estimate consumes. -/
theorem le_of_band_exterior_spectra
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hAB : B = TauCeti.LinearPMap.addBounded A (0 : H →L[ℂ] H))
    {P W : Submodule ℂ H} [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hWred : TauCeti.LinearPMap.ReducesSubspace B W)
    {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred) ⊆ Set.Icc l r)
    (hWspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction B Wᗮ hWred.orthogonal)
      ⊆ bandExterior l r d) :
    P ≤ W := by
  subst hAB
  have hzero : (0 : H →L[ℂ] H).IsSymmetric := by
    intro x y
    simp
  have hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A (0 : H →L[ℂ] H)) Wᗮ hWred.orthogonal) d :=
    .intervalExterior hlr (Or.inl ⟨hPspec, hWspec⟩)
  have hle := TauCeti.DavisKahan1970.Section8.directedGap_le_of_reducingGap_unbounded_complex
    hA (0 : H →L[ℂ] H) hzero hPred hWred hd hgap
  rw [norm_zero] at hle
  have hnn : (0 : ℝ) ≤ P.directedProjectionGap W :=
    norm_nonneg (Wᗮ.starProjection ∘L P.starProjection)
  refine le_of_directedGap_eq_zero P W (le_antisymm ?_ hnn)
  nlinarith [hle, hd, hnn]

end

end DavisKahan
end TauCeti
