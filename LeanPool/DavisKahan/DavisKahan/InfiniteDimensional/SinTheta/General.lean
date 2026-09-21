/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Restriction
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.SpectralBridge
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.GramContraction
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # General -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Infinite-dimensional `sin Θ` theorems

Literature writeup: local TeX, Sections 12--13.  Both residual and perturbation
forms are represented, including general separated spectra and ideal-norm
versions.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open DavisKahan
universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- A submodule with an orthogonal projection is closed in the complete
ambient space, hence complete: it is the equalizer of the projection and the
identity. -/
private theorem completeSpace_of_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U := by
  have hclosed : IsClosed (U : Set E) := by
    have heq : (U : Set E) = {x : E | U.starProjection x = x} := by
      ext x
      exact ⟨fun hx => Submodule.starProjection_eq_self_iff.mpr hx,
        fun hx => Submodule.starProjection_eq_self_iff.mp hx⟩
    rw [heq]
    exact isClosed_eq U.starProjection.continuous continuous_id
  exact hclosed.completeSpace_coe

/-- The real spectrum of a bounded operator is bounded by its norm.

Used below in place of compactness of the spectrum: the cut construction needs
only `BddAbove` / `BddBelow`, and those follow from `‖λ‖ ≤ ‖T‖` for `λ` in the
spectrum without any of the topology. -/
private theorem abs_le_norm_of_mem_realSpectrum {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] {T : G →L[𝕜] G} {r : ℝ}
    (hr : r ∈ TauCeti.DavisKahan.Foundation.realSpectrum T) :
    |r| ≤ ‖T‖ * ‖(1 : G →L[𝕜] G)‖ := by
  -- `norm_le_norm_of_mem` would give the cleaner `‖T‖`, but it wants
  -- `NormOneClass (G →L[𝕜] G)`, which fails when `G` is trivial.
  have h : ‖((r : 𝕜))‖ ≤ ‖T‖ * ‖(1 : G →L[𝕜] G)‖ := spectrum.norm_le_norm_mul_of_mem hr
  rwa [RCLike.norm_ofReal] at h

/-- **A common cut between two ordered spectra**, over a general `RCLike` field.

This is `exists_common_cut_of_orderedSeparation` (`Sylvester/OrderedSemigroup`)
with `ℂ` relaxed to `𝕜`.  Nothing in the argument was complex: the cut is
`sSup (realSpectrum B)` when that spectrum is nonempty and
`sInf (realSpectrum A) - d` when it is not, and the boundedness it needs is the
norm bound above rather than compactness of the spectrum. -/
private theorem exists_common_cut_of_orderedSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {d : ℝ}
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      TauCeti.DavisKahan.Foundation.realSpectrum B ⊆ Set.Iic c ∧
      TauCeti.DavisKahan.Foundation.realSpectrum A ⊆ Set.Ici (c + d) := by
  obtain ⟨hInvB, hInvA, hord⟩ := hsep
  have hkey : ∀ b ∈ TauCeti.DavisKahan.Foundation.realSpectrum B,
      ∀ a ∈ TauCeti.DavisKahan.Foundation.realSpectrum A, b + d ≤ a := by
    intro b hb a ha
    refine hord b ?_ a ?_
    · rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top]; exact hb
    · rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top]; exact ha
  rcases (TauCeti.DavisKahan.Foundation.realSpectrum B).eq_empty_or_nonempty
    with hB0 | hBne
  · rcases (TauCeti.DavisKahan.Foundation.realSpectrum A).eq_empty_or_nonempty
      with hA0 | hAne
    · exact ⟨0, by simp [hB0], by simp [hA0]⟩
    · refine ⟨sInf (TauCeti.DavisKahan.Foundation.realSpectrum A) - d,
        by simp [hB0], fun a ha => ?_⟩
      have hbdd : BddBelow (TauCeti.DavisKahan.Foundation.realSpectrum A) :=
        ⟨-(‖A‖ * ‖(1 : F →L[𝕜] F)‖), fun r hr =>
          neg_le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)⟩
      have := csInf_le hbdd ha
      simp only [Set.mem_Ici]
      linarith
  · refine ⟨sSup (TauCeti.DavisKahan.Foundation.realSpectrum B),
      fun b hb => ?_, fun a ha => ?_⟩
    · exact le_csSup ⟨‖B‖ * ‖(1 : E →L[𝕜] E)‖, fun r hr =>
        le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)⟩ hb
    · have hsup : sSup (TauCeti.DavisKahan.Foundation.realSpectrum B) ≤ a - d :=
        csSup_le hBne fun b hb => by linarith [hkey b hb a ha]
      simp only [Set.mem_Ici]
      linarith

/-- **The constant-one ordered Sylvester estimate over a general `RCLike`
field.**

This was a leaf obligation until 2026-07-30, on the stated grounds that the `ℂ`
case is `norm_sylvester_le_of_orderedSeparation` and "the general case is its
complexification transport".  **No transport is needed and none is done here.**
`ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap` is already
proved over general `RCLike`, for every rectangular ideal family, with constant
one; `sinTheta_perturbation` below instantiates it at `operatorNormFamily` in
exactly the same way.

The only real step is the shape change.  Ordered separation says one spectrum
sits below the other, which gives a *cut*; the bridge wants an
*interval/exterior* pair.  Putting `B` in `Icc β c` for the cut `c` and any
`β` below both `-‖B‖` and `c` leaves `A` in the exterior `{x | c + d ≤ x}`, which
is what ordered separation already gives. -/
theorem norm_sylvester_le_of_orderedSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  obtain ⟨c, hBc, hAc⟩ := exists_common_cut_of_orderedSeparation_rclike hsep
  set β : ℝ := min (-(‖B‖ * ‖(1 : E →L[𝕜] E)‖) - 1) (c - 1) with hβ
  have hβc : β ≤ c := (min_le_right _ _).trans (by linarith)
  have hgap : ExactSinTheta.IntervalExteriorGap A B β c d := by
    refine Or.inr ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [boundedRealSpectrum_eq_realSpectrum] at hr
      have hup : r ≤ c := hBc hr
      have hlow : -(‖B‖ * ‖(1 : E →L[𝕜] E)‖) ≤ r :=
        neg_le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)
      exact ⟨le_trans (min_le_left _ _) (by linarith), hup⟩
    · rw [boundedRealSpectrum_eq_realSpectrum] at hr
      exact Or.inr (hAc hr)
  have hsolve := ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (TauCeti.operatorNormFamily.{u, v} 𝕜) hA hB hβc hd hgap hEq
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily _)
  exact hsolve.2

open TauCeti.RealComplexification in
open scoped TauCeti.DavisKahan.Foundation.RealScalarRestriction in
/-- **The universal `π/2` Sylvester estimate over a general `RCLike` field.**

Proved by restricting scalars to `ℝ` and complexifying, which is the route the
leaf obligation this replaced described as "its complexification transport". -/
theorem norm_sylvester_le_of_generalSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  have hEqr : (A.restrictScalars ℝ) ∘L (X.restrictScalars ℝ)
      - (X.restrictScalars ℝ) ∘L (B.restrictScalars ℝ) = C.restrictScalars ℝ := by
    ext x
    have := congrArg (fun T : E →L[𝕜] F => T x) hEq
    simpa [ContinuousLinearMap.sylvesterOperator] using this
  have hEqc : ContinuousLinearMap.sylvesterOperator (complexify (A.restrictScalars ℝ))
      (complexify (B.restrictScalars ℝ)) (complexify (X.restrictScalars ℝ)) =
      complexify (C.restrictScalars ℝ) := by
    show complexify (A.restrictScalars ℝ) ∘L complexify (X.restrictScalars ℝ)
      - complexify (X.restrictScalars ℝ) ∘L complexify (B.restrictScalars ℝ) = _
    rw [← complexify_comp, ← complexify_comp, ← complexify_sub, hEqr]
  -- self-adjointness survives both steps: restricting scalars takes the real part
  -- of the form, and `complexify_adjoint` moves the adjoint through the second.
  have hsymr : ∀ (G : Type v) (_ : NormedAddCommGroup G) (_ : InnerProductSpace 𝕜 G),
      True := fun _ _ _ => trivial
  have hAr : (A.restrictScalars ℝ).IsSymmetric := fun x y => by
    simpa [real_inner_eq_re_inner (𝕜 := 𝕜)] using congrArg RCLike.re (hA x y)
  have hBr : (B.restrictScalars ℝ).IsSymmetric := fun x y => by
    simpa [real_inner_eq_re_inner (𝕜 := 𝕜)] using congrArg RCLike.re (hB x y)
  have hAc : (complexify (A.restrictScalars ℝ)).IsSymmetric := by
    have hsa : IsSelfAdjoint (complexify (A.restrictScalars ℝ)) := by
      show ContinuousLinearMap.adjoint _ = _
      rw [← TauCeti.RealComplexification.complexify_adjoint]
      exact congrArg complexify
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hAr)
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa
  have hBc : (complexify (B.restrictScalars ℝ)).IsSymmetric := by
    have hsa : IsSelfAdjoint (complexify (B.restrictScalars ℝ)) := by
      show ContinuousLinearMap.adjoint _ = _
      rw [← TauCeti.RealComplexification.complexify_adjoint]
      exact congrArg complexify
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hBr)
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa
  -- the separation survives both steps: `realSpectrum` is what a `⊤`-separation
  -- hypothesis is about, it is the `ℝ`-spectrum after restricting scalars, and it
  -- is unchanged by complexification.
  have hreal : ∀ (G : Type v) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
      [CompleteSpace G] (T : G →L[𝕜] G),
      Foundation.realSpectrum (complexify (T.restrictScalars ℝ)) =
        Foundation.realSpectrum T := by
    intro G _ _ _ T
    rw [TauCeti.DavisKahan.Foundation.RealComplexification.realSpectrum_complexify (T.restrictScalars ℝ),
      Foundation.realSpectrum_eq_spectrum_restrictScalars T]
    rfl
  have hsepc : SpectraSeparated (complexify (A.restrictScalars ℝ)) ⊤
      (complexify (B.restrictScalars ℝ)) ⊤ d := by
    show Foundation.SpectraSeparated _ ⊤ _ ⊤ d
    rw [Foundation.spectraSeparated_top_iff]
    intro a ha b hb
    rw [hreal F A] at ha
    rw [hreal E B] at hb
    exact (Foundation.spectraSeparated_top_iff A B d).1 hsep a ha b hb
  have hmain := norm_sylvester_le_of_generalSeparation hAc hBc hd hsepc hEqc
  rwa [TauCeti.RealComplexification.norm_complexify,
    TauCeti.RealComplexification.norm_complexify,
    ContinuousLinearMap.norm_restrictScalars,
    ContinuousLinearMap.norm_restrictScalars] at hmain

/-- Residual `sin Θ` theorem for an isometric trial map.

Lean proof route for a weaker agent:

1. Set `Y=(I-P_U)X` and derive `A|_{Uᗮ} Y - Y M = (I-P_U) residual A X M`.
2. Apply the ordered constant-one Sylvester theorem using `hsep`.
3. Bound the projected residual by the full residual norm.
4. Identify `Y` with `sinThetaEmbedding U X`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed residual theorem. The
isometric embedding is needed for the subspace interpretation, although the raw
Sylvester norm estimate itself uses only boundedness.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_residual
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {X : F →L[𝕜] E} (_hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : M.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated M ⊤ A Uᗮ d) :
    d * ‖sinThetaEmbedding U X‖ ≤ ‖residual A X M‖ := by
  let Y : F →L[𝕜] Uᗮ :=
    (((Uᗮ).starProjection ∘L X)).codRestrict Uᗮ (fun x => Uᗮ.starProjection_apply_mem _)
  let C : F →L[𝕜] Uᗮ :=
    (((Uᗮ).starProjection ∘L residual A X M)).codRestrict Uᗮ
      (fun x => Uᗮ.starProjection_apply_mem _)
  have hEq : ContinuousLinearMap.sylvesterOperator (A.restrict hU.2) M Y = C :=
    directedResidual_sylvesterEquation hA hU
  have hsep' : OrderedSpectraSeparated M ⊤
      (A.restrict hU.2) ⊤ d := by
    obtain ⟨hM, hAperp, hord⟩ := hsep
    refine ⟨hM, fun x _ => Submodule.mem_top, ?_⟩
    intro a ha b hb
    refine hord a ha b ?_
    have hb' : b ∈ TauCeti.DavisKahan.Foundation.realSpectrum
        (A.restrict hU.2) :=
      (TauCeti.DavisKahan.Foundation.restrictedSpectrum_top
        (A.restrict hU.2)) ▸ hb
    have h2 : TauCeti.DavisKahan.Foundation.restrictedSpectrum
          A Uᗮ =
        TauCeti.DavisKahan.Foundation.realSpectrum
          (A.restrict hU.2) :=
      TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A Uᗮ hU.2
    rw [h2]
    exact hb'
  have hbound := norm_sylvester_le_of_orderedSeparation_rclike
    (LinearMap.IsSymmetric.restrict_invariant hA hU.2) hM hd hsep' hEq
  have hY : ‖Y‖ = ‖sinThetaEmbedding U X‖ :=
    ContinuousLinearMap.opNorm_codRestrict_eq _ _ _
  have hC : ‖C‖ ≤ ‖residual A X M‖ := by
    calc
      ‖C‖ = ‖(Uᗮ).starProjection ∘L residual A X M‖ :=
        ContinuousLinearMap.opNorm_codRestrict_eq _ _ _
      _ ≤ ‖residual A X M‖ :=
        projection_comp_opNorm_le Uᗮ _
  simpa [hY] using hbound.trans hC

/-- One-sided perturbation theorem for spectral subspaces.

Lean proof route for a weaker agent:

1. Derive the off-diagonal Sylvester equation for `X=(I-P_V)P_U`.
2. Use the interval/exterior decomposition to apply the constant-one ordered Sylvester estimate to the lower and upper pieces.
3. Bound the right-hand residual by `‖B-A‖`.
4. Rewrite `‖X‖` as the directed gap.


Ext-agent signature audit (GPT 5.6 High): Correct as a one-sided directed-angle theorem.
One mixed interval/exterior gap is intentionally insufficient for a full
projector-difference conclusion.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {left right d : ℝ} (hlr : left ≤ right) (hd : 0 < d)
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    d * U.directedProjectionGap V ≤ ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    (((Vᗮ).starProjection ∘L U.subtypeL)).codRestrict Vᗮ (fun x => Vᗮ.starProjection_apply_mem _)
  let C : U →L[𝕜] Vᗮ :=
    (((Vᗮ).starProjection ∘L (B - A) ∘L U.subtypeL)).codRestrict Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hgap' : ExactSinTheta.IntervalExteriorGap
      (B.restrict hV.2) (A.restrict hU.1)
      left right d := by
    exact intervalExteriorSeparated_restrictions hA hB hU hV hgap
  have : CompleteSpace U := completeSpace_of_hasOrthogonalProjection U
  have : CompleteSpace Vᗮ := completeSpace_of_hasOrthogonalProjection Vᗮ
  have hsolve := ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (TauCeti.operatorNormFamily.{u, v} 𝕜)
    (LinearMap.IsSymmetric.restrict_invariant hB hV.2)
    (LinearMap.IsSymmetric.restrict_invariant hA hU.1)
    hlr hd hgap' hEq
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily _)
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  have h2 : d * ‖((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
    (fun x => Vᗮ.starProjection_apply_mem _)‖ ≤ ‖B - A‖ :=
    hsolve.2.trans hC
  rw [directedGap_eq_restrictedBlock_norm U V] at h2
  exact h2

/-- Symmetric projector-difference form requiring both mixed gaps.

Lean proof route for a weaker agent:

1. Apply `sinTheta_perturbation` to `(U,V)` and again to `(V,U)` using the reverse gap.
2. Use the two-projection norm identity that the full gap is the maximum of the two directed gaps.
3. Combine the two inequalities with `max_le` and simplify the perturbation sign.


Ext-agent signature audit (GPT 5.6 High): Correct with both mixed gaps. The full
projection gap is the maximum of the two directed gaps in operator norm.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_symmetric
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    d * U.projectionGap V ≤ ‖B - A‖ := by
  have h1 : d * U.directedProjectionGap V ≤ ‖B - A‖ :=
    sinTheta_perturbation hA hB hU hV hlr hd hUV
  have h2 : d * V.directedProjectionGap U ≤ ‖A - B‖ :=
    sinTheta_perturbation hB hA hV hU hlr' hd hVU
  rw [show A - B = -(B - A) by abel, norm_neg] at h2
  have hmax : U.projectionGap V = max (U.directedProjectionGap V) (V.directedProjectionGap U) := by
    show ‖U.starProjection - V.starProjection‖ =
      max ‖Vᗮ.starProjection ∘L U.starProjection‖
        ‖Uᗮ.starProjection ∘L V.starProjection‖
    rw [Submodule.norm_starProjection_sub_eq_max,
      Submodule.starProjection_orthogonal' V,
      Submodule.starProjection_orthogonal' U]
  rw [hmax, mul_max_of_nonneg _ _ hd.le]
  exact max_le h1 h2

/-- General separated-spectrum form with the optimal universal `π / 2`
Sylvester constant.

Lean proof route for a weaker agent:

1. Derive the Sylvester equation for `(I-P_V)P_U` from the two reducing relations.
2. Apply `norm_sylvester_le_of_generalSeparation` with the hybrid spectral gap.
3. Bound the residual block by `‖B-A‖` using projection contractions.
4. Rewrite the block norm as `directedGap U V`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed theorem with the `π/2`
constant. The hybrid gap matches the cross block `P_{Vᗮ}P_U`.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {d : ℝ} (hd : 0 < d) (hgap : HybridGap A B U V d) :
    d * U.directedProjectionGap V ≤ (Real.pi / 2) * ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    (((Vᗮ).starProjection ∘L U.subtypeL)).codRestrict Vᗮ (fun x => Vᗮ.starProjection_apply_mem _)
  let C : U →L[𝕜] Vᗮ :=
    (((Vᗮ).starProjection ∘L (B - A) ∘L U.subtypeL)).codRestrict Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hsep : SpectraSeparated (B.restrict hV.2) ⊤
      (A.restrict hU.1) ⊤ d :=
    hybridGap_restrictions hA hB hU hV hgap
  have : CompleteSpace U := completeSpace_of_hasOrthogonalProjection U
  have : CompleteSpace Vᗮ := completeSpace_of_hasOrthogonalProjection Vᗮ
  have hsol := norm_sylvester_le_of_generalSeparation_rclike
    (LinearMap.IsSymmetric.restrict_invariant hB hV.2)
    (LinearMap.IsSymmetric.restrict_invariant hA hU.1) hd hsep hEq
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  have h2 : d * ‖((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
    (fun x => Vᗮ.starProjection_apply_mem _)‖ ≤
      (Real.pi / 2) * ‖B - A‖ :=
    hsol.trans (mul_le_mul_of_nonneg_left hC (by positivity))
  rw [directedGap_eq_restrictedBlock_norm U V] at h2
  exact h2

/-! ## Bounded measurable spectral subspaces

Actually constructing the measurable spectral subspace of a bounded
self-adjoint operator over a general `RCLike` field requires the bounded Borel
functional calculus.  Over `ℂ` that calculus exists in this development and is
*not* experimental: it is `TauCeti.BorelCalculus.boundedPVM`, with the spectral
subspace itself at
`DavisKahan/SpectralTheory/BoundedSelfAdjointSpectralProjection.lean` as
`boundedSelfAdjointSpectralSubspace`.  The general case is its complexification
transport, which does not exist yet.

That `ℂ` construction cannot simply be reused here, because
`TauCeti.ProjValMeasure` fixes the scalar field **in its own binder** — it is
declared over `[InnerProductSpace ℂ H]` — while this section is over a general
`𝕜 : RCLike`.  Reusing it would mean either restricting this section to `ℂ` or
generalising `ProjValMeasure`, and neither is necessary.

The bounded Borel projection assignment is therefore still carried as the explicit
`BoundedBorelProjection` hypothesis below.  This is separate from the bounded operator modulus,
whose continuous functional calculus is now available directly over arbitrary `RCLike` fields.
Relative to `BoundedBorelProjection` the three former leaf obligations are ordinary theorems,
and the `sin Θ` consequences are fully proved.
-/

section SpectralSubspace

/-- **Hypothesis class: the bounded Borel functional calculus of a self-adjoint
operator**, presented as the projection assignment it induces.

Only the two laws actually needed downstream are demanded — idempotence, which
makes the range a closed subspace with an orthogonal projection, and commutation
with the operator, which makes that subspace reducing.  Nothing here asserts
countable additivity or multiplicativity in `s`; a genuine projection-valued
measure supplies this and much more, so the hypothesis is weaker than the object
that discharges it.

At `𝕜 = ℂ` it is discharged by `TauCeti.BorelCalculus.boundedPVM`: `proj_idem`
is its `proj_idem` field, and `proj_comm` is the commutation of a spectral
projection with its own operator.  The instance is deliberately *not* declared
in this file, which would drag the whole Borel-calculus import chain into this
generic `RCLike` module; it lives in `BoundedBorelProjectionComplex.lean`. -/
class BoundedBorelProjection (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The spectral projection of `A` over a Borel set `s`. -/
  proj : ∀ (A : E →L[𝕜] E), A.IsSymmetric →
    ∀ s : Set ℝ, MeasurableSet s → E →L[𝕜] E
  /-- Spectral projections are idempotent. -/
  proj_idem : ∀ (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s), IsIdempotentElem (proj A hA s hs)
  /-- Spectral projections commute with their operator. -/
  proj_comm : ∀ (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s),
    A ∘L proj A hA s hs = proj A hA s hs ∘L A

variable [BoundedBorelProjection 𝕜 E]

/-- The measurable spectral subspace of a bounded operator: the range of the
spectral projection of `s`.

Relative to the `BoundedBorelProjection` hypothesis this is a real definition
rather than a leaf obligation, so the results below unfold it. -/
noncomputable def spectralSubspace (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Submodule 𝕜 E :=
  (BoundedBorelProjection.proj A hA s hs).range

omit [CompleteSpace E] in
/-- Unfolding lemma: the spectral subspace *is* the range of the spectral
projection.  Stated so that downstream rewrites do not have to unfold a `def`. -/
theorem spectralSubspace_eq_range (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    spectralSubspace A hA s hs = (BoundedBorelProjection.proj A hA s hs).range :=
  rfl

/-- The spectral subspace is closed, hence admits an orthogonal projection in
the complete ambient space.

This needs only idempotence: the range of a bounded idempotent is closed. -/
noncomputable instance spectralSubspace_hasOrthogonalProjection
    (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (spectralSubspace A hA s hs).HasOrthogonalProjection :=
  ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (BoundedBorelProjection.proj_idem A hA s hs)

/-- The measurable spectral projection: the orthogonal projection onto the
spectral subspace. -/
noncomputable def spectralProjection (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    E →L[𝕜] E :=
  (spectralSubspace A hA s hs).starProjection

omit [CompleteSpace E] in
/-- Spectral subspaces of a self-adjoint operator reduce it.

Only invariance has to be checked: `IsSymmetric.reduces_of_invariant` supplies
invariance of the orthogonal complement from symmetry of `A`.  Invariance is
immediate from commutation, since `A (P y) = P (A y)` is again in the range. -/
theorem isInvariant_spectralSubspace (A : E →L[𝕜] E)
    (hA : A.IsSymmetric) (s : Set ℝ) (hs : MeasurableSet s) :
    A.Reduces (spectralSubspace A hA s hs) := by
  refine ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA ?_
  rintro x ⟨y, rfl⟩
  refine ⟨A y, ?_⟩
  exact congrFun (congrArg DFunLike.coe
    (BoundedBorelProjection.proj_comm A hA s hs).symm) y

/-- The subspace projection of the spectral subspace is the spectral
projection. -/
theorem projection_spectralSubspace_eq (A : E →L[𝕜] E) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Submodule.starProjection (spectralSubspace A hA s hs) = spectralProjection A hA s hs :=
  rfl

/-- Canonical spectral-projection form.

Lean proof route for a weaker agent:

1. Convert the four spectral-containment hypotheses into the two `IntervalExteriorSeparated` predicates.
2. Apply `sinTheta_symmetric` to the canonical spectral subspaces, using `isInvariant_spectralSubspace`.
3. Rewrite the subspace gap as the norm of the two spectral projections.


Ext-agent signature audit (GPT 5.6 High): Correct after the measurable-set hypotheses
were added. The four containments encode exactly the two mixed interval/exterior gaps.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem spectralProjection_sinTheta
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hAs : SpectrumIn A (spectralSubspace A hA s hs) (Set.Icc left right))
    (hBt : SpectrumIn B (spectralSubspace B hB t ht)ᗮ
      {x | x ≤ left - d ∨ right + d ≤ x})
    (hBs : SpectrumIn B (spectralSubspace B hB t ht) (Set.Icc left' right'))
    (hAt : SpectrumIn A (spectralSubspace A hA s hs)ᗮ
      {x | x ≤ left' - d ∨ right' + d ≤ x}) :
    d * ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖ ≤
      ‖B - A‖ := by
  let U := spectralSubspace A hA s hs
  let V := spectralSubspace B hB t ht
  have hredA := isInvariant_spectralSubspace A hA s hs
  have hredB := isInvariant_spectralSubspace B hB t ht
  have hUV : IntervalExteriorSeparated A U B Vᗮ left right d :=
    ⟨hAs, hBt⟩
  have hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d :=
    ⟨hBs, hAt⟩
  have h := sinTheta_symmetric hA hB hredA hredB hlr hlr' hd hUV hVU
  have hgapeq : U.projectionGap V =
      ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖ := rfl
  calc d * ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖
      = d * U.projectionGap V := by rw [hgapeq]
    _ ≤ ‖B - A‖ := h

end SpectralSubspace

/-! ## Ideal-valued form

The bounded-operator modulus used by the ideal-valued sine theorem is
`ContinuousLinearMap.modulus`.  Its `RCLike` continuous functional calculus and real scalar
structure are internal to `ForTauCeti`; theorem signatures here carry only the Hilbert-space
and completeness assumptions.
-/

section OperatorModulus

/-- The full ambient sine-angle operator of two subspaces: the modulus of the projector
difference. -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (U.starProjection - V.starProjection).modulus

/-- **Symmetric norm ideals contain moduli with equal gauge, given a polar contraction.**

Only the two factorization identities and the operator-norm bounds are needed.  The ideal
axioms give the two gauge inequalities directly. -/
theorem SymmetricNormIdeal.modulus_mem_and_gauge_eq_of_polar
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) {T W : E →L[𝕜] E}
    (hT : I.mem T)
    (hWT : W ∘L T.modulus = T)
    (hWadj : (ContinuousLinearMap.adjoint W) ∘L T = T.modulus)
    (hWnorm : ‖W‖ ≤ 1) (hWadjnorm : ‖ContinuousLinearMap.adjoint W‖ ≤ 1) :
    I.mem T.modulus ∧ I.gauge T.modulus = I.gauge T := by
  have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habs : ContinuousLinearMap.adjoint W ∘L T ∘L ContinuousLinearMap.id 𝕜 E =
      T.modulus := by
    rw [ContinuousLinearMap.comp_id]
    exact hWadj
  have hmem : I.mem T.modulus := by
    have := I.ideal_mem (ContinuousLinearMap.adjoint W) (ContinuousLinearMap.id 𝕜 E) hT
    rwa [habs] at this
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · have hb := I.ideal_bound (ContinuousLinearMap.adjoint W) (ContinuousLinearMap.id 𝕜 E) hT
    rw [habs] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge T := I.nonneg hT
    calc ‖ContinuousLinearMap.adjoint W‖ * I.gauge T * ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge T * 1 := by
          gcongr
      _ = I.gauge T := by ring
  · have hT' : W ∘L T.modulus ∘L ContinuousLinearMap.id 𝕜 E = T := by
      rw [ContinuousLinearMap.comp_id]
      exact hWT
    have hb := I.ideal_bound W (ContinuousLinearMap.id 𝕜 E) hmem
    rw [hT'] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge T.modulus := I.nonneg hmem
    calc ‖W‖ * I.gauge T.modulus * ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge T.modulus * 1 := by
          gcongr
      _ = I.gauge T.modulus := by ring

/-- **Symmetric norm ideals contain moduli with equal gauge.**

The Gram identity for `T.modulus` supplies a contraction polar factor through
`exists_contraction_of_gram_eq`; the ideal estimate then follows from
`modulus_mem_and_gauge_eq_of_polar`. -/
theorem SymmetricNormIdeal.modulus_mem_and_gauge_eq
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) {T : E →L[𝕜] E}
    (hT : I.mem T) :
    I.mem T.modulus ∧ I.gauge T.modulus = I.gauge T := by
  have hgram : T.modulus ∘L T.modulus = ContinuousLinearMap.adjoint T ∘L T := by
    simpa only [ContinuousLinearMap.mul_def] using T.modulus_mul_self
  obtain ⟨W, hWnorm, hWadjnorm, hWT, hWadj⟩ :=
    ContinuousLinearMap.exists_contraction_of_gram_eq T.modulus_isSelfAdjoint hgram
  exact I.modulus_mem_and_gauge_eq_of_polar hT hWT hWadj hWnorm hWadjnorm

/-! ### Reduction of the ideal-valued projector-difference estimate

The leaf below is stated with the sharp constant **one**, and its own earlier
description — "requiring the ideal-valued Sylvester engine on both off-diagonal
blocks" — understates it, because that engine already exists and is proved
(`sylvester_mem_and_gauge_le_of_intervalExteriorGap`, general `RCLike`, constant
one).  The two lemmas below carry out the reduction, so that what is left is one
precisely identified gap rather than a vague campaign.

Write `S = P_U − P_V` and `R = B − A`.  Then:

* `S` satisfies a **Sylvester equation** on the nose,
  `A S − S B = R P_V − P_U R` (`projectionDifference_sylvester`, proved below,
  and needing only that `A` reduces `U` and `B` reduces `V`);
* its right-hand side is a **reflection pinch** of `R`, hence gauge-contractive:
  `R P_V − P_U R = (R J_V − J_U R)/2` with `J = 2P − 1` the reflections, so
  `gauge (R P_V − P_U R) ≤ gauge R`
  (`gauge_projectionCross_le`, proved below).

**What is still missing, precisely.**  `S` is purely off-diagonal for the block
structure `(U ⊕ Uᗮ, V ⊕ Vᗮ)`: its `(U,V)` and `(Uᗮ,Vᗮ)` blocks vanish.  The
hypotheses separate exactly the two *surviving* corners — `spec(A|U)` from
`spec(B|Vᗮ)`, and `spec(A|Uᗮ)` from `spec(B|V)` — and say nothing about the other
two, which is correct because `S` is zero there.  But the Sylvester engine is a
statement about the *global* spectra of `A` and `B`, and those are not separated.
Shifting by `κ P_Uᗮ` and `κ P_V` leaves the equation invariant (precisely because
`S`'s `(U,V)` block vanishes) and can align the two interval centres, but it
cannot make all four corner pairs separated at once.

Applying the engine to each corner separately and adding gives constant **2**,
which is what `Sylvester/Spectrum.lean`'s `sinTheta_spectrum_gauge_symmetric`
already proves.  Constant one needs the Schur-multiplier form of the estimate on
the *union of two* interval/exterior rectangles — i.e. a kernel representation of
`(a − b)⁻¹` of total mass `1/d` valid on that union — and that is the missing
piece.  The statement itself is believed true and sharp: equality holds at
`B − A = d (P_U − P_V)`.
-/

omit [CompleteSpace E] in
/-- **The projector difference solves a Sylvester equation.**

With `A` reducing `U` and `B` reducing `V`,
`A (P_U − P_V) − (P_U − P_V) B = (B − A) P_V − P_U (B − A)`.

Pure algebra: the two reducing hypotheses let `A` and `P_U` swap, and `B` and
`P_V` swap, after which everything cancels. -/
theorem projectionDifference_sylvester
    {A B : E →L[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V) :
    A ∘L (U.starProjection - V.starProjection) - (U.starProjection - V.starProjection) ∘L B =
      (B - A) ∘L V.starProjection - U.starProjection ∘L (B - A) := by
  have hAU : A ∘L U.starProjection = U.starProjection ∘L A :=
    (ContinuousLinearMap.starProjection_comp_comm_of_reduces A U hU).symm
  have hBV : V.starProjection ∘L B = B ∘L V.starProjection :=
    ContinuousLinearMap.starProjection_comp_comm_of_reduces B V hV
  simp only [← ContinuousLinearMap.mul_def] at hAU hBV ⊢
  rw [mul_sub, sub_mul, sub_mul, mul_sub, hAU, hBV]
  abel

omit [CompleteSpace E] in
/-- **The cross term is a reflection pinch**: `R P_V − P_U R = (R J_V − J_U R)/2`.

Immediate from `J = 2P − 1`, but worth naming: it is what makes the right-hand
side of `projectionDifference_sylvester` gauge-contractive in `R`. -/
theorem projectionCross_eq_reflectionPinch
    (R : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    R ∘L V.starProjection - U.starProjection ∘L R =
      ((2 : 𝕜)⁻¹) • (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) := by
  have hU : (U.reflectionOperator : E →L[𝕜] E) =
      (2 : 𝕜) • U.starProjection - ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_eq_two_smul_sub_id U
  have hV : (V.reflectionOperator : E →L[𝕜] E) =
      (2 : 𝕜) • V.starProjection - ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_eq_two_smul_sub_id V
  rw [hU, hV]
  ext x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.coe_id', id_eq, map_sub, map_smul]
  match_scalars <;> (try field_simp) ; ring

/-- **The cross term is gauge-contractive**: `gauge (R P_V − P_U R) ≤ gauge R`.

The two-subspace analogue of `gauge_offDiagonalPart_le`, which pinches against a
single reflection.  Both one-sided factors are reflections, so each has operator
norm at most one and the ideal bound applies on either side; the triangle
inequality and the factor `1/2` then give constant one. -/
theorem SymmetricNormIdeal.gauge_projectionCross_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {R : E →L[𝕜] E} (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hR : I.mem R) :
    I.mem (R ∘L V.starProjection - U.starProjection ∘L R) ∧
      I.gauge (R ∘L V.starProjection - U.starProjection ∘L R) ≤ I.gauge R := by
  have hJU : ‖(U.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 :=
    Submodule.norm_reflectionOperator_le_one U
  have hJV : ‖(V.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 :=
    Submodule.norm_reflectionOperator_le_one V
  -- `R J_V` and `J_U R` are ideal members with gauge at most `gauge R`.
  have hrightMem : I.mem (R ∘L V.reflectionOperator) := by
    have := I.ideal_mem (ContinuousLinearMap.id 𝕜 E) V.reflectionOperator hR
    simpa using this
  have hleftMem : I.mem (U.reflectionOperator ∘L R) := by
    have := I.ideal_mem U.reflectionOperator (ContinuousLinearMap.id 𝕜 E) hR
    simpa using this
  have hrightGauge : I.gauge (R ∘L V.reflectionOperator) ≤ I.gauge R := by
    have hb := I.ideal_bound (ContinuousLinearMap.id 𝕜 E) V.reflectionOperator hR
    simp only [ContinuousLinearMap.id_comp] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge R := I.nonneg hR
    have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖ContinuousLinearMap.id 𝕜 E‖ * I.gauge R *
          ‖(V.reflectionOperator : E →L[𝕜] E)‖
        ≤ 1 * I.gauge R * 1 := by gcongr
      _ = I.gauge R := by ring
  have hleftGauge : I.gauge (U.reflectionOperator ∘L R) ≤ I.gauge R := by
    have hb := I.ideal_bound U.reflectionOperator (ContinuousLinearMap.id 𝕜 E) hR
    simp only [ContinuousLinearMap.comp_id] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge R := I.nonneg hR
    have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖(U.reflectionOperator : E →L[𝕜] E)‖ * I.gauge R *
          ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge R * 1 := by gcongr
      _ = I.gauge R := by ring
  have hnegMem : I.mem (-(U.reflectionOperator ∘L R)) := by
    simpa using I.smul_mem (-1 : 𝕜) hleftMem
  have hnegGauge : I.gauge (-(U.reflectionOperator ∘L R)) =
      I.gauge (U.reflectionOperator ∘L R) := by
    have h := I.gauge_smul (-1 : 𝕜) hleftMem
    simpa using h
  have hdiffMem : I.mem (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) := by
    have := I.add_mem hrightMem hnegMem
    simpa [sub_eq_add_neg] using this
  have hdiffGauge :
      I.gauge (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) ≤
        I.gauge R + I.gauge R := by
    have ht := I.triangle hrightMem hnegMem
    rw [hnegGauge] at ht
    have hrw : R ∘L V.reflectionOperator + -(U.reflectionOperator ∘L R) =
        R ∘L V.reflectionOperator - U.reflectionOperator ∘L R := by
      rw [sub_eq_add_neg]
    rw [hrw] at ht
    linarith
  rw [projectionCross_eq_reflectionPinch R U V]
  refine ⟨I.smul_mem _ hdiffMem, ?_⟩
  rw [I.gauge_smul _ hdiffMem]
  have hnorm : ‖((2 : 𝕜)⁻¹)‖ = 1 / 2 := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [hnorm]
  linarith

end OperatorModulus

end DavisKahanExt
end TauCeti
